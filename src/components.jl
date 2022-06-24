# must be outermost layer
function Result(parser)
    function(::Type{T}, source, pos, len, opts::Options, ::Type{RT}=T) where {T, RT}
        startpos = pos
        code = SUCCESS
        b = eof(source, pos, len) ? 0x00 : peekbyte(source, pos)
        pl = poslen(pos, 0)
        pos, code, pl, x = parser(T, source, pos, len, b, code, pl, opts)
        tlen = pos - startpos
        if valueok(code)
            y::T = x
            return Result{RT}(code, tlen, y)
        else
            return Result{RT}(code, tlen)
        end
    end
end

function emptysentinel(parser)
    function(::Type{T}, source, pos, len, b, code, pl, opts) where {T}
        if eof(source, pos, len)
            if isempty(opts.sentinel)
                code |= SENTINEL | EOF
                pl = withmissing(pl)
            else
                code |= INVALID | EOF
            end
            return pos, code, pl, nothing
        end
        pos, code, pl, x = parser(T, source, pos, len, b, code, pl, opts)
        if pos == pl.pos
            code &= ~(OK | INVALID)
            code |= SENTINEL
            pl = withmissing(pl)
        end
        return pos, code, pl, x
    end
end

# just ' ' and '\t'
function whitespace(parser)
    function(::Type{T}, source, pos, len, b, code, pl, opts) where {T}
        # strip leading whitespace
        while b == UInt8(' ') || b == UInt8('\t')
            pos += 1
            incr!(source)
            if (quoted(code) && opts.stripquoted) || opts.stripwhitespace
                # we're in a quoted string and user has requested
                # to strip whitespace inside, OR user has requested
                # to strip whitespace outside of quoted strings
                pl = poslen(pos, 0)
            end
            if eof(source, pos, len)
                code |= INVALID | EOF
                return pos, code, pl, nothing
            end
            b = peekbyte(source, pos)
        end
        pos, code, pl, x = parser(T, source, pos, len, b, code, pl, opts)
        # strip trailing whitespace
        if !eof(code) && (!isgreedy(T) || (quoted(code) && escapedstring(code)))
            b = peekbyte(source, pos)
            while b == UInt8(' ') || b == UInt8('\t')
                pos += 1
                incr!(source)
                if eof(source, pos, len)
                    code |= EOF
                    return pos, code, pl, nothing
                end
                b = peekbyte(source, pos)
            end
        end
        return pos, code, pl, x
    end
end

function findendquoted(::Type{T}, source, pos, len, b, code, pl, opts, quoted, x) where {T}
    # for quoted fields, find the closing quote character
    # we should be positioned at the correct place to find the closing quote character if everything is as it should be
    # if we don't find the quote character immediately, something's wrong, so mark INVALID
    if quoted
        same = opts.cq == opts.e
        first = true
        # b is the first byte after oq for greedy
        while true
            # if opts.stripquoted, we need to handle it here
            # instead of in the whitespace parser for strings
            if isgreedy(T) && (!opts.stripquoted || (b != UInt8(' ') && b != UInt8('\t')))
                pl = poslen(pl.pos, (pos - pl.pos) + 1)
            end
            pos += 1
            incr!(source)
            if same && b == opts.e
                # cq = '"', e = '"', and b = '"', so we might be done
                if eof(source, pos, len)
                    # we're done! cq was last possible byte
                    code |= EOF
                    if !first && !isgreedy(T)
                        code |= INVALID
                    end
                    return pos, code, pl, x
                elseif peekbyte(source, pos) != opts.cq
                    # we're done! e wasn't followed by cq
                    if !first && !isgreedy(T)
                        code |= INVALID
                    end
                    break
                end
                # this means we had e followed by cq
                # so the next byte is escaped
                code |= ESCAPED_STRING
                pl = withescaped(pl)
                pos += 1
                incr!(source)
            elseif b == opts.e
                if eof(source, pos, len)
                    # "dangling" e, invalid
                    code |= INVALID_QUOTED_FIELD | EOF
                    return pos, code, pl, x
                end
                # e, so next byte is escaped
                code |= ESCAPED_STRING
                pl = withescaped(pl)
                pos += 1
                incr!(source)
            elseif b == opts.cq
                if !first && !isgreedy(T)
                    code |= INVALID
                end
                if eof(source, pos, len)
                    code |= EOF
                    return pos, code, pl, x
                end
                # found cq, so we're done
                break
            end
            if eof(source, pos, len)
                code |= INVALID_QUOTED_FIELD | EOF
                return pos, code, pl, x
            end
            first = false
            b = peekbyte(source, pos)
        end
    end
    return pos, code, pl, x
end

function quoted(parser)
    function(::Type{T}, source, pos, len, b, code, pl, opts) where {T}
        quoted = b == opts.oq
        if quoted
            code |= QUOTED
            pos += 1
            pl = poslen(pos, 0)
            incr!(source)
            if eof(source, pos, len)
                # "dangling" oq, not valid
                code |= INVALID_QUOTED_FIELD
                return pos, code, pl, nothing
            end
            b = peekbyte(source, pos)
        end
        pos, code, pl, x = parser(T, source, pos, len, b, code, pl, opts)
        if isgreedy(T) && quoted
            return pos, code, pl, x
        end
        if eof(code)
            if quoted
                # if we detected a quote character, it's an invalid quoted field due to eof in the middle
                code |= INVALID_QUOTED_FIELD
            end
            return pos, code, pl, x
        end
        b = peekbyte(source, pos)
        return findendquoted(T, source, pos, len, b, code, pl, opts, quoted, x)
    end
end

function sentinel(parser)
    function(::Type{T}, source, pos, len, b, code, pl, opts) where {T}
        sentinelpos = checksentinel(source, pos, len, opts.sentinel)
        pos, code, pl, x = parser(T, source, pos, len, b, code, pl, opts)
        if sentinelpos >= pos
            # if we matched a sentinel value that was as long or longer than our type value
            code &= ~(OK | INVALID | OVERFLOW)
            pos = sentinelpos
            fastseek!(source, pos - 1)
            code |= SENTINEL
            pl = withmissing(pl)
            if eof(source, pos, len)
                code |= EOF
            end
        end
        return pos, code, pl, x
    end
end

function finddelimiter(::Type{T}, source, pos, len, b, code, pl, opts, x) where {T}
    delim = opts.delim
    # now we check for a delimiter; if we don't find it, keep parsing until we do
    while true
        if !opts.ignorerepeated
            # we're checking for a single appearance of a delimiter
            if delim isa UInt8
                if b == delim
                    pos += 1
                    incr!(source)
                    code |= DELIMITED
                    break
                end
            elseif delim isa String
                predelimpos = pos
                pos = checkdelim(source, pos, len, delim)
                if pos > predelimpos
                    # found the delimiter we were looking for
                    code |= DELIMITED
                    break
                end
            else
                error()
            end
        else
            # keep parsing as long as we keep matching delims/newlines
            if delim isa UInt8
                matched = false
                matchednewline = false
                while true
                    if b == delim
                        matched = true
                        code |= DELIMITED
                        pos += 1
                        incr!(source)
                    elseif !matchednewline && b == UInt8('\n')
                        matchednewline = matched = true
                        pos += 1
                        incr!(source)
                        pos = checkcmtemptylines(source, pos, len, opts.cmt, opts.ignoreemptylines)
                        code |= NEWLINE | ifelse(eof(source, pos, len), EOF, SUCCESS)
                    elseif !matchednewline && b == UInt8('\r')
                        matchednewline = matched = true
                        pos += 1
                        incr!(source)
                        if !eof(source, pos, len) && peekbyte(source, pos) == UInt8('\n')
                            pos += 1
                            incr!(source)
                        end
                        pos = checkcmtemptylines(source, pos, len, opts.cmt, opts.ignoreemptylines)
                        code |= NEWLINE | ifelse(eof(source, pos, len), EOF, SUCCESS)
                    else
                        break
                    end
                    if eof(source, pos, len)
                        code |= EOF
                        break
                    end
                    b = peekbyte(source, pos)
                end
                if matched || eof(code)
                    break
                end
            elseif delim isa String
                matched = false
                matchednewline = false
                while true
                    predelimpos = pos
                    pos = checkdelim(source, pos, len, delim)
                    if pos > predelimpos
                        matched = true
                        code |= DELIMITED
                    elseif !matchednewline && b == UInt8('\n')
                        matchednewline = matched = true
                        pos += 1
                        incr!(source)
                        pos = checkcmtemptylines(source, pos, len, opts.cmt, opts.ignoreemptylines)
                        code |= NEWLINE | ifelse(eof(source, pos, len), EOF, SUCCESS)
                    elseif !matchednewline && b == UInt8('\r')
                        matchednewline = matched = true
                        pos += 1
                        incr!(source)
                        if !eof(source, pos, len) && peekbyte(source, pos) == UInt8('\n')
                            pos += 1
                            incr!(source)
                        end
                        pos = checkcmtemptylines(source, pos, len, opts.cmt, opts.ignoreemptylines)
                        code |= NEWLINE | ifelse(eof(source, pos, len), EOF, SUCCESS)
                    else
                        break
                    end
                    if eof(source, pos, len)
                        code |= EOF
                        break
                    end
                    b = peekbyte(source, pos)
                end
                if matched || eof(code)
                    break
                end
            else
                error()
            end
        end
        # didn't find delimiter, but let's check for a newline character
        if b == UInt8('\n')
            pos += 1
            incr!(source)
            pos = checkcmtemptylines(source, pos, len, opts.cmt, opts.ignoreemptylines)
            code |= NEWLINE | ifelse(eof(source, pos, len), EOF, SUCCESS)
            break
        elseif b == UInt8('\r')
            pos += 1
            incr!(source)
            if !eof(source, pos, len) && peekbyte(source, pos) == UInt8('\n')
                pos += 1
                incr!(source)
            end
            pos = checkcmtemptylines(source, pos, len, opts.cmt, opts.ignoreemptylines)
            code |= NEWLINE | ifelse(eof(source, pos, len), EOF, SUCCESS)
            break
        end
        if !isgreedy(T) || quoted(code)
            # didn't find delimiter or newline, so we're invalid, keep parsing until we find delimiter, newline, or len
            code |= INVALID_DELIMITER
        end
        if isgreedy(T) && (!opts.stripwhitespace || (b != UInt8(' ') && b != UInt8('\t')))
            pl = poslen(pl.pos, (pos - pl.pos) + 1)
        end
        pos += 1
        incr!(source)
        if eof(source, pos, len)
            code |= EOF
            break
        end
        b = peekbyte(source, pos)
    end
    return pos, code, pl, x
end

function delimiter(parser)
    function(::Type{T}, source, pos, len, b, code, pl, opts) where {T}
        pos, code, pl, x = parser(T, source, pos, len, b, code, pl, opts)
        if delimited(code) || eof(code) # greedy case
            return pos, code, pl, x
        end
        b = peekbyte(source, pos)
        return finddelimiter(T, source, pos, len, b, code, pl, opts, x)
    end
end
