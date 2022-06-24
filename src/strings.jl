isgreedy(::Type{T}) where {T <: AbstractString} = true
isgreedy(T) = false

function typeparser(::Type{T}, source, pos, len, b, code, pl, opts) where {T <: AbstractString}
    if quoted(code)
        return findendquoted(T, source, pos, len, b, code, pl, opts, true, nothing)
    elseif opts.delim !== nothing
        return finddelimiter(T, source, pos, len, b, code, pl, opts, nothing)
    else
        # no delimiter, so read until EOF
        while !eof(source, pos, len)
            b = peekbyte(source, pos)
            if !opts.stripwhitespace || (b != UInt8(' ') && b != UInt8('\t'))
                pl = poslen(pl.pos, (pos - pl.pos) + 1)
            end
            pos += 1
            incr!(source)
        end
        return pos, code, pl, nothing
    end
end
