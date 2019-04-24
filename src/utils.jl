struct Error <: Exception
    str::String
    T
    code
end

Error(buf::AbstractString, T, code, pos, totallen) = Error(buf, T, code)
Error(buf::AbstractVector{UInt8}, T, code, pos, totallen) = Error(String(copy(buf)), T, code)

function Error(buf::IO, T, code, pos, totallen)
    fastseek!(buf, pos)
    bytes = read(buf, totallen)
    return Error(String(bytes), T, code)
end

function Base.showerror(io::IO, e::Error)
    c = e.code
    println(io, "Parsers.Error ($(codes(c))):")
    println(io, text(c))
    println(io, "attempted to parse $(e.T) from: \"$(escape_string(e.str))\"")
end

const ReturnCode = Int16

const SUCCESS = 0b0000000000000000 % ReturnCode
const INVALID = 0b1000000000000000 % ReturnCode

# success flags
const OK                   = 0b0000000000000001 % ReturnCode
const SENTINEL             = 0b0000000000000010 % ReturnCode

# property flags
const QUOTED               = 0b0000000000000100 % ReturnCode
const DELIMITED            = 0b0000000000001000 % ReturnCode
const NEWLINE              = 0b0000000000010000 % ReturnCode
const EOF                  = 0b0000000000100000 % ReturnCode
const ESCAPED_STRING       = 0b0000001000000000 % ReturnCode

# invalid flags
const INVALID_QUOTED_FIELD = 0b1000000001000000 % ReturnCode
const INVALID_DELIMITER    = 0b1000000010000000 % ReturnCode
const OVERFLOW             = 0b1000000100000000 % ReturnCode

succeeded(x::ReturnCode) = x > 0
ok(x::ReturnCode) = (x & (OK | INVALID)) == OK
invalid(x::ReturnCode) = x < 0
sentinel(x::ReturnCode) = (x & SENTINEL) == SENTINEL
quoted(x::ReturnCode) = (x & QUOTED) == QUOTED
delimited(x::ReturnCode) = (x & DELIMITED) == DELIMITED
newline(x::ReturnCode) = (x & NEWLINE) == NEWLINE
escapedstring(x::ReturnCode) = (x & ESCAPED_STRING) == ESCAPED_STRING
invalidquotedfield(x::ReturnCode) = (x & INVALID_QUOTED_FIELD) == INVALID_QUOTED_FIELD
invaliddelimiter(x::ReturnCode) = (x & INVALID_DELIMITER) == INVALID_DELIMITER
overflow(x::ReturnCode) = (x & OVERFLOW) == OVERFLOW
quotednotescaped(x::ReturnCode) = (x & (QUOTED | ESCAPED_STRING)) == QUOTED

memcmp(a::Ptr{UInt8}, b::Ptr{UInt8}, len::Int) = ccall(:memcmp, Cint, (Ptr{UInt8}, Ptr{UInt8}, Csize_t), a, b, len) == 0

@inline function checksentinel(source::AbstractVector{UInt8}, pos, len, sentinel, debug)
    sentinelpos = 0
    startptr = pointer(source, pos)
    # sentinel is an iterable of Tuple{Ptr{UInt8}, Int}, sorted from longest sentinel string to shortest
    for (ptr, ptrlen) in sentinel
        if pos + ptrlen - 1 <= len
            match = memcmp(startptr, ptr, ptrlen)
            if match
                if debug
                    println("matched sentinel value: \"$(escape_string(unsafe_string(ptr, ptrlen)))\"")
                end
                sentinelpos = pos + ptrlen
                break
            end
        end
    end
    return sentinelpos
end

@inline function checksentinel(source::IO, pos, len, sentinel, debug)
    sentinelpos = 0
    origpos = position(source)
    for (ptr, ptrlen) in sentinel
        matched = match!(source, ptr, ptrlen)
        if matched
            if debug
                println("matched sentinel value: \"$(escape_string(unsafe_string(ptr, ptrlen)))\"")
            end
            sentinelpos = pos + ptrlen
            break
        end
    end
    fastseek!(source, origpos)
    return sentinelpos
end

@inline function checkdelim(source::AbstractVector{UInt8}, pos, len, (ptr, ptrlen))
    startptr = pointer(source, pos)
    delimpos = pos
    if pos + ptrlen - 1 <= len
        match = memcmp(startptr, ptr, ptrlen)
        if match
            delimpos = pos + ptrlen
        end
    end
    return delimpos
end

@inline function checkdelim(source::IO, pos, len, (ptr, ptrlen))
    delimpos = pos
    matched = match!(source, ptr, ptrlen)
    if matched
        delimpos = pos + ptrlen
    end
    return delimpos
end

@inline function match!(source::IO, ptr, ptrlen)
    b = peekbyte(source)
    c = unsafe_load(ptr)
    if b != c
        return false
    elseif ptrlen == 1
        incr!(source)
        return true
    end
    pos = position(source)
    i = 1
    while true
        incr!(source)
        if Base.eof(source)
            fastseek!(source, pos)
            return false
        end
        b = peekbyte(source)
        c = unsafe_load(ptr + i)
        if b != c
            fastseek!(source, pos)
            return false
        elseif i == ptrlen - 1
            break
        end
        i += 1
    end
    incr!(source)
    return true
end

"""
    Parsers.fastseek!(io::IO, n::Integer)

    Without valididty checks, seek an `IO` to desired byte position `n`. Used in Parsers.jl to
    seek back to a previous location already parsed.
"""
function fastseek! end

fastseek!(io::IO, n::Integer) = seek(io, n)
function fastseek!(io::IOBuffer, n::Integer)
    io.ptr = n + 1
    return
end
fastseek!(io::AbstractVector{UInt8}, n::Integer) = nothing

"""
    Parsers.readbyte(io::IO)::UInt8

    Consume a single byte from an `IO` without checking `eof(io)`.
"""
function readbyte end

"""
    Parsers.peekbyte(io::IO)::UInt8

    Return, but do not consume, the next byte from an `IO` without checking `eof(io)`.
"""
function peekbyte end

incr!(io::IO) = readbyte(io)
readbyte(from::IO) = Base.read(from, UInt8)
peekbyte(from::IO) = UInt8(Base.peek(from))

function readbyte(from::IOBuffer)
    i = from.ptr
    @inbounds byte = from.data[i]
    from.ptr = i + 1
    return byte
end

function peekbyte(from::IOBuffer)
    @inbounds byte = from.data[from.ptr]
    return byte
end

function incr!(from::IOBuffer)
    from.ptr += 1
    return
end

incr!(from::AbstractVector{UInt8}) = nothing
peekbyte(from::IO, pos) = peekbyte(from)
function peekbyte(from::AbstractVector{UInt8}, pos)
    @inbounds b = from[pos]
    return b
end

eof(source::AbstractVector{UInt8}, pos::Integer, len::Integer) = pos > len
eof(source::IO, pos::Integer, len::Integer) = Base.eof(source)

function text(r)
    str = ""
    if r & QUOTED > 0
        str = "encountered an opening quote character, initial value parsing "
    else
        str = "initial value parsing "
    end
    if r & OK > 0
        str *= "succeeded"
    else
        str *= "failed"
    end
    if r & (~INVALID & OVERFLOW) > 0
        str *= ", value overflowed"
    end
    if r & SENTINEL > 0
        str *= ", a sentinel value was parsed"
    end
    if r & ESCAPED_STRING > 0
        str *= ", encountered escape character"
    end
    if r & (~INVALID & INVALID_QUOTED_FIELD) > 0
        str *= ", invalid quoted value"
    end
    if r & DELIMITED > 0
        str *= ", a valid delimiter was parsed"
    end
    if r & NEWLINE > 0
        str *= ", a newline was encountered"
    end
    if r & EOF > 0
        str *= ", reached EOF"
    end
    if r & (~INVALID & INVALID_DELIMITER) > 0
        str *= ", invalid delimiter"
    end
    return str
end

codes(r) = chop(chop(string(
    ifelse(r > 0, "SUCCESS: ", "INVALID: "),
    ifelse(r & OK > 0, "OK | ", ""),
    ifelse(r & SENTINEL > 0, "SENTINEL | ", ""),
    ifelse(r & QUOTED > 0, "QUOTED | ", ""),
    ifelse(r & ESCAPED_STRING > 0, "ESCAPED_STRING | ", ""),
    ifelse(r & DELIMITED > 0, "DELIMITED | ", ""),
    ifelse(r & NEWLINE > 0, "NEWLINE | ", ""),
    ifelse(r & EOF > 0, "EOF | ", ""),
    ifelse(r & (~INVALID & INVALID_QUOTED_FIELD) > 0, "INVALID_QUOTED_FIELD | ", ""),
    ifelse(r & (~INVALID & INVALID_DELIMITER) > 0, "INVALID_DELIMITER | ", ""),
    ifelse(r & (~INVALID & OVERFLOW) > 0, "OVERFLOW | ", "")
)))

defaultdateformat(T) = Dates.dateformat""
defaultdateformat(::Type{T}) where {T <: Dates.TimeType} = Dates.default_format(T)
ptrlen(s::String) = (pointer(s), sizeof(s))