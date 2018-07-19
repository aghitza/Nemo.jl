###############################################################################
#
#   qadic.jl : flint qadic numbers
#
###############################################################################

export FlintQadicField, qadic, prime, teichmuller, log

###############################################################################
#
#   Data type and parent object methods
#
###############################################################################

doc"""
    O(R::FlintQadicField, m::fmpz)
> Construct the value $0 + O(p^n)$ given $m = p^n$. An exception results if $m$
> is not found to be a power of `p = prime(R)`.
"""
function O(R::FlintQadicField, m::fmpz)
   if isone(m)
      N = 0
   else
      p = prime(R)
      if m == p
         N = 1
      else
         N = flog(m, p)
         p^(N) != m && error("Not a power of p in p-adic O()")
      end
   end
   d = qadic(N)
   d.parent = R
   return d
end

doc"""
    O(R::FlintQadicField, m::fmpq)
> Construct the value $0 + O(p^n)$ given $m = p^n$. An exception results if $m$
> is not found to be a power of `p = prime(R)`.
"""
function O(R::FlintQadicField, m::fmpq)
   d = denominator(m)
   if isone(d)
      return O(R, numerator(m))
   end
   !isone(numerator(m)) && error("Not a power of p in p-adic O()")
   p = prime(R)
   if d == p
      N = -1
   else
     N = -flog(d, p)
     p^(-N) != d && error("Not a power of p in p-adic O()")
   end
   r = qadic(N)
   r.parent = R
   return r
end

doc"""
    O(R::FlintQadicField, m::Integer)
> Construct the value $0 + O(p^n)$ given $m = p^n$. An exception results if $m$
> is not found to be a power of `p = prime(R)`.
"""
O(R::FlintQadicField, m::Integer) = O(R, fmpz(m))

elem_type(::Type{FlintQadicField}) = qadic

doc"""
    base_ring(a::FlintQadicField)
> Returns `Union{}` as this field is not dependent on another field.
"""
base_ring(a::FlintQadicField) = Union{}

doc"""
    base_ring(a::qadic)
> Returns `Union{}` as this field is not dependent on another field.
"""
base_ring(a::qadic) = Union{}

doc"""
    parent(a::qadic)
> Returns the parent of the given p-adic field element.
"""
parent(a::qadic) = a.parent

isdomain_type(::Type{qadic}) = true

isexact_type(R::Type{qadic}) = false

function check_parent(a::qadic, b::qadic)
   parent(a) != parent(b) &&
      error("Incompatible qadic rings in qadic operation")
end

parent_type(::Type{qadic}) = FlintQadicField

###############################################################################
#
#   Basic manipulation
#
###############################################################################

function Base.deepcopy_internal(a::qadic, dict::ObjectIdDict)
   z = parent(a)()
   ccall((:qadic_set, :libflint), Void,
         (Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}), z, a, parent(a))
   return z
end

function Base.hash(a::qadic, h::UInt)
   return xor(hash(lift(FlintQQ, a), h), xor(hash(prime(parent(a)), h), h))
end

function degree(R::FlintQadicField)
   return ccall((:qadic_ctx_degree, :libflint), Int, (Ref{FlintQadicField}, ), R)
end

doc"""
    prime(R::FlintQadicField)
> Return the prime $q$ for the given $q$-adic field.
"""
function prime(R::FlintQadicField)
   z = fmpz()
   ccall((:padic_ctx_pow_ui, :libflint), Void,
         (Ref{fmpz}, Int, Ref{FlintQadicField}), z, 1, R)
   return z
end

doc"""
    precision(a::qadic)
> Return the precision of the given $q$-adic field element, i.e. if the element
> is known to $O(p^n)$ this function will return $n$.
"""
precision(a::qadic) = a.N

doc"""
    valuation(a::qadic)
> Return the valuation of the given $q$-adic field element, i.e. if the given
> element is divisible by $p^n$ but not a higher power of $q$ then the function
> will return $n$.
"""
valuation(a::qadic) = ccall((:qadic_val, :libflint), Int, (Ref{qadic}, ), a)

doc"""
    zero(R::FlintQadicField)
> Return zero in the given $q$-adic field, to the default precision.
"""
function zero(R::FlintQadicField)
   z = qadic(R.prec_max)
   ccall((:qadic_zero, :libflint), Void, (Ref{qadic},), z)
   z.parent = R
   return z
end

doc"""
    one(R::FlintQadicField)
> Return zero in the given $q$-adic field, to the default precision.
"""
function one(R::FlintQadicField)
   z = qadic(R.prec_max)
   ccall((:qadic_one, :libflint), Void, (Ref{qadic},), z)
   z.parent = R
   return z
end

doc"""
    iszero(a::qadic)
> Return `true` if the given p-adic field element is zero, otherwise return
> `false`.
"""
iszero(a::qadic) = Bool(ccall((:qadic_is_zero, :libflint), Cint,
                              (Ref{qadic},), a))

doc"""
    isone(a::qadic)
> Return `true` if the given p-adic field element is one, otherwise return
> `false`.
"""
isone(a::qadic) = Bool(ccall((:qadic_is_one, :libflint), Cint,
                             (Ref{qadic},), a))

doc"""
    isunit(a::qadic)
> Return `true` if the given p-adic field element is invertible, i.e. nonzero,
> otherwise return `false`.
"""
isunit(a::qadic) = !Bool(ccall((:qadic_is_zero, :libflint), Cint,
                              (Ref{qadic},), a))

###############################################################################
#
#   AbstractString I/O
#
###############################################################################

function show(io::IO, x::qadic)
   R = FlintPadicField(prime(parent(x)), parent(x).prec_max)
   for i in 0:degree(parent(x))
     z = R()
     ccall((:padic_poly_get_coeff_padic, :libflint), Void, (Ref{padic}, Ref{qadic}, Int, Ref{FlintQadicField}), z, x, i, parent(x))
     print(io, "(")
     print(io, z)
     print(io, ")")
     if i < degree(parent(x))
       print(io, "*a^$i + ")
     else
       print(io, "*a^$i")
     end
   end
   print("\n")
end

function show(io::IO, R::FlintQadicField)
   print(io, "Unramified extension of $(prime(R))-adic numbers of degree $(degree(R))")
end

needs_parentheses(x::qadic) = true

isnegative(x::qadic) = false

show_minus_one(::Type{qadic}) = true

###############################################################################
#
#   Canonicalisation
#
###############################################################################

canonical_unit(x::qadic) = x

###############################################################################
#
#   Unary operators
#
###############################################################################

function -(x::qadic)
   if iszero(x)
      return x
   end
   ctx = parent(x)
   z = qadic(x.N)
   ccall((:qadic_neg, :libflint), Void,
         (Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}),
                     z, x, ctx)
   z.parent = ctx
   return z
end

###############################################################################
#
#   Binary operators
#
###############################################################################

function +(x::qadic, y::qadic)
   check_parent(x, y)
   ctx = parent(x)
   z = qadic(min(x.N, y.N))
   z.parent = ctx
   ccall((:qadic_add, :libflint), Void,
         (Ref{qadic}, Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}),
               z, x, y, ctx)
   return z
end

function -(x::qadic, y::qadic)
   check_parent(x, y)
   ctx = parent(x)
   z = qadic(min(x.N, y.N))
   z.parent = ctx
   ccall((:qadic_sub, :libflint), Void,
         (Ref{qadic}, Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}),
                  z, x, y, ctx)
   return z
end

function *(x::qadic, y::qadic)
   check_parent(x, y)
   ctx = parent(x)
   z = qadic(min(x.N + valuation(y), y.N + valuation(x)))
   z.parent = ctx
   ccall((:qadic_mul, :libflint), Void,
         (Ref{qadic}, Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}),
               z, x, y, ctx)
   return z
end

###############################################################################
#
#   Ad hoc binary operators
#
###############################################################################

+(a::qadic, b::Integer) = a + parent(a)(b)

+(a::qadic, b::fmpz) = a + parent(a)(b)

+(a::qadic, b::fmpq) = a + parent(a)(b)

+(a::Integer, b::qadic) = b + a

+(a::fmpz, b::qadic) = b + a

+(a::fmpq, b::qadic) = b + a

-(a::qadic, b::Integer) = a - parent(a)(b)

-(a::qadic, b::fmpz) = a - parent(a)(b)

-(a::qadic, b::fmpq) = a - parent(a)(b)

-(a::Integer, b::qadic) = parent(b)(a) - b

-(a::fmpz, b::qadic) = parent(b)(a) - b

-(a::fmpq, b::qadic) = parent(b)(a) - b

*(a::qadic, b::Integer) = a*parent(a)(b)

*(a::qadic, b::fmpz) = a*parent(a)(b)

*(a::qadic, b::fmpq) = a*parent(a)(b)

*(a::Integer, b::qadic) = b*a

*(a::fmpz, b::qadic) = b*a

*(a::fmpq, b::qadic) = b*a

###############################################################################
#
#   Comparison
#
###############################################################################

function ==(a::qadic, b::qadic)
   check_parent(a, b)
   ctx = parent(a)
   z = qadic(min(a.N, b.N))
   ccall((:qadic_sub, :libflint), Void,
         (Ref{qadic}, Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}),
               z, a, b, ctx)
   return Bool(ccall((:qadic_is_zero, :libflint), Cint,
                (Ref{qadic},), z))
end

function isequal(a::qadic, b::qadic)
   if parent(a) != parent(b)
      return false
   end
   return a.N == b.N && a == b
end

###############################################################################
#
#   Ad hoc comparison
#
###############################################################################

==(a::qadic, b::Integer) = a == parent(a)(b)

==(a::qadic, b::fmpz) = a == parent(a)(b)

==(a::qadic, b::fmpq) = a == parent(a)(b)

==(a::Integer, b::qadic) = parent(b)(a) == b

==(a::fmpz, b::qadic) = parent(b)(a) == b

==(a::fmpq, b::qadic) = parent(b)(a) == b

###############################################################################
#
#   Powering
#
###############################################################################

function ^(a::qadic, n::fmpz)
   ctx = parent(a)
   z = qadic(a.N + (Int(n) - 1)*valuation(a))
   z.parent = ctx
   ccall((:qadic_pow, :libflint), Void,
                 (Ref{qadic}, Ref{qadic}, Ref{fmpz}, Ref{FlintQadicField}),
               z, a, n, ctx)
   return z
end

###############################################################################
#
#   Exact division
#
###############################################################################

function divexact(a::qadic, b::qadic)
   iszero(b) && throw(DivideError())
   return a * inv(b)
end

#function divexact(a::qadic, b::qadic)
#   iszero(b) && throw(DivideError())
#   check_parent(a, b)
#   ctx = parent(a)
#   bv = valuation(b)
#   av = valuation(a)
#   z = qadic(min(a.N - bv, b.N - 2*bv + av))
#   z.parent = ctx
#   ccall((:qadic_div, :libflint), Cint,
#         (Ref{qadic}, Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}),
#               z, a, b, ctx)
#   return z
#end

###############################################################################
#
#   Ad hoc exact division
#
###############################################################################

divexact(a::qadic, b::Integer) = a*(fmpz(1)//fmpz(b))

divexact(a::qadic, b::fmpz) = a*(1//b)

divexact(a::qadic, b::fmpq) = a*inv(b)

divexact(a::Integer, b::qadic) = fmpz(a)*inv(b)

divexact(a::fmpz, b::qadic) = inv((fmpz(1)//a)*b)

divexact(a::fmpq, b::qadic) = inv(inv(a)*b)

###############################################################################
#
#   Inversion
#
###############################################################################

doc"""
    inv(a::qadic)
> Returns $a^{-1}$. If $a = 0$ a `DivideError()` is thrown.
"""
function inv(a::qadic)
   iszero(a) && throw(DivideError())
   ctx = parent(a)
   z = qadic(a.N - 2*valuation(a))
   z.parent = ctx
   ccall((:qadic_inv, :libflint), Cint,
         (Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}), z, a, ctx)
   return z
end

###############################################################################
#
#   Divides
#
###############################################################################

doc"""
    divides(f::qadic, g::qadic)
> Returns a pair consisting of a flag which is set to `true` if $g$ divides
> $f$ and `false` otherwise, and a value $h$ such that $f = gh$ if
> such a value exists. If not, the value of $h$ is undetermined.
"""
function divides(a::qadic, b::qadic)
   if iszero(a)
     return true, zero(parent(a))
   end
   if iszero(b)
     return false, zero(parent(a))
   end
   return true, divexact(a, b)
end

###############################################################################
#
#   GCD
#
###############################################################################

doc"""
    gcd(x::qadic, y::qadic)
> Returns the greatest common divisor of $x$ and $y$, i.e. the function returns
> $1$ unless both $a$ and $b$ are $0$, in which case it returns $0$.
"""
function gcd(x::qadic, y::qadic)
   check_parent(x, y)
   if iszero(x) && iszero(y)
      z = zero(parent(x))
   else
      z = one(parent(x))
   end
   return z
end

###############################################################################
#
#   Square root
#
###############################################################################

doc"""
    sqrt(a::qadic)
> Return the $q$-adic square root of $a$. We define this only when the
> valuation of $a$ is even. The precision of the output will be
> precision$(a) -$ valuation$(a)/2$. If the square root does not exist, an
> exception is thrown.
"""
function Base.sqrt(a::qadic)
   av = valuation(a)
   (av % 2) != 0 && error("Unable to take qadic square root")
   ctx = parent(a)
   z = qadic(a.N - div(av, 2))
   z.parent = ctx
   res = Bool(ccall((:qadic_sqrt, :libflint), Cint,
                    (Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}), z, a, ctx))
   !res && error("Square root of p-adic does not exist")
   return z
end

###############################################################################
#
#   Special functions
#
###############################################################################

doc"""
    exp(a::qadic)
> Return the $q$-adic exponential of $a$. We define this only when the
> valuation of $a$ is positive (unless $a = 0$). The precision of the output
> will be the same as the precision of the input. If the input is not valid an
> exception is thrown.
"""
function Base.exp(a::qadic)
   !iszero(a) && valuatoin(a) <= 0 && throw(DomainError())
   ctx = parent(a)
   z = qadic(a.N)
   z.parent = ctx
   res = Bool(ccall((:qadic_exp, :libflint), Cint,
                    (Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}), z, a, ctx))
   !res && error("Unable to compute exponential")
   return z
end

doc"""
    log(a::qadic)
> Return the $q$-adic logarithm of $a$. We define this only when the valuation
> of $a$ is zero (but not for $a == 0$). The precision of the output will be
> the same as the precision of the input. If the input is not valid an
> exception is thrown.
"""
function log(a::qadic)
   av = valuation(a)
   (av > 0 || av < 0 || iszero(a)) && throw(DomainError())
   ctx = parent(a)
   z = qadic(a.N)
   z.parent = ctx
   res = Bool(ccall((:qadic_log, :libflint), Cint,
                    (Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}), z, a, ctx))
   !res && error("Unable to compute logarithm")
   return z
end

doc"""
    teichmuller(a::qadic)
> Return the Teichmuller lift of the $q$-adic value $a$. We require the
> valuation of $a$ to be nonnegative. The precision of the output will be the
> same as the precision of the input. For convenience, if $a$ is congruent to
> zero modulo $q$ we return zero. If the input is not valid an exception is
> thrown.
"""
function teichmuller(a::qadic)
   valuation(a) < 0 && throw(DomainError())
   ctx = parent(a)
   z = qadic(a.N)
   z.parent = ctx
   ccall((:qadic_teichmuller, :libflint), Void,
         (Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}), z, a, ctx)
   return z
end

###############################################################################
#
#   Unsafe operators
#
###############################################################################

function zero!(z::qadic)
   z.N = parent(z).prec_max
   ctx = parent(z)
   ccall((:qadic_zero, :libflint), Void,
         (Ref{qadic}, Ref{FlintQadicField}), z, ctx)
   return z
end

function mul!(z::qadic, x::qadic, y::qadic)
   z.N = min(x.N + valuation(y), y.N + valuation(x))
   ctx = parent(x)
   ccall((:qadic_mul, :libflint), Void,
         (Ref{qadic}, Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}),
               z, x, y, ctx)
   return z
end

function addeq!(x::qadic, y::qadic)
   x.N = min(x.N, y.N)
   ctx = parent(x)
   ccall((:qadic_add, :libflint), Void,
         (Ref{qadic}, Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}),
               x, x, y, ctx)
   return x
end

function addeq!(z::qadic, x::qadic, y::qadic)
   z.N = min(x.N, y.N)
   ctx = parent(x)
   ccall((:qadic_add, :libflint), Void,
         (Ref{qadic}, Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}),
               z, x, y, ctx)
   return z
end

###############################################################################
#
#   Conversions and promotions
#
###############################################################################

promote_rule(::Type{qadic}, ::Type{T}) where {T <: Integer} = qadic

promote_rule(::Type{qadic}, ::Type{fmpz}) = qadic

promote_rule(::Type{qadic}, ::Type{fmpq}) = qadic

promote_rule(::Type{qadic}, ::Type{padic}) = qadic

###############################################################################
#
#   Parent object overloads
#
###############################################################################

function (R::FlintQadicField)()
   z = qadic(R.prec_max)
   z.parent = R
   return z
end

function gen(R::FlintQadicField)
   z = qadic(R.prec_max)
   ccall((:qadic_gen, :libflint), Void,
         (Ref{qadic}, Ref{FlintQadicField}), z, R)
   z.parent = R
   return z
end

function (R::FlintQadicField)(a::UInt)
   z = qadic(R.prec_max)
   ccall((:qadic_set_ui, :libflint), Void,
         (Ref{qadic}, UInt, Ref{FlintQadicField}), z, a, R)
   z.parent = R
   return z
end

function (R::FlintQadicField)(a::Int)
   z = qadic(R.prec_max)
   ccall((:padic_poly_set_si, :libflint), Void,
         (Ref{qadic}, Int, Ref{FlintQadicField}), z,a, R)
   z.parent = R
   return z
end

function (R::FlintQadicField)(n::fmpz)
   if isone(n)
      N = 0
   else
      p = prime(R)
      N, = remove(n, p)
   end
   z = qadic(N + R.prec_max)
   ccall((:padic_poly_set_fmpz, :libflint), Void,
         (Ref{qadic}, Ref{fmpz}, Ref{FlintQadicField}), z, n, R)
   z.parent = R
   return z
end

function (R::FlintQadicField)(n::fmpq)
   m = denominator(n)
   if isone(m)
      return R(numerator(n))
   end
   p = prime(R)
   if m == p
      N = -1
   else
     N = -flog(m, p)
   end
   z = qadic(N + R.prec_max)
   ccall((:padic_poly_set_fmpq, :libflint), Void,
         (Ref{qadic}, Ref{fmpq}, Ref{FlintQadicField}), z, n, R)
   z.parent = R
   return z
end

(R::FlintQadicField)(n::Integer) = R(fmpz(n))

function (R::FlintQadicField)(n::qadic)
   parent(n) != R && error("Unable to coerce into q-adic field")
   return n
end

###############################################################################
#
#   FlintQadicField constructor
#
###############################################################################

# inner constructor is also used directly

doc"""
    FlintQadicField(p::Integer, d::Int, prec::Int)
> Returns the parent object for the $q$-adic field for given prime $p$ and
> degree $d$, where the default absolute precision of elements of the field
is given by `prec`.
"""
function FlintQadicField(p::Integer, d::Int, prec::Int)
   return FlintQadicField(fmpz(p), d, prec)
end
