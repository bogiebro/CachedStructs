module CachedStructs
export cached
using MLStyle

get_var(syntax) = @match syntax begin
    :( $a :: $b )  => a
    :( $a :: $ty = $f) => a
    _ => missing
end

rewrite_f(f, accum, vs) = @match f begin
    a::Symbol && GuardBy(x->x ∈ vs) => begin
        push!(accum, a)
        Expr(:., :self, QuoteNode(a))
    end
    Expr(sym, args...) => Expr(sym, map(x->rewrite_f(x, accum, vs), args)...)
    other => other
end

rewrite_field(syntax) = @match syntax begin
    :( $a :: $ty = $f) => :($a :: Union{$ty, Nothing})
    other => other
end

prep_accessor(syntax, g, vars) = @match syntax begin
    :( $a :: $ty = $f) => begin
        accum = Symbol[]
        field = Expr(:., :self, QuoteNode(a))
        getter = quote
            if $g == $(QuoteNode(a)) && isnothing($field)
                $field = $(rewrite_f(f, accum, vars))
            end
        end
        setter = quote
            if $g ∈ $accum
                $field = nothing
            end
        end
        (getter, setter)
    end
    other => missing
end

make_getfield(name, g, ite) = :(Base.getproperty(self:: $name , $(g) ::Symbol) = $ite )

make_setfield(name, g, ite) = :(Base.setproperty!(self:: $name , $(g) ::Symbol, val) = $ite )

make_constructor(name, vars) = :(
    $(Expr(:call, name, [Expr(:kw, a, nothing) for a in vars]...)) = 
    $(Expr(:call, name, vars...)))

rewrite_struct(syntax) = @match syntax begin
    Expr(:struct, _, name, Expr(:block, b...)) => begin
        vars = skipmissing(map(get_var, b))
        struct_decl = Expr(:struct, true, name, Expr(:block, map(rewrite_field, b)...))
        g = gensym(:prop)
        fallback_getter = :(getfield(self, $g))
        fallback_setter = :(setfield!(self, $g, val))
        acc_vals = skipmissing(map(x->prep_accessor(x, g, vars), b))
        getters = Expr(:block, first.(acc_vals)..., fallback_getter)
        setters = Expr(:block, [setter for (_, setter) in acc_vals]..., fallback_setter)
        esc(quote
            $struct_decl
            $(make_constructor(name, vars))
            $(make_getfield(name, g, getters))
            $(make_setfield(name, g, setters))
        end)
    end
end

macro cached(syntax)
    rewrite_struct(syntax)
end

# Say we have a = f(b,c) and b = g(c, a)
# If we assign c, that invalidates both a and b. 
# But to compute a, we need b. And to compute b, we need a. 
# So we really need to be able to assign multiple at once. 
# Maybe what we want is an immutable struct. We can assemble it with exactly the params we want. 
# BUT WAIT: this is overkill for our use case. We never modify, only construct new ones. 

end # module
