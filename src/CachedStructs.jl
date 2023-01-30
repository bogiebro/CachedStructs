module CachedStructs
export @cached
using MLStyle

get_var(syntax) = @match syntax begin
    :( $a :: $b )  => a
    :( $a :: $ty = $f) => a
    _ => missing
end

rewrite_f(f, vs) = @match f begin
    a::Symbol && GuardBy(x->x ∈ vs) => Expr(:., :self, QuoteNode(a))
    Expr(sym, args...) => Expr(sym, map(x->rewrite_f(x, vs), args)...)
    other => other
end

rewrite_field(syntax) = @match syntax begin
    :( $a :: $ty = $f) => :($a :: Union{$ty, Nothing})
    other => other
end

prep_accessor(syntax, g, vars) = @match syntax begin
    :( $a :: $ty = $f) => begin
        quote
            if $g == $(QuoteNode(a)) && isnothing(getfield(self, $g))
                setfield!(self, $g, $(rewrite_f(f, vars)))
            end
        end
    end
    other => missing
end

make_getfield(name, g, ite) = :(Base.getproperty(self:: $name , $(g) ::Symbol) = $ite )

function make_constructor(name, vars)
    kwvals = [Expr(:kw, a, nothing) for a in vars]
    :($(Expr(:call, name, Expr(:parameters, kwvals...))) = 
        $(Expr(:call, name, vars...)))
end

extract_name(decl) = @match decl begin
    :($(name){$(args...)} <: $parent) => name
    :($(name){$(args...)}) => name
    :($name <: $parent) => name
    other => other
end

rewrite_struct(syntax) = @match syntax begin
    Expr(:struct, _, decl, Expr(:block, b...)) => begin
        vars = skipmissing(map(get_var, b))
        struct_decl = Expr(:struct, true, decl, Expr(:block, map(rewrite_field, b)...))
        name = extract_name(decl)
        g = gensym(:prop)
        fallback_getter = :(getfield(self, $g))
        acc_vals = skipmissing(map(x->prep_accessor(x, g, vars), b))
        getters = Expr(:block, acc_vals..., fallback_getter)
        esc(quote
            $struct_decl
            $(make_constructor(name, vars))
            $(make_getfield(name, g, getters))
        end)
    end
end

macro cached(syntax)
    rewrite_struct(syntax)
end

# What's going wrong?

end # module
