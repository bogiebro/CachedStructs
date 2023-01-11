module CachedStructs
export cached
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

get_accessor(syntax, g, vars) = @match syntax begin
    :( $a :: $ty = $f) => quote
        if $g == $(QuoteNode(a))
            $(Expr(:., :self, QuoteNode(a))) = $(rewrite_f(f, vars))
        end
    end
    other => missing
end

make_getfield(name, g, ite) = :(Base.getproperty(self:: $name , $(g) ::Symbol) = $ite )

make_constructor(name, vars) = :(
    $(Expr(:call, name, [Expr(:kw, a, nothing) for a in vars]...)) = 
    $(Expr(:call, name, vars...)))

rewrite_struct(syntax) = @match syntax begin
    Expr(:struct, _, name, Expr(:block, b...)) => begin
        vars = skipmissing(map(get_var, b))
        struct_decl = Expr(:struct, true, name, Expr(:block, map(rewrite_field, b)...))
        g = gensym(:prop)
        fallback = :(getfield(self, $g))
        ite = Expr(:block, skipmissing(map(x->get_accessor(x, g, vars), b))..., fallback)
        esc(quote
            $struct_decl
            $(make_constructor(name, vars))
            $(make_getfield(name, g, ite))
        end)
    end
end

macro cached(syntax)
    rewrite_struct(syntax)
end

# Use:
# @cached struct Foo
#   a :: Type1
#   b :: Type2 = fn(sdsdf) 
  
# end

# It defines accessors for each field
# which do the right thing. 

end # module
