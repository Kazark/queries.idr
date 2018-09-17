# The struggle and headache/heartache here

An investigation into DSLs with free monads and queries etc, using Idris

I have been using a lot of query/command style DSLs in my F# code. I define
functor instances for the queries; it helps many things, such as composability.
When I hit a problem where I need to both unify 0 queries with 1 query, and
1 query with 2 queries I recognize the need for some sort of monoid. I usually
implement this as a free monad. This is however painful given F#'s limitations.

I would like to know how I would work if I did not have these sorts of
limitations. Immediately though I hit upon the fact that my typical
Haskell-style `Free` definition results in partial code in Idris, since it is
not strictly positive! After investigating what that means, I see the problem
and grapple with it a lot... It seems very hard to both retain totality and my
functor/applicative/monad instances, all at the same time. However, I don't see
why, categorically, I don't see have those algebras at play. It's somewhat
dissatisfying not to be able to use idiom brackets and do notation, etc,
though. Is SizedFunctor/SizedMonad/SizedApplicative a thing? Should I just be
comfortable with this?

What if instead of relying on Free I had some way of relying on a Tree?

And once I really learn the ropes here, how do I translate it back to something
I can use in my (many, some large) F# codebases?
