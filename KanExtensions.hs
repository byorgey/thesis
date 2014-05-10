{-# LANGUAGE GADTs      #-}
{-# LANGUAGE RankNTypes #-}

module KanExtensions where

data Lan f x a where
  Lan :: (x c) -> (f c -> a) -> Lan f x a

-- one direction of the Yoneda lemma
yonedaR :: (forall a. (c -> a) -> f a) -> f c
yonedaR y = y id

yonedaL :: Functor f => f c -> (forall a. (c -> a) -> f a)
yonedaL f g = fmap g f

-- hom(-,a) turns colimits into limits
homL1 :: (forall a. Lan f x a -> g a) -> (forall a c. (x c, f c -> a) -> g a)
homL1 l (xa,fca) = l (Lan xa fca)

homL2 :: (forall a c. (x c, f c -> a) -> g a) -> (forall a. Lan f x a -> g a)
homL2 g (Lan xc fca) = g (xc, fca)

-- apply the Yoneda lemma on the RHS of the hom
step3R :: (forall c. x c -> (forall a. (f c -> a) -> g a)) -> (forall c. x c -> g (f c))
step3R f x = yonedaR (f x)

step3L :: Functor g => (forall c. x c -> g (f c)) -> (forall c. x c -> (forall a. (f c -> a) -> g a))
step3L g x = yonedaL (g x)

lanAdjointR :: (forall a. Lan f x a -> g a) -> (forall c. x c -> g (f c))
lanAdjointR l = step3R (curry (homL1 l)) -- fmap yoneda (curry (homL l . swap))

{-
    step3 (curry (homL l)) x
  = yoneda (curry (homL l) x)
  = yoneda (curry (\(xa,fca) -> l (Lan xa fca)) x)
  = yoneda ((\xa fca -> l (Lan xa fca)) x)
  = yoneda (\fca -> l (Lan x fca))
  = yoneda (l . Lan x)
  = (l . Lan x) id
  = l (Lan x id)

  In the particular case of species, we transform a polymorphic
  function l into a species morphism  \x -> l (Lan x id).

  Hmm, I don't quite get it.  Let's do the other direction.
-}

lanAdjointL :: Functor g => (forall c. x c -> g (f c)) -> (forall a. Lan f x a -> g a)
lanAdjointL g = homL2 (uncurry (step3L g))

{-

    homL2 (uncurry (step3L g)) (Lan sp m)
  = uncurry (step3L g) (sp, m)
  = step3L g sp m
  = yonedaL (g sp) m
  = fmap m (g sp)

  Here, we transform a species morphism g : F -> G.i into a
polymorphic function F^ -> G.  In particular, a value of type F^ A
consists of an L-labelled F-shape together with a mapping L -> A; we
apply g to the F-shape, resulting in an L-labelled G.i-shape; we then
map the L->A mapping over this to get a G A value.

I think this is the interesting direction.  The point is that *every*
polymorphic function on F^ A arises in this way.  I.e. every
polymorphic function has to be described by a process of splitting
into shape + data mapping, reshaping, and then re-applying the
labelling.

How is this more restrictive than just any old polymorphic function?
Note, it does depend on F. The point is that for certain functors H
(the ones that arise as H = F^ for some species F), *all* polymorphic
functions arise in this way.  It is probably the case that all Haskell
functors are analytic.  So we have to be a bit more creative to come
up with examples of non-analytic functors, which have map-commuting
polymorphic functions on them which cannot be decomposed in this way.
Well, I suppose it's not so much the *maps* that can't be decomposed
but the functors themselves.

Should Google for "non-analytic functor" and see what comes up.  Also,
read more about analytic functors in general, the way they decompose
into generating functions, etc.

Refer to Barry Jay's work here?

-}
