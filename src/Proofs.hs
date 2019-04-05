{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Proofs where

import           Data.Kind          (Type)
import           Data.Type.Equality ((:~:) (..), gcastWith)
import           Data.Void          (Void, absurd)

import           GHC.TypeLits       (ErrorMessage (..), TypeError)


----------------------------
-- length-indexed vectors --
----------------------------

-- type-level natural numbers
data Nat = Z | S Nat

type One = S Z
type Two = S One


-- vectors
data Vec :: Type -> Nat -> Type where
  VNil  :: Vec a Z
  (:>) :: a -> Vec a n -> Vec a (S n)

infixr 5 :>


-- we can write simple functions
vhead :: Vec a (S n) -> a
vhead (x:>_) = x

vlast :: Vec a (S n) -> a
vlast (x:>xs)
  = case xs of
      VNil -> x
      _:>_ -> vlast xs

vtail :: Vec a (S n) -> Vec a n
vtail (_:>VNil) = VNil
vtail (_:>xs)   = xs

vinit :: Vec a (S n) -> Vec a n
vinit (x:>xs) = vinit' x xs
  where
    -- no need for ScopedTypeVariables
    vinit' :: a -> Vec a n -> Vec a n
    vinit' _ VNil    = VNil
    vinit' y (z:>zs) = y :> vinit' z zs

vnull :: Vec a n -> Bool
vnull VNil = True
vnull _    = False

vlength :: Vec a n -> Int
vlength VNil    = 0
vlength (_:>xs) = 1 + vlength xs

vmap :: (a -> b) -> Vec a n -> Vec b n
vmap _ VNil    = VNil
vmap f (x:>xs) = f x :> vmap f xs

-- etc

-- what about appending?
-- (++>) :: Vec a n -> Vec a m -> Vec a ???






















---------------------------
-- type-level arithmetic --
---------------------------
type family a + b where
  a + Z   = a          -- (1)
  a + S b = S (a + b)  -- (2)

type family a * b where
  a * Z   = Z
  a * S b = (a * b) + a

-- now what about appending?

-- (++>) :: Vec a n -> Vec a m -> Vec a (n + m)
-- VNil ++> ys = ys

-- • Could not deduce: ('Z + m) ~ m
--   from the context: n ~ 'Z
--     bound by a pattern with constructor: VNil :: forall a. Vec a 'Z,























----------------------------
-- propositional equality --
----------------------------
zeroPlusZeroIsZero :: Z + Z :~: Z
zeroPlusZeroIsZero = Refl

plusRightIdentity :: n + Z :~: n
plusRightIdentity = Refl

-- but

-- plusLeftIdentity :: Z + n :~: n
-- plusLeftIdentity = Refl

-- • Couldn't match type ‘n’ with ‘'Z + n’























------------------------
-- proof by induction --
------------------------
-- https://en.wikipedia.org/wiki/Proofs_involving_the_addition_of_natural_numbers

-- not quite

-- ( gcastWith :: (a :~: b) -> (a ~ b => r) -> r )

-- plusLeftIdentity :: forall n. Z + S n :~: S n
-- plusLeftIdentity = gcastWith (plusLeftIdentity @n) Refl



























----------------
-- singletons --
----------------
data SNat :: Nat -> Type where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

-- implicit version
class               IsNat (n :: Nat) where nat :: SNat n
instance            IsNat Z          where nat =  SZ
instance IsNat n => IsNat (S n)      where nat =  SS nat

-- and some operations
(!+) :: SNat a -> SNat b -> SNat (a + b)
x !+ SZ     = x
x !+ (SS y) = SS (x !+ y)

(!*) :: SNat a -> SNat b -> SNat (a * b)
x !* SZ     = SZ
x !* (SS y) = (x !* y) !+ x

-- now we can write the proof
plusLeftIdentity :: SNat a -> Z + a :~: a
plusLeftIdentity SZ     = Refl
plusLeftIdentity (SS x) = gcastWith (plusLeftIdentity x) Refl

-- 10x
plusLeftIdentity' :: forall a. IsNat a => Z + a :~: a
plusLeftIdentity'
  = case nat @a of
      SZ   -> Refl
      SS x -> gcastWith (plusLeftIdentity' @a) Refl

-- and we can go crazy
plusAssoc
  :: SNat a
  -> SNat b
  -> SNat c
  -> ((a + b) + c) :~: (a + (b + c))
plusAssoc _ _ SZ = Refl
plusAssoc a b (SS c)
  -- same as wikipedia proof, but we don't have to prove the properties of
  -- addition, ghc does this for us
  = gcastWith (plusAssoc a b c) Refl


-- in case you don't believe me
plusProp2 :: SNat a -> SNat b -> (a + S b) :~: S (a + b)
plusProp2 _ _ = Refl

plusAssoc'
  :: SNat a
  -> SNat b
  -> SNat c
  -> ((a + b) + c) :~: (a + (b + c))
plusAssoc' _ _ SZ = Refl
plusAssoc' a b (SS c)
  = gcastWith (plusProp2 b (SS c))
  $ gcastWith (plusProp2 a (SS (b !+ c)))
  $ gcastWith (plusAssoc' a b c)
  $ gcastWith (plusProp2 (a !+ b) (SS c))
      Refl

-- commutativity
plusComm :: SNat a -> SNat b -> (a + b) :~: (b + a)
plusComm a      SZ      = gcastWith (plusLeftIdentity a) Refl
plusComm SZ     (SS SZ) = Refl
plusComm (SS a) (SS SZ) = gcastWith (plusComm a (SS SZ)) Refl
plusComm a k@(SS b)
  = gcastWith (plusComm a (SS SZ))
  $ gcastWith (plusAssoc b (SS SZ) a)
  $ gcastWith (plusComm a b)
  $ gcastWith (plusAssoc a k (SS SZ))
      Refl





















---------------------
-- back to vectors --
---------------------

-- whoops

-- vappend :: SNat n -> SNat m -> Vec a n -> Vec a m -> Vec a (n + m)
-- vappend SZ m VNil ys = gcastWith (plusLeftIdentity m) ys
-- vappend n m (x:>xs) ys = x :> vappend ??? m xs ys

-- ghc is smart about this
spred :: SNat (S n) -> SNat n
spred (SS n) = n


-- whoops v2

-- vappend :: SNat n -> SNat m -> Vec a n -> Vec a m -> Vec a (n + m)
-- vappend SZ m VNil ys = gcastWith (plusLeftIdentity m) ys
-- vappend n m (x:>xs) ys = x :> vappend (spred n) m xs ys

-- • Could not deduce: ('S n1 + m) ~ 'S (n1 + m)
--   from the context: n ~ 'S n1

-- let's construct a proof:

--   S n + m
-- = m + S n   (commutativity)
-- = S (m + n) (2)
-- = S (n + m) (commutativity)

ourProof :: SNat n -> SNat m -> S n + m :~: S (n + m)
ourProof n m
  = gcastWith (plusComm n m)
  $ gcastWith (plusComm m (SS n))
      Refl

-- attempt n. 100000

vappend :: SNat n -> SNat m -> Vec a n -> Vec a m -> Vec a (n + m)
vappend SZ m VNil ys = gcastWith (plusLeftIdentity m) ys
vappend n m (x:>xs) ys
  = gcastWith (ourProof pn m) (x :> vappend pn m xs ys)
  where
    pn = spred n

-- 100x
(++>)
  :: forall a n m. (IsNat n, IsNat m)
  => Vec a n
  -> Vec a m
  -> Vec a (n + m)
(++>) = vappend (nat @n) (nat @m)


-- a more difficult proof

-- intersperse for Vec a n gives a Vec with length 2 * n - 1

type family P n where
  P Z     = Z
  P (S n) = n

-- intersperse' :: forall n a. SNat n -> a -> Vec a n -> Vec a (P (Two * n))
-- intersperse' _ _ VNil = VNil
-- intersperse' _ _ l@(_:>VNil) = l
-- intersperse' n a (x:>xs)
--   = x :> a :> intersperse' pn a xs
--   where pn = spred n

-- • Could not deduce: ('S One * n1) ~ 'S (P ('S One * n1))
--   from the context: n ~ 'S n1

succPredCancelProof :: SNat n -> (n :~: Z -> Void) -> S (P n) :~: n
succPredCancelProof n nonZero
  = case n of
      SZ    -> absurd $ nonZero Refl
      SS n' -> Refl

-- works OK but undefined is not good

-- intersperse' n a (x:>xs)
--   = gcastWith (succPredCancelProof pn undefined) $ x :> a :> intersperse' pn a xs
--   where pn = spred n

-- how about constructing the 'nonZero' proof?

type family NonZero n where
  NonZero Z     = TypeError (Text "`Z` is not non-zero")
  NonZero (S n) = True ~ True

natNonZero :: NonZero n => SNat n -> n :~: Z -> Void
natNonZero _ nonZero = case nonZero of {}

intersperse' :: forall n a. SNat n -> a -> Vec a n -> Vec a (P (Two * n))
intersperse' _ _ VNil = VNil
intersperse' _ _ l@(_:>VNil) = l
intersperse' n a (x:>xs@(_:>_))  -- I lied, intersperse works without the proofs if we specify this
  = gcastWith (succPredCancelProof pn (natNonZero pn)) $ x :> a :> intersperse' pn a xs
  where pn = spred n

intersperse :: forall n a. IsNat n => a -> Vec a n -> Vec a (P (Two * n))
intersperse = intersperse' (nat @n)





















-------------
-- helpers --
-------------

instance Show a => Show (Vec a n) where
  show v = "[" ++ go v
    where go :: Show a' => Vec a' n' -> String
          go v = case v of
            VNil      -> "]"
            (x :> xs) -> show x ++ sep ++ go xs
              where sep = case xs of
                      VNil -> ""
                      _    -> ", "

x = 1 :> 2 :> 3 :> 4 :> VNil
y = 5 :> 6 :> 7 :> 8 :> 9 :> VNil
