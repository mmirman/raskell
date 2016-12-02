-- /show
{-# LANGUAGE
  DataKinds,
  FlexibleContexts,
  FlexibleInstances,
  FunctionalDependencies,
  KindSignatures,
  MultiParamTypeClasses,
  NoMonomorphismRestriction,
  RankNTypes,
  TypeFamilies,
  TypeOperators,
  UndecidableInstances,
  AllowAmbiguousTypes,
  GADTs,
  InstanceSigs,
  ScopedTypeVariables
 #-}

module Ordered where
--
-- Type level Nats
--
data Nat = Z | S Nat


data Cont = Lin Nat | Om Nat | Reg Nat | None

--
-- Type level Nat equality
--

class EQ (x::Nat) (y::Nat) (b::Bool) | x y -> b
instance {-# OVERLAPPABLE #-} (b ~ False) => EQ x y b
instance {-# OVERLAPPING #-} EQ x x True


class UseTwo (v::Nat) (i::[Cont]) (o::[Cont]) | v i -> o

instance (UseTwo v i o) => UseTwo v (None : i) (None : o)
instance (UseTwo v i o) => UseTwo v (Lin x : i) (Lin x : o)
instance (UseTwo v i o) => UseTwo v (Reg x : i) (Reg x : o)

instance UseTwo x (Om (S x) : Om x : i) (None : None : i)



--
-- Type level machinery for consuming a variable in a list of variables.
--
class ConsumeOrd (v::Nat) (i::[Cont]) (o::[Cont]) | v i -> o
class ConsumeOrdHelperLin (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o
class ConsumeOrdHelperReg (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o

instance (ConsumeOrd v i o) => ConsumeOrd v (None : i) (None : o)
instance ConsumeOrd x (Om x : i) (None : i)

instance (EQ v x b, ConsumeOrdHelperLin b v x i o) => ConsumeOrd v (Lin x : i) o
instance                     ConsumeOrdHelperLin True v x i (None : i)
instance ConsumeOrd v i o => ConsumeOrdHelperLin False v x i (Lin x : o)

instance (EQ v x b, ConsumeOrdHelperReg b v x i o) => ConsumeOrd v (Reg x : i) o
instance                     ConsumeOrdHelperReg True v x i (Reg x : i)
instance ConsumeOrd v i o => ConsumeOrdHelperReg False v x i (Reg x : o)


class ConsumeLin (v::Nat) (i::[Cont]) (o::[Cont]) | v i -> o
class ConsumeLinHelper (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o
class ConsumeLinHelperReg (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o

instance ConsumeLin v i o                       => ConsumeLin v (None : i) (None : o)
instance ConsumeLin v i o                       => ConsumeLin v (Om x: i) (Om x: o)

instance (EQ v x b, ConsumeLinHelper b v x i o) => ConsumeLin v (Lin x: i) o
instance                     ConsumeLinHelper True v x i (None : i)
instance ConsumeLin v i o => ConsumeLinHelper False v x i (Lin x : o)

instance (EQ v x b, ConsumeLinHelperReg b v x i o) => ConsumeLin v (Reg x: i) o
instance                     ConsumeLinHelperReg True v x i (None : i)
instance ConsumeLin v i o => ConsumeLinHelperReg False v x i (Reg x : o)

-- all this does is make sure that the variable is actually in the context.  It doesn't remove it.
class ConsumeReg (v::Nat) (i::[Cont]) (o::[Cont]) | v i -> o
class ConsumeRegHelper (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o

instance ConsumeReg v i o                       => ConsumeReg v (None : i) (None : o)
instance ConsumeReg v i o                       => ConsumeReg v (Lin x : i) (Lin x : o)
instance ConsumeReg v i o                       => ConsumeReg v (Om x : i) (Om x : o)

instance (EQ v x b, ConsumeRegHelper b v x i o) => ConsumeReg v (Reg x: i) o
instance                     ConsumeRegHelper True  v x i (Reg x : i)
instance ConsumeReg v i o => ConsumeRegHelper False v x i (Reg x : o)


class End (l :: [Cont]) (v :: Cont) (l' :: [Cont]) | l v -> l'
instance End '[] a (a : '[])
instance End a v2 b => End (v : a) v2 (v : b)

class Start (l :: [Cont]) (v :: Cont) (l' :: [Cont]) | l v -> l'
instance Start l v (v ': l)

class Concat (a :: [Cont]) (b :: [Cont]) (c :: [Cont]) | a b -> c, c a -> b
instance Concat '[] b b
instance Concat a b c => Concat (h : a) b (h : c)

newtype a :>-> b = SLolli {unSLolli :: a -> b}
newtype a :->> b = ELolli {unELolli :: a -> b}
newtype a :-<> b = LLolli {unLLolli :: a -> b}
newtype a :<>: b = Together { unTogether :: (a,b) }


type OrdVar repr vid a = forall (v::Nat) (i::[Cont]) (o::[Cont]) . ConsumeOrd vid i o => repr v i o vid a 
type LinVar repr vid a = forall (v::Nat) (i::[Cont]) (o::[Cont]) . ConsumeLin vid i o => repr v i o vid a
type RegVar repr vid a = forall (v::Nat) (i::[Cont]) (o::[Cont]) . ConsumeReg vid i o => repr v i o vid a

class OrdSeq (repr :: Nat -> [Cont] -> [Cont] -> Nat -> * -> *) where
  forward :: (forall v . repr v hi ho y a)
          -> repr vid hi ho x a

  sR :: (OrdVar repr vid a -> repr (S vid) (Om vid : hi) (None : ho) x b)
     -> repr vid hi ho x (a :>-> b)


  -- this necessarily can only use ordered variables.  But shouldn't we be able to use non ordered variables also?
  sL' :: ( UseTwo x hi ho
         , ConsumeOrd (S x) hi hi2  -- these enforce that life is ordered.
         , ConsumeOrd x hi2 ho 
         ) 
      => (forall v . repr v hi hi2 (S x) a)  -- S x == w
      -> (forall v . repr v hi2 ho x (a :>-> b)) -- this necessarily uses only a single variable 
      -> (OrdVar repr x b -> repr vid hi2 ho2 z c)
      -> repr vid hi ho2 z c

  -- this can use linear variables, but if they are ordered, it ensures that they come correctly identified.
  sendL' :: (forall v . repr v hi hi2 w a)  -- How?  ordered variables can only be used in concert by nature of them.
         -> (forall v . repr v hi2 ho x (a :>-> b))
         -> (OrdVar repr x b -> repr vid hi2 ho2 z c)
         -> repr vid hi ho2 z c

  llam :: (LinVar repr vid a -> repr (S vid) (Lin vid : hi)  (None : ho) x b)
       -> repr vid hi ho x (a :-<> b)
          
  lam :: (RegVar repr vid a -> repr (S vid) (Reg vid:hi) (Reg vid:ho) x b)
      -> repr vid hi ho x (a -> b)
  

eval :: R Z '[] '[] chan a -> a
eval = unR



newtype R (vid::Nat) (hi::[Cont]) (ho::[Cont]) (x :: Nat) a = R { unR :: a }

instance OrdSeq R where
  forward x = R $ unR x
  sR f = R $ SLolli $ \x -> unR $ f $ R x
  llam f = R $ LLolli $ \x -> unR $ f $ R x
  
  sL' vWa vXf procQ = R $ unR $ procQ $ R $ (unSLolli $ unR vXf) $ unR vWa
  sendL' vWa vXf procQ = R $ unR $ procQ $ R $ (unSLolli $ unR vXf) $ unR vWa

  lam f = R $ \x -> unR $ f $ R x  



{-
       y : B |- y <-> x :: x : B
 --------------------------------------------------
   y : A ->> B, z : A |- send y z ; y <-> x :: x : B
-------------------------------------------------------------
  y : A ->> B |- z <- rec x; send y z ; y <-> x :: x :  A ->> B
-------------------------------------------------------------------------------
. |- y <- rec x; z <- rec x; send y z ;  y <-> x :: x :  (A ->> B) ->> (A ->> B)
-}

tm = eval $ sR $ \y -> sR $ \z -> sL' z y (\f -> f)
tm1 = eval $ sR $ \y -> sR $ \z -> sendL' z y (\f -> f)
tm2 = eval $ llam $ \y -> llam $ \z -> sendL' y z (\f -> f)
-- tm2' = eval $ llam $ \y -> llam $ \z -> sL' y z (\f -> f) -- DOESN'T COMPILE because sL' only works with actual ordered chanels

tm3 = eval $ lam $ \y -> lam $ \z -> sendL' y z (\f -> f)


main = do
  -- putStrLn $ unLolli (eval $ good <^> llam (\x -> x)) "I was passed to a real function."
  putStrLn "ok"



