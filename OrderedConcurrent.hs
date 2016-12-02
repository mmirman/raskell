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

module OrderedConcurrent where

import Control.Applicative
import Control.Concurrent

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

--
-- Type level machinery for consuming a variable in a list of variables.
--
class ConsumeOrd (v::Nat) (i::[Cont]) (o::[Cont]) | v i -> o
class ConsumeOrdHelperLin (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o
class ConsumeOrdHelperReg (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o

instance (ConsumeOrd v i o) => ConsumeOrd v (None:i) (None:o)
instance ConsumeOrd x (Om x:i) (None:i)

instance (EQ v x b, ConsumeOrdHelperLin b v x i o) => ConsumeOrd v (Lin x:i) o
instance                     ConsumeOrdHelperLin True v x i (None:i)
instance ConsumeOrd v i o => ConsumeOrdHelperLin False v x i (Lin x:o)

instance (EQ v x b, ConsumeOrdHelperReg b v x i o) => ConsumeOrd v (Reg x:i) o
instance                     ConsumeOrdHelperReg True v x i (Reg x:i)
instance ConsumeOrd v i o => ConsumeOrdHelperReg False v x i (Reg x:o)


class ConsumeLin (v::Nat) (i::[Cont]) (o::[Cont]) | v i -> o
class ConsumeLinHelper (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o
class ConsumeLinHelperReg (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o

instance ConsumeLin v i o                       => ConsumeLin v (None:i) (None:o)
instance ConsumeLin v i o                       => ConsumeLin v (Om x: i) (Om x: o)

instance (EQ v x b, ConsumeLinHelper b v x i o) => ConsumeLin v (Lin x: i) o
instance                     ConsumeLinHelper True v x i (None:i)
instance ConsumeLin v i o => ConsumeLinHelper False v x i (Lin x:o)

instance (EQ v x b, ConsumeLinHelperReg b v x i o) => ConsumeLin v (Reg x: i) o
instance                     ConsumeLinHelperReg True v x i (None:i)
instance ConsumeLin v i o => ConsumeLinHelperReg False v x i (Reg x:o)

-- all this does is make sure that the variable is actually in the context.  It doesn't remove it.
class ConsumeReg (v::Nat) (i::[Cont]) (o::[Cont]) | v i -> o
class ConsumeRegHelper (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o

instance ConsumeReg v i o                       => ConsumeReg v (None:i) (None:o)
instance ConsumeReg v i o                       => ConsumeReg v (Lin x:i) (Lin x:o)
instance ConsumeReg v i o                       => ConsumeReg v (Om x:i) (Om x:o)

instance (EQ v x b, ConsumeRegHelper b v x i o) => ConsumeReg v (Reg x: i) o
instance                     ConsumeRegHelper True  v x i (Reg x:i)
instance ConsumeReg v i o => ConsumeRegHelper False v x i (Reg x:o)


class End (l :: [Cont]) (v :: Cont) (l' :: [Cont]) | l v -> l'
instance End '[] a (a:'[])
instance End a v2 b => End (v:a) v2 (v:b)

class Start (l :: [Cont]) (v :: Cont) (l' :: [Cont]) | l v -> l'
instance Start l v (v ': l)

class Concat (a :: [Cont]) (b :: [Cont]) (c :: [Cont]) | a b -> c, c a -> b
instance Concat '[] b b
instance Concat a b c => Concat (h:a) b (h:c)

newtype a :>-> b = SLolli {unSLolli :: a -> b}
newtype a :->> b = ELolli {unELolli :: a -> b}
newtype a :-<> b = LLolli {unLLolli :: a -> b}
newtype a :<>: b = Together { unTogether :: (a,b) }


type OrdVar repr vid a = forall (v::Nat) (i::[Cont]) (o::[Cont]) . ConsumeOrd vid i o => repr v i o vid a 
type LinVar repr vid a = forall (v::Nat) (i::[Cont]) (o::[Cont]) . ConsumeLin vid i o => repr v i o vid a
type RegVar repr vid a = forall (v::Nat) (i::[Cont]) (o::[Cont]) . ConsumeReg vid i o => repr v i o vid a

class OrdSeq (repr :: Nat -> [Cont] -> [Cont] -> Nat -> * -> *) where
  
  sRecv :: (OrdVar repr vid a -> repr (S vid) (Om vid:hi) (None:ho) x b)
        -> repr vid hi ho x (a :>-> b)

  sSend :: (forall v . repr v hi hi2 w a) -- This can use non-ordered variables, but if they are ordered,
        -> (forall v . repr v hi2 ho x (a :>-> b)) -- it ensures that they are in fact ordered, as they come with a type constraint ensuring they are used this way.
        -- The abstraction reuses "x" so we don't need to increment the depth counter.
        -> (OrdVar repr x b -> repr vid hi2 ho2 z c) -- "ho2" is used instead of "ho" in the abstraction because it might use more variables from further up the scope.
        -> repr vid hi ho2 z c

  lRecv :: (LinVar repr vid a -> repr (S vid) (Lin vid:hi)  (None:ho) x b)
       -> repr vid hi ho x (a :-<> b)
          
  recv :: (RegVar repr vid a -> repr (S vid) (Reg vid:hi) (Reg vid:ho) x b)
      -> repr vid hi ho x (a -> b)

          
newtype C (vid::Nat) (hi::[Cont]) (ho::[Cont]) (x :: Nat) a = C { unC :: IO a }

instance OrdSeq IOR where
  sRecv f = IOR $ SLolli $ \x -> unR $ f $ R x

  {-
     new f = Nu <$> newChan >>= f
     a ||| b = forkIO a >> fork b
     inn (Nu x) f = readChan x >>= fork . f
     out (Nu x) y b = writeChan x y >> b
     rep = forever
     nil = return ()
     embed = id
-}

  










newtype R (vid::Nat) (hi::[Cont]) (ho::[Cont]) (x :: Nat) a = R { unR :: a }

instance OrdSeq R where
  
  sRecv f = R $ SLolli $ \x -> unR $ f $ R x
  lRecv f = R $ LLolli $ \x -> unR $ f $ R x
  recv f = R $ \x -> unR $ f $ R x
  
  sSend vWa vXf procQ = R $ unR $ procQ $ R $ (unSLolli $ unR vXf) $ unR vWa


  
evalR :: R Z '[] '[] chan a -> a
evalR = unR

tm = evalR $ sRecv $ \y -> sRecv $ \z -> sSend z y (\f -> f)
tm2 = evalR $ lRecv $ \y -> lRecv $ \z -> sSend y z (\f -> f)
tm3 = evalR $ recv $ \y -> recv $ \z -> sSend y z (\f -> f)




