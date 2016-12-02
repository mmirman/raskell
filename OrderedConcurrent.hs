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
  ScopedTypeVariables,
  GeneralizedNewtypeDeriving
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



type OrdVar repr vid a = forall (v::Nat) (i::[Cont]) (o::[Cont]) . ConsumeOrd vid i o => repr v i o vid a 
type LinVar repr vid a = forall (v::Nat) (i::[Cont]) (o::[Cont]) . ConsumeLin vid i o => repr v i o vid a
type RegVar repr vid a = forall (v::Nat) (i::[Cont]) (o::[Cont]) . ConsumeReg vid i o => repr v i o vid a


newtype a :->> b = ELolli {unELolli :: Chan (a, Chan b) }
newtype a :-<> b = LLolli {unLLolli :: Chan (a, Chan b) }  
newtype a :->  b = Lolli  {unLolli  :: Chan (a, Chan b) }

class OrdSeq (repr :: Nat -> [Cont] -> [Cont] -> Nat -> * -> *) where
  type Name repr :: Nat -> [Cont] -> [Cont] -> Nat -> * -> *

  lRecv :: (LinVar (Name repr) vid a -> repr (S vid) (Lin vid:hi)  (None:ho) x b)
       -> repr vid hi ho x (a :-<> b)
          
  recv :: (RegVar (Name repr) vid a -> repr (S vid) (Reg vid:hi) (Reg vid:ho) x b)
      -> repr vid hi ho x (a :-> b)
          
  sSend :: (forall v . Name repr v hi hi2 w a) -- This can use non-ordered variables, but if they are ordered,
        -> (forall v . Name repr v hi2 ho x (a :>-> b)) -- it ensures that they are in fact ordered, as they come with a type constraint ensuring they are used this way.
        -- The abstraction reuses "x" so we don't need to increment the depth counter.
        -> (OrdVar (Name repr) x b -> repr vid hi2 ho2 z c) -- "ho2" is used instead of "ho" in the abstraction because it might use more variables from further up the scope.
        -> repr vid hi ho2 z c

  sRecv :: (OrdVar (Name repr) y a -> repr (S y) (Om y:hi) (None:ho) x b)
        -> repr y hi ho x (a :>-> b)

newtype C (vid::Nat) (hi::[Cont]) (ho::[Cont]) (x :: Nat) a = C { unC :: Chan a -> IO () }

newtype a :>-> b = SLolli {unSLolli :: (Chan b , Chan a -> IO ()) }

instance OrdSeq C where
  
  type Name C = C

  sRecv (f :: OrdVar C y a -> C (S y) (Om y:hi) (None:ho) x b) = C $ \cxab -> do
    (cb,ca_io) <- unSLolli <$> readChan cxab
    (unC $ f $ C ca_io) cb

  sSend (C ca_io) (C cab_io) procB_C = C $ unC $ procB_C $ C $ \cb -> do
    cab <- newChan
    forkIO $ cab_io cab
    writeChan cab $ SLolli (cb, ca_io)

evalC :: C Z '[] '[] chan a -> a -> IO ()
evalC e a = do
  c <- newChan
  forkIO $ unC e c
  writeChan c a

tm :: (a :>-> b) :>-> (a :>-> b) -> IO ()
tm = evalC $ sRecv $ \y -> sRecv $ \z -> sSend z y id
