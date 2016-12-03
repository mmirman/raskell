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


class ConsumeOrdAsLin (v::Nat) (i::[Cont]) (o::[Cont]) | v i -> o
class ConsumeOrdAsLinHelperOrd (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o
class ConsumeOrdAsLinHelper (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o
class ConsumeOrdAsLinHelperReg (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o

instance ConsumeOrdAsLin v i o                          => ConsumeOrdAsLin v (None:i) (None:o)
instance (EQ v x b, ConsumeOrdAsLinHelperOrd b v x i o) => ConsumeOrdAsLin v (Om x: i)  o
instance (EQ v x b, ConsumeOrdAsLinHelper b v x i o)    => ConsumeOrdAsLin v (Lin x: i) o
instance (EQ v x b, ConsumeOrdAsLinHelperReg b v x i o) => ConsumeOrdAsLin v (Reg x: i) o

instance                          ConsumeOrdAsLinHelperOrd True  v x i (None:i)
instance ConsumeOrdAsLin v i o => ConsumeOrdAsLinHelperOrd False v x i (Om x:o)

instance                          ConsumeOrdAsLinHelper True  v x i (None:i)
instance ConsumeOrdAsLin v i o => ConsumeOrdAsLinHelper False v x i (Lin x:o)

instance                          ConsumeOrdAsLinHelperReg True  v x i (None:i)
instance ConsumeOrdAsLin v i o => ConsumeOrdAsLinHelperReg False v x i (Reg x:o)


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

-- PartCtx is a bit like concat, but regular variables must be treated differently
class PartCtx (a :: [Cont]) (b :: [Cont]) (c :: [Cont]) | a b -> c, c a -> b
instance PartCtx '[] b b
instance PartCtx a b c => PartCtx (Om h:a) b (Om h:c)
instance PartCtx a b c => PartCtx (Lin h:a) b (Lin h:c)
instance PartCtx a b c => PartCtx (Reg h:a) b (Reg h:c)
instance PartCtx a b c => PartCtx (Reg h:a) (Reg h:b) (Reg h:c)




class NotOrd (l :: [Cont]) (n :: Nat)
instance NotOrd (Lin x:l) x
instance NotOrd (Reg x:l) x
instance (NotOrd l x) => NotOrd (None:l)  x
instance (EQ x y False, NotOrd l x) => NotOrd (Om y:l)  x
instance (EQ x y False, NotOrd l x) => NotOrd (Lin y:l) x
instance (EQ x y False, NotOrd l x) => NotOrd (Reg y:l) x


type OrdVar repr vid a = forall (v::Nat) (i::[Cont]) (o::[Cont]) . ConsumeOrd vid i o => repr v i o vid a 
type LinVar repr vid a = forall (v::Nat) (i::[Cont]) (o::[Cont]) . ConsumeLin vid i o => repr v i o vid a
type RegVar repr vid a = forall (v::Nat) (i::[Cont]) (o::[Cont]) . ConsumeReg vid i o => repr v i o vid a

newtype C (vid::Nat) (hi::[Cont]) (ho::[Cont]) (x :: Nat) a = C { unC :: Chan a -> IO () }

newtype a :>-> b = SLolli {unSLolli :: (Chan b , Chan a -> IO ()) }
newtype a :->> b = ELolli {unELolli :: (Chan b , Chan a -> IO ()) }
newtype a :-<> b = LLolli {unLLolli :: (Chan b , Chan a -> IO ()) }
newtype a :->  b = Lolli  {unLolli  :: (Chan b , Chan a -> IO ()) }

class OrdSeq (repr :: Nat -> [Cont] -> [Cont] -> Nat -> * -> *) where
  type Name repr :: Nat -> [Cont] -> [Cont] -> Nat -> * -> *

  par :: ( PartCtx hi1 hi'  hi
         , PartCtx ho1 ho'  ho
           
         , PartCtx hi2 hi3 hi'
         , PartCtx ho2 ho3 ho'
           
         , PartCtx hi1 (Om vid:hi3) hi13
         , PartCtx ho1 (None:ho3) ho13           
         )
       => repr vid hi2 ho2 x a
       -> (OrdVar (Name repr) x a -> repr (S vid) hi13 ho13 z c)
       -> repr vid hi ho z c 

  -- no concurrency introduced
  send :: (forall v . Name repr v hi hi w a) -- no context modifications at all ensures regularity
       -> (forall v . Name repr v hi hi x (a :-> b))
       -> (RegVar (Name repr) x b -> repr vid hi ho z c)
       -> repr vid hi ho z c
          
  -- no concurrency introduced
  recv :: (RegVar (Name repr) vid a -> repr (S vid) (Reg vid:hi) (Reg vid:ho) x b)
       -> repr vid hi ho x (a :-> b)   

          
  lSend :: (NotOrd hi w, NotOrd hi x)
        => (forall v . Name repr v hi hi2 w a)
        -> (forall v . Name repr v hi2 ho x (a :-<> b))
        -> (LinVar (Name repr) x b -> repr vid hi2 ho2 z c)
        -> repr vid hi ho2 z c
           
  lRecv :: (LinVar (Name repr) vid a -> repr (S vid) (Lin vid:hi)  (None:ho) x b)
       -> repr vid hi ho x (a :-<> b)

          
  sSend :: (forall v . Name repr v hi hi2 w a) -- This can use non-ordered variables, but if they are ordered,
        -> (forall v . Name repr v hi2 ho x (a :>-> b)) -- it ensures that they are in fact ordered, as they come with a type constraint ensuring they are used this way.
        -- The abstraction reuses "x" so we don't need to increment the depth counter.
        -> (OrdVar (Name repr) x b -> repr vid hi2 ho2 z c) -- "ho2" is used instead of "ho" in the abstraction because it might use more variables from further up the scope.
        -> repr vid hi ho2 z c

  sRecv :: (OrdVar (Name repr) y a -> repr (S y) (Om y:hi) (None:ho) x b)
        -> repr y hi ho x (a :>-> b)
           
  eSend :: ConsumeOrdAsLin w hi ho2    -- this case is strange as we need to make sure we eat w in ho2 since we never see w there
        => (forall v . Name repr v hi hi2 x (a :->> b))
        -> (forall v . Name repr v hi2 ho w a)
        -> (OrdVar (Name repr) x b -> repr vid hi ho2 z c)
        -> repr vid hi ho2 z c         

  eRecv :: (End hi (Om y) hi', End ho None ho')
        => (OrdVar (Name repr) y a -> repr (S y) hi' ho' x b)
        -> repr y hi ho x (a :->> b)
  

instance OrdSeq C where
  type Name C = C

  recv f = C $ \cab -> do
    (cb,ca_io) <- unLolli <$> readChan cab
    (unC $ f $ C ca_io) cb

  send (C ca_io) (C cab_io) procB_C = C $ unC $ procB_C $ C $ \cb -> do
    cab <- newChan
    writeChan cab $ Lolli (cb, ca_io)    
    cab_io cab

  lRecv f = C $ \cab -> do
    (cb,ca_io) <- unLLolli <$> readChan cab
    (unC $ f $ C ca_io) cb

  -- do we want concurrency here?  je pense
  lSend (C ca_io) (C cab_io) procB_C = C $ unC $ procB_C $ C $ \cb -> do
    cab <- newChan
    forkIO $ cab_io cab
    writeChan cab $ LLolli (cb, ca_io)

  sRecv f = C $ \cab -> do
    (cb,ca_io) <- unSLolli <$> readChan cab
    (unC $ f $ C ca_io) cb

  sSend (C ca_io) (C cab_io) procB_C = C $ unC $ procB_C $ C $ \cb -> do
    cab <- newChan
    forkIO $ cab_io cab
    writeChan cab $ SLolli (cb, ca_io)

  eRecv f = C $ \cab -> do
    (cb,ca_io) <- unELolli <$> readChan cab
    (unC $ f $ C ca_io) cb

  eSend (C cab_io) (C ca_io) procB_C = C $ unC $ procB_C $ C $ \cb -> do
    cab <- newChan
    forkIO $ cab_io cab
    writeChan cab $ ELolli (cb, ca_io)


    

evalC :: C Z '[] '[] chan a -> a -> IO ()
evalC e a = do
  c <- newChan
  writeChan c a  
  unC e c


tm :: (a :>-> b) :>-> (a :>-> b) -> IO ()
tm = evalC $ sRecv $ \y -> sRecv $ \z -> sSend z y id


tm2 :: b :>-> b -> IO ()
tm2 = evalC $ sRecv id

void x = x >> return ()

main = do
  a <- newChan
  -- this doesn't block
  tm2 $ SLolli (a, const $ putStrLn "ho")

  b <- newChan
  -- this blocks. 
  tm $ SLolli (b, const $ putStrLn "hi")
  
