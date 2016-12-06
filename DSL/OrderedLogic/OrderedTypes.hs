module DSL.OrderedLogic.OrderedTypes where

import Control.Applicative
import Control.Concurrent


void x = x >> return ()

--
-- Type level Nats
--
data Nat = Z | S Nat

data Cont = Om Nat | None

--
-- Type level Nat equality
--
class EQ (x::Nat) (y::Nat) (b::Bool) | x y -> b
instance {-# OVERLAPPABLE #-} (b ~ False) => EQ x y b
instance {-# OVERLAPPING #-} EQ x x True


class EQC (x::Cont) (y::Cont) (b::Bool) | x y -> b
instance {-# OVERLAPPABLE #-} (b ~ False) => EQC x y b
instance {-# OVERLAPPING #-} EQC x x True


--
-- Type level machinery for consuming a variable in a list of variables.
--
class ConsumeOrd (v::Nat) (i::[Cont]) (o::[Cont]) | v i -> o
instance (ConsumeOrd v i o) => ConsumeOrd v (None:i) (None:o)
instance ConsumeOrd x (Om x:i) (None:i)



class ConsumeLin (v::Nat) (i::[Cont]) (o::[Cont]) | v i -> o
class ConsumeLinHelper (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o

instance ConsumeLin v i o                       => ConsumeLin v (None:i) (None:o)
instance (EQ v x b, ConsumeLinHelper b v x i o) => ConsumeLin v (Om x: i) o
instance                     ConsumeLinHelper True v x i (None:i)
instance ConsumeLin v i o => ConsumeLinHelper False v x i (Om x:o)


class ConsumeReg (v::Nat) (i::[Cont]) (o::[Cont])
instance {-# INCOHERENT #-} ConsumeReg v '[] '[]
instance {-# INCOHERENT #-} (ConsumeReg v i o) => ConsumeReg v (None:i) (None:o)
instance {-# INCOHERENT #-} (EQ v w False, ConsumeReg v i o) => ConsumeReg v (Om w:i) (Om w:o)
instance {-# INCOHERENT #-} ConsumeReg x (Om x:i) (None:i)
instance {-# INCOHERENT #-} ConsumeReg x (Om x:i) (Om x:i)


class ConsumeOrdAsLin (v::Nat) (i::[Cont]) (o::[Cont]) | v i -> o
class ConsumeOrdAsLinHelperOrd (b::Bool) (v::Nat) (x::Nat) (i::[Cont]) (o::[Cont]) | b v x i -> o

instance ConsumeOrdAsLin v i o                          => ConsumeOrdAsLin v (None:i) (None:o)
instance (EQ v x b, ConsumeOrdAsLinHelperOrd b v x i o) => ConsumeOrdAsLin v (Om x: i)  o

instance                          ConsumeOrdAsLinHelperOrd True  v x i (None:i)
instance ConsumeOrdAsLin v i o => ConsumeOrdAsLinHelperOrd False v x i (Om x:o)



class EndH (l :: [Cont]) (v :: Cont) (l' :: [Cont]) | v l -> l'
instance EndH '[] a (a:'[])
instance EndH a v2 b => EndH (v:a) v2 (v:b)

class RemEnd (l :: [Cont])  (l' :: [Cont]) | l -> l'
instance RemEnd (a:'[]) '[]
instance RemEnd (v':a) b => RemEnd (v:v':a) (v:b)


class End (l :: [Cont]) (v :: Cont) (l' :: [Cont]) | v l -> l', l' -> l
instance (RemEnd l' l, EndH l v l') => End l v l'

type OrdVar repr vid a = forall (i::[Cont]) (o::[Cont]) . ConsumeOrd vid i o => repr i o vid a 
type RegVar repr (vid :: Nat) a = forall (i::[Cont]) (o :: [Cont]) . ConsumeReg vid i o => repr i o vid a

data Phant (i :: [Cont]) = P

class OrdSeq (repr :: Nat -> [Cont] -> [Cont] -> Nat -> * -> *) where
  type Name repr :: [Cont] -> [Cont] -> Nat -> * -> *

  type SLolli repr :: * -> * -> *
  type ELolli repr :: * -> * -> *
  type Lolli  repr :: * -> * -> *

  forward :: Name repr i o x a
          -> repr v i o y a

  -- no concurrency introduced
  send :: Name repr hi hi w a -- no context modifications at all ensures regularity
       -> Name repr hi hi x (Lolli repr a b)
       -> (RegVar (Name repr) x b -> repr vid hi ho z c)
       -> repr vid hi ho z c
          
  -- no concurrency introduced
  recv :: (RegVar (Name repr) vid a -> repr (S vid) hi ho x b)
       -> repr vid hi ho x (Lolli repr a b)   

  sSend :: ( ConsumeTog w x hi ho
           , ConsumeLin w hi hi'
           )
        => Name repr (Om w:'[]) (None:'[]) w a -- This can use non-ordered variables, but if they are ordered,
        -> Name repr (Om x:'[]) (None:'[]) x (SLolli repr a b) -- it ensures that they are in fact ordered, as they come with a type constraint ensuring they are used this way.
        -- The abstraction reuses "x" so we don't need to increment the depth counter.
        -> (OrdVar (Name repr) x b -> repr vid hi' ho z c) -- "ho2" is used instead of "ho" in the abstraction because it might use more variables from further up the scope.
        -> repr vid hi ho z c

  sRecv :: (OrdVar (Name repr) y a -> repr (S y) (Om y:hi) (None:ho) x b)
        -> repr y hi ho x (SLolli repr a b)
           
  eSend :: ( ConsumeTog x w hi ho
           , ConsumeLin w hi hi'
           )
        => Name repr (Om x:'[]) (None:'[]) x (ELolli repr a b)
        -> Name repr (Om w:'[]) (None:'[]) w a
        -> (OrdVar (Name repr) x b -> repr vid hi' ho z c)
        -> repr vid hi ho z c

  eRecv :: (End hi (Om y) hi', End ho None ho')
        => (OrdVar (Name repr) y a -> repr (S y) hi' ho' x b)
        -> repr y hi ho x (ELolli repr a b)

  bif :: ( Swap hi13 ho13 vid hi2 ho2 hi ho )
       => Phant hi13
       -> repr vid hi2 ho2 vid a  -- we use vid here to ensure the newness of "x"
       -> (OrdVar (Name repr) vid a -> repr (S vid) hi13 ho13 z c)
       -> repr vid hi ho z c

class ConsumeTog (w :: Nat) (x :: Nat) (hi :: [Cont]) (ho :: [Cont])
instance {-# INCOHERENT #-} ConsumeTog w x (Om w:Om x:hi) (t:None:ho) -- don't necessarily want to consume w since it could be unordered
instance {-# INCOHERENT #-} ConsumeTog w x hi ho => ConsumeTog w x (None:hi) (None:ho)
instance {-# INCOHERENT #-} (EQ w z False, EQ x z False, ConsumeTog w x hi ho) => ConsumeTog w x (Om z:hi) (t:ho)


class SameLen (a::[Cont]) (b::[Cont])
instance SameLen '[] '[]
instance SameLen a b => SameLen (i:a) (j:b)

class SwapRev (a::[Cont]) (a'::[Cont]) (x::Nat) (y::[Cont]) (y'::[Cont]) (b::[Cont])  (b'::[Cont])
    | a x b -> y
    , a x b' -> y'
    , a y b -> x
    , a y b' -> x
    , a y' b -> x
    , a y' b' -> x
instance SwapRev (Om h: '[]) (None: '[]) h '[] '[] '[] '[]
instance SwapRev (Om h: '[]) (None: '[]) h y y' b b'
      => SwapRev (Om h:'[]) (None: '[]) h (v:y) (v':y') (v:b) (v':b')
instance ( End y r y2
         , End y' r' y2'
         , SwapRev (Om h:a) (None:a') h y2 y2' b b'
         )
      => SwapRev (Om h:r:a) (None:r':a') h y y' b b'
instance ( EQ h h2 False
         , SwapRev a a' h2 y y' b b'
         )
         => SwapRev (Om h:a) (h':a') h2 y y' (Om h:b) (h':b')

class SwapFor (a::[Cont]) (a'::[Cont]) (x::Nat) (y::[Cont]) (y'::[Cont]) (b::[Cont])  (b'::[Cont])
    | a x b -> y
    , a x a' y' -> b'
    , a x a' b' -> y'
instance ( SameLen a a', SameLen y y', SameLen b b'
         , PartCtxBoth y a b
         , PartCtxBoth y' a' b'
         )
      => SwapFor (Om h:a) (h':a') h y y' b b'
instance ( EQ h h2 bool
         , SwapFor a a' h2 y y' b b'
         ) => SwapFor (Om h:a) (h':a') h2 y y' (Om h:b) (h':b')

class SwapB (a::[Cont]) (x::Nat) (y::[Cont]) (b::[Cont])
    | a x y -> b
    , a x b -> y
instance PartCtxBoth y a b
      => SwapB (Om h:a) h y b
instance ( EQ h h2 bool
         , SwapB a h2 y b
         ) => SwapB (Om h:a) h2 y (Om h:b)

class Swap (a::[Cont]) (a'::[Cont]) (x::Nat) (y::[Cont]) (y'::[Cont]) (b::[Cont])  (b'::[Cont])
    | a x y -> b
    , a x a' y' -> b'
    , a x a' b' -> y'
    , a x b -> y
    , a x b' -> y'
    , a y b -> x
    , a y b' -> x
    , a y' b -> x
    , a y' b' -> x
instance (SwapB a x y b, SwapRev a a' x y y' b b', SwapFor a a' x y y' b b') => Swap a a' x y y' b b'


class ReverseHelp (a :: [Cont]) (t :: [Cont]) (b :: [Cont]) | a t -> b, a b -> t
instance ReverseHelp '[] t t
instance ReverseHelp h (a:t) b => ReverseHelp (a:h) t b

class Reverse (a :: [Cont]) (b :: [Cont]) | a -> b, b -> a
instance (ReverseHelp a '[] b, ReverseHelp b '[] a)  => Reverse a b


class PartCtx (a :: [Cont]) (b :: [Cont]) (c :: [Cont]) | a b -> c, c a -> b
instance PartCtx '[] b b
instance PartCtx a b c => PartCtx (None:a)  b (None:c)
instance PartCtx a b c => PartCtx (Om h:a)  b (Om h:c)

class PartCtxR (a :: [Cont]) (b :: [Cont]) (c :: [Cont]) | a b -> c, b c -> a
instance (Reverse c c', Reverse a a', Reverse b b', PartCtx b' a' c') => PartCtxR a b c 

class PartCtxBoth (a :: [Cont]) (b :: [Cont]) (c :: [Cont]) | a b -> c, b c -> a, a c -> b
instance (PartCtxR a b c, PartCtx a b c) => PartCtxBoth a b c 


