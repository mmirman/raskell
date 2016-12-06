module DSL.OrderedLogic.OrderedTypes where

import Control.Applicative
import Control.Concurrent


void x = x >> return ()

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


class EQC (x::Cont) (y::Cont) (b::Bool) | x y -> b
instance {-# OVERLAPPABLE #-} (b ~ False) => EQC x y b
instance {-# OVERLAPPING #-} EQC x x True


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




class NotOrd (l :: [Cont]) (n :: Nat)
instance NotOrd (Lin x:l) x
instance NotOrd (Reg x:l) x
instance (NotOrd l x) => NotOrd (None:l)  x
instance (EQ x y False, NotOrd l x) => NotOrd (Om y:l)  x
instance (EQ x y False, NotOrd l x) => NotOrd (Lin y:l) x
instance (EQ x y False, NotOrd l x) => NotOrd (Reg y:l) x


type OrdVar repr vid a = forall (i::[Cont]) (o::[Cont]) . ConsumeOrd vid i o => repr i o vid a 
type LinVar repr vid a = forall (i::[Cont]) (o::[Cont]) . ConsumeLin vid i o => repr i o vid a
type RegVar repr vid a = forall (i::[Cont]) (o::[Cont]) . ConsumeReg vid i o => repr i o vid a



class OrdSeq (repr :: Nat -> [Cont] -> [Cont] -> Nat -> * -> *) where
  type Name repr :: [Cont] -> [Cont] -> Nat -> * -> *

  type SLolli repr :: * -> * -> *
  type ELolli repr :: * -> * -> *
  type LLolli repr :: * -> * -> *
  type Lolli  repr :: * -> * -> *

  forward :: Name repr i o x a
          -> repr v i o y a

  -- no concurrency introduced
  send :: Name repr hi hi w a -- no context modifications at all ensures regularity
       -> Name repr hi hi x (Lolli repr a b)
       -> (RegVar (Name repr) x b -> repr vid hi ho z c)
       -> repr vid hi ho z c
          
  -- no concurrency introduced
  recv :: (RegVar (Name repr) vid a -> repr (S vid) (Reg vid:hi) (Reg vid:ho) x b)
       -> repr vid hi ho x (Lolli repr a b)   

          
  lSend :: (NotOrd hi w, NotOrd hi x)
        => Name repr hi hi2 w a
        -> Name repr hi2 ho x (LLolli repr a b)
        -> (LinVar (Name repr) x b -> repr vid hi2 ho2 z c)
        -> repr vid hi ho2 z c
           
  lRecv :: (LinVar (Name repr) vid a -> repr (S vid) (Lin vid:hi)  (None:ho) x b)
       -> repr vid hi ho x (LLolli repr a b)

          
  sSend :: Name repr hi hi2 w a -- This can use non-ordered variables, but if they are ordered,
        -> Name repr hi2 ho x (SLolli repr a b) -- it ensures that they are in fact ordered, as they come with a type constraint ensuring they are used this way.
        -- The abstraction reuses "x" so we don't need to increment the depth counter.
        -> (OrdVar (Name repr) x b -> repr vid hi2 ho2 z c) -- "ho2" is used instead of "ho" in the abstraction because it might use more variables from further up the scope.
        -> repr vid hi ho2 z c

  sRecv :: (OrdVar (Name repr) y a -> repr (S y) (Om y:hi) (None:ho) x b)
        -> repr y hi ho x (SLolli repr a b)
           
  eSend :: ConsumeOrdAsLin w hi ho2    -- this case is strange as we need to make sure we eat w in ho2 since we never see w there
        => Name repr hi hi2 x (ELolli repr a b)
        -> Name repr hi2 ho w a
        -> (OrdVar (Name repr) x b -> repr vid hi ho2 z c)
        -> repr vid hi ho2 z c         

  eRecv :: (End hi (Om y) hi', End ho None ho')
        => (OrdVar (Name repr) y a -> repr (S y) hi' ho' x b)
        -> repr y hi ho x (ELolli repr a b)

  bif :: ( {-PartCtxBoth hi1 hi'  hi  -- bifurcate - "CUT"
         , PartCtxBoth ho1 ho'  ho
           
         , PartCtxBoth hi2 hi3 hi'
         , PartCtxBoth ho2 ho3 ho'
           
         , PartCtxBoth hi1 (Om vid:hi3) hi13
         , PartCtxBoth ho1 (None:ho3) ho13
         -}  
         {- TriCtx hi1 hi2 hi3 hi,
          TriCtx ho1 ho2 ho3 ho,
          PartCtxBoth hi1 (Om vid:hi3) hi13,
          PartCtxBoth ho1 (None:ho3) ho13
          -}
          Swap hi hi2 (Om vid:'[]) hi13,
          Swap ho ho2 (None:'[]) ho13
         )
       => repr vid hi2 ho2 vid a  -- we use vid here to ensure the newness of "x"
       -> (OrdVar (Name repr) vid a -> repr (S vid) hi13 ho13 z c)
       -> repr vid hi ho z c

class TriCtx (a::[Cont]) (m::[Cont]) (c::[Cont]) (d::[Cont])  | a m c -> d, m c d -> a, a c d -> m, a m d -> c
instance ( PartCtxBoth a m i
         , PartCtxBoth i c d
         ) => TriCtx a m c d




class SwapPart (a::[Cont]) (x::[Cont]) (y::[Cont]) (b::[Cont])  | a x y -> b
instance PartCtxBoth y a b => SwapPart a '[] y b
instance SwapPart a x y b => SwapPart (h:a) (h:x) y b
instance (EQC h h' bool, SwapPart a (h':x) y b)=> SwapPart (h:a) (h':x) y (h:b)

class Swap (a::[Cont]) (x::[Cont]) (y::[Cont]) (b::[Cont])  | a x y -> b, b x y -> a
instance (SwapPart a x y b, SwapPart b y x a) => Swap a x y b 

class ReverseHelp (a :: [Cont]) (t :: [Cont]) (b :: [Cont]) | a t -> b, a b -> t
instance ReverseHelp '[] t t
instance ReverseHelp h (a:t) b => ReverseHelp (a:h) t b

class Reverse (a :: [Cont]) (b :: [Cont]) | a -> b, b -> a
instance (ReverseHelp a '[] b, ReverseHelp b '[] a)  => Reverse a b


class PartCtx (a :: [Cont]) (b :: [Cont]) (c :: [Cont]) | a b -> c, c a -> b
instance PartCtx '[] b b
instance PartCtx a b c => PartCtx (Om h:a)  b (Om h:c)
instance PartCtx a b c => PartCtx (Lin h:a) b (Lin h:c)
instance PartCtx a b c => PartCtx (Reg h:a) b (Reg h:c)
instance PartCtx a b c => PartCtx (Reg h:a) (Reg h:b) (Reg h:c)

class PartCtxR (a :: [Cont]) (b :: [Cont]) (c :: [Cont]) | a b -> c, b c -> a
instance (Reverse c c', Reverse a a', Reverse b b', PartCtx b' a' c') => PartCtxR a b c 

class PartCtxBoth (a :: [Cont]) (b :: [Cont]) (c :: [Cont]) | a b -> c, b c -> a, a c -> b
instance (PartCtxR a b c, PartCtx a b c) => PartCtxBoth a b c 


