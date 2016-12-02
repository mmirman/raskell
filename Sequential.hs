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

--
-- Type level Nat equality
--

class EQ (x::Nat) (y::Nat) (b::Bool) | x y -> b
instance {-# OVERLAPPABLE #-} (b ~ False) => EQ x y b
instance {-# OVERLAPPING #-} EQ x x True



class UseTwo (v::Nat) (i::[Maybe Nat]) (o::[Maybe Nat]) | v i -> o
instance (UseTwo v i o) => UseTwo v (Nothing : Nothing : i) (Nothing : Nothing : o)
instance UseTwo x (Just (S x) : Just x : i) (Nothing : Nothing : i)



--
-- Type level machinery for consuming a variable in a list of variables.
--
class ConsumeOrd (v::Nat) (i::[Maybe Nat]) (o::[Maybe Nat]) | v i -> o
instance (ConsumeOrd v i o) => ConsumeOrd v (Nothing : i) (Nothing : o)
instance ConsumeOrd x (Just x : i) (Nothing : i) 


class ConsumeLin (v::Nat) (i::[Maybe Nat]) (o::[Maybe Nat]) | v i -> o
class ConsumeLinHelper (b::Bool) (v::Nat) (x::Nat) (i::[Maybe Nat]) (o::[Maybe Nat]) | b v x i -> o
instance (ConsumeLin v i o) => ConsumeLin v (Nothing : i) (Nothing : o)
instance (EQ v x b, ConsumeLinHelper b v x i o) => ConsumeLin v (Just x : i) o
instance ConsumeLinHelper True v x i (Nothing : i)
instance (ConsumeLin v i o) => ConsumeLinHelper False v x i (Just x : o)
                                      

class End (l :: [Maybe Nat]) (v :: Maybe Nat) (l' :: [Maybe Nat]) | l v -> l'
instance End '[] a (a : '[])
instance End a v2 b => End (v : a) v2 (v : b)

class Start (l :: [Maybe Nat]) (v :: Maybe Nat) (l' :: [Maybe Nat]) | l v -> l'
instance Start l v (v ': l)

class Concat (a :: [Maybe Nat]) (b :: [Maybe Nat]) (c :: [Maybe Nat]) | a b -> c, c a -> b
instance Concat '[] b b
instance Concat a b c => Concat (h : a) b (h : c)

newtype a :>-> b = SLolli {unSLolli :: a -> b}
newtype a :->> b = ELolli {unELolli :: a -> b}
newtype a :-<> b = LLolli {unLLolli :: a -> b}
newtype a :<>: b = Together { unTogether :: (a,b) }

data Phant (h :: [Maybe Nat]) = Phant

type OrdVar repr vid a = forall (v::Nat) (i::[Maybe Nat]) (o::[Maybe Nat]) . (ConsumeOrd vid i o) => repr v i o vid a 
type LinVar repr vid a = forall (v::Nat) (i::[Maybe Nat]) (o::[Maybe Nat]). (ConsumeLin vid i o) => repr v i o vid a
type RegVar repr (vid :: Nat) a = forall (v::Nat) (i::[Maybe Nat]) (c::Nat) . repr v i i vid a

class OrdSeq (repr :: Nat -> [Maybe Nat] -> [Maybe Nat] -> Nat -> * -> *) where
  forward :: (forall v . repr v hi ho y a)
          -> repr vid hi ho x a

  sR :: (OrdVar repr vid a -> repr (S vid) (Just vid : hi) (Nothing : ho) x b)
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

  -- this can use non ordered variables, but if they are ordered, it ensures that they come correctly identified.
  sendL' :: (forall v . repr v hi hi2 w a)
         -> (forall v . repr v hi2 ho x (a :>-> b))
         -> (OrdVar repr x b -> repr vid hi2 ho2 z c)
         -> repr vid hi ho2 z c
            
  llam :: (LinVar repr vid a -> repr (S vid) (Just vid : hi)  (Nothing : ho) x b)
       -> repr vid hi ho x (a :-<> b)
          
  lam :: (RegVar repr vid a -> repr (S vid) hi ho x b)
      -> repr vid hi ho x (a -> b)

  
eval :: R Z '[Nothing] '[Nothing] chan a -> a
eval = unR

tm = eval $ sR $ \y -> sR $ \z -> sL' z y (\f -> f)
tm1 = eval $ sR $ \y -> sR $ \z -> sendL' z y (\f -> f)

tm2 = eval $ llam $ \y -> llam $ \z -> sendL' y z (\f -> f)
-- tm2' = eval $ llam $ \y -> llam $ \z -> sL' y z (\f -> f) -- DOESN'T COMPILE because sL' only works with actual ordered chanels

-- tm3 = eval $ lam $ \y -> lam $ \z -> sendL' y z (\f -> f) -- DOESN'T COMPILE because sendL' only works with ordered or linear chanels

-- tm3 = eval $ lam $ \y -> lam $ \z -> sendL' y z (\f -> f) -- DOESN'T COMPILE because sendL' only works with ordered or linear chanels


newtype R (vid::Nat) (hi::[Maybe Nat]) (ho::[Maybe Nat]) (x :: Nat) a = R { unR :: a }

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



main = do
  -- putStrLn $ unLolli (eval $ good <^> llam (\x -> x)) "I was passed to a real function."
  putStrLn "ok"


