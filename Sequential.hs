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


--
-- Type level machinery for consuming a variable in a list of variables.
--
class ConsumeOrd (v::Nat) (i::[Maybe Nat]) (o::[Maybe Nat]) | v i -> o
class ConsumeOrdHelper (b::Bool) (v::Nat) (x::Nat) (i::[Maybe Nat]) (o::[Maybe Nat]) | b v x i -> o
instance (ConsumeOrd v i o) => ConsumeOrd v (Nothing : i) (Nothing : o)
-- so this was easy, just remove the possibility of continuing if there's anything in the context we don't like.
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

class Concat (a :: [Maybe Nat]) (b :: [Maybe Nat]) (c :: [Maybe Nat]) -- | a b -> c, c a -> b
instance Concat '[] b b
instance Concat a b c => Concat (h : a) b (h : c)
                    

newtype OrdVar repr (vid::Nat) a = OrdVar { unOrdVar :: forall (v::Nat) (i::[Maybe Nat]) (o::[Maybe Nat]) . (ConsumeOrd vid i o) => repr v i o  a }

newtype a :>-> b = SLolli {unSLolli :: a -> b}
newtype a :->> b = ELolli {unELolli :: a -> b}
newtype a :<>: b = Together { unTogether :: (a,b) }

data Phant (h :: [Maybe Nat]) = Phant

class OrdSeq (repr :: Nat -> [Maybe Nat] -> [Maybe Nat] -> * -> *) where


  sL' :: forall hi ho hi' hi'' ho' ho'' hiU hoU vid a b c hi2.
          (Concat hi' (Just vid : hi'') hiU, -- hiU = hi',v,hi''
           Concat ho' (Nothing  : ho'') hoU, -- hoU = ho',N,ho''

           Concat hi' (Just vid : Just (S vid) : hi'') hi, -- hi = hi',v,v',hi''
           Concat ho' (Nothing  : Nothing : ho'') ho -- ho = ho',N,N,ho''

          , ConsumeOrd vid hi hi2
          , ConsumeOrd (S vid) hi2 ho
          )      
      => Phant hi2
      -> Phant hi'
      -> Phant ho'
      -> Phant hi''
      -> Phant ho''      
      -> (OrdVar repr vid b -> repr (S (S vid)) hiU hoU c)
      -> (forall v hi . (ConsumeOrd vid hi hi2) => repr v hi hi2 a)
      -> (forall v ho . (ConsumeOrd (S vid) hi2 ho) => repr v hi2 ho (a :>-> b))
      -> repr (S (S vid)) hi ho c
          
  eR :: (End hi (Just vid) hi', End ho Nothing ho')
     => (OrdVar repr vid a -> repr (S vid) hi' ho' b)
     -> repr vid hi ho (a :->> b)
          
  sR :: (OrdVar repr vid a -> repr (S vid) (Just vid : hi) (Nothing : ho) b)
       -> repr vid hi ho (a :>-> b)

  eL' ::  forall hi ho hi' hi'' ho' ho'' hiU hoU hi2 vid a b c .
          (Concat hi' (Just vid : hi'') hiU, -- hiU = hi',v,hi''
           Concat ho' (Nothing  : ho'') hoU, -- hoU = ho',N,ho''

           Concat hi' (Just vid : Just (S vid) : hi'') hi, -- hi = hi',v,v',hi''
           Concat ho' (Nothing  : Nothing : ho'') ho, -- ho = ho',N,N,ho''

           ConsumeOrd vid hi hi2,
           ConsumeOrd (S vid) hi2 ho
          )      
      => (OrdVar repr vid b -> repr (S (S vid)) hiU hoU c)
      -> repr vid hi hi2 (a :->> b) -> repr (S vid) hi2 ho a -> repr (S (S vid)) hi ho c


newtype R (vid::Nat) (hi::[Maybe Nat]) (ho::[Maybe Nat]) a = R { unR :: a }

var :: b -> OrdVar R vid b
var a = OrdVar $ R a

term :: ConsumeOrd vid i o => OrdVar repr vid a -> repr v i o a
term var = unOrdVar var

instance OrdSeq R where
    sR f = R $ SLolli $ \x -> unR $ f $ OrdVar $ R x
    eR f = R $ ELolli $ \x -> unR $ f $ OrdVar $ R x
{-
    eL' (procQ :: OrdVar R vid b -> R (S (S vid)) hiU hoU z c) (vXf :: forall x . R vid hi hi2 x (a :->> b)) (vWa :: forall w . R (S vid) hi2 ho w a) =
      R $ unR $ procQ $ var $ (((unELolli $ unR $ (vXf :: R vid hi hi2 w (a :->> b))
                              ) $ unR (vWa :: R (S vid) hi2 ho w a)
                             ) :: b) -}
    eL' procQ vXf vWa = R $ unR $ procQ $ var $ (unELolli $ unR vXf) $ unR vWa

    sL' :: forall hi ho hi' hi'' ho' ho'' hiU hoU vid a b c hi2.
          (Concat hi' (Just vid : hi'') hiU, -- hiU = hi',v,hi''
           Concat ho' (Nothing  : ho'') hoU, -- hoU = ho',N,ho''

           Concat hi' (Just vid : Just (S vid) : hi'') hi, -- hi = hi',v,v',hi''
           Concat ho' (Nothing  : Nothing : ho'') ho -- ho = ho',N,N,ho''

          , ConsumeOrd vid hi hi2
          , ConsumeOrd (S vid) hi2 ho
          )      
      => Phant hi2
      -> Phant hi'
      -> Phant ho'
      -> Phant hi''
      -> Phant ho''            
      -> (OrdVar R vid b -> R (S (S vid)) hiU hoU c)
      -> (forall v hi . (ConsumeOrd vid hi hi2) => R v hi hi2 a)
      -> (forall v ho . (ConsumeOrd (S vid) hi2 ho) => R v hi2 ho (a :>-> b))
      -> R (S (S vid)) hi ho c
    sL' _ _ _ _ _ procQ vWa vXf =
      R $ unR $ procQ $ var $ (unSLolli $ unR vXf) $ unR (vWa :: R vid hi hi2 a)

eval :: R Z '[] '[] a -> a
eval = unR

{-

                ------------------------ Id
                   x : B |- Q :: z : B
   -------------------------------------------------- sL*
       w: A, x : A >-> B |- (send x w ; Q) :: z : B
---------------------------------------------------------------  sR
     x : A >-> B |- (w ← recv z ; send x w ; Q)  :: z : A >-> B
-----------------------------------------------------------------------------  sR
|- (x ← recv z ; (w ← recv z ; (send x w ; Q))  :: z : (A >-> B) >-> (A >-> B)

-}
--good = eval $ sR $ \x -> sR $ \w -> sL' (\f -> undefined) (term x) (term w)

main = do
  -- putStrLn $ unLolli (eval $ good <^> llam (\x -> x)) "I was passed to a real function."
  putStrLn "ok"

