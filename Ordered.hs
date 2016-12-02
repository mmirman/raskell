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
  GADTs
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
instance (ConsumeOrd v i o) => ConsumeOrd v (Nothing ': i) (Nothing ': o)
-- so this was easy, just remove the possibility of continuing if there's anything in the context we don't like.
instance ConsumeOrd x (Just x ': i) (Nothing ': i) 



class ConsumeLin (v::Nat) (i::[Maybe Nat]) (o::[Maybe Nat]) | v i -> o
class ConsumeLinHelper (b::Bool) (v::Nat) (x::Nat) (i::[Maybe Nat]) (o::[Maybe Nat]) | b v x i -> o
instance (ConsumeLin v i o) => ConsumeLin v (Nothing ': i) (Nothing ': o)
instance (EQ v x b, ConsumeLinHelper b v x i o) => ConsumeLin v (Just x ': i) o
instance ConsumeLinHelper True v x i (Nothing ': i)
instance (ConsumeLin v i o) => ConsumeLinHelper False v x i (Just x ': o)
                                      

class End (l :: [Maybe Nat]) (v :: Maybe Nat) (l' :: [Maybe Nat]) | l v -> l'
instance End '[] a (a ': '[])
instance End a v2 b => End (v ': a) v2 (v ': b)

class Start (l :: [Maybe Nat]) (v :: Maybe Nat) (l' :: [Maybe Nat]) | l v -> l'
instance Start l v (v ': l)

class Concat (a :: [Maybe Nat]) (b :: [Maybe Nat]) (c :: [Maybe Nat]) | a b -> c, c a -> b
instance Concat '[] b b
instance Concat a b c => Concat (h ': a) b (h ': c)
                    

type OrdVar repr (vid::Nat) a = forall (v::Nat) (i::[Maybe Nat]) (o::[Maybe Nat]). (ConsumeOrd vid i o) => repr v i o a
type LinVar repr (vid::Nat) a = forall (v::Nat) (i::[Maybe Nat]) (o::[Maybe Nat]). (ConsumeLin vid i o) => repr v i o a
type RegVar repr a = forall (v::Nat) (i::[Maybe Nat]) . repr v i i a

class Arrow (t :: * -> * -> *) where
  unArrow :: t a b -> (a -> b)

instance Arrow (->) where
  {-# INLINE unArrow #-}
  unArrow f = f

newtype a :>-> b = SLolli {unSLolli :: a -> b}
instance Arrow (:>->) where
  {-# INLINE unArrow #-}
  unArrow = unSLolli
                            
newtype a :->> b = ELolli {unELolli :: a -> b}
instance Arrow (:->>) where
  {-# INLINE unArrow #-}
  unArrow = unELolli

newtype a :-<> b = Lolli {unLolli :: a -> b}                            
instance Arrow (:-<>) where
  {-# INLINE unArrow #-}
  unArrow = unLolli

newtype a :<>: b = Together { unTogether :: (a,b) }

class OrdNat (repr :: Nat -> [Maybe Nat] -> [Maybe Nat] -> * -> *) where
  slam :: (OrdVar repr vid a -> repr (S vid) (Just vid ': hi) (Nothing ': ho) b)
       -> repr vid hi ho (a :>-> b)
          
  elam :: (End hi (Just vid) hi', End ho Nothing ho')
       => (OrdVar repr vid a -> repr (S vid) hi' ho' b)
       -> repr vid hi ho (a :->> b)


  useTogether :: (Concat hi1 hi2 hi,
                  Concat ho1 ho2 ho,

                  End hi1 (Just vid) hi1',
                  End ho1 Nothing ho1',
                  
                  Start hi2 (Just (S vid)) hi2',
                  Start ho2 Nothing ho2',

                  Concat hi1' hi2' hi'',
                  Concat ho1' ho2' ho''
                  )
              => repr vid hi' hi (a :<>: b)
              -> (OrdVar repr vid a -> OrdVar repr (S vid) b -> repr (S (S vid)) hi'' ho'' c)
              -> repr vid hi' ho c

  

  llam :: (LinVar repr vid a -> repr (S vid) (Just vid ': hi)  (Nothing ': ho) b)
       -> repr vid hi ho (a :-<> b)

  lam :: (RegVar repr a -> repr vid hi ho b)
      -> repr vid hi ho (a -> b)

  -- polymorphism could be good, could be bad.  Who's to say?
  ($$) :: Arrow t => repr vid hi h (t a b) -> repr vid h ho a -> repr vid hi ho b  



newtype R (vid::Nat) (hi::[Maybe Nat]) (ho::[Maybe Nat]) a = R { unR :: a }

instance OrdNat R where
    elam f = R $ ELolli $ \x -> unR $ f $ R x
    slam f = R $ SLolli $ \x -> unR $ f $ R x
    llam f = R $ Lolli $ \x -> unR $ f $ R x
    lam f = R $ \x -> unR $ f $ R x

    useTogether tog f = let (x,y) = unTogether $ unR tog in R $ unR $ f (R x) (R y)
    
    {-# INLINE ($$) #-}    
    f $$ x = R $ unArrow (unR f) (unR x)
    
eval :: R Z '[] '[] a -> a
eval = unR

good = eval $ llam $ \r -> slam $ \f -> slam $ \x -> (\a b -> b $$ a) f x $$ r

main = do
  -- putStrLn $ unLolli (eval $ good <^> llam (\x -> x)) "I was passed to a real function."
  putStrLn "ok"

