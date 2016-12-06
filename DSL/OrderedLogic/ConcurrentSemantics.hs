{-# LANGUAGE PartialTypeSignatures #-}
module DSL.OrderedLogic.ConcurrentSemantics where

import DSL.OrderedLogic.OrderedTypes

import Control.Applicative
import Control.Concurrent (forkIO)
import Control.Concurrent.Chan.Forwardable
import Debug.Trace


newtype Ch (hi::[Cont]) (ho::[Cont]) (x::Nat) a = Ch { unCh :: Chan a }
newtype C (vid::Nat) (hi::[Cont]) (ho::[Cont]) (x :: Nat) a = C { unC :: (forall hi ho . Ch hi ho x a) -> IO () }


newtype a :>-> b = SLolli {unSLolli :: (Chan a, Chan b) }
newtype a :->> b = ELolli {unELolli :: (Chan a, Chan b) }
newtype a :-<> b = LLolli {unLLolli :: (Chan a, Chan b) }
newtype a :->  b = Lolli  {unLolli  :: (Chan a, Chan b) }
  
instance OrdSeq C where
  type Name C = Ch

  type SLolli C = (:>->)
  type ELolli C = (:->>)  
  type LLolli C = (:-<>)
  type Lolli C = (:->)

  forward (Ch y) = C $ \(Ch x) -> forwardChan x y
  
  bif _ (C pa) qa_c = C $ \cc -> do
    cw <- newChan
    forkIO $ (unC $ qa_c $ Ch cw) cc
    pa $ Ch cw


  sRecv f = C $ \cab -> do
    (ca,cb) <- unSLolli <$> readChan (unCh cab)
    unC (f $ Ch ca) $ Ch cb
    
  sSend ca cab procB_C = C $ \cc -> do
    cb <- newChan
    writeChan (unCh cab) $ SLolli (unCh ca, cb)
    unC (procB_C $ Ch cb) cc


  eRecv f = C $ \cab -> do
    (ca,cb) <- unELolli <$> readChan (unCh cab)
    unC (f $ Ch ca) $ Ch cb

  eSend cab ca procB_C = C $ \cc -> do
    cb <- newChan
    forkIO $ unC (procB_C $ Ch cb) cc
    writeChan (unCh cab) $ ELolli (unCh ca, cb)    


  lRecv f = C $ \cab -> do
    (ca,cb) <- unLLolli <$> readChan (unCh cab)
    unC (f $ Ch ca) $ Ch cb

  lSend ca cab procB_C = C $ \cc -> do
    cb <- newChan
    forkIO $ unC (procB_C $ Ch cb) cc
    writeChan (unCh cab) $ LLolli (unCh ca, cb)    


  recv f = C $ \cab -> do
    (ca,cb) <- unLolli <$> readChan (unCh cab)
    unC (f $ Ch ca) $ Ch cb

  send ca cab procB_C = C $ \cc -> do
    cb <- newChan
    writeChan (unCh cab) $ Lolli (unCh ca, cb)        
    unC (procB_C $ Ch cb) cc


evalC :: C Z '[] '[] chan a -> a -> IO ()
evalC e a = do
  c <- newChan
  writeChan c a
  unC e $ Ch c

tm :: (a :>-> b) :>-> (a :>-> b) -> IO ()
tm = evalC $ sRecv $ \y ->
  bif P -- (P :: Phant (Om (S Z):'[]))
    (sRecv $ \z -> sSend z y forward )
  $ forward
  

tm2 :: b :>-> b -> IO ()
tm2 = evalC $ sRecv forward

main = do
  a <- newChan
  b <- newChan

  tm2 $ SLolli (a, b)
  putStrLn "hi"  
  tm $ SLolli (a, b)


