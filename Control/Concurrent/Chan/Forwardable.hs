module Control.Concurrent.Chan.Forwardable ( Chan()
                                           , newChan
                                           , writeChan
                                           , readChan
                                           , forwardChan
                                           ) where

import qualified Control.Concurrent.Chan.Unagi as U
import Control.Concurrent.MVar


type UnagiChan a = (U.InChan a, U.OutChan a)

newtype Chan a = Chan { unChan :: (MVar (U.InChan a), MVar (U.OutChan a)) }


newChan = do
  (ci,co) <- U.newChan
  mi <- newMVar ci
  mo <- newMVar co 
  return $ Chan (mi,mo)


writeChan (Chan (mi,mo)) v = withMVar mi $ \ci -> U.writeChan ci v
  
readChan (Chan (mi,mo)) = do
  co <- takeMVar mo
  v <- U.readChan co
  tryPutMVar mo co
  return v

-- how does this behave with multiple forwardings?
forwardChan (Chan (mi,mo)) (Chan (mi',mo')) = do
  ci' <- withMVar mi $ swapMVar mi'

  -- it's safe to perform what is essentially a read here,
  -- since we already placed c's input channel in c' so further
  -- inputs on both channels will be mapped to here.
  withMVar mo $ \co -> do
    mco' <- tryTakeMVar mo'
    case mco' of
      Nothing -> do
        -- we know somebody is reading "co'" and nothing will
        -- ever write to "ci'" because we already performed the swap.
        v <- U.readChan co
        -- thusly, its safe to do a putMVar here since we know
        -- that "tryPutMVar mo co" won't do anything after we've done this.
        -- and that future "takeMVars mo'" are going to rely
        -- on the new "co" rather than "ci'" so they are permitted to run
        -- concurrently.
        putMVar mo' co        
        U.writeChan ci' v
        
      Just co' -> do
        putMVar mo' co
