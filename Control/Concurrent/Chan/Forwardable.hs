module Control.Concurrent.Chan.Forwardable {- ( Chan()
                                           , newChan
                                           , writeChan
                                           , readChan
                                           , forwardChan
                                           ) -} where

import qualified Control.Concurrent.Chan.Unagi as U
import Control.Concurrent.MVar
import Data.IORef
import Control.Concurrent (forkIO)

type UChan a = (U.InChan a, U.OutChan a)
type WIO a = Either a (IO a)

newtype Chan a = Chan { unChan :: (MVar (U.InChan (WIO a)), IORef (U.OutChan (WIO a))) }


newChan = do
  (ci,co) <- U.newChan
  mi <- newMVar ci
  to <- newIORef co


  return $ Chan (mi,to)

-- can't put a rwlock between these because both a rwRead/rwWrite on the readChan
-- might block either the rwWrite/rwRead necessary to unblock it on the writeChan
writeChan (Chan (mi,_)) v = withMVar mi $ \ci -> U.writeChan ci (Left v)


-- can't put a rwlock between readChan and forwardChan because both a rwRead/rwWrite on the readChan
-- might block either rwWrite/rwRead forwardChan which might open up a writeChan on the opposite
-- channel
readChan (Chan (mi,to)) = do
  v <- readIORef to >>= U.readChan
  case v of
    Right b -> b
    Left v -> return v
  
-- how does this behave with multiple forwardings?
forwardChan :: forall a . Chan a -> Chan a -> IO ()    
forwardChan c@(Chan (mi,to)) (Chan (mi',to')) = do
  ci' <- withMVar mi $ swapMVar mi'
  
  co' <- readIORef to'
  atomicWriteIORef to' =<< readIORef to
    
  let getOldOrNew :: IO a
      getOldOrNew = do
        (v,_) <- U.tryReadChan co'
        v <- U.tryRead v
        case v of
          Just (Left v) -> do
            -- we know we just read from the chan co' because getOldOrNew was called
            v' <- U.readChan co' -- thus we need to actually read it.
            return v
          _ -> do -- we know we aren't putting anything new on ci', so we need something off co
            readChan c
        
  U.writeChan ci' $ Right getOldOrNew -- executes if we're stuck on a read.
    

void = (>> return ())

