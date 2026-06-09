{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Trans.Compose
-- Copyright   :  (C) 2026 The transformers Authors
-- License     :  BSD-style (see the file LICENSE)
--
-- This combines two transformers into a single compound transformer.
-- Potentially useful for when a single transformer is required as a type
-- argument.
-----------------------------------------------------------------------------

module Control.Monad.Trans.Composed where

import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Trans.Class (MonadTrans (lift), MonadTransUnder (liftUnder))
import Data.Kind (Type, Constraint)

import Control.Monad.Trans.Compose
import Control.Monad.Trans.Identity (IdentityT (IdentityT))
import Control.Monad.Trans.Reader (ReaderT (ReaderT), ask)
import Control.Monad.Trans.State.Strict (StateT (StateT), put, get)
import Data.Functor.Identity (Identity (runIdentity))

type GetComposed :: [(Type -> Type) -> Type -> Type] -> (Type -> Type) -> Type -> Type
type family GetComposed (ts :: [(Type -> Type) -> Type -> Type]) where
  GetComposed '[] = IdentityT
  GetComposed (t : ts) = t `ComposeT` GetComposed ts

newtype ComposedT (ts :: [(Type -> Type) -> Type -> Type]) m a
  = MkComposedT { runComposedT :: (GetComposed ts) m a }

type ComposedT' ts a = ComposedT ts Identity a

deriving instance Functor (GetComposed ts m) => Functor (ComposedT ts m)
deriving instance Applicative (GetComposed ts m) => Applicative (ComposedT ts m)
deriving instance Monad (GetComposed ts m) => Monad (ComposedT ts m)
deriving instance (MonadIO (GetComposed ts m)) => MonadIO (ComposedT ts m)

class TransformerIn t ts where
  liftTo :: Monad m => t Identity a -> ComposedT ts m a

instance {-# OVERLAPPING #-} (MonadTransUnder t, (forall m . Monad m => Monad (ComposedT ts m))) => TransformerIn t (t : ts) where
  liftTo :: (Monad m) =>
    t Identity a -> ComposedT (t : ts) m a
  liftTo action = MkComposedT (ComposeT $ liftUnder (runComposedT @ts . pure . runIdentity) action)

instance (MonadTransUnder t', TransformerIn t ts, MonadTrans t', (forall m . Monad m => Monad (ComposedT ts m))) => TransformerIn t (t' : ts) where
  liftTo :: forall m a. (Monad m) =>
    t Identity a -> ComposedT (t' : ts) m a
  liftTo action = MkComposedT $ ComposeT $ liftUnder runComposedT $ (lift @t' @(ComposedT ts m)) (liftTo @t @ts action)

test :: ComposedT [ReaderT Int, StateT String] IO ()
test = do
  r <- liftTo ask
  liftTo $ put "world!"
  liftIO $ print (r :: Int)
  liftIO . putStrLn =<< liftTo get

type (:>) :: ((Type -> Type) -> Type -> Type) -> [(Type -> Type) -> Type -> Type] -> Constraint
type t :> ts = (forall m . Monad m => Monad (ComposedT ts m), TransformerIn t ts)

-- test1 :: (ReaderT Int :> ts, StateT String :> ts, IOT :> ts) => ComposedT' ts ()
-- test1 = do
--   r <- liftTo ask
--   liftTo $ put "world!"
--   liftIO $ print (r :: Int)
--   liftIO . putStrLn =<< liftTo get

runAct :: (forall n . t n a -> n b) -> ComposedT (t : ts) m a -> ComposedT ts m b
runAct runSomeAct (MkComposedT act) = MkComposedT (runSomeAct (runComposeT act))

runReader :: forall r ts m a . r -> ComposedT (ReaderT r : ts) m a -> ComposedT ts m a
runReader r = runAct runSomeReader
  where
  runSomeReader :: ReaderT r n a -> n a
  runSomeReader (ReaderT f) = f r

runState :: forall s ts m a . s -> ComposedT (StateT s : ts) m a -> ComposedT ts m (a, s)
runState s = runAct runSomeState
  where
  runSomeState :: StateT s n a -> n (a, s)
  runSomeState (StateT f) = f s

runEmpty :: ComposedT '[] m a -> m a
runEmpty (MkComposedT (IdentityT ma)) = ma
