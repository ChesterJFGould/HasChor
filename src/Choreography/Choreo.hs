{-# LANGUAGE GADTs              #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE StandaloneKindSignatures #-}

-- | This module defines `Choreo`, the monad for writing choreographies.
module Choreography.Choreo where

import Choreography.Location
import Choreography.Network
import Control.Monad.Freer
import Data.Kind
import Data.List
import Data.Proxy
import Data.Type.Equality
import Data.Type.Ord
import Data.Void
import GHC.TypeLits

-- * The Choreo monad

-- | A constrained version of `unwrap` that only unwraps values located at a
-- specific location.
type Unwrap l = forall a. a @ l -> a

-- | Effect signature for the `Choreo` monad. @m@ is a monad that represents
-- local computations.
data ChoreoSig locTy (s :: locTy -> Type) (n :: locTy) (m :: * -> *) a where
  Local :: s l
        -> (n :~: l -> m a)
        -> ChoreoSig locTy s n m (At n l a)

  Comm :: (Show a, Read a)
       => s l
       -> At n l a
       -> s l'
       -> ChoreoSig locTy s n m (At n l' a)

  Cond :: (Show a, Read a)
       => s l
       -> At n l a
       -> (a -> Choreo locTy s n m b)
       -> ChoreoSig locTy s n m b

-- | Monad for writing choreographies.
type Choreo locTy (s :: locTy -> Type) (n :: locTy) (m :: * -> *) = Freer (ChoreoSig locTy s n m)

data Unit = It

data UnitS (u :: Unit) where
  ItS :: UnitS It

-- | Run a `Choreo` monad directly.
runChoreo :: Monad m => Choreo Unit UnitS It m a -> m a
runChoreo = interpFreer handler
  where
    handler :: Monad m => ChoreoSig Unit UnitS It m a -> m a
    -- handler (Local (_ :: Proxy l) loc) = gcastWith (unitContractible :: It :~: l) (loc unitContractible)
    handler (Local ItS loc) = fmap (\a _ -> a) (loc Refl)
    handler (Comm ItS a ItS) = return a
    handler (Cond ItS a c) = runChoreo (c (a Refl))

-- | Endpoint projection.
epp :: forall n m a. Functor m => Choreo LocTy SSymbol n m a -> SSymbol n -> Network m a
epp c l'@SSymbol = interpFreer handler c
  where
    handler :: forall a. ChoreoSig LocTy SSymbol n m a -> Network m a
    handler (Local l@SSymbol m)
      | Right Refl <- decideSymbol l l' = run ((\a Refl -> a) <$> m Refl) -- run (fmap (\a _ -> a) (m Refl))
      | Left neq <- decideSymbol l l'   = return (\eq -> absurd (neq (sym eq)))
    handler (Comm s@SSymbol a r@SSymbol) =
      case (decideSymbol s r, decideSymbol s l', decideSymbol r l') of
        (Right Refl, Right Refl, Right Refl) -> return (\Refl -> a Refl)
        (_, Right Refl, Left neq) -> send (a Refl) (toLocTm r) >> return (\Refl -> absurd (neq Refl))
        (_, _, Right Refl) -> (\a Refl -> a) <$> recv (toLocTm s)
        (_, _, Left neq) -> return (\Refl -> absurd (neq Refl))
    handler (Cond l@SSymbol a c)
      | Right Refl <- decideSymbol l l' = broadcast (a Refl) >> epp (c (a Refl)) l'
      | otherwise = recv (toLocTm l) >>= \x -> epp (c x) l'

-- * Choreo operations

-- | Perform a local computation at a given location.
locally :: s l           -- ^ Location performing the local computation.
        -> m a -- ^ The local computation given a constrained
                             -- unwrap function.
        -> Choreo locTy s n m (At n l a)
locally l m = toFreer (Local l (\Refl -> m))

-- | Communication between a sender and a receiver.
(~>) :: (Show a, Read a)
     => (s l, At n l a)  -- ^ A pair of a sender's location and a value located
                          -- at the sender
     -> s l'          -- ^ A receiver's location.
     -> Choreo locTy s n m (At n l' a)
(~>) (l, a) l' = toFreer (Comm l a l')

-- | Conditionally execute choreographies based on a located value.
cond :: (Show a, Read a)
     => (s l, At n l a)  -- ^ A pair of a location and a scrutinee located on
                          -- it.
     -> (a -> Choreo locTy s n m b) -- ^ A function that describes the follow-up
                          -- choreographies based on the value of scrutinee.
     -> Choreo locTy s n m b
cond (l, a) c = toFreer (Cond l a c)

-- | A variant of `~>` that sends the result of a local computation.
(~~>) :: (Show a, Read a)
      => (s l, m a) -- ^ A pair of a sender's location and a local
                                    -- computation.
      -> s l'                   -- ^ A receiver's location.
      -> Choreo locTy s n m (At n l' a)
(~~>) (l, m) l' = do
  x <- l `locally` m
  (l, x) ~> l'

-- | A variant of `cond` that conditonally executes choregraphies based on the
-- result of a local computation.
cond' :: (Show a, Read a)
      => (s l, m a) -- ^ A pair of a location and a local
                                    -- computation.
      -> (a -> Choreo locTy s n m b)          -- ^ A function that describes the follow-up
                                    -- choreographies based on the result of the
                                    -- local computation.
      -> Choreo locTy s n m b
cond' (l, m) c = do
  x <- l `locally` m
  cond (l, x) c
