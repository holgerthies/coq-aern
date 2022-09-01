{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module R_Test2 where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
real_limit_p :: (Prelude.Integer -> AERN2.CReal) -> AERN2.CReal
real_limit_p = AERN2.limit

r_test2 :: (Prelude.Integer -> AERN2.CReal) -> AERN2.CReal
r_test2 =
  real_limit_p

