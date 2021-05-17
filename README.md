# coq-aern

Coq formalization of constructive reals for exact real computation and code extraction to Haskell/AERN.

## Installation instructions

You should have coq installed and running.
We tested our code with coq version 8.13.2.

The square root example has some additional dependencies:

* coquelicot 3.2
* mathcomp-ssreflect 1.12.0
* interval 4.2.0

## Code extraction to Haskell/AERN 

Code extraction is available in two modes, as defined in the following files, respectively:

* `Extract.v`
* `ExtractMB.v`

After processing these files, coq produces Haskell files, one for each example and mode.  The files need minor mechanical post-processing described below.  The extracted post-processed compilable code is also available in folder [extracted-examples/src](extracted-examples/src).
For example, the executable versions of `realmax` are in files `Max.hs` and `MaxMB.hs`.

### Post-processing

* `Extract.v`
  1. Add the following import statements

        ```Haskell
        import Prelude hiding (pred, succ, (==),(/=),(<),(<=),(>),(>=),not,(&&),(||))
        import Numeric.OrdGenericBool
        import MixedTypesNumPrelude (ifThenElse, integer)
        import Math.NumberTheory.Logarithms (integerLog2)
        import AERN2.Real
        ```

* `ExtractMB.v`
  1. Add the following import statements:

      ```Haskell
      import Prelude hiding (pred, succ, (==),(/=),(<), (<=),(>),(>=),not,(&&),(||))
      import Numeric.OrdGenericBool
      import MixedTypesNumPrelude (ifThenElse, integer,   Kleenean(..), kleenean)
      import Math.NumberTheory.Logarithms (integerLog2)
      import Numeric.CollectErrors (CN,cn,liftTakeErrors)
      import AERN2.MP
      import AERN2.MP.Dyadic ()
      import AERN2.MP.WithCurrentPrec
      import AERN2.Limit
      import AERN2.Real(select)
      import AERN2.Real.Type
      ```

  2. Add the following LANGUAGE options:

      ```Haskell
      {-# LANGUAGE DataKinds #-}
      {-# LANGUAGE PolyKinds #-}
      ```

  3. Add the following type constraint to all functions whose type signature contains the type variable `p`:

      ```Haskell
      (HasCurrentPrecision p) => 
      ```

## Benchmark measurements

The file [all.ods](extracted-examples/bench/all.ods) in folder [extracted-examples/bench](extracted-examples/bench) summarises our benchmark measurements.
The measurements were made on a Lenovo T440p laptop with Intel i7-4710MQ CPU and 16GB RAM, OS Ubuntu 18.04, compiled using Haskell Stackage LTS 17.2.

The benchmarks measurements can be reproduced using the provided script [runBench.sh](extracted-examples/bench/runBench.sh) and the executable `coq-aern-extracted-bench` which can be compiled using the instructions below.

## Executing extracted code

