# coq-aern

Coq formalization of constructive reals for exact real computation and code extraction to Haskell/AERN.

## Installation instructions

Our formalization is implemented in the [Coq proof assistant](https://coq.inria.fr/).
You should have Coq installed and running.
We tested our code with Coq version 8.13.2.

To built the code you can just clone this repository and run `make` in the `formalization` subfolder.

Most of the implementation does not have any additional dependencies.
The only exception is the file `sqrt.v` which uses some libraries for classical analysis.

To execute `sqrt.v` you additionally need to install the following Coq packages:

* [Coquelicot 3.2](http://coquelicot.saclay.inria.fr/)
* [mathcomp-ssreflect 1.12.0](https://math-comp.github.io/)
* [interval 4.2.0](http://coq-interval.gforge.inria.fr/)

These libraries can be installed e.g. using `opam install`.

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
      import Prelude hiding (pi, pred, succ, (==),(/=),(<),(<=),(>),(>=),not,(&&),(||))
      import Numeric.OrdGenericBool
      import MixedTypesNumPrelude (ifThenElse, integer)
      import Math.NumberTheory.Logarithms (integerLog2)
      import AERN2.Real
      ```

* `ExtractMB.v`
  1. Add the following import statements:

      ```Haskell
      import Prelude hiding (pi, pred, succ, (==),(/=),(<), (<=),(>),(>=),not,(&&),(||))
      import Numeric.OrdGenericBool
      import MixedTypesNumPrelude (ifThenElse, integer,   Kleenean(..), kleenean)
      import Math.NumberTheory.Logarithms (integerLog2)
      import Numeric.CollectErrors (CN,cn,liftTakeErrors)
      import AERN2.MP
      import AERN2.MP.Dyadic ()
      import AERN2.MP.WithCurrentPrec
      import AERN2.Real
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

* Install `stack` (a Haskell build tool).

  * [Official stack installation instructions](https://docs.haskellstack.org/en/stable/install_and_upgrade/)

* Build the package using stack:

  * Locate the folder `extracted-examples`

  * (optional) Check that the provided `stack.yaml` meets your needs.

  * Run `stack install` in the `extracted-examples` folder.
  
    * The first time round it may take long time and install a large number of packages.
  
  * Test the executable:

    ```Text
    $ coq-aern-extracted-bench realmaxE 100
    [0 ± ~2.2569e-36 ~2^(-118)]
    accuracy: bits 118
    ```

* Execute the code in the Haskell interactive environment:

  ```Text
  $ stack repl src/Max.hs
  *Max> realmax ((sqrt 2)/2) (1/(sqrt 2)) ? (prec 1000)
  [0.707106781186547524400844362104849039284835937688474036588339868995366239231053519425193767163820... ± ~0.0000 ~2^(-1229)]
  ```
