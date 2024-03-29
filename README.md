# Axiomatic Reals and Certified Efficient Exact Real Computation <!-- omit in toc -->

Coq formalization of constructive reals for exact real computation and code extraction to Haskell/AERN.

## Table of contents <!-- omit in toc -->

- [1. Installation instructions](#1-installation-instructions)
- [2. Code extraction to Haskell/AERN](#2-code-extraction-to-haskellaern)
  - [2.1. Post-processing](#21-post-processing)
- [3. Executing extracted code](#3-executing-extracted-code)
  - [3.1. Executing interactively](#31-executing-interactively)
  - [3.2. Compiling benchmark executable](#32-compiling-benchmark-executable)
- [4. Benchmark measurements](#4-benchmark-measurements)

## 1. Installation instructions

Our formalization is implemented in the [Coq proof assistant](https://coq.inria.fr/).
You should have Coq installed and running.
We tested our code with Coq version 8.13.2.

To built the code you can just clone this repository and run `make` in the `formalization` subfolder.

Most of the implementation does not have any additional dependencies.
The only exception is the file `sqrt.v` which uses some libraries for classical analysis.

To execute `sqrt.v` you additionally need to install the following Coq packages:

- [Coquelicot 3.2](http://coquelicot.saclay.inria.fr/)
- [mathcomp-ssreflect 1.12.0](https://math-comp.github.io/)
- [interval 4.2.0](http://coq-interval.gforge.inria.fr/)

These libraries can be installed e.g. using `opam install`.

## 2. Code extraction to Haskell/AERN

Code extraction is defined in the following file:

- `extract.v`

After processing this file, Coq produces Haskell files, one for each example.  The files need minor mechanical post-processing described below.  The extracted post-processed compilable code is also readily available in folder [extracted-examples/src](extracted-examples/src).
For example, the extracted version of `real_max` is in file `Max.hs`.

### 2.1. Post-processing

1. Add the following statements after the last import statement in the generated file:

    ```Haskell
    import MixedTypesNumPrelude (ifThenElse)
    import qualified Numeric.OrdGenericBool as OGB
    import qualified Unsafe.Coerce as UC
    import qualified Control.Monad
    import qualified Data.Functor
    import qualified MixedTypesNumPrelude as MNP
    import qualified Math.NumberTheory.Logarithms as Logs
    import qualified AERN2.Real as AERN2

    __uc :: a -> b
    __uc = UC.unsafeCoerce
    __K :: a -> AERN2.CKleenean
    __K = UC.unsafeCoerce
    __R :: a -> AERN2.CReal
    __R = UC.unsafeCoerce
    ```

## 3. Executing extracted code

- Install `stack` (a Haskell build tool).

  - [Official stack installation instructions](https://docs.haskellstack.org/en/stable/install_and_upgrade/)
- Locate the folder `extracted-examples`

- (optional) Check that the provided `stack.yaml` meets your needs.

### 3.1. Executing interactively

  ```Text
  $ stack repl src/Max.hs --ghci-options "-Wno-unused-matches -Wno-unused-imports -Wno-type-defaults"

  *Max> import Prelude
  *Max Prelude> import AERN2.Real hiding (pi)
  *Max Prelude AERN2.Real> r_real_max ((sqrt 2)/2) (1/(sqrt 2)) ? (bits 1000)
  [0.707106781186547524400844362104849039284835937688474036588339868995366239231053519425193767163820... ± ~0.0000 ~2^(-1229)]

  *Max Prelude AERN2.Real> (r_real_max (pi-pi) 0) ? (bits 1000)
  [0 ± ~0.0000 ~2^(-1228)]
  ```

### 3.2. Compiling benchmark executable

- Run `stack install` in the `extracted-examples` folder.
  
  - The first time round it may take long time and install a large number of packages.
  
- Test the executable:

  ```Text
  $ coq-aern-extracted-bench realmaxE 100
  [0 ± ~2.2569e-36 ~2^(-118)]
  accuracy: bits 118
  ```

## 4. Benchmark measurements

The file [all.ods](extracted-examples/bench/all.ods) in folder [extracted-examples/bench](extracted-examples/bench) summarises our benchmark measurements.
The measurements were made on a Lenovo T440p laptop with Intel i7-4710MQ CPU and 16GB RAM, OS Ubuntu 18.04, compiled using Haskell Stackage LTS 17.2.

The benchmarks measurements can be reproduced using the provided `bash` script [runBench.sh](extracted-examples/bench/runBench.sh):

```Text
$ mkdir -pv logs/{civt{1,2,3},sqrt{1,2},realmax}
...
mkdir: created directory 'logs/realmax'

$ bash bench/runBench.sh my_all.csv
/usr/bin/time -v coq-aern-extracted-bench realmaxE 1000000 (running and logging in logs/realmax/run-realmax-1000000-E.log)
...
```
