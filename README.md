# Axiomatic Reals and Certified Efficient Exact Real Computation <!-- omit in toc -->

Coq formalization of constructive reals for exact real computation and code extraction to Haskell/AERN.

## Table of contents <!-- omit in toc -->

- [1. Installation instructions](#1-installation-instructions)
- [2. Code extraction to Haskell/AERN](#2-code-extraction-to-haskellaern)
  - [2.1. Post-processing](#21-post-processing)
- [3. Executing extracted code](#3-executing-extracted-code)
  - [3.1. Executing interactively](#31-executing-interactively)
  - [3.2. ODE solver example](#32-ode-solver-example)
  - [3.3. Compiling benchmark executable](#33-compiling-benchmark-executable)
- [4. Benchmark measurements](#4-benchmark-measurements)

## 1. Installation instructions

Our formalization is implemented in the [Coq proof assistant](https://coq.inria.fr/).
You should have Coq installed and running, with the option to install further packages via `opam`.
We tested our code with Coq version 8.18.0 [installed via opam](https://coq.inria.fr/opam-using.html).

To build the code you can just clone this repository and run `make` in the `formalization` subfolder.

Most of the implementation does not have any additional dependencies.
The only exception is the file `sqrt.v` which uses some libraries for classical analysis.

To execute `sqrt.v` you additionally need to install the following Coq packages:

- [Coquelicot 3.4.2](http://coquelicot.saclay.inria.fr/)
- [mathcomp-ssreflect 1.19.0](https://math-comp.github.io/)
- [interval 4.11.0](http://coq-interval.gforge.inria.fr/)

These libraries can be installed e.g. using `opam install`.

## 2. Code extraction to Haskell/AERN

Code extraction is defined in the following file:

- `Extract.v`

After processing this file, Coq produces Haskell files, one for each example.  The files need minor mechanical post-processing described below.  The extracted post-processed compilable code is also readily available in folder [extracted-examples/src](extracted-examples/src).
For example, the extracted version of `real_max` is in file `Max.hs`.

### 2.1. Post-processing

1. Add the following statements after the last import statement in the generated file:

    ```Haskell
    import Prelude ((+),(-),(/))
    import qualified Prelude as P
    import MixedTypesNumPrelude (ifThenElse)
    import qualified Numeric.OrdGenericBool as OGB
    import qualified Unsafe.Coerce as UC
    import qualified Control.Monad
    import qualified Data.Functor
    import qualified MixedTypesNumPrelude as MNP
    import qualified Math.NumberTheory.Logarithms as Logs
    import qualified AERN2.Real as AERN2
    import qualified AERN2.Continuity.Principles as AERN2Principles

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
  *Max Prelude AERN2.Real> real_max ((sqrt 2)/2) (1/(sqrt 2)) ? (bits 1000)
  [0.707106781186547524400844362104849039284835937688474036588339868995366239231053519425193767163820... ± ~0.0000 ~2^(-1229)]

  *Max Prelude AERN2.Real> (real_max (pi-pi) 0) ? (bits 1000)
  [0 ± ~0.0000 ~2^(-1228)]
  ```

### 3.2. ODE solver example
- The examples  `ode_exp.hs` and  `ode_tan.hs` in the `extracted-examples/src` folder are extracted from the examples in the `ode.v` script. 
- The extracted programs demonstrate the step wise ODE solver for the initial value problems  `y' = y; y(0) =1` which is solved by the exponential function  and `y' = 1+y^2; y(0) = 0` which is solved by the tan function.
- See the below example on how to execute the example interactively for an arbitrary number of steps.
- The program returns a list of real number pairs corresponding to (t, y(t)).
  ```Text
  $ stack repl src/ode_exp.hs --ghci-options "-Wno-unused-matches -Wno-unused-imports -Wno-type-defaults"

  *> exp_example 100
  ```
### 3.3. Compiling benchmark executable

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
