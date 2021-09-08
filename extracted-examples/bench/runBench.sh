#!/bin/bash

resultscsv=$1
if [ "$resultscsv" == "" ]; then echo "usage: $0 <results csv file name>"; exit 1; fi

#benchmain=haskell-reals-comparison
benchmain=coq-aern-extracted-bench

reuselogs="true"
# reuselogs=""

overwritelogs="true"

# put headers in the results csv file if it is new:
if [ ! -f $resultscsv ]
    then echo "Time,Bench,BenchParams,Method,AccuracyTarget(bits),Accuracy(bits),UTime(s),STime(s),Mem(kB)" > $resultscsv
    if [ $? != 0 ]; then exit 1; fi
fi

function runForBenchParamss
{
  for benchParams in $bparamss
  do
    runOne
  done
}

function runOne
# parameters:
#  $dir where to put individual logs
#  $bench
#  $benchParams
#  $method
#  $params
{
    runlog="logs/$dir/run-$bench-$benchParams-$method.log"
    CMD="/usr/bin/time -v $benchmain $bench$method $benchParams"
    echo -n $CMD
    if [ ! -f $runlog ] || [ "$overwritelogs" = "true" ] || grep -q "terminated" $runlog
        then
            echo " (running and logging in $runlog)"
            $CMD >& $runlog
            if [ $? != 0 ]; then rm $runlog; exit 1; fi
            getDataFromRunlog
        else
          if [ "$reuselogs" != "true" ]
            then
              echo " (skipping due to existing log $runlog)"
            else
              echo " (reusing existing log $runlog)"
              getDataFromRunlog
          fi
    fi
}

function getDataFromRunlog
{
  utime=`grep "User time (seconds)" $runlog | sed 's/^.*: //'`
  stime=`grep "System time (seconds)" $runlog | sed 's/^.*: //'`
  mem=`grep "Maximum resident set size (kbytes)" $runlog | sed 's/^.*: //'`
  exact=`grep -i "accuracy: Exact" $runlog | sed 's/accuracy: Exact/exact/'`
  bits=`grep -i "accuracy: bits " $runlog | sed 's/accuracy: [bB]its //'`
  now=`date`
  echo "$now,$bench,$benchParams,$method,$params,$exact$bits,${utime/0.00/0.01},${stime/0.00/0.01},$mem" >> $resultscsv
}

function runForAllMethods
{
  if [ "$method_E_bparamss" != "" ]; then
    method="E"; bparamss="$method_E_bparamss" method_E_bparamss=""
    runForBenchParamss
  fi
  if [ "$method_H_bparamss" != "" ]; then
    method="H"; bparamss="$method_H_bparamss" method_H_bparamss=""
    runForBenchParamss
  fi
  if [ "$method_N_bparamss" != "" ]; then
    method="N"; bparamss="$method_N_bparamss" method_N_bparamss=""
    runForBenchParamss
  fi
  # if [ "$method_MBE_bparamss" != "" ]; then
  #   method="MBE"; bparamss="$method_MBE_bparamss" method_MBE_bparamss=""
  #   runForBenchParamss
  # fi
  # if [ "$method_MBH_bparamss" != "" ]; then
  #   method="MBH"; bparamss="$method_MBH_bparamss" method_MBH_bparamss=""
  #   runForBenchParamss
  # fi
  # if [ "$method_MBN_bparamss" != "" ]; then
  #   method="MBN"; bparamss="$method_MBN_bparamss" method_MBN_bparamss=""
  #   runForBenchParamss
  # fi
}

#################
### realmax
#################

function realmaxAllMethods
{
     step="1000000"
   stepMB="1000000"
    steps=`printf "$step %.0s" {1..10}`
  stepsMB=`printf "$stepMB %.0s" {1..10}`

    method_E_bparamss="$steps";
    method_H_bparamss="$steps";
    method_N_bparamss="$steps";
  method_MBE_bparamss="$stepsMB";
  method_MBH_bparamss="$stepsMB";
  method_MBN_bparamss="$stepsMB";

  bench="realmax"; dir="$bench";
  params="";
  runForAllMethods
}

function sqrt1AllMethods
{
    step="1000000"
    stepN="1000000"
   stepMB="1000000"
  stepMBN="1000000"
    steps=`printf "$step %.0s" {1..10}`
   stepsN=`printf "$stepN %.0s" {1..10}`
  stepsMB=`printf "$stepMB %.0s" {1..10}`
 stepsMBN=`printf "$stepMBN %.0s" {1..10}`

    method_E_bparamss="$steps";
    method_H_bparamss="$steps";
    method_N_bparamss="$stepsN";
  method_MBE_bparamss="$stepsMB";
  method_MBH_bparamss="$stepsMB";
  method_MBN_bparamss="$stepsMBN";

  bench="sqrt1"; dir="$bench";
  params="";
  runForAllMethods
}

function sqrt2AllMethods
{
    step="1000000"
    stepN="1000000"
   stepMB="1000000"
  stepMBN="1000000"
    steps=`printf "$step %.0s" {1..10}`
   stepsN=`printf "$stepN %.0s" {1..10}`
  stepsMB=`printf "$stepMB %.0s" {1..10}`
 stepsMBN=`printf "$stepMBN %.0s" {1..10}`

    method_E_bparamss="$steps";
    method_H_bparamss="$steps";
    method_N_bparamss="$stepsN";
  method_MBE_bparamss="$stepsMB";
  method_MBH_bparamss="$stepsMB";
  method_MBN_bparamss="$stepsMBN";

  bench="sqrt2"; dir="$bench";
  params="";
  runForAllMethods
}

function civt1AllMethods
{
     step="1100"
   stepMB="1400"
    steps=`printf "$step %.0s" {1..10}`
  stepsMB=`printf "$stepMB %.0s" {1..10}`

  #   steps="100 140 200 280 400 560 800 1120"
  # stepsMB="140 200 280 400 560 800 1120 1600"

    method_E_bparamss="$steps";
    method_H_bparamss="$steps";
  method_MBE_bparamss="$stepsMB";
  method_MBH_bparamss="$stepsMB";

  bench="civt1"; dir="$bench";
  params="";
  runForAllMethods
}

function civt2AllMethods
{
     step="1100"
   stepMB="1400"
    steps=`printf "$step %.0s" {1..10}`
  stepsMB=`printf "$stepMB %.0s" {1..10}`

  #   steps="100 140 200 280 400 560 800 1120"
  # stepsMB="140 200 280 400 560 800 1120 1600"

    method_E_bparamss="$steps";
    method_H_bparamss="$steps";
  method_MBE_bparamss="$stepsMB";
  method_MBH_bparamss="$stepsMB";

  bench="civt2"; dir="$bench";
  params="";
  runForAllMethods
}

function civt3AllMethods
{
     step="1100"
   stepMB="1400"
    steps=`printf "$step %.0s" {1..10}`
  stepsMB=`printf "$stepMB %.0s" {1..10}`

  #   steps="100 140 200 280 400 560 800 1120"
  # stepsMB="140 200 280 400 560 800 1120 1600"

    method_E_bparamss="$steps";
    method_H_bparamss="$steps";
  method_MBE_bparamss="$stepsMB";
  method_MBH_bparamss="$stepsMB";

  bench="civt3"; dir="$bench";
  params="";
  runForAllMethods
}

realmaxAllMethods
sqrt1AllMethods
sqrt2AllMethods
civt1AllMethods
civt2AllMethods
civt3AllMethods

