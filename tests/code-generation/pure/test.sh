#!/bin/bash

echo "BLANK"
echo "" > blank.eff
../../../eff.native --pure --compile blank.eff
echo "INTERPRETER"
cp -f ../benchmarks/interp/interp.eff .
../../../eff.native --pure --compile interp.eff
echo "LOOP"
cp -f ../benchmarks/loop/loop.eff .
../../../eff.native --pure --compile loop.eff
echo "LOOP EFFECTS"
cp -f ../benchmarks/loopEffect/loopEffect.eff .
../../../eff.native --pure --compile loopEffect.eff
echo "PARSER"
cp -f ../benchmarks/parser/parser.eff .
../../../eff.native --pure --compile parser.eff
echo "QUEENS"
cp -f ../benchmarks/queens/queens.eff .
../../../eff.native --pure --compile queens.eff
