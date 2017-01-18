#!/bin/bash

echo "BLANK"
../eff.native --compile blank.eff
echo "INTERPRETER"
../eff.native --compile interp.eff
echo "LOOP"
../eff.native --compile loop.eff
echo "LOOP EFFECTS"
../eff.native --compile loopEffect.eff
echo "PARSER"
echo "  DIVERGES"
# ../eff.native --compile parser.eff
echo "QUEENS"
../eff.native --compile queens.eff
