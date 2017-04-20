#!/bin/bash

echo "LOOP"
cd loop
../../../../eff.native --pure --no-pervasives --compile loop.eff
mv loop.eff.ml loopOptPure.ml
../../../../eff.native --pure --no-opt --no-pervasives --compile loop.eff
mv loop.eff.ml loopNoOptPure.ml
../../../../eff.native --no-pervasives --compile loop.eff
mv loop.eff.ml loopOptImpure.ml
../../../../eff.native --no-opt --no-pervasives --compile loop.eff
mv loop.eff.ml loopNoOptImpure.ml
rm -rf _tmp
cd ..
echo "QUEENS"
cd queens
../../../../eff.native --pure --no-pervasives --compile queens.eff
mv queens.eff.ml queensOptPure.ml
../../../../eff.native --pure --no-opt --no-pervasives --compile queens.eff
mv queens.eff.ml queensNoOptPure.ml
../../../../eff.native --no-pervasives --compile queens.eff
mv queens.eff.ml queensOptImpure.ml
../../../../eff.native --no-opt --no-pervasives --compile queens.eff
mv queens.eff.ml queensNoOptImpure.ml
rm -rf _tmp
cd ..
echo "INTERPRETER"
cd interp
../../../../eff.native --pure --no-pervasives --compile interp.eff
mv interp.eff.ml interpOptPure.ml
../../../../eff.native --pure --no-opt --no-pervasives --compile interp.eff
mv interp.eff.ml interpNoOptPure.ml
../../../../eff.native --no-pervasives --compile interp.eff
mv interp.eff.ml interpOptImpure.ml
../../../../eff.native --no-opt --no-pervasives --compile interp.eff
mv interp.eff.ml interpNoOptImpure.ml
rm -rf _tmp
cd ..
