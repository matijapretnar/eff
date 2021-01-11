#!/bin/bash

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
