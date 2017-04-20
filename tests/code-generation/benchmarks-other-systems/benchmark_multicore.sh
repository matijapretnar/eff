
# # Install multicore compiler:
# opam remote add multicore https://github.com/ocamllabs/multicore-opam.git
# opam switch 4.02.2+multicore

cd multicore
eval `opam config env --switch=4.02.2+multicore` # Multicore ocaml compiler
echo "compiling multicore native"
ocamlbuild multicore_cps.native
ocamlbuild multicore_option.native
ocamlbuild multicore_all.native
echo "compiling multicore byte"
ocamlbuild multicore_cps.byte
ocamlbuild multicore_option.byte
ocamlbuild multicore_all.byte
echo "compiling eff native"
ocamlbuild queens_cps.native
ocamlbuild queens_option.native
ocamlbuild queens_all.native
cd ..
cd loop
echo "compiling loop multicore native"
ocamlbuild multicore.native
cd ..
eval `opam config env --switch=4.02.2+local-git-`
cd delimcc
echo "compiling eff byte"
ocamlbuild queens_cps.byte
ocamlbuild queens_option.byte
ocamlbuild queens_all.byte
echo "compiling eff directly in ocaml byte"
ocamlbuild -use-ocamlfind -package delimcc effInOcaml_cps.byte
ocamlbuild -use-ocamlfind -package delimcc effInOcaml_option.byte
ocamlbuild -use-ocamlfind -package delimcc effInOcaml_all.byte
echo "compiling handlers in action byte"
ocamlbuild -use-ocamlfind -package delimcc handlersInAction_cps.byte
ocamlbuild -use-ocamlfind -package delimcc handlersInAction_option.byte
ocamlbuild -use-ocamlfind -package delimcc handlersInAction_all.byte
cd ..
cd native
echo "compiling native byte"
ocamlbuild native_cps.byte
ocamlbuild native_option.byte
ocamlbuild native_exep.byte
ocamlbuild native_all.byte
cd ..
cd native
echo "compiling native native"
ocamlbuild native_cps.native
ocamlbuild native_option.native
ocamlbuild native_exep.native
ocamlbuild native_all.native
cd ..
cd loop
echo "compiling loop eff native"
./../../../../eff.native --pure --no-pervasives --compile loop.eff

 mv loop.eff.ml loop.ml
ocamlbuild loop.native
cd ..

QUALITY=10
#NUMBER_OF_QUEENS=11

for NUMBER_OF_QUEENS in 8 9 10 11 12 13 14
do
  cd multicore
  echo "\n\nMULTICORE NATIVE ($NUMBER_OF_QUEENS queens)"
  echo "Multicore ocaml: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) (5 runs)"
  time for ((i=1;i<=$QUALITY;i++)); do ./multicore_cps.native $NUMBER_OF_QUEENS; done
  echo "\n\nMulticore ocaml: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) (5 runs)"
  time for ((i=1;i<=$QUALITY;i++)); do ./multicore_option.native $NUMBER_OF_QUEENS; done
  echo "\n\nMulticore ocaml: ALL QUEENS ($NUMBER_OF_QUEENS queens) (5 runs)"
  time for ((i=1;i<=$QUALITY;i++)); do ./multicore_all.native $NUMBER_OF_QUEENS; done
  cd ..

  # cd multicore
  # echo "\n\nMULTICORE BYTE ($NUMBER_OF_QUEENS queens)"
  # echo "Multicore ocaml: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) (5 runs)"
  # time for ((i=1;i<=$QUALITY;i++)); do ./multicore_cps.byte $NUMBER_OF_QUEENS; done
  # echo "\n\nMulticore ocaml: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) (5 runs)"
  # time for ((i=1;i<=$QUALITY;i++)); do ./multicore_option.byte $NUMBER_OF_QUEENS; done
  # echo "\n\nMulticore ocaml: ALL QUEENS ($NUMBER_OF_QUEENS queens) (5 runs)"
  # time for ((i=1;i<=$QUALITY;i++)); do ./multicore_all.byte $NUMBER_OF_QUEENS; done
  # cd ..

  # cd multicore
  # echo "\n\n\n\nEFF ($NUMBER_OF_QUEENS queens)"
  # echo "Generated, pure, optimized: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) (5 runs)"
  # time for ((i=1;i<=$QUALITY;i++)); do ./queens_cps.native $NUMBER_OF_QUEENS; done
  # echo "\n\nGenerated, pure, optimized: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) (5 runs)"
  # time for ((i=1;i<=$QUALITY;i++)); do ./queens_option.native $NUMBER_OF_QUEENS; done
  # echo "\n\nGenerated, pure, optimized: ALL QUEENS ($NUMBER_OF_QUEENS queens) (5 runs)"
  # time for ((i=1;i<=$QUALITY;i++)); do ./queens_all.native $NUMBER_OF_QUEENS; done
  # cd ..

  #cd delimcc
  #echo "\n\n\n\nEFF BYTE ($NUMBER_OF_QUEENS queens)"
  #echo "Generated, pure, optimized: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) (5 runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./queens_cps.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nGenerated, pure, optimized: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) (5 runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./queens_option.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nGenerated, pure, optimized: ALL QUEENS ($NUMBER_OF_QUEENS queens) (5 runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./queens_all.byte $NUMBER_OF_QUEENS; done
  #cd ..

  #cd delimcc
  #echo "\n\n\n\nEFF IN OCAML BYTE ($NUMBER_OF_QUEENS queens)"
  #echo "\n\nEff in OCaml: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) (5 runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./effInOcaml_cps.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nEff in OCaml: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) (5 runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./effInOcaml_option.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nEff in OCaml: ALL QUEENS ($NUMBER_OF_QUEENS queens) (5 runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./effInOcaml_all.byte $NUMBER_OF_QUEENS; done
  #cd ..

  #cd delimcc
  #echo "\n\n\n\nHANDLERS IN ACTION ($NUMBER_OF_QUEENS queens)"
  #echo "\n\nHandlers in action: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) (5 runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./handlersInAction_cps.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nHandlers in action: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) (5 runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./handlersInAction_option.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nHandlers in action: ALL QUEENS ($NUMBER_OF_QUEENS queens) (5 runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./handlersInAction_all.byte $NUMBER_OF_QUEENS; done
  #cd ..

  #cd native
  #echo "\n\n\n\nNATIVE BYTE ($NUMBER_OF_QUEENS queens)"
  #echo "\n\nNative: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) (5 runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./native_cps.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nNative: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) (5 runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./native_option.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nNative: ONE QUEENS: EXCEPTION ($NUMBER_OF_QUEENS queens) (5 runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./native_exep.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nNative: ALL QUEENS ($NUMBER_OF_QUEENS queens) (5 runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./native_all.byte $NUMBER_OF_QUEENS; done
  #cd ..

  cd native
  echo "\n\n\n\nNATIVE NATIVE ($NUMBER_OF_QUEENS queens)"
  echo "\n\nNative: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) (5 runs)"
  time for ((i=1;i<=$QUALITY;i++)); do ./native_cps.native $NUMBER_OF_QUEENS; done
  echo "\n\nNative: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) (5 runs)"
  time for ((i=1;i<=$QUALITY;i++)); do ./native_option.native $NUMBER_OF_QUEENS; done
  echo "\n\nNative: ONE QUEENS: EXCEPTION ($NUMBER_OF_QUEENS queens) (5 runs)"
  time for ((i=1;i<=$QUALITY;i++)); do ./native_exep.native $NUMBER_OF_QUEENS; done
  echo "\n\nNative: ALL QUEENS ($NUMBER_OF_QUEENS queens) (5 runs)"
  time for ((i=1;i<=$QUALITY;i++)); do ./native_all.native $NUMBER_OF_QUEENS; done
  cd ..
done

# cd loop
# echo "\n\n\n\nCOMPARISON LOOP MULTICORE-EFF NATIVE"
# echo "\n\nMulticore"
# time for ((i=1;i<=$QUALITY;i++)); do ./multicore.native; done
# echo "\n\nEff"
# time for ((i=1;i<=$QUALITY;i++)); do ./loop.native; done
# cd ..

# cd links
# echo "\n\n\n\nLINKS"
# echo "Links: ONE QUEENS: CPS (8 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_cps_8.links; done
# echo "Links: ONE QUEENS: CPS (9 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_cps_9.links; done
# echo "Links: ONE QUEENS: CPS (10 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_cps_10.links; done
# echo "Links: ONE QUEENS: CPS (11 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_cps_11.links; done
# echo "Links: ONE QUEENS: CPS (12 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_cps_12.links; done
# echo "\n\nLinks: ONE QUEENS: OPTION (8 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_option_8.links; done
# echo "\n\nLinks: ONE QUEENS: OPTION (9 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_option_9.links; done
# echo "\n\nLinks: ONE QUEENS: OPTION (10 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_option_10.links; done
# echo "\n\nLinks: ONE QUEENS: OPTION (11 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_option_11.links; done
# echo "\n\nLinks: ONE QUEENS: OPTION (12 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_option_12.links; done
# echo "\n\nLinks: ALL QUEENS (8 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_all_8.links; done
# echo "\n\nLinks: ALL QUEENS (9 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_all_9.links; done
# echo "\n\nLinks: ALL QUEENS (10 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_all_10.links; done
# echo "\n\nLinks: ALL QUEENS (11 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_all_11.links; done
# echo "\n\nLinks: ALL QUEENS (12 queens) (5 runs)"
# time for ((i=1;i<=$QUALITY;i++)); do ./links-effects/links queens_all_12.links; done
# cd ..
