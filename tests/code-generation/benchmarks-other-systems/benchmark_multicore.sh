
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

QUALITY=5
#NUMBER_OF_QUEENS=11

for NUMBER_OF_QUEENS in 8 9 10 11 12
do
  # cd multicore
  # echo "\n\nMULTICORE ($NUMBER_OF_QUEENS queens)"
  # echo "Multicore ocaml: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  # time for ((i=1;i<=$QUALITY;i++)); do ./multicore_cps.native $NUMBER_OF_QUEENS; done
  # echo "\n\nMulticore ocaml: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  # time for ((i=1;i<=$QUALITY;i++)); do ./multicore_option.native $NUMBER_OF_QUEENS; done
  # echo "\n\nMulticore ocaml: ALL QUEENS ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  # time for ((i=1;i<=$QUALITY;i++)); do ./multicore_all.native $NUMBER_OF_QUEENS; done
  # cd ..

  cd multicore
  echo "\n\nMULTICORE BYTE ($NUMBER_OF_QUEENS queens)"
  #echo "Multicore ocaml: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./multicore_cps.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nMulticore ocaml: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./multicore_option.byte $NUMBER_OF_QUEENS; done
  echo "\n\nMulticore ocaml: ALL QUEENS ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  time for ((i=1;i<=$QUALITY;i++)); do ./multicore_all.byte $NUMBER_OF_QUEENS; done
  cd ..

  # cd multicore
  # echo "\n\n\n\nEFF ($NUMBER_OF_QUEENS queens)"
  # echo "Generated, pure, optimized: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  # time for ((i=1;i<=$QUALITY;i++)); do ./queens_cps.native $NUMBER_OF_QUEENS; done
  # echo "\n\nGenerated, pure, optimized: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  # time for ((i=1;i<=$QUALITY;i++)); do ./queens_option.native $NUMBER_OF_QUEENS; done
  # echo "\n\nGenerated, pure, optimized: ALL QUEENS ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  # time for ((i=1;i<=$QUALITY;i++)); do ./queens_all.native $NUMBER_OF_QUEENS; done
  # cd ..

  #cd delimcc
  #echo "\n\n\n\nEFF BYTE ($NUMBER_OF_QUEENS queens)"
  #echo "Generated, pure, optimized: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./queens_cps.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nGenerated, pure, optimized: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./queens_option.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nGenerated, pure, optimized: ALL QUEENS ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./queens_all.byte $NUMBER_OF_QUEENS; done
  #cd ..

  #cd delimcc
  #echo "\n\n\n\nEFF IN OCAML BYTE ($NUMBER_OF_QUEENS queens)"
  #echo "\n\nEff in OCaml: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./effInOcaml_cps.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nEff in OCaml: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./effInOcaml_option.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nEff in OCaml: ALL QUEENS ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./effInOcaml_all.byte $NUMBER_OF_QUEENS; done
  #cd ..

  #cd delimcc
  #echo "\n\n\n\nHANDLERS IN ACTION ($NUMBER_OF_QUEENS queens)"
  #echo "\n\nHandlers in action: ONE QUEENS: CPS ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./handlersInAction_cps.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nHandlers in action: ONE QUEENS: OPTION ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./handlersInAction_option.byte $NUMBER_OF_QUEENS; done
  #echo "\n\nHandlers in action: ALL QUEENS ($NUMBER_OF_QUEENS queens) ($QUALITY runs)"
  #time for ((i=1;i<=$QUALITY;i++)); do ./handlersInAction_all.byte $NUMBER_OF_QUEENS; done
  #cd ..
done

#cd links
#echo "\n\n\n\nLINKS"
#echo "Links: ONE QUEENS: CPS"
#time for ((i=1;i<=$QUALITY;i++)); do ./queens_cps; done
#echo "\n\nLinks: ONE QUEENS: OPTION"
#time for ((i=1;i<=$QUALITY;i++)); do ./queens_option; done
#echo "\n\nLinks: ALL QUEENS"
#time for ((i=1;i<=$QUALITY;i++)); do ./queens_all; done
#cd ..
