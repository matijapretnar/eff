
# # Install multicore compiler:
# opam remote add multicore https://github.com/ocamllabs/multicore-opam.git
# opam switch 4.02.2+multicore

cd multicore
eval `opam config env --switch=4.02.2+multicore` # Multicore ocaml compiler
ocamlbuild multicore_cps.native
ocamlbuild multicore_option.native
ocamlbuild multicore_all.native
ocamlbuild queens_cps.native
ocamlbuild queens_option.native
ocamlbuild queens_all.native
cd ..

QUALITY=100
NUMBER_OF_QUEENS=8

cd multicore
echo "\n\nMULTICORE"
echo "Multicore ocaml: ONE QUEENS: CPS ($QUALITY runs)"
time for ((i=1;i<=$QUALITY;i++)); do ./multicore_cps.native $NUMBER_OF_QUEENS; done
echo "\n\nMulticore ocaml: ONE QUEENS: OPTION ($QUALITY runs)"
time for ((i=1;i<=$QUALITY;i++)); do ./multicore_option.native $NUMBER_OF_QUEENS; done
echo "\n\nMulticore ocaml: ALL QUEENS ($QUALITY runs)"
time for ((i=1;i<=$QUALITY;i++)); do ./multicore_all.native $NUMBER_OF_QUEENS; done

echo "\n\n\n\nEFF"
echo "Generated, pure, optimized: ONE QUEENS: CPS ($QUALITY runs)"
time for ((i=1;i<=$QUALITY;i++)); do ./queens_cps.native $NUMBER_OF_QUEENS; done
echo "\n\nGenerated, pure, optimized: ONE QUEENS: OPTION ($QUALITY runs)"
time for ((i=1;i<=$QUALITY;i++)); do ./queens_option.native $NUMBER_OF_QUEENS; done
echo "\n\nGenerated, pure, optimized: ALL QUEENS ($QUALITY runs)"
time for ((i=1;i<=$QUALITY;i++)); do ./queens_all.native $NUMBER_OF_QUEENS; done
cd ..

cd links
echo "\n\n\n\nLINKS"
echo "Links: ONE QUEENS: CPS"
time for ((i=1;i<=$QUALITY;i++)); do ./queens_cps; done
echo "\n\nLinks: ONE QUEENS: OPTION"
time for ((i=1;i<=$QUALITY;i++)); do ./queens_option; done
echo "\n\nLinks: ALL QUEENS"
time for ((i=1;i<=$QUALITY;i++)); do ./queens_all; done
cd ..
