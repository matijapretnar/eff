for i in {1..50}; do
    echo $i;
    { time ocaml blank ; };
    { time ocaml list.ml ; };
    { time ocaml map.ml ; };
    { time ocaml set.ml ; };
    { time ocaml garsia_wachs.ml ; };
    { time ../../eff.native -n blank ; };
    { time ../../eff.native -n list.eff ; };
    { time ../../eff.native -n map.eff ; };
    { time ../../eff.native -n set.eff ; };
    { time ../../eff.native -n garsia_wachs.eff ; }
done
