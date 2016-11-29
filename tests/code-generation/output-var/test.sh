#!/bin/bash

BASEDIR=`dirname "$0"`
DIFF=`which diff`
EFF_DIR="$BASEDIR/../../.."

MAIN="main.ml"

NO_OPT_DIR="_tmp_no_opt"
OPT_DIR="_tmp"

cd "$BASEDIR"

# Check if the `diff` command exists
if [ ! -x "$DIFF" ]
then
    echo "Cannot find the diff command. Exiting."
    exit 1
fi

# Find the eff executable
if [ -x "$EFF_DIR/eff" ]
then
  EFF="$EFF_DIR/eff"
elif [ -x "$EFF_DIR/eff.native" ]
then
  EFF="$EFF_DIR/eff.byte"
elif [ -x "$EFF_DIR/eff.byte" ]
then
  EFF="$EFF_DIR/eff.byte"
else
  echo "Cannot find the eff executable. Compile eff first."
  exit 1
fi

function takeVariableFromType () {
  while read LINE; do
    NB=$(awk -F"val | : $1 =" '{print NF}' <<< $LINE)
    if [ "$NB" = "3" ]
      then
        # We have captured a variable
        VARIABLE=$(awk -F"val | : $1 =" '{print $2}' <<< $LINE)
        CODE="Printf.printf \"%s := $2 = $2\n\" (\"$VARIABLE\") (Notopt.$VARIABLE) (Opt.$VARIABLE);"
        echo $CODE >> "$BASEDIR/$MAIN"
    fi
  done < "$3"
}

for FILE in $BASEDIR/*.eff
  do
    "$EFF" --compile "$FILE"

    # This is required to run the ml files
    echo ";;" >> $BASEDIR/$OPT_DIR/$FILE.ml
    echo ";;" >> $BASEDIR/$NO_OPT_DIR/$FILE.ml
    ocaml < $BASEDIR/$OPT_DIR/$FILE.ml > $BASEDIR/$FILE.out

    echo "Printf.printf \"Testing: $FILE\n\";" > "$BASEDIR/$MAIN"
    echo "Printf.printf \"name := expected = result\n\";" >> "$BASEDIR/$MAIN"

    cp $BASEDIR/$NO_OPT_DIR/$FILE.ml $BASEDIR/notopt.ml
    cp $BASEDIR/$OPT_DIR/$FILE.ml $BASEDIR/opt.ml

    # Here, we chop off everything after the string that marks the end of pervasives
    sed -i '' '1,/End of pervasives/d' "$BASEDIR/$FILE.out"
    TMP=$(tr -d "#" < "$BASEDIR/$FILE.out")
    echo "$TMP" > "$BASEDIR/$FILE.out"
    TMP=$(sed 's/^ *//g' < "$BASEDIR/$FILE.out")
    echo "$TMP" > "$BASEDIR/$FILE.out"
    awk '/val/{flag=1;next}/\:/{flag=0}flag' "$BASEDIR/$FILE.out"

    takeVariableFromType "int" "%d" "$BASEDIR/$FILE.out"
    takeVariableFromType "string" "%s" "$BASEDIR/$FILE.out"
    takeVariableFromType "float" "%f" "$BASEDIR/$FILE.out"
    takeVariableFromType "bool" "%B" "$BASEDIR/$FILE.out"

    ocamlc "$BASEDIR/notopt.ml" "$BASEDIR/opt.ml" "$BASEDIR/$MAIN"
    ./a.out
    echo ""
done

# Remove the generated files
rm $BASEDIR/*.out
rm $BASEDIR/*.ml
rm $BASEDIR/*.cmi
rm $BASEDIR/*.cmo
rm -r $BASEDIR/$OPT_DIR/
rm -r $BASEDIR/$NO_OPT_DIR/
