#!/bin/bash

BASEDIR=`dirname "$0"`
DIFF=`which diff`
EFF_DIR="$BASEDIR/../.."

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

echo "Compare if the optimized code is equivalent to the non-optimized code"
for FILE in $BASEDIR/*.eff
  do
    "$EFF" --compile "$FILE"

    # This is required to run both ml files
    echo ";;" >> $BASEDIR/$NO_OPT_DIR/$FILE.ml
    echo ";;" >> $BASEDIR/$OPT_DIR/$FILE.ml

    # Run the files through the interpreter
    ocaml < $BASEDIR/$NO_OPT_DIR/$FILE.ml > $BASEDIR/$NO_OPT_DIR/$FILE.out
    ocaml < $BASEDIR/$OPT_DIR/$FILE.ml > $BASEDIR/$OPT_DIR/$FILE.out

    RESULT=`"$DIFF" "$BASEDIR/$NO_OPT_DIR/$FILE.out" "$BASEDIR/$OPT_DIR/$FILE.out" --ignore-space-change`
    if [ "$?" = "0" ]
	    then
	    echo "Passed:  $FILE"
    else
	    echo "FAILED:  $FILE"
    fi
done

# Remove the generated files
rm $BASEDIR/*.out
rm $BASEDIR/*.ml
rm -r $BASEDIR/$OPT_DIR/
rm -r $BASEDIR/$NO_OPT_DIR/
