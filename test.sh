#!/bin/bash

BASEDIR=`dirname $0`
DIFF="diff"

if [ -x "$BASEDIR/src/eff.native" ]
then
  EFF="$BASEDIR/src/eff.native"
elif [ -x "$BASEDIR/src/eff.byte" ]
then
  EFF="$BASEDIR/src/eff.byte"
else
  echo "Cannot find the eff executable. Run make in the src subdirectory to compile it."
  exit 1
fi

VALIDATE=0
if [ "$1" = "-v" ]
    then
    VALIDATE=1
fi

for FILE in $BASEDIR/tests/*.eff $BASEDIR/tests/*/*.eff
  do
  $EFF $FILE &> $FILE.out
  if [ -f $FILE.ref ]
      then
      RESULT=`$DIFF $FILE.out $FILE.ref`
      if [ "$?" = "0" ]
	  then
	  echo "Passed:  $FILE"
	  rm $FILE.out
      else
	  echo "FAILED:  $FILE"
	  if [ $VALIDATE = "1" ]
	      then
	      $DIFF $FILE.out $FILE.ref
	      read -p "Validate $FILE.out as new $FILE.ref? (y/n) [n] " ans
	      if [ "$ans" = "y" -o "$ans" = "Y" ]
		  then
		  mv $FILE.out $FILE.ref
		  echo Validated: $FILE
	      fi
	  fi
      fi

  else
      mv $FILE.out $FILE.ref
      echo Created: $FILE.ref
  fi
done
