#!/bin/bash

BASEDIR=`dirname "$0"`
DIFF=`which diff`

cd "$BASEDIR"

if [ ! -x "$DIFF" ]
then
    echo "Cannot find the diff command. Exiting."
    exit 1
fi

if [ -x "$BASEDIR/../eff" ]
then
  EFF="$BASEDIR/../eff"
elif [ -x "$BASEDIR/../eff.native" ]
then
  EFF="$BASEDIR/../eff.byte"
elif [ -x "$BASEDIR/../eff.byte" ]
then
  EFF="$BASEDIR/../eff.byte"
else
  echo "Cannot find the eff executable. Compile eff first."
  exit 1
fi

VALIDATE=0
if [ "$1" = "-v" ]
then
    VALIDATE=1
fi

for FILE in $BASEDIR/*.eff $BASEDIR/*/*.eff
  do
  "$EFF" "$FILE" >"$FILE.out" 2>&1
  if [ -f $FILE.ref ]
      then
      RESULT=`"$DIFF" "$FILE.out" "$FILE.ref"`
      if [ "$?" = "0" ]
	  then
	  echo "Passed:  $FILE"
	  rm "$FILE.out"
      else
	  echo "FAILED:  $FILE"
	  if [ $VALIDATE = "1" ]
	      then
	      "$DIFF" "$FILE.out" "$FILE.ref"
	      read -p "Validate $FILE.out as new $FILE.ref? (y/n) [n] " ans
	      if [ "$ans" = "y" -o "$ans" = "Y" ]
		  then
		  mv "$FILE.out" "$FILE.ref"
		  echo "Validated: $FILE"
	      fi
	  fi
      fi

  else
      mv "$FILE.out" "$FILE.ref"
      echo "Created: $FILE.ref"
  fi
done
