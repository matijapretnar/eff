#!/bin/bash

BASEDIR=`dirname "$0"`
DIFF=`which diff`
COLUMNS=`tput cols`

if [ ! -x "$DIFF" ]; then
    echo "Cannot find the diff command. Exiting."
    exit 1
fi

if [ -x "$BASEDIR/../eff.native" ]; then
    EFF="$BASEDIR/../eff.native"
elif [ -x "$BASEDIR/../eff.byte" ]; then
    EFF="$BASEDIR/../eff.byte"
else
    echo "Cannot find the eff executable. Compile eff first."
    exit 1
fi

if [ "$1" = "-v" ]; then
    VALIDATE=1
else
    VALIDATE=0
fi

CORRECT=1
for FILE in $BASEDIR/*.eff $BASEDIR/*/*.eff; do
    printf "%-${COLUMNS}s\r" "Testing: $FILE"
    $EFF $FILE &> $FILE.out
    if [ -f $FILE.ref ]; then
        RESULT=`$DIFF $FILE.out $FILE.ref`
        if [ "$?" = "0" ]; then
            rm $FILE.out
        else
            echo "FAILED: $FILE"
            CORRECT=0
            if [ $VALIDATE = "1" ]; then
                $DIFF $FILE.out $FILE.ref
                read -p "Validate $FILE.out as new $FILE.ref? (y/n) [n] " ans
                if [ "$ans" = "y" -o "$ans" = "Y" ]; then
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

if [ $CORRECT = "1" ]; then
    printf "%-${COLUMNS}s" "All files passed tests."
fi
