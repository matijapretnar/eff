#! /bin/bash



# Configuration
EFF=/home/brecht/projects/eff-bs/eff.native
# RESULTS_FILE=results.txt
RESULTS_FILE=/dev/stdout
QUOTA=1

NUMBER_OF_LOOPS=100
NUMBER_OF_QUEENS=5
NUMBER_OF_RANGE=100
# NUMBER_OF_LOOPS=69
# NUMBER_OF_QUEENS=69
# NUMBER_OF_RANGE=69

RUN_LOOP_PURE=true
RUN_LOOP_LATENT=true
RUN_LOOP_INCR=false
RUN_LOOP_INCR2=false
RUN_LOOP_STATE=false
RUN_QUEENS_ONE=true
RUN_QUEENS_ALL=false
RUN_INTERP=false
RUN_RANGE=false




# Code

function print_config {
    cat <<EOF
Configuration:
EFF = $EFF
RESULTS_FILE = $RESULTS_FILE
QUOTA = $QUOTA

NUMBER_OF_LOOPS = $NUMBER_OF_LOOPS
NUMBER_OF_QUEENS = $NUMBER_OF_QUEENS
NUMBER_OF_RANGE = $NUMBER_OF_RANGE

RUN_LOOP_PURE = $RUN_LOOP_PURE
RUN_LOOP_LATENT = $RUN_LOOP_LATENT
RUN_LOOP_INCR = $RUN_LOOP_INCR
RUN_LOOP_INCR2 = $RUN_LOOP_INCR2
RUN_LOOP_STATE = $RUN_LOOP_STATE
RUN_QUEENS_ONE = $RUN_QUEENS_ONE
RUN_QUEENS_ALL = $RUN_QUEENS_ALL
RUN_INTERP = $RUN_INTERP
RUN_RANGE = $RUN_RANGE
EOF
}

function effcompile() {
    # Benchmark an Eff file
    name="$1"
    variant="$2"
    file="$3"
    case "$variant" in
        "opt")
            opts=""
            ;;
        "noopt")
            opts="--no-opts"
            ;;
        *)
            echo "invalid variant: $variant"
            exit 1
            ;;
    esac

    echo "LOG: running [$1 -> $2] with file '$file'"
    "$EFF" --explicit-subtyping --no-pervasives $opts --profile "$file" \
        | grep time \
        | while read -r line
    do
        echo "RESULT: $name - $variant - $line"
    done
}

function benchmark_ocaml() {
    # Benchmark the Ocaml files
    # First update the config of benchmark.ml
    echo "Preparing benchmark.ml"
    sed -i \
        -re "s/^(.*number_of_loops\s*=\s*).*/\1$NUMBER_OF_LOOPS/g" \
        -re "s/^(.*number_of_queens\s*=\s*).*/\1$NUMBER_OF_QUEENS/g" \
        -re "s/^(.*number_of_range\s*=\s*).*/\1$NUMBER_OF_RANGE/g" \
        -re "s/^(.*run_loop_pure\s*=\s*).*/\1$RUN_LOOP_PURE/g" \
        -re "s/^(.*run_loop_latent\s*=\s*).*/\1$RUN_LOOP_LATENT/g" \
        -re "s/^(.*run_loop_incr\s*=\s*).*/\1$RUN_LOOP_INCR/g" \
        -re "s/^(.*run_loop_incr'\s*=\s*).*/\1$RUN_LOOP_INCR2/g" \
        -re "s/^(.*run_loop_state\s*=\s*).*/\1$RUN_LOOP_STATE/g" \
        -re "s/^(.*run_queens_one\s*=\s*).*/\1$RUN_QUEENS_ONE/g" \
        -re "s/^(.*run_queens_all\s*=\s*).*/\1$RUN_QUEENS_ALL/g" \
        -re "s/^(.*run_interp\s*=\s*).*/\1$RUN_INTERP/g" \
        -re "s/^(.*run_range\s*=\s*).*/\1$RUN_RANGE/g" \
        benchmark.ml
    # Build benchmark.native from benchmark.ml
    echo "Building benchmark.native"
    ocamlbuild -use-ocamlfind benchmark.native
    # Benchmark it
    echo "Running benchmark.native"
    ./benchmark.native -quota "$QUOTA"
}

function benchmark_eff() {
    # Benchmark the Eff files
    echo "Running Eff benchmarks"
    if [ $RUN_LOOP_PURE = "true" ]; then
        sed -i -re "s/^(in.*test_pure\s*).*/\1$NUMBER_OF_LOOPS/g" loop/loopPure.eff
        effcompile loop_pure noopt loop/loopPure.eff
        effcompile loop_pure opt loop/loopPure.eff
    fi
    if [ $RUN_LOOP_LATENT = "true" ]; then
        sed -i -re "s/^(in.*test_latent\s*).*/\1$NUMBER_OF_LOOPS/g" loop/loopLatent.eff
        effcompile loop_latent noopt loop/loopLatent.eff
        effcompile loop_latent opt loop/loopLatent.eff
    fi
    if [ $RUN_LOOP_INCR = "true" ]; then
        sed -i -re "s/^(in.*test_incr\s*).*/\1$NUMBER_OF_LOOPS/g" loop/loopIncr.eff
        effcompile loop_incr noopt loop/loopIncr.eff
        effcompile loop_incr opt loop/loopIncr.eff
    fi
    if [ $RUN_LOOP_INCR2 = "true" ]; then
        sed -i -re "s/^(in.*test_incr'\s*).*/\1$NUMBER_OF_LOOPS/g" loop/loopIncr2.eff
        effcompile loop_incr2 noopt loop/loopIncr2.eff
        effcompile loop_incr2 opt loop/loopIncr2.eff
    fi
    if [ $RUN_LOOP_STATE = "true" ]; then
        sed -i -re "s/^(in.*test_state\s*).*/\1$NUMBER_OF_LOOPS/g" loop/loopState.eff
        effcompile loop_state noopt loop/loopState.eff
        effcompile loop_state opt loop/loopState.eff
    fi

    if [ $RUN_QUEENS_ONE = "true" ]; then
        sed -i -re "s/^(in.*test_queens\s*).*/\1$NUMBER_OF_QUEENS/g" queens/queensOne.eff
        effcompile queens_one noopt queens/queensOne.eff
        effcompile queens_one opt queens/queensOne.eff
    fi
    if [ $RUN_QUEENS_ALL = "true" ]; then
        sed -i -re "s/^(in.*test_queens\s*).*/\1$NUMBER_OF_QUEENS/g" queens/queensAll.eff
        effcompile queens_all noopt queens/queensAll.eff
        effcompile queens_all opt queens/queensAll.eff
    fi

    if [ $RUN_INTERP = "true" ]; then
        # sed -re "s/^(in.*test_pure\s*).*/\1$NUMBER_OF_LOOPS/g" interp/interp.eff
        effcompile interp noopt interp/interp.eff
        effcompile interp opt interp/interp.eff
    fi

    if [ $RUN_RANGE = "true" ]; then
        # sed -re "s/^(.*test_pure\s*).*/\1$NUMBER_OF_RANGE/g" range/range.eff
        effcompile range noopt range/range.eff
        effcompile range opt range/range.eff
    fi
}


# Run both benchmarks, send output to a file
print_config > "$RESULTS_FILE"
benchmark_ocaml >> "$RESULTS_FILE"
benchmark_eff >> "$RESULTS_FILE"
