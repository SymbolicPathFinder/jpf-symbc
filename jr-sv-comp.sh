#!/bin/bash
SECONDS=0
DURATION=800
DEPTH_LIMIT[0]=13
DEPTH_LIMIT[1]=17
DEPTH_LIMIT[1]=21
DEPTH_LIMIT[2]=156

export RESULT="initial"


itr=0


# parse arguments
declare -a BM
BM=()
PROP_FILE=""
WITNESS_FILE=""

TOOL_BINARY=jpf-core/bin/jpf
FIND_OPTIONS="-name '*.java'"

while [ -n "$1" ] ; do
case "$1" in
  --32|--64) BIT_WIDTH="${1##--}" ; shift 1 ;;
  --propertyfile) PROP_FILE="$2" ; shift 2 ;;
  --graphml-witness) WITNESS_FILE="$2" ; shift 2 ;;
  --version) echo 2027; exit 0 ;;
  *) SRC=(`eval "find $1 $FIND_OPTIONS"`) ; BM=("${BM[@]}" "${SRC[@]}") ; shift 1 ;;
esac
done

#depth_limit=$1
#date -r java-ranger/build/jpf-symbc.jar

if [ -z "${BM[0]}" ] || [ -z "$PROP_FILE" ] ; then
echo "Missing benchmark or property file"
exit 1
fi

if [ ! -s "${BM[0]}" ] || [ ! -s "$PROP_FILE" ] ; then
echo "Empty benchmark or property file"
exit 1
fi

echo "PROP_FILE=$PROP_FILE"
  ASSERTION_MODE="FALSE"
  RUNTIME_EXCEPTION_MODE="FALSE"
  grep "assert" $PROP_FILE
  if [ $? -eq 0 ]; then
    ASSERTION_MODE="TRUE"
  fi

  grep "Exception" $PROP_FILE
  if [ $? -eq 0 ]; then
    RUNTIME_EXCEPTION_MODE="TRUE"
  fi

echo "ASSERTION_MODE=$ASSERTION_MODE"
echo "RUNTIME_EXCEPTION_MODE=$RUNTIME_EXCEPTION_MODE"

LOG=`mktemp -t jpf-log.XXXXXX`
DIR=`mktemp -d -t jpf-benchmark.XXXXXX`
trap "rm -rf $DIR" EXIT

# create target directory
mkdir -p $DIR/target/classes
PWD=`pwd`

# build src files from benchmark
javac --release 8 -g -cp $PWD/java-ranger/build/classes:$DIR/target/classes:$PWD/java-ranger/lib/JSAP-2.1.jar:$PWD/java-ranger/lib/foundry-1.0.jar -d $DIR/target/classes "${BM[@]}"

echo "after javac"

while [ $DURATION -gt 0 ] && [ $itr -lt 3 ]
do
  #timeout $DURATION . $CURRENT_DIR/jr-sv-compStep "$@"
  rm -f $LOG
  LOG=`mktemp -t jpf-log.XXXXXX`

  ####begining of old script

  # create configuration file
  echo "target=Main" > $DIR/config.jpf
  echo "classpath=$PWD/java-ranger/build/classes,$DIR/target/classes" >> $DIR/config.jpf
  echo "symbolic.dp=z3bitvector" >> $DIR/config.jpf
  #echo "symbolic.dp=z3" >> $DIR/config.jpf
  echo "symbolic.min_int=-2147483648" >> $DIR/config.jpf
  echo "symbolic.max_int=2147483647" >> $DIR/config.jpf
  echo "symbolic.min_double=-2147483648.0" >> $DIR/config.jpf
  echo "symbolic.max_double=2147483648.0" >> $DIR/config.jpf
  echo "symbolic.bvlength=64" >> $DIR/config.jpf
  echo "search.depth_limit=${DEPTH_LIMIT[$itr]}" >> $DIR/config.jpf
  #echo "search.depth_limit=13" >> $DIR/config.jpf
  echo "symbolic.strings=true" >> $DIR/config.jpf
  echo "symbolic.string_dp=z3str3" >> $DIR/config.jpf
  #echo "symbolic.string_range=/[A-Z]{0,4}/" >> $DIR/config.jpf
  #echo "symbolic.strings=yes" >> $DIR/config.jpf
  #echo "symbolic.string_dp=ABC" >> $DIR/config.jpf
  echo "symbolic.string_dp_timeout_ms=3000" >> $DIR/config.jpf
  echo "symbolic.lazy=on" >> $DIR/config.jpf
  #echo "symbolic.arrays=true" >> $DIR/config.jpf
  echo "symbolic.jrarrays=true" >> $DIR/config.jpf
  echo "veritestingMode = 5" >> $DIR/config.jpf
  echo "recursiveDepth= 200" >> $DIR/config.jpf
  echo "listener=.symbc.VeritestingListener" >> $DIR/config.jpf
  echo "singlePathOptimization=true" >> $DIR/config.jpf
  #echo "symbolic.optimizechoices=false" >> $DIR/config.jpf
  echo "symbolic.fp = true" >> $DIR/config.jpf
  echo "vm.sysprop.keys=path.separator,line.separator,file.separator,user.name,user.dir,user.timezone,user.country,java.home,java.version,java.io.tmpdir,java.class.path,os.name,java.awt.headless/true" >> $DIR/config.jpf
  # VeritestingListener sets search.multiple_errors from this (true for runtime_exception, false for validity)
  if [ $RUNTIME_EXCEPTION_MODE = "TRUE" ] ; then
    echo "targetProperty=runtime_exception" >> $DIR/config.jpf
  else
    echo "targetProperty=validity" >> $DIR/config.jpf
  fi
  if [ $RUNTIME_EXCEPTION_MODE = "TRUE" ] ; then
    # assert statements are not part of the runtime-exception property: disable them, but only in the
    # benchmark's own classes (everything javac compiled from the script arguments into
    # $DIR/target/classes), excluding the SV-COMP harness in org/sosy_lab (from ../common/).
    # Assertions in SPF/JR model classes stay enabled.
    BM_CLASSES=$(cd $DIR/target/classes && find . -name '*.class' ! -path './org/sosy_lab/*' \
                 | sed -e 's|^\./||' -e 's|\.class$||' -e 's|/|.|g' | paste -sd, -)
    if [ -n "$BM_CLASSES" ]; then
      echo "vm.disable_assertions=$BM_CLASSES" >> $DIR/config.jpf
    fi
  fi
  cat $DIR/config.jpf

  # run Java Ranger
  export LD_LIBRARY_PATH=$PWD/java-ranger/lib:$LD_LIBRARY_PATH
  echo "LD_LIBRARY_PATH=$LD_LIBRARY_PATH"
  export TARGET_CLASSPATH_WALA=$DIR/target/classes/
  # VeritestingListener prints a "Metrics Vector:" every 10 seconds after 2 minutes TIMEOUT_MINS,
  # so that we still have its statistics if ulimit kills it before it prints its report
  export TIMEOUT_MINS=2
  echo $TARGET_CLASSPATH_WALA
  #jpf-core/bin/jpf $DIR/config.jpf
  if test -z "$JVM_FLAGS"; then
    JVM_FLAGS="-Xmx1024m -ea"
  fi

  ulimit -t $DURATION ; /usr/lib/jvm/java-8-openjdk-amd64/bin/java  $JVM_FLAGS -Djava.library.path=/usr/local/lib -jar $PWD/jpf-core/build/RunJPF.jar $DIR/config.jpf > $LOG

  TIMEOUT_EXIT_CODE=$?
  echo "time out code = $TIMEOUT_EXIT_CODE"
  echo "seconds  = $SECONDS"
  # check the result
  grep "no errors detected" $LOG > /dev/null
  if [ $? -eq 0 ]; then
    grep "depth limit reached" $LOG > /dev/null
    if [ $? -eq 0 ]; then
      echo " state1 = SAFE_DEPTH_REACHED"
      RESULT="SAFE_DEPTH_REACHED"
    else
      echo " state2 = SAFE"
      RESULT="SAFE"
    fi
  else
    if [ $ASSERTION_MODE = "TRUE" ]; then
      echo "inside assertion_mode=true"
      grep "^error.*NoUncaughtExceptionsProperty.*AssertionError" $LOG > /dev/null
      if [ $? -eq 0 ]; then
        echo " state3 = UNSAFE"
        RESULT="UNSAFE"
      else
        echo " state4 = UNKNOWN"
        RESULT="UNKNOWN"
      fi
    elif [ $RUNTIME_EXCEPTION_MODE = "TRUE" ]; then
      echo "inside runtime=true"
      grep -E "^error.*NoUncaughtExceptionsProperty \"[A-Za-z0-9_.$]*Exception" $LOG > /dev/null
      if [ $? -eq 0 ]; then
        echo " state3 = UNSAFE"
        RESULT="UNSAFE"
      else
        echo " state4 = UNKNOWN"
        RESULT="UNKNOWN"
      fi
    else
      echo unsupported case. Failing
      exit 1;
    fi
  fi

  ####end of old script

  # if the VeritestingListener report was printed, keep it all, it is usually longer than 120 lines
  if grep -q "VeritestingListener report:" "$LOG"; then
    sed -n '/VeritestingListener report:/,$p' "$LOG" > "$LOG.tail"
  else
    tail -n 120 "$LOG" > "$LOG.tail"
    # no report (e.g. killed on timeout): the last printed metrics vector is the closest we have
    LAST_METRICS=$(grep -A1 "^Metrics Vector:" "$LOG" | tail -n 1)
    if [ -n "$LAST_METRICS" ]; then
      echo "Last Metrics Vector (no report printed):" >> "$LOG.tail"
      echo "$LAST_METRICS" >> "$LOG.tail"
    fi
  fi && mv "$LOG.tail" "$LOG"
  cat "$LOG"

  if [ $TIMEOUT_EXIT_CODE -gt 0  ]; then #TIMEOUT happened
    #echo "inside the timeout if-stmt"
    if [ $itr -eq 0 ]; then #DEPTH_LIMIT has not changed indicating first time
      RESULT="TIMEOUT"
      break
    else
      if [ $RESULT = "UNKNOWN" ] ; then
        RESULT="SAFE" #we timed out on subsequent iterations, but you can only be here if the result was SAFE_DEPTH_REACHED
        break
      else #somehow we timed out but we got an interesting result than UNKNOWN, in which case we would want to return that
        break
      fi
    fi
  fi

  if [ $RESULT = "UNSAFE" ] || [ $RESULT = "UNKNOWN" ] || [ $RESULT = "SAFE" ]; then
    #echo "inside break if statement"
    break
  fi

  #source $CURRENT_DIR/jr-sv-compStep "$@"
  DURATION=$((DURATION-SECONDS))
  SECONDS=0
  itr=$((itr+1))
done

rm -f $LOG

#parsing the output
if [ $RESULT = "SAFE_DEPTH_REACHED" ] ; then
  echo "SAFE"
else
  echo $RESULT
fi