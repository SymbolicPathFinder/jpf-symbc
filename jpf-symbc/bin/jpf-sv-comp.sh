#!/bin/bash

# create site.properties
SITE_PROPERTIES=site.properties
echo "jpf-core = `pwd`/jpf-core" > $SITE_PROPERTIES
echo "jpf-symbc = `pwd`/jpf-symbc" >> $SITE_PROPERTIES
echo "extensions=\${jpf-core},\${jpf-symbc}" >> $SITE_PROPERTIES

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
    --version) date -r jpf-symbc/build/jpf-symbc.jar ; exit 0 ;;
    *) SRC=(`eval "find $1 $FIND_OPTIONS"`) ; BM=("${BM[@]}" "${SRC[@]}") ; shift 1 ;;
  esac
done

if [ -z "${BM[0]}" ] || [ -z "$PROP_FILE" ] ; then
  echo "Missing benchmark or property file"
  exit 1
fi

if [ ! -s "${BM[0]}" ] || [ ! -s "$PROP_FILE" ] ; then
  echo "Empty benchmark or property file"
  exit 1
fi

# we ignore the property file (there is only one property at the moment)
# we ignore the witness file (not used yet)

LOG=`mktemp -t jpf-log.XXXXXX`
DIR=`mktemp -d -t jpf-benchmark.XXXXXX`
trap "rm -rf $DIR" EXIT

# create target directory
mkdir -p $DIR/target/classes

# build src files from benchmark
/Library/Java/JavaVirtualMachines/zulu-8.jdk/Contents/Home/bin/javac -g -cp $DIR/target/classes:../wit4java/sv-benchmarks/java/common:../wit4java/sv-benchmarks/java/securibench/micro:../wit4java/sv-benchmarks/java/java-ranger-regression/infusion/impl -d $DIR/target/classes "${BM[@]}"

# create configuration file
echo "target=Main" > $DIR/config.jpf
echo "classpath=`pwd`/jpf-symbc/build/classes:$DIR/target/classes" >> $DIR/config.jpf
echo "symbolic.dp=z3bitvector" >> $DIR/config.jpf
echo "symbolic.bvlength=64" >> $DIR/config.jpf
echo "search.depth_limit=200" >> $DIR/config.jpf
echo "symbolic.strings=true" >> $DIR/config.jpf
#echo "symbolic.optimizechoices=false" >> $DIR/config.jpf
echo "symbolic.string_dp=z3str3" >> $DIR/config.jpf
echo "symbolic.string_dp_timeout_ms=3000" >> $DIR/config.jpf
echo "symbolic.lazy=on" >> $DIR/config.jpf
echo "symbolic.arrays=true" >> $DIR/config.jpf
echo "listener = .symbc.SymbolicListener" >> $DIR/config.jpf

# run SPF
export DYLD_LIBRARY_PATH=`pwd`/jpf-symbc/lib:$DYLD_LIBRARY_PATH
#jpf-core/bin/jpf $DIR/config.jpf
if test -z "$JVM_FLAGS"; then
  JVM_FLAGS="-Xmx1024m -ea"
fi
timeout 900 /Library/Java/JavaVirtualMachines/zulu-8.jdk/Contents/Home/bin/java $JVM_FLAGS -jar `pwd`/jpf-core/build/RunJPF.jar $DIR/config.jpf | tee $LOG

if [ $? -eq 124 ]; then
  echo "UNKNOWN"
  exit 0
fi

# check the result
grep "no errors detected" $LOG > /dev/null
if [ $? -eq 0 ]; then
  echo "SAFE"
else
  grep "^error.*NoUncaughtExceptionsProperty.*AssertionError" $LOG > /dev/null
  if [ $? -eq 0 ]; then
    echo "UNSAFE"
  else
    echo "UNKNOWN"
  fi
fi

