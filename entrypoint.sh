#!/bin/sh
# Command 1
echo "Running ls..."
ls

# Command 2
echo "Running cd jpf-core..."
cd pwd

# Run the main application command
echo "Running the Gradle version cmd..."
gradle -version

# Run 
echo "Running the current working dir cmd..."
pwd

#Build the jpf-core
echo "Running the Gradle build cmd for JPF-CORE..."
gradle :jpf-core:buildJars

#Build the jpf-core
echo "Running the Gradle build cmd for JPF-SYMBC..."
gradle :jpf-symbc:buildJars

#Run SPF Tests
echo "Run SPF Tests"
gradle :jpf-symbc:test

#keep container running
echo "Keep container running"
tail -f /dev/null