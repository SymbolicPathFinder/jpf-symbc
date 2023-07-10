#!/bin/bash


echo "Running ls..."
ls


echo "Running cd jpf-core..."
cd jpf-core

echo "Running the Gradle version cmd..."
gradle -version


echo "Running the current working dir cmd..."
cd ..
pwd


echo "Running the Gradle build cmd for JPF-CORE..."
gradle :jpf-core:buildJars


echo "Running the Gradle build cmd for JPF-SYMBC..."
gradle :jpf-symbc:buildJars


echo "Run SPF Tests"
gradle :jpf-symbc:test


echo "Container is running"
tail -f /dev/null