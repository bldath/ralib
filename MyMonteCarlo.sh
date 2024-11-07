#!/bin/bash

# From linux command line:
# chmod 755 MyMonteCarlo.sh


java -ea -jar target/ralib-0.1-SNAPSHOT-jar-with-dependencies.jar iosimulator -f config > output.txt
cat output.txt | grep -F 'Counterexamples' | grep -o -E '[0-9]+'>> ce_count.txt
cat output.txt | grep -F 'CE max length' | grep -o -E '[0-9]+'>> ce_max.txt
cat output.txt | grep -F 'CE avg length' | grep -o -E '[0-9]+'>> ce_avg.txt
cat output.txt | grep -F 'Testing'>> testing.txt