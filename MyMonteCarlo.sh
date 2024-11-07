#!/bin/bash

# From linux command line, run:
# chmod 755 MyMonteCarlo.sh

# To clean all, run:
# rm ce_count.txt ce_max.txt ce_avg.txt testing.txt output.txt tmp1.txt tmp2.txt resets.txt inputs.txt

n=1

while [ $n -le 4 ]
do
    java -ea -jar target/ralib-0.1-SNAPSHOT-jar-with-dependencies.jar iosimulator -f config > output.txt
    cat output.txt | grep -F 'Counterexamples' | grep -o -E '[0-9]+' >> ce_count.txt
    cat output.txt | grep -F 'CE max length' | grep -o -E '[0-9]+' >> ce_max.txt
    cat output.txt | grep -F 'CE avg length' | grep -o -E '[0-9]+' >> ce_avg.txt
    cat output.txt | grep -F 'Testing' >> testing.txt
    n=$(($n+1))
done
n=$(($n-1))
awk '{print $5}' testing.txt | grep -o -E '[0-9]+' >> resets.txt
awk '{print $7}' testing.txt | grep -o -E '[0-9]+' >> inputs.txt
rm output.txt
awk '{ sum += $1 } END { print sum }' inputs.txt
