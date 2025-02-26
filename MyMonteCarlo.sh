#!/bin/bash

# From linux command line, run:
# chmod 755 MyMonteCarlo.sh

# To clean all, run:
rm ce_count.txt ce_max.txt ce_avg.txt testing.txt output.txt resets.txt inputs.txt rwp.txt
rm ce_count_result.txt ce_max_result.txt ce_avg_result.txt resets_result.txt inputs_result.txt rwp_result.txt

n=0
while [ $n -lt 10 ]
do
    java -ea -jar target/ralib-0.1-SNAPSHOT-jar-with-dependencies.jar iosimulator -f config > output.txt
    cat output.txt | grep -F 'Counterexamples' | grep -o -E '[0-9]+' >> ce_count.txt
    cat output.txt | grep -F 'CE max length' | grep -o -E '[0-9]+' >> ce_max.txt
    cat output.txt | grep -F 'CE avg length' | grep -o -E '[0-9]+' >> ce_avg.txt
    cat output.txt | grep -F 'RWP_CE' | grep -o -E '[0-9]+' >> rwp.txt
    cat output.txt | grep -F 'Testing' >> testing.txt
    n=$(($n+1))
done
awk '{print $5}' testing.txt | grep -o -E '[0-9]+' >> resets.txt
awk '{print $7}' testing.txt | grep -o -E '[0-9]+' >> inputs.txt
sum=`awk '{ sum += $1 } END { print sum }' ce_count.txt`
#echo $((sum/n)) >> ce_count_result.txt
echo $((sum)) >> ce_count_result.txt
sum=`awk '{ sum += $1 } END { print sum }' ce_max.txt`
#echo $((sum/n)) >> ce_max_result.txt
echo $((sum)) >> ce_max_result.txt
sum=`awk '{ sum += $1 } END { print sum }' ce_avg.txt`
#echo $((sum/n)) >> ce_avg_result.txt
echo $((sum)) >> ce_avg_result.txt
sum=`awk '{ sum += $1 } END { print sum }' rwp.txt`
#echo $((sum/n)) >> rwp_result.txt
echo $((sum)) >> rwp_result.txt
sum=`awk '{ sum += $1 } END { print sum }' resets.txt`
#echo $((sum/n)) >> resets_result.txt
echo $((sum)) >> resets_result.txt
sum=`awk '{ sum += $1 } END { print sum }' inputs.txt`
#echo $((sum/n)) >> inputs_result.txt
echo $((sum)) >> inputs_result.txt
# rm output.txt ce_count.txt ce_max.txt ce_avg.txt testing.txt output.txt resets.txt inputs.txt rwp.txt

#Preliminary results:

#10 X 10 Runs

#                        New oracle              RALib
#Average CE count        5.93                    9.61
#Average CE length       7.55                    7.66
#Average CE max length   14.40                   15.94
#Average inputs          84908.16                19041.86
#Average resets          20217.12                1934.43
