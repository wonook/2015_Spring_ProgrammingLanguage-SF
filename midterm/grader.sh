#!/usr/bin/env bash

NAME=mid
NPROBS=8
WORKSPACE=_workspace

LIBRARIES="${NAME}_00"

# 1. empty the workspace
rm -rf ${WORKSPACE} && mkdir ${WORKSPACE}

# 2. populate the library files in the workspace
for l in ${LIBRARIES}; do
    cp original/${l}.v ${WORKSPACE}
    coqc -I ${WORKSPACE} ${WORKSPACE}/${l}.v
done

# 3. for each problem number `i`,
for i in $(seq -f "%02g" 1 ${NPROBS}); do
    echo "Problem ${i}:"

    # 3-1. compile the submitted version; and 
    cp submission/${NAME}_${i}.v ${WORKSPACE}
    coqc -I ${WORKSPACE} ${WORKSPACE}/${NAME}_${i}.v
    ec=$?
    if [[ ${ec} != 0 ]]; then
        echo "Error! Please fix the error before submission."
        exit ${ec}
    fi

    # 3-2. compile the original version (for later problems)
    cp original/${NAME}_${i}.v ${WORKSPACE}
    coqc -I ${WORKSPACE} ${WORKSPACE}/${NAME}_${i}.v
done
