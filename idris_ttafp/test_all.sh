#!/bin/bash

for g in defs/testing/good/*.def; do
    ./defs_main "$g"
    retVal=$?
    if [ $retVal -ne 0 ]; then
        echo "Test failed. Should have type checked: $g"
        exit 1
    fi
done

for b in defs/testing/bad/*.def; do
    ./defs_main "$b"
    retVal=$?
    if [ $retVal -eq 0 ]; then
        echo "Test failed. Should have NOT type checked: $b"
        exit 1
    fi
done

echo ""
echo "======================================="
echo ""
echo "All tests passed!"
