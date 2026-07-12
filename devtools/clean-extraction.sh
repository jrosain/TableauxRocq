#!/bin/bash

folder=$1

for file in $(ls $1/*.ml*); do
	if [ $(stat -c %s "$file") -eq 2 ]; then
		rm $file
	fi
done
