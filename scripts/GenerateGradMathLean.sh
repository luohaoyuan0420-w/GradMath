#!/bin/bash
path=$(cd `dirname $0`; pwd);
cd $path/..;
find ./GradMath  -name "*.lean" | env LC_ALL=C sort \
	| awk -F "." 'BEGIN{ s="";l=0} {s="";l= split($2,a,/\//);for (i=2;i<l;i++){s=s""a[i]"."};s="import "s""a[l];;print s}'\
	>GradMath.lean;

