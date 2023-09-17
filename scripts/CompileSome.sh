#!/bin/bash
path=$(cd `dirname $0`; pwd);
cd $path/..;
let DirNum=0;
let FileNum=0;
let exception=0;
dir=();
file=();
let f=0;
echo 'Please enter a directory or a file. Enter "." to start compiling: ';
while [ $f -eq 0 ]
do 
	read -p '>> ' TempArg
	let exception=1;
	if [ -z $TempArg ]
	then exception=0
	else
	if [ $TempArg = '.' ]
		then let f=1;let exception=0;
		else 
			if [ -d $TempArg ]
			then let exception=0;let DirNum++;dir[DirNum]=$TempArg;
			fi
			if [ -f $TempArg ]
			then
				ending=$(echo $TempArg|awk -F "." '{print $NF}')
				if [ $ending = 'lean' ]
				then let exception=0;let FileNum++;file[FileNum]=$TempArg;
				fi
			fi
	fi
	fi
	[ $exception -eq 1 ]&& echo 'Invalid input. Try again'
done

echo 'Please enter configuration file';
conf="";
let f=0;
while [ $f -eq 0 ]
do
	read -p ">> " TempArg
	let exception=1;
	if [ -z $TempArg  ]
		then let f=1;let exception=0;
		else
			if [ -f $TempArg ]
			then let exception=0; 
				conf=$(cat $TempArg)
			fi
	fi
	[ $exception -eq 1 ]&& echo 'Invalid input. Try again'
done	
echo >GradMath.lean;

if [ $DirNum -gt 0 ]
then
for (( i=1; i<=$DirNum; i++)) 
do
	find "./${dir[i]}"  -name "*.lean" | env LC_ALL=C sort \
          | awk -F "." 'BEGIN{ s="";l=0} {s="";l= split($2,a,/\//);for (i=2;i<l;i++){s=s""a[i]"."};s="import "s""a[l];;print s}'\
          >>GradMath.lean;
done
fi

if [ $FileNum -gt 0 ]
then
for (( i=1; i<=$FileNum; i++))
do
	echo "./${file[i]}"| awk -F "." 'BEGIN{ s="";l=0} {s="";l= split($2,a,/\//);for (i=2;i<l;i++){s=s""a[i]"."};s="import "s""a[l];;print s}'\
          >>GradMath.lean;
done
fi

echo >lakefile.lean
echo "import  Lake"   >>lakefile.lean ;
echo "open Lake DSL"  >>lakefile.lean ;
echo "package gradMath"  >>lakefile.lean ;
#echo 'require mathlib from git "https://github.com/luohaoyuan0420-w/mathlib4" @ "02346994ffa7375bc5a45792d47616018fa83488"'>>lakefile.lean ;
echo 'require mathlib from  "./../mathlib4" ' >>lakefile.lean ;
echo "@[default_target]">>lakefile.lean ;
echo "lean_lib GradMath where">>lakefile.lean ;
echo 'srcDir:="./"'>>lakefile.lean ;
echo $conf >>lakefile.lean ;
lake  build ;









