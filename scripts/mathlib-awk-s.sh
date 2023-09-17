
cd ~/LeanProjDir/target3
list2=$(find s)
cd template 
list1=$(find s)
cd ../output
for file in $list2
do
if [ ! -f "../"$file ]
then 
	mkdir $file
else
	n=0
	for name in $list1
	do
		if [ $file = $name ]&&[  -f "../template/"$name ]
		then
			n=1
		fi
	done
	if [ $n -eq 1 ]
	then
		cp "../"$file  $file
	fi
fi
done


##将模板文件放入template/s 源文件放入s 则会根据模板文件中的文件名复制s中对应文件到output/s
