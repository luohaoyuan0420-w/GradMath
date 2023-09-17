
cd ~/LeanProjDir
list=$(find target)
for file in $list
do
if [ -f $file ]
then 
	awk '($1 != "#align")&&($1 != "#noalign")&&($2 !="Mathlib.Mathport.Rename")&&($2 !="Mathlib.Mathport.Syntax")&&($2 !="Mathlib.Mathport.Attributes")&&($2 !="Mathlib.Mathport.Notation") {print $0 }' $file >"target2/"$file
fi
done
#awk '($1 != "#align")&&($2 !="Mathlib.Mathport.Rename") {print $0}'
#Mathlib.Mathport.Notation
#awk '($1 != "#align")&&($2 !="Mathlib.Mathport.Rename") {print $0}'
#去除 "#align" 和 "Mathlib.Mathport.Rename" 同时对于 aesop和std的引用改为对 Mathlib.Aesop Mathlib.Std的引用
#将需要处理的文件放入 target和target2/target中，结果是target2/target中的文件被按照要求处理
