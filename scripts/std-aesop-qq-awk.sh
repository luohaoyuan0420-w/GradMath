
cd ~/LeanProjDir
list=$(find target)
for file in $list
do
if [ -f $file ]
then
	awk '{split($2,a,"\.");if ((  (a[1]=="Std")||(a[1]=="Aesop")||(a[1]=="Qq"))&&($1 == "import")){$2="Mathlib."$2 } ;print $0 }' $file >"target2/"$file
fi
done


#need to create a folder named target under ~/LeanProjDir/, which contains the source code of [Std/Qq/Aesop]. Then create a folder target2 under ~/LeanProjDir/. Copy the files under 'target' into 'target2'
