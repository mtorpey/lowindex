# Read in the appropriate files
Read("~/scratch/lowindex/low-coin.g");;
Read("~/scratch/lowindex/low-coin.g");;
Read("~/scratch/lowindex/use.g");

# Try running the algorithm on group 14
LowIndexSubgroups(T[14],15,4);

# Tests for index 20
times20 := List([1..14],i->[]);
for i in [1,3,4,5,7,9,11,12,13,14] do
    for j in [1,2,4,8,16,32] do
        times20[i][j] := Bench(LowIndexSubgroups,T[i],20,j);
        Print(i,",",j,": ",times20[i][j],"\n");
    od;
od;