# Read in the appropriate files
Read("~/lowindex/low-coin.g");;
Read("~/lowindex/use.g");

# Try running the algorithm on group 14
LowIndexSubgroups(T[14],15,4);

# Tests for index 10
times10 := List([1..14],i->[]);
for i in [1..14] do
    for j in [1,2,4,8,16,32] do
        times10[i][j] := Bench(LowIndexSubgroups,T[i],10,j);
        Print(i,",",j,": ",times10[i][j],"\n");
    od;
od;

Print("INDEX 10: ",times10,"\n");

# Tests for index 15
times15 := List([1..14],i->[]);
for i in [1..14] do
    for j in [1,2,4,8,16,32] do
        times15[i][j] := Bench(LowIndexSubgroups,T[i],15,j);
        Print(i,",",j,": ",times15[i][j],"\n");
    od;
od;

Print("INDEX 15: ",times15,"\n");

# Tests for index 20
times20 := List([1..14],i->[]);
for i in [1,3,4,5,7,9,11,12,13,14] do
    for j in [1,2,4,8,16,32] do
        times20[i][j] := Bench(LowIndexSubgroups,T[i],20,j);
        Print(i,",",j,": ",times20[i][j],"\n");
    od;
od;

Print("INDEX 20: ",times20,"\n");