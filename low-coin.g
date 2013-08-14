#####
# IsCompleteCosetTable(table)
# Returns true iff this coset table is complete
#####
IsCompleteCosetTable := function(table)
    local row;  # Loop variable

    # Check for undefined values (fail)
    for row in table do
        if row <> fail and fail in row then
            return false;
        fi;
    od;

    # All values are defined
    return true;            
end;



#####
# ShallowCopyCosetTable(table)
# Returns a shallow copy of the given coset table
#####
ShallowCopyCosetTable := function(table)
    local newTable,     # New table to be populated
          row;          # Loop variable

    # Copy the parent table to edit it separately
    newTable := [];
    for row in table do
        Add(newTable,ShallowCopy(row));
    od;
    return newTable;
end;



#####
# CyclicConjugates(w)
# Returns all cyclic conjugates of the associative word w.
#####
CyclicConjugates := function(w)
    local S, v;
    S := [];
    v := w;
    repeat
        v := Subword(v,Length(v),Length(v)) * Subword(v,1,Length(v)-1);
        Add(S,v);
    until w = v;
    return Set(S);
end;



#####
# Coincidence(table, a, b, relsX)
# Combines two cosets a and b in the table, then scans them under relsX
# Iff the label is violated, return false
#####
Coincidence := function(table, alphabet, label, a, b, relsX)
    local i,        # Row number in table
          j,        # Column number in row
          x, y,     # Pair of cosets to coincide next
          coin,     # A coincidence to be processed
          queue,    # List of coincidences to process
          coins,    # List of coincidences already effected
          def,      # A new definition made
          defs,     # List of new definitions made
          kill,     # List of rows to be deleted
          rel;

    queue := [ SortedList([a,b]) ];
    coins := [];
    defs := [];
    kill := [];

    while not IsEmpty(queue) do
        x := queue[1][1];
        y := queue[1][2];
        Add(coins,Remove(queue,1));
        #Print("COIN ",x,",",y,"(",label,"): ",table,"\n");

        # Replace all occurrences of y by x
        for i in [1..Size(table)] do
            # Ignore redundant rows
            if table[i] = fail then
                continue;
            fi;

            # Replace in table
            for j in [1..Size(table[i])] do
                if table[i][j] = y then
                    table[i][j] := x;
                fi;
                Add(defs, [i,j]);
            od;

            # Replace in definitions
            for def in defs do
                if def[1] = y then
                    def[1] := x;
                fi;
            od;

            # Replace in queue
            for coin in queue do
                if coin[1] = y then
                    coin[1] := x;
                fi;
                if coin[2] = y then
                    coin[2] := x;
                fi;
                Sort(coin);
                queue := DuplicateFreeList(queue);
            od;
        od;

        # Move entries from y into x
        for j in [1..Size(table[y])] do
            if table[y][j] = fail then
                continue;
            elif table[x][j] = fail then
                table[x][j] := table[y][j];
                Add(defs, [x,j]);
            elif table[x][j] <> table[y][j] then
                # Coincidence between xj and yj
                coin := SortedList([table[x][j], table[y][j]]);
                # Check negative conditions (to avoid duplicate subgroups)
                if coin[1] < label and coin[2] < label then
                    return false;
                elif not (coin in coins or coin in queue) then
                    Add(queue,coin);
                fi;
            fi;
            Add(defs, [x,j]);
        od;
        table[y] := fail;
        #Print(table,"\n");
    od;

    # Scan any new definitions resulting from the coincidence
    defs := DuplicateFreeList(defs);
    for def in defs do
        if table[def[1]] <> fail then
            for rel in relsX[def[2]] do
                # If scanning violates a negative condition, discard this table
                if not Scan(table, alphabet, label, def[1], rel, relsX) then
                    return false;
                fi;
            od;
        fi;
    od;

    #Print("HAPPY!\n");
    # All scans produced valid results
    return true;
end;



#####
# Renumber(table)
# Removes any holes from the table, renumbering any remaining rows
#####
#Renumber := function(table)
#    local i,j,k,row;    # Loop variables
#
#    # Delete all the redundant rows, and renumber
#    for i in Reversed([1..Size(table)]) do
#        if table[i] = fail then
#            for j in [i+1..Length(table)] do
#                # Decrement all occurrences of j
#                for row in Filtered(table, r->r<>fail) do
#                    for k in [1..Size(row)] do
#                        if row[k] = j then
#                            row[k] := j-1;
#                        fi;
#                    od;
#                od;
#            od;
#            # Remove row i
#            Remove(table,i);
#        fi;
#    od;
#end;



#####
# MakeAssignment(table, alphabet, relsX, a, x, b)
# Assign the value b to the position a^x, and process
# any deductions with respect to the relators given
# Return true iff the assignment was successful
#####
MakeAssignment := function(table, alphabet, reps, label, relsX, a, x, b)
    local posX,     # Position of letter x in the alphabet
          posXI,    # Position of x-inverse in the alphabet
          rel;      # Loop variable for a relator in relsX

    # If row b does not exist, add it
    if b > Size(table) then
        table[b] := ListWithIdenticalEntries(Size(alphabet), fail);
        reps[b] := reps[a] * x;
       #Print(reps,"\n");
    fi;

    # Make the assignment a^x = b in the table
    posX := Position(alphabet,x);
    posXI:= Position(alphabet,x^-1);
    table[a][posX] := b;
    table[b][posXI]:= a;

    # Process any deductions from a^x
    for rel in relsX[posX] do
        if not Scan(table, alphabet, label, a, rel, relsX) then
            return false;
        fi;
    od;

    # Process any deductions from b^(x^-1)
    for rel in relsX[posXI] do
        if not Scan(table, alphabet, label, b, rel, relsX) then
            return false;
        fi;
    od;

    # Successful assignment!
    return true;
end;



#####
# Scan(table, alphabet, label, a, rel, relsX)
# Scan coset 'a' under relation 'rel' and make any deductions
# Iff any deductions violate the label, return false
#####
Scan := function(table, alphabet, label, a, rel, relsX)
    local f,        # Coset being inspected in forward scan
          b,        # Coset being inspected in backward scan
          i,        # Location in rel in forward scan
          j,        # Location in rel in backward scan
          nextPos,  # Alphabet position of next character in forward scan
          prevPos,  # Alphabet position of inverse of next character in backward scan
          defs;     # New definitions which arise from a discovered coincidence

    # If this row has been removed, we do not need to scan it
    if table[a] = fail then
        #Print("SCAN*(",a,", ",rel,")\n");
        return true;
    fi;
    
    #DUMMY
    #Print("SCAN (",a,", ",rel,")\n");

    # Scan forwards
    f := a;
    i := 1;
    while i <= Length(rel) do
        nextPos := Position(alphabet,Subword(rel,i,i));
        if table[f][nextPos] <> fail then 
            f := table[f][nextPos];
            i := i + 1;
        else
            break;
        fi;
    od;
    # Check for coincidence
    if i > Length(rel) then
        if f <> a then
            # Coincidence
            if f < label and a < label then
                return false;
            else
                return Coincidence(table, alphabet, label, f, a, relsX);
            fi;
        else
            # Scan completed correctly
            return true;
        fi;
    fi;

    # Scan backwards
    b := a;
    j := Length(rel);
    while j >= i do
        prevPos := Position(alphabet,Subword(rel,j,j)^-1);
        if table[b][prevPos] <> fail then
            b := table[b][prevPos];
            j := j - 1;
        else
            break;
        fi;
    od;
    # Check for coincidence or deduction
    if j < i then
        # Coincidence
        if f < label and b < label then
            return false;
        else
            return Coincidence(table, alphabet, label, f, b, relsX);
        fi;
    elif j = i then
        # Deduction: make an assignment and scan it
        return MakeAssignment(table, alphabet, [], label, relsX, f, Subword(rel,i,i), b);
    fi;

    # Scan completed successfully
    return true;
end;



#####
# FirstInClass(table, alphabet)
# See Holt, Eick & O'Brien 5.4.2 for details
# Returns true iff this table could be the canonical representative of its conjugacy class
#####
FirstInClass := function(table, alphabet)
    local mu,       # Maps new table to old
          v,        # Maps old table to new
          a,        # Loop variable for rows to try
          b,        # Loop variable for rows to inspect
          posX,     # Loop variable for columns
          lambda,   # Number of cosets assigned to new table
          gamma,
          delta,
         #table,
          contA;    # Signal to skip to the next iteration of the outer loop
    
#    table := ShallowCopyCosetTable(tableA);
#    Renumber(table);
    lambda := 0;
    v := ListWithIdenticalEntries(Size(table),0);
    mu := [];

    for a in Filtered([2..Size(table)], i->table[i]<>fail) do
        # Reset break signal
        contA := false;

        # Reset v to 0 after previous value of a
        for b in [1..lambda] do
            if IsBound(mu[b]) then
                v[mu[b]] := 0;
            fi;
        od;

        # Try a as the new point 1 in new table
        v[a] := 1;
        mu[1] := a;
        lambda := 1;

        # Compare corresponding entries b in old and new table
        for b in Filtered([1..Size(table)], i->table[i]<>fail) do
            for posX in [1..Size(alphabet)] do
                if (table[b][posX] = fail) or (table[mu[b]][posX] = fail) then
                    contA := true;
                    break;
                fi;
                gamma := table[b][posX];
                delta := table[mu[b]][posX];

                if v[delta] = 0 then
                    # delta becomes the next point in the table
                    repeat
                        lambda := lambda + 1;
                    until table[lambda] <> fail;
                    v[delta] := lambda;
                    mu[lambda] := delta;
                fi;
                if v[delta] < gamma then
                    # This cannot be the canonical representative
                    return false;
                elif v[delta] > gamma then
                    contA := true;
                    break;
                fi;
            od;
            # Break out of loop if appropriate
            if contA then
                break;
            fi;
        od;
    od;

    # This might be the canonical representative
    return true;
end;



#####
# DescendantSubgroups(table, alphabet, label, relsX, maxIndex, maxCosets)
# Recursively finds all the descendants of this coset table which correspond to
# subgroups of index at most maxIndex subject to all the relations in relsX.
#####
DescendantSubgroups := function(table, alphabet, reps, gens, label, relsX, maxIndex, maxCosets, workQueue, resultsChan, numJobs, depthFirst)
    local rel, b,       # Loop variables
          a, x,         # Coset-letter pair with no entry in table
          childTable,   # Copy of this table, to be modified
          childReps,    # Copy of coset representatives, to be modified
          newGen,       # Generator to be added for the new branch
          subgp,        # Loop variable for subgroups
          descendants,  # List of subgroups found recursively in a branch
          subgps,       # List of valid subgroups
          tasks,        # List of threaded tasks
          task,         # Loop variable
          numBranches,
          newJob;       # New job to be added to the work queue

    subgps := [];
    tasks := [];

    # Run Todd-Coxeter coset enumeration
    while Size(Filtered(table,t->t<>fail)) < maxCosets and not IsCompleteCosetTable(table) do
        # Define a new coset and check for coincidences
        for a in [1..Size(table)] do
            if table[a] <> fail and fail in table[a] then
                x := alphabet[Position(table[a],fail)];
                if not MakeAssignment(table, alphabet, reps, label, relsX, a, x, Size(table)+1) then
                    #Print("MakeAssignment failed!\n");
                    return;
                fi;
                break;
            fi;
        od;
    od;
    
    if not FirstInClass(table, alphabet) then
       #Print("NOT!\n");
        return;
    fi;

    # If the table is a complete and valid solution, add it
    if IsCompleteCosetTable(table) and Size(Filtered(table,t->t<>fail)) <= maxIndex then
        SendChannel(resultsChan,StructuralCopy(gens));
        #Print("ADD ",table,"\n");
    fi;
    
    # Expand the tree by attempting a forced coincidence of each pair (a,b)
    for b in Filtered([label..Size(table)], t->table[t]<>fail) do
        for a in Filtered([1..b-1], t->table[t]<>fail) do
            childTable := ShallowCopyCosetTable(table);
            if Coincidence(childTable, alphabet, b, a, b, relsX) then
                # The new generator of the subgroup is a*b^-1
                newGen := reps[a] * reps[b]^-1;
                
                if depthFirst then
                    DescendantSubgroups(childTable,alphabet,ShallowCopy(reps),Concatenation(gens,[newGen]),b,relsX,maxIndex,maxCosets,workQueue,resultsChan,numJobs,true);
                else
                    # Add this to the work queue
                    newJob := rec(
                                  table := childTable,
                                  reps := ShallowCopy(reps),
                                  label := b,
                                  gens := Concatenation(gens,[newGen])
                                  );
                    SendChannel(workQueue, newJob);
                    atomic numJobs do
                        numJobs[1] := numJobs[1] + 1;
                    od;
                fi;
            fi;
        od;
    od;
end;



#####
# Work(workQueue, resultsChan, numJobs, fin, alphabet, relsX, maxIndex, maxCosets)
# Checks the work queue for available tasks, calculates subgroups, and
# sends output to the results channel
#####
Work := function(workQueue, resultsChan, numJobs, fin, alphabet, relsX, maxIndex, maxCosets, numWorkers)
    local j,            # Record describing a job to be done
          depthFirst;   # Whether to continue depth-first or not
    
    while true do
        # Read from the channel
        j := ReceiveChannel(workQueue);
        
        # If there is no more work, quit
        if j = fail then
            SendChannel(workQueue,fail);
            break;
        fi;
        
        # Check the size of the work queue
        # If there are jobs available, use depth-first
        # Otherwise, create new jobs with breadth-first
        atomic readonly numJobs do
            depthFirst := numJobs > numWorkers;
        od;
        # Enter the function
        DescendantSubgroups(j.table, alphabet, j.reps, j.gens, j.label, relsX, maxIndex, maxCosets, workQueue, resultsChan, numJobs, depthFirst);
        
        # Decrement the job counter
        atomic numJobs do
            numJobs[1] := numJobs[1] - 1;
            # If there are no jobs left, signal that all the work is done
            if numJobs[1] = 0 then
                SignalSemaphore(fin);
            fi;
        od;
    od;
end;



##### 
# LowIndexSubgroups(G, maxIndex)
# Returns representatives of all subgroups of the finitely presented group G
# of index no more than maxIndex.
#####
LowIndexSubgroups := function(G, maxIndex, numWorkers)
    local table,        # Coset table
          alphabet,     # Alphabet of coset table - generators and their inverses
          reps,         # Representatives for all defined cosets
          gens,         # Generators of G
          rels,         # Relators of G
          relsC,        # Cyclic conjugates of rels
          relsX,        # Cyclic conjugates of relsS by first letter
          maxCosets,    # Maximum number of cosets to define
          subgps,       # List of subgroups
          subgp,        # Variable for a single subgroup
          elt,          # Current element
          letter,       # Loop variable for letters
          rel,          # Loop variable for relators
          i,            # Loop variable for subgroups
          tables,       # List of coset tables for subgroups
          workers,      # List of worker threads
          workQueue,    # Channel used to communicate jobs to threads
          resultsChan,  # Channel for solutions
          numJobs,      # Counter of how many jobs have not been completed
          fin;          # Semaphore activated when all work is complete

    # Make some definitions
    gens := FreeGeneratorsOfFpGroup(G);
    rels := RelatorsOfFpGroup(G);
    #List(RelatorsOfFpGroup(G), x->ElementOfFpGroup(FamilyObj(gens[1]),x));
    alphabet := MakeImmutable(Concatenation(gens, List(gens,x->x^-1)));

    # Initialise the coset table with the coset representatives
    table := [];
    reps := [];

    # Define the first coset representing the subgroup itself
    table[1] := ListWithIdenticalEntries(Size(alphabet), fail); # fail = undefined
    reps[1] := One(FreeGroupOfFpGroup(G));

    # Compute the cyclic conjugates of all of the relators
    relsC := [];
    for rel in rels do
        Append(relsC,CyclicConjugates(rel));
    od;

    # Split these relators by initial letter
    relsX := EmptyPlist(Size(alphabet));
    for letter in [1..Size(alphabet)] do
        relsX[letter] := Filtered(relsC, w -> Subword(w,1,1) = alphabet[letter]);
    od;
    MakeImmutable(relsX);

    #Print(relsX);

    # Define a maximum number of cosets that may be defined before a coincidence is forced
    maxCosets := maxIndex + 1;
    
    # Create worker threads
    workQueue := CreateChannel();
    numJobs := [0];
    fin := CreateSemaphore();
    ShareObj(numJobs);
    resultsChan := CreateChannel();
    workers := List([1..numWorkers], i->CreateThread(Work, workQueue, resultsChan, numJobs, fin, alphabet, relsX, maxIndex, maxCosets, numWorkers));

    # Start function
    DescendantSubgroups(table,alphabet,reps,[],2,relsX,maxIndex,maxCosets,workQueue,resultsChan,numJobs,false);
    
    # Wait for all threads to finish, then kill all threads
    WaitSemaphore(fin);
    SendChannel(workQueue,fail);
    
    # Read results from results channel
    subgps := [];
    while true do
        subgp := TryReceiveChannel(resultsChan,fail);
        if subgp = fail then
            break;
        else
            Add(subgps,subgp);
        fi;        
    od;
    
    # Convert these free elements to their corresponding elements in G
    subgps := List(subgps, subgp ->
                   List(subgp, elt->
                        ElementOfFpGroup(FamilyObj(G.1), elt)
                        )
                   );
    
    # Return the subgroups made by these generators
    return List(subgps, subgp->Subgroup(G, subgp));
end;