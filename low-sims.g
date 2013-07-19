#####
# IsCompleteCosetTable(table, alphabet)
# Returns true iff this coset table with this alphabet is complete
#####
IsCompleteCosetTable := function(table, alphabet)
    local row;  # Loop variable

    # Check for undefined values (fail)
    for row in table do
        if fail in row then
            return false;
        fi;
    od;

    # All values are defined
    return true;            
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
# MakeAssignment(table, alphabet, rels, a, x, b)
# Assign the value b to the position a^x, and process
# any deductions with respect to the relators given
# Return true iff the assignment was successful
#####
MakeAssignment := function(table, alphabet, rels, a, x, b)
    local posX,     # Position of letter x in the alphabet
          posXI,    # Position of x-inverse in the alphabet
          rel;      # Loop variable for a relator in rels

    # Make the assignment a^x = b in the table
    posX := Position(alphabet,x);
    posXI:= Position(alphabet,x^-1);
    table[a][posX] := b;
    table[b][posXI]:= a;

    # Process any deductions from a^x
    for rel in rels[posX] do
        # If ScanCheck fails, discard this table
        if not ScanCheck(table, alphabet, a, rel, rels) then
            return false;
        fi;
    od;

    # Process any deductions from b^(x^-1)
    for rel in rels[posXI] do
        # If ScanCheck fails, discard this table
        if not ScanCheck(table, alphabet, b, rel, rels) then
            return false;
        fi;
    od;

    # Successful assignment!
    return true;
end;



#####
# ScanCheck(table, a, rel, relsSX)
# Scan coset 'a' under relation 'rel'
# Return false iff the scan completes incorrectly
#####
ScanCheck := function(table, alphabet, a, rel, relsSX)
    local f,        # Coset being inspected in forward scan
          b,        # Coset being inspected in backward scan
          i,        # Location in rel in forward scan
          j,        # Location in rel in backward scan
          nextPos,  # Alphabet position of next character in forward scan
          prevPos;  # Alphabet position of inverse of next character in backward scan

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
            # Scan completed incorrectly (coincidence)
            return false;
        else
            # Scan did not complete
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
        # Scan completed incorrectly (coincidence)
        return false;
    elif j = i then
        # Deduction: make an assignment and check whether it holds
        if not MakeAssignment(table, alphabet, relsSX, f, Subword(rel,i,i), b) then
            return false;
        fi;
    fi;
    
    # Scan completed correctly
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
          contA;    # Signal to skip to the next iteration of the outer loop

    lambda := 0;
    v := ListWithIdenticalEntries(Size(table),0);
    mu := [];

    for a in [2..Size(table)] do
        # If this a has already been disregarded in an
        # ancestor table, we need not try it again
        if table[a][Size(alphabet)+1] = false then
            continue;
        fi;
        
        # Reset break signal
        contA := false;

        # Reset v to 0 after previous value of a
        for b in [1..lambda] do
            v[mu[b]] := 0;
        od;

        # Try a as the new point 1 in newTable
        v[a] := 1;
        mu[1] := a;
        lambda := 1;

        # Compare corresponding entries b in old and new table
        for b in [1..Size(table)] do
            for posX in [1..Size(alphabet)] do
                if (table[b][posX] = fail) or (table[mu[b]][posX] = fail) then
                    contA := true;
                    break;
                fi;
                gamma := table[b][posX];
                delta := table[mu[b]][posX];

                if v[delta] = 0 then
                    # delta becomes the next point in the table
                    lambda := lambda + 1;
                    v[delta] := lambda;
                    mu[lambda] := delta;
                fi;
                if v[delta] < gamma then
                    # This cannot be the canonical representative
                    return false;
                elif v[delta] > gamma then
                    # We need not try this a in any descendants
                    table[a][Size(alphabet)+1] := false;
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

    # This could be the canonical representative
    return true;
end;



#####
# TryDescendant(table, alphabet, relsSX, relsL, maxIndex, a, x, b)
# Attempt to assign a^x = b to a copy of the coset table.
# Return any valid descendants of that table subject to the relators.
#####
TryDescendant := function(table, alphabet, relsSX, relsL, maxIndex, a, x, b)
    local newTable, # Descendant table we construct
          posX,     # Position of letter x in the alphabet
          posXI,    # Position of x's inverse in the alphabet
          rel,      # Loop variable for a relator in relsSX
          row;      # Loop variable for a row in table
          
    # Copy the parent table to edit it separately
    newTable := [];
    for row in table do
        Add(newTable,ShallowCopy(row));
    od;

    # Add a new row if necessary
    if b > Size(newTable) then
        Add(newTable, ListWithIdenticalEntries(Size(alphabet), fail));
        Add(newTable[b],true);
    fi;

    # Attempt to make the assignment
    if not MakeAssignment(newTable, alphabet, relsSX, a, x, b) then
        # If MakeAssignment rejects the table, discard it
        return [];
    fi;

    # If this can be the canonical representative of its
    # conjugacy class, then return all its descendants
    if FirstInClass(newTable,alphabet) then
        return DescendantSubgroups(newTable, alphabet, relsSX, relsL, maxIndex);
    else
        return [];
    fi;
end;



#####
# DescendantSubgroups(table, alphabet, relsSX, relsL, maxIndex)
# Recursively finds all the descendants of this coset table which correspond to
# subgroups of index at most maxIndex subject to all the specified relations.
#####
DescendantSubgroups := function(table, alphabet, relsSX, relsL, maxIndex)
    local rel, b,   # Loop variables
          a, x,     # Coset-letter pair with no entry in table
          tables;   # Set of tables

    tables := [];

    if IsCompleteCosetTable(table,alphabet) then
        # Check whether the "long" relators are satisfied
        for rel in relsL do
            for b in [1..Size(table)] do
                if not ScanCheck(table,alphabet,b,rel,[]) then
                    # Discard this table and return nothing
                    return [];
                fi;
            od;
        od;
        # The relators are satisfied
        Add(tables,table);
    else
        # Find the first undefined entry a^x
        for a in [1..Size(table)] do
            if fail in table[a] then
                x := alphabet[Position(table[a],fail)];
                break;
            fi;
        od;
        # Try any valid descendants with a^x := b
        for b in [1..Size(table)+1] do
            if b <= maxIndex and (b>Size(table) or table[b][Position(alphabet,x^-1)] = fail) then
                # Try assigning b to a^x
                Append(tables,TryDescendant(table,alphabet,relsSX,relsL,maxIndex,a,x,b));
            fi;
        od;
    fi;

    # Return the (possibly amended) list of tables
    return tables;
end;



##### 
# LowIndexSubgroups(G, maxIndex)
# Returns representatives of all subgroups of the finitely presented group G
# of index no more than maxIndex.
#####
LowIndexSubgroups := function(G, maxIndex)
    local table,        # Coset table
          alphabet,     # Alphabet of coset table - generators and their inverses
          gens,         # Generators of G
          rels,         # Relators of G
          relsS,        # "Short" relators
          relsL,        # "Long" relators
          relsSC,       # Cyclic conjugates of relsS
          relsSX,       # Cyclic conjugates of relsS by first letter
          subgps,       # List of subgroups
          subgp,        # Current subgroup
          letter,       # Loop variable for letters
          rel,          # Loop variable for relators
          tables;       # List of coset tables for subgroups

    # Make some definitions
    gens := FreeGeneratorsOfFpGroup(G);
    rels := RelatorsOfFpGroup(G);
    alphabet := Union(gens,List(gens,x->x^-1));

    # Initialise the coset table
    table := [];

    # Define the first coset
    table[1] := ListWithIdenticalEntries(Size(alphabet), fail); # fail = undefined
    
    # Each coset has an additional entry in the table to remember results from FirstInClass
    # true: Renumbering this coset "1" MAY produce a "lower" equivalent table
    # false: Renumbering this coset "1" CANNOT produce a "lower" equivalent table
    Add(table[1],false);

    # Split the relators into "short" and "long"
    relsS := [];
    relsL := [];
    for rel in rels do
        if Length(rel) < 16 then
            Add(relsS,rel);
        else
            Add(relsL,rel);
        fi;
    od;
    
    # Add all the cyclic conjugates of all of the short relators
    relsSC := [];
    for rel in relsS do
        Append(relsSC,CyclicConjugates(rel));
    od;

    # Split the short relators by first letter
    relsSX := EmptyPlist(Size(alphabet));
    for letter in [1..Size(alphabet)] do
        relsSX[letter] := Filtered(relsSC, w -> Subword(w,1,1) = alphabet[letter]);
    od;

    # Enter recursive function
    tables := DescendantSubgroups(table,alphabet,relsSX,relsL,maxIndex);
    
    # Construct subgroups from coset tables
    subgps := [];
    for table in tables do
        table := TransposedMat(table);
        table := table{[1..Size(alphabet)]};
        subgp := Objectify(NewType(FamilyObj(G),IsGroup and IsAttributeStoringRep ), rec() ); 
        SetParent(subgp, G);
        SetCosetTableInWholeGroup(subgp, table);
        SetIndexInWholeGroup(subgp, Size(table));
        Add(subgps, subgp);
    od;
    
    return subgps;
end;