# 
# GAP code to Check Erdős-Gyárfás conjecture for Cayley graphs
# 


# 
# 
# 
SkipList:=function( n, ln, ls, pos )
    local i;
    for i in [pos+1..ln] do ls[i]:=n; od;
    return ls;
end;;

# 
# 
# 
GetNextList:=function( n, ln, ls )
	local r, k, m, i;
	r := [];
	if ls = 0 then
        for i in [1..ln] do
            Add(r, 1);
        od;
        return r;        
	fi;
	m := ln;
	while ls[m] >= n do
        m := m - 1;
        if m < 1 then 
            return false; 
        fi;
    od;
    if ls[m] < n then
        for i in [1..m-1] do
            Add(r, ls[i]);
        od;  
        Add(r, ls[m]+1);
        for i in [m+1..ln] do
            Add(r, 1);
        od;
        return r;
    fi;
	return r;
end;;



# 
# 
# 
checkCycle := function( S, C )
    local c, g, e, szC, i, j, k;
    e := S[C[1]] * ( S[C[1]]^(-1) );
    g := e;
    szC := Size(C);
    for i in [1..szC] do
        g := g * S[C[i]];
    od;
    if not g = e then  Print("[Bad: g=",g,"]");return false; fi;
    for i in [1..szC] do
        for j in [i .. szC] do
            g := e;
            for k in [i .. j] do
                g := g * S[C[k]];
            od;
            if g = e and not (i=1 and j=szC) then Print("[Bad:",i,",",j,"]"); return false; fi;
        od;
    od;
    return true;
end;


# 
# 
# 
checkCycleSilent := function( S, C )
    local c, g, e, szC, i, j, k;
    e := S[C[1]] * ( S[C[1]]^(-1) );
    g := e;
    szC := Size(C);
    for i in [1..szC] do
        g := g * S[C[i]];
    od;
    if not g = e then  return false; fi;
    for i in [1..szC] do
        for j in [i .. szC] do
            g := e;
            for k in [i .. j] do
                g := g * S[C[k]];
            od;
            if g = e and not (i=1 and j=szC) then return false; fi;
        od;
    od;
    return true;
end;


# 
# 
# 
print2mCycles := function(G, S, stop_on_first)
    local e, s, i, j, l, k, d, szS, szG, A, g, a, b, badarr, found, H, pth;
    e := S[1] * (S[1]^(-1));
    for i in [1..Size(S)] do
        Add( S, S[i]^(-1) );
    od;
    S := AsSet( S );
#     Print( "\nAsSet(S):", S );
    S := AsList( S );
#     Print( "\nAsList(S):", S );
    szG := Size(G);
    szS := Size(S);
    H := Subgroup( G, S );
    if not szG = Size(H) then Print("\n\nCay(G,S) is not connected!"); return -1; fi;
    found := false;
    for i in [2..szG] do
        if found then break; fi;
        l := 2^i;
        if l > szG then break; fi;
#         Print("\nlength:", l);
        d := 0;
        while not d=false do
            d := GetNextList( szS, l, d );
            if d=false then break; fi;
            A := [];
            for k in [1..l] do Add( A, S[ d[k] ] ); od;            
            g := e;
            badarr := false;
            for k in [1..l] do
                g := g * A[k];
                if g=e and k<l then d:=SkipList(szS, l, d, k ); badarr:= true; break; fi;
            od;
            if badarr then continue; fi;
            if not g=e then continue; fi;
#             k := l;
#             g := e;
#             badarr := false;
#             while k>1 do
#                 g := A[k] * g;
#                 if g = e then badarr := true; break; fi;
#                 k := k-1;
#             od;
#             if badarr then continue; fi;
            if (not checkCycleSilent(S,d)) then continue; fi;
            if l>1 then
                Print("\n\nLength: ", Size(A));
                Print("\nValid cycle:", A);
                Print("\nIndex in S: ", d);
#                 pth := [e];
#                 for k in [1..Size(A)] do Add(pth, pth[k]*A[k] ); od;
#                 Print("\nPath: ", pth);
            fi;
            found := true;
            if stop_on_first then return l; fi;
        od;
    od;
    return -1;
end;;


# 
# 
# 
CreateCycleByList := function( ls )
	local i, h ,g;
	g := ();
	for i in [2..Size(ls)] do
		g := g * (ls[1],ls[i]);
	od;
	return g;
end;;


# 
# 
# 
createPremutionByCycStr := function( cyst , ls )
	local i, j, g, k, l, ls2;
	g := ();
	j := 1;
	for i in [1..Size(cyst)] do
        if (not IsBound(cyst[i]) ) then continue; fi;
		for k in [1..cyst[i]] do
			ls2:=[]; for l in [j..j+i] do ls2[l-j+1]:= ls[l]; od;
			g := g * CreateCycleByList(ls2);
			j := j + i+1;
		od;
	od;
	return g;
end;;


# 
# 
# 
checkGuessForSmallGroups := function( minn, maxn )
    local n, G, e, GS, S, SS, r, szS, nm, GCS, S1, CS, szSS;
    for n in [minn..maxn] do
        nm:=0;
        G := SymmetricGroup(n);
        GS := Difference( Set(AsList(G)), Set([()]) );
        GCS := AsSet(List(AsList(G),x->CycleStructurePerm(x)));
#         Print(GCS); continue;
        Print("\n\n\n*****************************************\nn=", n);
        for szS in [2..3] do
            for CS in GCS do
                S1 := createPremutionByCycStr(CS, [1..n]);
                for S in IteratorOfCombinations(GS, szS-1) do
                    Add(S,S1);
#                     Print(S); continue;
                    if S[1]*S[2]=S[2]*S[1] then continue; fi;
                    if szS>2 then
                        if S[1]*S[3]=S[3]*S[1] then continue; fi;
                        if S[3]*S[2]=S[2]*S[3] then continue; fi;
                    fi;
                    SS := Union(S, Set(List(AsList(S),x->x^(-1))));
                    szSS := Size(SS);
                    if szSS<3 then continue; fi;
                    nm:=nm+1;
                    r := print2mCycles(G,S,true);
                    if r>1 then  
                        Print("\n\n\nFor S=", S);
    #                     Print("\nSS=", SS);
                        Print("\n|SS|=", szSS); 
                        Print("\nFounded cycle's length: ", r);
                    else     
                        Print("\n\n\nFor S=", S);
    #                     Print("\nSS=", SS);
                        Print("\n|SS|=", szSS); 
                        Print("\nNot Founded!");
#                         return;
                    fi;
                od;
            od;
        od;
        Print("\nItems for n=", n, ": ", nm);
    od;
end;;




# # # # # # # # # # # # # # # # 
# Sample tests:


# # # Check conjecture for G = T_{4n}

n := 3;

f := FreeGroup( "r", "s" );
G := f / [ f.1^(2*n), f.2^(-2) * f.1^n, f.1 * f.2^-1 * f.1 * f.2 ];
# # PR := PresentationFpGroup(G);
# # FP := FpGroupPresentation( PR );
r := G.1;
s := G.2;

Print("\nG = ",StructureDescription(G));

S := [ r, s ];
Print("\nS=",AsSet(S));

print2mCycles(G,S, true);



# # # Check conjecture for groups of order 3..6:
# checkGuessForSmallGroups(3,6);






