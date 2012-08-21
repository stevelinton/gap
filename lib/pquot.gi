#############################################################################
##  
#W  pquot.gi                    GAP Library                     Werner Nickel
##
#H  $Id$
##
#Y  Copyright (C) 1998, . . . . . . . . .  University of St Andrews, Scotland
##
Revision.pquot_gi :=
    "$Id$";

CHECK := false;
NumberOfCommutators := function( ranks )
    local   class,  hclass,  coranks,  ngens,  cl,  nofc;

    class := Length(ranks);
    hclass := Int( (class)/2 );

    ##  corank[cl] is the number of generators g of weight at least cl+1 such
    ##  that wt(g) + cl <= class.
    coranks := [];
    ngens := Sum( ranks );
    for cl in [1..hclass] do
        ngens := ngens - ranks[cl] - ranks[ class - cl + 1];
        coranks[ cl ] := ngens;
    od;

    nofc := 0;
    for cl in [1..hclass] do
        nofc := nofc + ranks[cl] * coranks[cl]
                     + (ranks[cl] * (ranks[cl]-1))/2;
    od;
    return nofc;
end;

#############################################################################
##
#F  PQStatistics  . . . . . . . . . . . . . . . . . . . p-quotient statistics
##
PQStatistics := rec(
                    TailCountBNA := 0,
                    TailCountBAN := 0,
                    TailCountCBA := 0,
                    ConsCountANA := 0,
                    ConsCountBNA := 0,
                    ConsCountBAN := 0,
                    ConsCountCBA := 0 );

IncreaseCounter := function( string )

    PQStatistics.(string) := PQStatistics.(string) + 1;
end;

PrintCounters := function()

    Print( "Number of consistency checks:\n" );
    Print( "a^p a   : ", PQStatistics.ConsCountANA, "\n" );
    Print( "b a^p   : ", PQStatistics.ConsCountBAN, "\n" );
    Print( "b^p a   : ", PQStatistics.ConsCountBNA, "\n" );
    Print( "c (b a) : ", PQStatistics.ConsCountCBA, "\n" );

    Print( "Number of tail computations:\n" );
    Print( "b a^p   : ", PQStatistics.TailCountBAN, "\n" );
    Print( "b^p a   : ", PQStatistics.TailCountBNA, "\n" );
    Print( "c (b a) : ", PQStatistics.TailCountCBA, "\n" );
end;

ClearPQuotientStatistics := function() 

    PQStatistics.TailCountBNA := 0;
    PQStatistics.TailCountBAN := 0;
    PQStatistics.TailCountCBA := 0;
    PQStatistics.ConsCountANA := 0;
    PQStatistics.ConsCountBNA := 0;
    PQStatistics.ConsCountBAN := 0;
    PQStatistics.ConsCountCBA := 0;

end;

#############################################################################
##
##  The following UTM functions will be replaced by conceptually cleaner
##  functions.  Perhaps Thomas' MutableBases() can now do the jow just as
##  quickly (and not quite as dirty :-).
##
##  This file contains functions working with upper trianguar matrices (UTM).
##  An upper triangular matrix is  a list M of vectors  such that the leading
##  entry of  M[i] is i.  A  UTM is a  record containing the upper triangular
##  matrix,     the zero  of   its  coefficient    domain  and possibly other
##  information.
##

#############################################################################
##
#F  LeadingEntriesUTM . . . . . . . . . . . . return list of leading of a UTM
##
##
LeadingEntriesUTM := function( UTM )

    return Filtered( [1..Length(UTM.matrix)], r->IsBound(UTM.matrix[r]) );
end;

#############################################################################
##
#F  ReducedVectorUTM  . . . . . . . . . . . . . a vector reduced modulo a UTM
##
ReducedVectorUTM := function( UTM, v )
    local   M,  zero,  i;

    M := UTM.matrix;
    zero := UTM.zero;

    if IsBound(M[1]) and Length(v) <> Length(M[1]) then
        Error( "incompatible lengths" );
    fi;

    for i in UTM.bound do
        if v[i] <> zero then
            v := v - v[i] * M[i];
        fi;
    od;

    return v;
end;

#############################################################################
##
#F  AddVectorUTM  . . . . . . . . . . . . . . . . . . . add a vector to a UTM
##
AddVectorUTM := function( UTM, v )
    local   M,  zero,  leadingEntry,  i;

    M    := UTM.matrix;
    zero := UTM.zero;

    if not IsBound( UTM.nullvector ) then
        UTM.nullvector := zero * v;
    fi;

    v := v + zero;
    ##  Reduce vector modulo the matrix
    for i in UTM.bound do
        if v[i] <> zero then
            v := v - v[i] * M[i];
        fi;
    od;

    ##  Check if the vector is zero and, if not, normalize it, add it to the
    ##  upper triangular matrix.
    if v <> UTM.nullvector then
        for leadingEntry in [1..Length(v)] do
            if v[ leadingEntry ] <> zero then
                break;
            fi;
        od;
        v := v / v[ leadingEntry ];
        UTM.matrix[ leadingEntry ] := v;

        InsertElmList( UTM.bound, 
                PositionSorted( UTM.bound, leadingEntry ),
                leadingEntry );
    fi;
    
end;

#############################################################################
##
#F  RowEchelonFormUTM . . . .  row echelon form of an upper triangular matrix
##
RowEchelonFormUTM := function( UTM )
    local   i,  j;

    for i in [1..Length(UTM.matrix)] do
        if IsBound( UTM.matrix[i] ) then
            for j in [1..i-1] do
                if IsBound(UTM.matrix[j]) then
                    UTM.matrix[j] := UTM.matrix[j]
                                     - UTM.matrix[j][i] * UTM.matrix[i]; 
                fi;
            od;
        fi;
    od;
end;

#############################################################################
##
#F  UpperTriangularMatrix . . . . . . . initialize an upper triangular matrix
##
UpperTriangularMatrix := function( field )
    local   UTM;

    UTM := rec();
    UTM.field := field;
    UTM.zero := Zero( field );
    UTM.matrix := [];
    UTM.bound := [];

    return UTM;
end;

#############################################################################
##
#F  QuotSysDefinitionByIndex  . . . . . . . . . . convert index to definition
##
InstallGlobalFunction( QuotSysDefinitionByIndex,
function( qs, index )
    local   r,  j,  i;

    r := RanksOfDescendingSeries( qs )[1];

    if index <= r*(r-1)/2 then
        j := 0; while j*(j-1)/2 < index do j := j+1; od;
        i := index - (j-1)*(j-2)/2;
        return [j,i];
    else
        j := index - r*(r-1)/2;
        if j mod r = 0 then
            return [ j / r + r, r ];
        else
            return [ Int( j / r ) + 1 + r, j mod r ];
        fi;
    fi;

end );

#############################################################################
##
#F  QuotSysIndexByDefinition  . . . . . . . . . . convert definition to index
##
InstallGlobalFunction( QuotSysIndexByDefinition,
function( qs, def )
    local   r;

    r := RanksOfDescendingSeries( qs )[1];
    if def[1] <= r then
        return (def[1]-2) * (def[1]-1) / 2 + def[2];
    else
        return (r-1)*r/2 +  r * (def[1]-2 - (r-1)) + def[2];
    fi;
end );

#############################################################################
##  
#M  GetDefinitionNC . . . . . . . . . . . . get the definition of a generator
##
InstallMethod( GetDefinitionNC, true, [IsPQuotientSystem, IsPosInt], 0,
function( qs , g )

    return qs!.definitions[ g ];
end );

#############################################################################
##
#M  SetDefinitionNC . . . . . . . . . . . . set the definition of a generator
##
InstallMethod( SetDefinitionNC, true,
        [ IsPQuotientSystem, IsPosInt, IsObject ], 0,
function( qs, g, def )

    qs!.definitions[g] := def;
    if IsPosInt( def ) then
        qs!.isDefiningPower[ def ] := true;
    elif IsInt( def ) then
        # set image
        return;
    else
       qs!.isDefiningConjugate[ QuotSysIndexByDefinition( qs, def ) ] := true;
    fi;
end );

#############################################################################
##
#M  ClearDefinitionNC . . . . . . . . . . clear the definition of a generator
##
InstallMethod( ClearDefinitionNC, true, [ IsPQuotientSystem, IsPosInt ], 0,
function( qs, g )
    local   def;

    def := GetDefinitionNC( qs, g );

    Unbind( qs!.definitions[g] );
    if IsPosInt( def ) then
        qs!.isDefiningPower[ def ] := false;
    elif IsInt( def ) then
        return;
    else
       qs!.isDefiningConjugate[ QuotSysIndexByDefinition( qs, def ) ] := false;
    fi;
end );

#############################################################################
##
#F  UpdateWeightInfo  . . . . . . . . . . . . . update the weight information
##
UpdateWeightInfo := function( qs )
    local   n,  nhwg,  ranks,  class,  last_in_cl,  avector,  cl,  wt,  
            avc2,  g,  h;

    n     := GeneratorNumberOfQuotient(qs);
    nhwg  := qs!.numberOfHighestWeightGenerators;
    ranks := RanksOfDescendingSeries(qs);
    class := LengthOfDescendingSeries(qs);

    ##  Update the a-vector.
    last_in_cl := n;
    avector    := [];
    for cl in [1..Int( (LengthOfDescendingSeries(qs)+1)/2 )] do
        Append( avector, [1..ranks[cl]] * 0 + last_in_cl );
        last_in_cl := last_in_cl - ranks[ class - cl + 1 ];
    od;
    Append( avector, [Length(avector)+1..n+nhwg] );
    qs!.collector![SCP_AVECTOR] := avector;

    ##  Update the weight informataion
    class := class + 1;
    qs!.collector![SCP_CLASS] := class;

    wt := qs!.collector![SCP_WEIGHTS];
    wt{n+[1..nhwg]} := [1..nhwg] * 0 + class;

    avc2 := [1..n]+0;
    for g in [1..n] do
        if 3*wt[g] > class then
            break;
        fi;
        h := avector[g];
        while g < h and 2*wt[h] + wt[g] > class do h := h-1; od;
        avc2[g] := h;
    od;
    qs!.collector![SCP_AVECTOR2] := avc2;

    SetFeatureObj( qs!.collector, IsUpToDatePolycyclicCollector, true );
end;

#############################################################################
##
#M  DefineNewGenerators . . . . . . . . . . . .  generators of the next layer
##
InstallMethod( DefineNewGenerators,
        "p-quotient system",
        true,
        [ IsPQuotientSystem ], 0,
function( qs )
    local   gens,  n,  g,  cl,  h,  commute;

    gens := GeneratorsOfRws( qs!.collector );
    n := GeneratorNumberOfQuotient(qs);

    ##  Define a new generator for each non-defining image.
    for g in qs!.nonDefiningImages do
        n := n+1;
        qs!.images[g] := qs!.images[g] * gens[n];
        SetDefinitionNC( qs, n, -g );
    od;

    ##  Add new generators to the p-quotient.
    for cl in [1..LengthOfDescendingSeries(qs)] do

        ##  Each commutator relation of the form [c,1] which is not a
        ##  definition will get a new generator.
        for h in GeneratorsOfLayer( qs, cl ) do
            for g in GeneratorsOfLayer( qs, 1 ) do
                if g >= h then break; fi;
                if not [h,g] in qs!.definitions then
                    n := n+1;
#                    Print( "Defining ", [h,g], " = ", n, "\n" );
                    SetConjugateANC( qs!.collector, h, g, 
                            GetConjugateNC( qs!.collector, h, g ) 
                            * gens[n] );
                    SetDefinitionNC( qs, n, [h,g] );
                fi;
            od;
        od;

        ##  A p-th power of a generator defines a new generator if the
        ##  generator was itself defined by a p-th power. 
        for g in GeneratorsOfLayer( qs, cl ) do
            if not g in qs!.definitions then
                if IsInt( GetDefinitionNC( qs , g ) ) then
                    n := n+1;
#                    Print( "Defining ", g, "^p = ", n, "\n" );
                    SetPowerANC( qs!.collector, g, 
                            GetPowerNC( qs!.collector, g ) * gens[n] );
                    SetDefinitionNC( qs, n, g );
                else
                    qs!.isDefiningPower[ g ] := false;
                fi;
            fi;
        od;
    od;
 
    qs!.numberOfHighestWeightGenerators := n - GeneratorNumberOfQuotient(qs);
    Print( "    Defined ", qs!.numberOfHighestWeightGenerators, 
           " new generators\n" );

    UpdateWeightInfo( qs );
end );

#############################################################################
##
#M  SplitWordTail . . . . . . . . . . . . . . split a word in prefix and tail
##
InstallMethod( SplitWordTail,
        "p-quotient system, word",
        true,
        [ IsPQuotientSystem, IsAssocWord ], 0,
function( qs, w )
    local   n,  c,  one,  zero,  i,  h,  t,  j;

    n := GeneratorNumberOfQuotient(qs);
    c := qs!.numberOfHighestWeightGenerators;
    one := One( qs!.field );
    zero := 0 * one;


    w := ExtRepOfObj( w );

    ##  Find the beginning of the tail.
    i := 1; while i <= Length(w) and w[i] <= n do i := i+2; od;

    ##  Chop off the head.
    h := w{[1..i-1]};

    ##  Convert the tail into an exponent vector.
    t := [];
    for j in Reversed([1..c]) do t[j] := zero; od;

    while i <= Length(w) do
        t[ w[i] - n ] := w[i+1] * one;
        i := i+2;
    od;

    return [ h, t ];
end );

#############################################################################
##
#M  ExtRepByTailVector  . . . . .  ext repr from an exponent vector of a tail
##
InstallMethod( ExtRepByTailVector,
        "p-quotient system, vector",
        true,
        [ IsPQuotientSystem, IsVector ], 0,
function( qs, v )
    local   extrep,  i,  zero;

    extrep := [];    
    if IsInt( v[1] ) then
        for i in [1..Length(v)] do
            if v[i] <> 0 then
                Add( extrep, GeneratorNumberOfQuotient(qs) + i );
                Add( extrep, v[i] mod qs!.prime );
            fi;
        od;
    else
        zero := Zero( qs!.field );
        for i in [1..Length(v)] do
            if v[i] <> zero then
                Add( extrep, GeneratorNumberOfQuotient(qs) + i );
                Add( extrep, Int( v[i]) );
            fi;
        od;
    fi;
    return extrep;
end );

        
#############################################################################
##
#M  TailsInverses . . compute the tails of the inverses in a single collector
##
InstallMethod( TailsInverses,
        "p-quotient system",
        true,
        [ IsPQuotientSystem ], 0,
function( qs )
    local   n,  h,  M,  type,  inverses,  v,  zeroes,  g,  
            t;

    n := GeneratorNumberOfQuotient(qs);
    h := n + qs!.numberOfHighestWeightGenerators;
    M := qs!.centralRelations;

    type     := qs!.collector![SCP_DEFAULT_TYPE];
    inverses := qs!.collector![SCP_INVERSES];

    v      := ListWithIdenticalEntries( h, 0 );
    zeroes := v{[n+1..h]};
    for g in [1..n] do
        repeat 
            v[g] := 1;
        until CollectWordOrFail( qs!.collector, v, inverses[g] ) = true;

        t := ExtRepByTailVector( qs, ReducedVectorUTM( M, -v{[n+1..h]} ) );
        
        inverses[g] := 
          AssocWord( type, Concatenation( ExtRepOfObj( inverses[g] ), t ) );

        v{[n+1..h]} := zeroes;
    od;

end );

#############################################################################
##
#M  ComputeTails  . . . . . . . . . . . . compute the tails of a presentation
##
InstallMethod( ComputeTails,
        "p-quotient system",
        true,
        [ IsPQuotientSystem ], 0,
function( qs )
    local   S,  gens,  p,  type,  n,  m,  l,  r,  zeroes,  c,  g,  
            def,  b,  a,  t,  u,  y,  z,  x;

    S := qs!.collector;
    gens := GeneratorsOfRws( S );
    p := qs!.prime;
    type := S![ SCP_DEFAULT_TYPE ];
    n := GeneratorNumberOfQuotient(qs);
    m := n + qs!.numberOfHighestWeightGenerators;

    l := ListWithIdenticalEntries( m, 0 );
    r := ListWithIdenticalEntries( m, 0 );
    zeroes := ListWithIdenticalEntries( m, 0 );
                    
    for c in Reversed( [1..LengthOfDescendingSeries(qs)] ) do
        ##  The power relations.
        for g in GeneratorsOfLayer( qs, c ) do
            if not g in qs!.definitions then
                def := GetDefinitionNC( qs , g );
                if not IsInt( def ) then
                    b := def[1]; a := def[2];
                    EvaluateOverlapBNA( S, l, r, b, p, a );

                    IncreaseCounter( "TailCountBNA" );
                    
                    t := ExtRepByTailVector( qs, l{[n+1..m]} - r{[n+1..m]} );
                    
                    SetPowerANC( S, g, 
                            GetPowerNC( S,g ) * AssocWord( type,t ) );

                    l{[1..m]} := zeroes;  r{[1..m]} := zeroes;
                fi;
            fi;
        od;
        
        ##  The conjugate relations.
        ##  a is the weight of the first generator, b the weight of the
        ##  second generator in a commutator.  Their sum is c.
        a := c+1-2; b := 2;
        while a >= b do
            for u in GeneratorsOfLayer( qs, b ) do
                ##  How is u defined?
                def := GetDefinitionNC( qs, u );
                ##  Compute the tail for [ z, u ]
                if IsInt( def ) then
                    y := def;
                    for z in GeneratorsOfLayer( qs, a ) do
                        if z > u then
                            IncreaseCounter( "TailCountBAN" );
                            EvaluateOverlapBAN( S, l, r, z, y, p );
                            t := ExtRepByTailVector( qs, 
                                         l{[n+1..m]} - r{[n+1..m]} );
                    
                            SetConjugateANC( S, z, u, 
                                    GetConjugateNC( S,z,u )
                                    * AssocWord( type,t ) );

                            l{[1..m]} := zeroes;  r{[1..m]} := zeroes;
                        fi;
                    od;
                else
                    y := def[1];  x := def[2];
                    for z in GeneratorsOfLayer( qs, a ) do
                        if z > u then
                            IncreaseCounter( "TailCountCBA" );
                            EvaluateOverlapCBA( S, l, r, z, y, x );
                            
                            t := ExtRepByTailVector( qs, 
                                         l{[n+1..m]} - r{[n+1..m]} );
                    
                            SetConjugateANC( S, z, u, 
                                    GetConjugateNC( S, z, u ) 
                                    * AssocWord( type,t ) );

                            l{[1..m]} := zeroes;  r{[1..m]} := zeroes;
                        fi;
                    od;
                fi;
            od;
            a := a - 1;  b := b + 1;
        od;
    od;
end );

#############################################################################
##
#M  EvaluateConsistency . . . . . . . . . . . . . . run the consistency tests
##
InstallMethod( EvaluateConsistency,
        "p-quotient system",
        true,
        [ IsPQuotientSystem ], 0,
function( qs )
    local   S,  gens,  n,  m,  p,  l,  r,  wt,  a,  i,  wta,  wtb,  bs,
            b,  c,  zeroes;

    S := qs!.collector;
    gens := GeneratorsOfRws( S );
    n := GeneratorNumberOfQuotient(qs);
    m := n + qs!.numberOfHighestWeightGenerators;
    p := qs!.prime;

    l := ListWithIdenticalEntries( m, 0 );
    r := ListWithIdenticalEntries( m, 0 );

    zeroes := ListWithIdenticalEntries( m, 0 );

    ##
    ##                      a^p a = a a^p
    ##  The weight condition on the first type of consistency checks is
    ##  2 wt(a) < class.
    ##
    wt := 1;
    while 2*wt < LengthOfDescendingSeries(qs)+1 do
        for a in GeneratorsOfLayer( qs, wt ) do
            EvaluateOverlapANA( S, l, r, a, p );
            if CHECK and l{[1..n]} - r{[1..n]} <> zeroes{[1..n]} then
                Error( "result not a tail" );
            fi;
            AddVectorUTM( qs!.centralRelations, l{[n+1..m]} - r{[n+1..m]} );
            IncreaseCounter( "ConsCountANA" );
            l{[1..m]} := zeroes; r{[1..m]} := zeroes;
        od;
        wt := wt + 1;
    od;

    ## 
    ##  Check all overlaps  b a^p  for  b > a and  wt(b)+wt(a) < class.
    ##
    for wt in [2..LengthOfDescendingSeries(qs)] do
        ##  wt = wt(a) + wt(b)
        wta := 1; wtb := wt - 1;
        while wtb >= wta do
            for a in GeneratorsOfLayer( qs, wta ) do
                bs := GeneratorsOfLayer( qs, wtb );
                if qs!.isDefiningPower[a] then
                    c := GeneratorSyllable( GetPowerNC( S, a ), 1 );
                    ##  For c < b, [b,c] is a commutator for which we have
                    ##  computed its tail by EvaluateBAN( ... b, a, p )
                    ##  Therefore, we only want to invoke EvaluateBAN() for
                    ##  those b with c >= b.
                    if c in bs then
                        bs := [bs[1]..c];
                    fi;
                fi;
#                if bs <> [] then Print( a, ": ", bs, "\n" ); fi;
                for b in bs do
                    if a < b then 
#                        Print( [b,a], "\n" );
                    EvaluateOverlapBAN( S, l, r, b, a, p );
                    IncreaseCounter( "ConsCountBAN" );

            if CHECK and l{[1..n]} - r{[1..n]} <> zeroes{[1..n]} then
                Error( "result not a tail" );
            fi;
                    AddVectorUTM( qs!.centralRelations, 
                            l{[n+1..m]} - r{[n+1..m]} );

                    l{[1..m]} := zeroes; r{[1..m]} := zeroes;
                    fi;
                od;
            od;
            wta := wta+1; wtb := wtb-1;
        od;
    od;

    ##
    ##  Check all overlaps b^p a for b > a, wt(a) = 1 and 
    ##  wt(a) + wt(b) < class.  Hence wt(b) < class - 1.
    ##
    wtb := 1;
    while wtb < LengthOfDescendingSeries(qs)+1 - 1 do
        for b in GeneratorsOfLayer( qs, wtb ) do
            for a in GeneratorsOfLayer( qs, 1 ) do
                if a >= b then break; fi;

                EvaluateOverlapBNA( S, l, r, b, p, a );
                
            if CHECK and l{[1..n]} - r{[1..n]} <> zeroes{[1..n]} then
                Error( "result not a tail" );
            fi;
                AddVectorUTM( qs!.centralRelations,
                        l{[n+1..m]} - r{[n+1..m]} );

                IncreaseCounter( "ConsCountBNA" );
                l{[1..m]} := zeroes; r{[1..m]} := zeroes;
            od;
        od;
        wtb := wtb + 1;
    od;

                
    ##
    ##  Check overlaps c b a with c > b > a and wt(a) = 1 and 
    ##  wt(a) + wt(b) + wt(c) <= class.
    ##
    ##  Since wt(a) = 1 and wt(b) <= wt(c) we can reformulate the above
    ##  condition to
    ##
    ##          wt(b) <= wt(c) = wt - wt(b) - 1
    ##  where wt runs from 1 to class.
    ##  So we get 2 * wt(b) <= wt - 1.
    wt := 2;
    while wt <= LengthOfDescendingSeries(qs)+1 do
        wtb := 1;
        while 2 * wtb <= wt - 1 do
            for c in GeneratorsOfLayer( qs, wt - wtb - 1 ) do
                for b in GeneratorsOfLayer( qs, wtb ) do
                    if b >= c then break; fi;

                    for a in GeneratorsOfLayer( qs, 1 ) do
                        if a >= b then break; fi;

                        EvaluateOverlapCBA( S, l, r, c, b, a );

            if CHECK and l{[1..n]} - r{[1..n]} <> zeroes{[1..n]} then
                Error( "result not a tail" );
            fi;
                        AddVectorUTM( qs!.centralRelations,
                                l{[n+1..m]} - r{[n+1..m]} );

                        IncreaseCounter( "ConsCountCBA" );
                        l{[1..m]} := zeroes; r{[1..m]} := zeroes;
                    od;
                od;
            od;
            wtb := wtb + 1;
        od;
        wt := wt + 1;
    od;
end );

#############################################################################
##
#M  IncorporateCentralRelations . . . . . . . . . . .  relations into pc pres
##
InstallMethod( IncorporateCentralRelations,
        "p-quotient system",
        true,
        [ IsPQuotientSystem ], 0,
function( qs )
    local   M,  coll,  one,  type,  i,  pair,  g,  wt,  wth,  
            h,  w;

    M := qs!.centralRelations;
    coll := qs!.collector;
    one := One( qs!.field );
    type := coll![SCP_DEFAULT_TYPE];

    
    ##  At first we run through the images.
    for i in qs!.nonDefiningImages do
        pair := SplitWordTail( qs, qs!.images[i] );
        pair[2] := ExtRepByTailVector( qs, ReducedVectorUTM( M, pair[2] * one ) );
        qs!.images[i] := 
          AssocWord( type, Concatenation( pair[1], pair[2] ) );
    od;

    ##  Run through the inverses.
    for g in [1..GeneratorNumberOfQuotient(qs)] do
        w := qs!.collector![SCP_INVERSES][g];
        pair := SplitWordTail( qs, w );
        pair[2] := ExtRepByTailVector( qs, 
                           ReducedVectorUTM( M, pair[2] * one ) );
        qs!.collector![SCP_INVERSES][g] :=
                AssocWord( type, Concatenation( pair[1], pair[2] ) );
    od;

    ##  Run through the power relations.
    for g in [1..GeneratorNumberOfQuotient(qs)] do
        pair := SplitWordTail( qs, GetPowerNC( qs!.collector, g ) );
        pair[2] := ExtRepByTailVector( qs, ReducedVectorUTM( M, pair[2] * one ) );
        SetPowerANC( qs!.collector, g,
                AssocWord( type, Concatenation( pair[1], pair[2] ) ) );
    od;

    ##  Run through the commutator relations.
    for wt in Reversed([2..LengthOfDescendingSeries(qs)+1]) do
        wth := wt-1;
        while 2*wth >= wt do
            for h in GeneratorsOfLayer( qs, wth ) do
                for g in GeneratorsOfLayer( qs, wt - wth ) do
                    if g >= h then break; fi;
                    
                    pair := SplitWordTail( qs,
                                    GetConjugateNC( qs!.collector, h, g ) );
                    pair[2] := ExtRepByTailVector( qs,
                                       ReducedVectorUTM( M, pair[2] * one ) );
                    SetConjugateANC( qs!.collector, h, g,
                            AssocWord( type, 
                                    Concatenation( pair[1], pair[2] ) ) );

                od;
            od;
            wth := wth - 1;
        od;
    od;

    ##  Update the definitions:  The relations and images defining generators
    ##  which have been eliminated are no longer definitions.
    for g in LeadingEntriesUTM( qs!.centralRelations ) do
        ClearDefinitionNC( qs, GeneratorNumberOfQuotient(qs) + g );
    od;

    ##  Keep the eliminated generators.
    qs!.eliminatedGens := 
      Union( qs!.eliminatedGens, LeadingEntriesUTM( qs!.centralRelations ) );

    ##  Throw away the central relations and initialize for the next layer? 
    qs!.centralRelations := UpperTriangularMatrix( GF(qs!.prime) );

end );

#############################################################################
##
#M  RenumberHighestWeightGenerators . . . . . . . . . . . renumber generators
##
InstallMethod( RenumberHighestWeightGenerators,
        "p-quotient system",
        true,
        [ IsPQuotientSystem ], 0,
function( qs )
    local   n,  c,  gens,  surgens,  oldgens,  newgens,  g,  
            i,  w,  h,  wt,  wth,  renumber;

    ##  Those generators which have been eliminated from the quotient system
    ##  don't occur anymore.  Now we replace the surviving generators by a
    ##  consecutive list of generators.
    n := GeneratorNumberOfQuotient(qs);
    c := qs!.numberOfHighestWeightGenerators;

       gens := GeneratorsOfRws( qs!.collector );
    surgens := n + DifferenceLists( [1..c], qs!.eliminatedGens );
    oldgens := Concatenation( gens{[1..n]}, gens{surgens} );
    newgens := gens{[1..n+Length(surgens)]};

    renumber := [];
    renumber{Concatenation([1..n], surgens)} := [1..n+Length(surgens)];

    ##  Update the definitions of the surviving generators.
    for g in [1..Length(surgens)] do
        SetDefinitionNC( qs, n+g, GetDefinitionNC( qs, surgens[g] ) );
    od;
    qs!.definitions := qs!.definitions{[1..Length(newgens)]};

    ##  Run through all non-defining images.
    for i in qs!.nonDefiningImages do
        qs!.images[i] := RenumberedWord( qs!.images[i], renumber );
    od;

    ##  Run through all inverses
    for g in [1..GeneratorNumberOfQuotient(qs)] do
        w := qs!.collector![SCP_INVERSES][g];
        w := RenumberedWord( w, renumber );
        qs!.collector![SCP_INVERSES][g] := w;
    od;

    ##  Run through all power relations
    for g in [1..GeneratorNumberOfQuotient(qs)] do
        w := GetPowerNC( qs!.collector, g );
        w := RenumberedWord( w, renumber );
        SetPowerANC( qs!.collector, g, w );
    od;
 
    ##  Run through all conjugate relations
    for wt in Reversed([2..LengthOfDescendingSeries(qs)+1]) do
        wth := wt-1;
        while 2*wth >= wt do
            for h in GeneratorsOfLayer( qs, wth ) do
                for g in GeneratorsOfLayer( qs, wt - wth ) do
                    if g >= h then break; fi;
                    
                    w := GetConjugateNC( qs!.collector, h, g );
                    w := RenumberedWord( w, renumber );
                    SetConjugateANC( qs!.collector, h, g, w );
                od;
            od;
            wth := wth - 1;
        od;
    od;

    Add( qs!.RanksOfDescendingSeries,
         qs!.numberOfHighestWeightGenerators - Length( qs!.eliminatedGens ) );

    qs!.numberOfGenerators := qs!.numberOfGenerators + 
                             qs!.numberOfHighestWeightGenerators - 
                             Length( qs!.eliminatedGens );

    qs!.numberOfHighestWeightGenerators := 0;
    qs!.eliminatedGens := [];
end );

#############################################################################
##
#M  EvaluateRelators  . . . . . . . evaluate relations of a p-quotient system
##
EvaluateRelation := function( sc, w, gens )
    local   v,  i,  g,  e,  j;

    v := ListWithIdenticalEntries( Length(gens), 0 );
    for i in [1..NumberSyllables(w)] do
        g := GeneratorSyllable( w, i );
        e := ExponentSyllable( w, i );
        if e > 0 then
            for j in [1..e] do
                if CollectWordOrFail( sc, v, gens[g] ) = fail then
                    return fail;
                fi;
            od;
        else
            for j in [1..-e] do
                if CollectWordOrFail( sc, v, sc![SCP_INVERSES][g] ) = fail then
                    return fail;
                fi;
            od;
        fi;
    od;
    return v;
end;


InstallMethod( EvaluateRelators,
        "p-quotient system",
        true,
        [ IsPQuotientSystem ], 0,
function( qs )
    local   G,  S,  n,  c,  F,  Fgens,  one,  UTM,  v,  
            zeroes,  r,  rr,  gens;

    G := qs!.preimage;
    S := qs!.collector;

    n := GeneratorNumberOfQuotient(qs);
    c := qs!.numberOfHighestWeightGenerators;
    gens := GeneratorsOfRws( S ){[1..n+c]};

    F     := FreeGroupOfFpGroup( G );
    Fgens := GeneratorsOfGroup( F );

    one := One( qs!.field );
    UTM := qs!.centralRelations;

    v := ListWithIdenticalEntries( n+c, 0 );
    zeroes := v{[n+1..n+c]};

    for r in RelatorsOfFpGroup( G ) do
        rr := MappedWord( r, Fgens, qs!.images );
#        v := EvaluateRelation( S, rr, gens );
#        while v = fail do
#            v := EvaluateRelation( S, rr, gens );
#        od;
        while CollectWordOrFail( S, v, rr ) = fail do
            Print( "#  Collector failed in evaluating relators\n" );
        od;
        AddVectorUTM( UTM, v{[n+1..n+c]} * one );
        
        v{[n+1..n+c]} := zeroes;
    od;
end );

#############################################################################
##
#M  LiftEpimorphism . . . . . . . .  lift the epimorphism onto the p-quotient
##
InstallMethod( LiftEpimorphism,
        "p-quotient system",
        true,
        [ IsPQuotientSystem ], 0,
function( qs )
    local   n,  k,  K,  gens,  g;

    #  Compute tails for inverses of generators.
    TailsInverses( qs );

    #  Evaluate relations.
    EvaluateRelators( qs );

    #  Use those relations in the collector.
#    IncorporateCentralRelations( qs );

end );

#############################################################################
##
#M  QuotientSystem  . . . . . . . . . . . . .  initialize a p-quotient system
##
InstallMethod( QuotientSystem,
        "pquotient",
        true,
        [ IsGroup, IsPosInt, IsPosInt, IsString ],
        0,
function( G, p, n, collector )
    local   qs,  fam,  type;

    if not IsPrime(p) then
        return Error( "prime expected" );
    fi;

    qs := rec();
    
    ## The finitely presented group.
    qs.preimage := G;

    ## The p-quotient.
    qs.prime := p;
    qs.field := GF(p);

    ##  The p-rank of each factor in the p-central series.  The p-class is
    ##  the length of this list.
    qs.LengthOfDescendingSeries := 0;
    qs.RanksOfDescendingSeries  := [];

    ##     images of the generators in G.
    qs.images := [];

    ##     definitions of the generators in P.
    qs.isDefiningPower := [];
    qs.isDefiningConjugate := [];
    qs.definitions := [];
    qs.nonDefiningImages := [];


    ##  Create the collector.  
    if collector = "combinatorial" then
        qs.collector := CombinatorialCollector( FreeGroup( n, "a" ), p );
    else
        qs.collector := SingleCollector( FreeGroup( n, "a" ), p );
    fi;
    
    qs.collector![SCP_INVERSES] := 
      List( qs!.collector![SCP_RWS_GENERATORS], g->g^(p-1) );
    qs.collector![SCP_CLASS]   := 0;
    qs.collector![SCP_WEIGHTS] := [];

    ##  Number of used generators in the collector not counting the highest
    ##  weight generators.
    qs.numberOfGenerators := 0;
    
    ##  Number of highest weight generators.
    qs.numberOfHighestWeightGenerators := 0;

    ##  Eliminated generators: contains those generators which have been
    ##  eliminated by applying central relations to the quotient system.
    ##  These are used when generators are renumbered.
    qs.eliminatedGens := [];
    
    ##  We call the relations obtained by the consistency check and the
    ##  evaluation of relations `central relations'.  They are stored as a
    ##  matrix over GF(p).
    qs.centralRelations := UpperTriangularMatrix( GF(p) );

    ##  Now turn this into a new object.
    fam  := NewFamily( "QuotientSystem", IsQuotientSystem );
    type := NewType( fam, IsPQuotientSystem and IsMutable );
    Objectify( type, qs );

    return qs;
end );

#############################################################################
##  
#M  GeneratorNumberOfQuotient . . . . . . . .  generator number of p-quotient
##
InstallMethod( GeneratorNumberOfQuotient,
    "p-quotient system",
    true,
    [IsPQuotientSystem], 0,
function( qs )
    return qs!.numberOfGenerators;
end );

#############################################################################
##
#M  GeneratorsOfLayer . . . .  generators of a layer in the descending series
##
InstallMethod( GeneratorsOfLayer,
    "p-quotient system",
    true,
    [IsPQuotientSystem, IsPosInt], 0,
function( qs, cl )
    local   ranks,  s;

    ranks := RanksOfDescendingSeries( qs );
    s     := Sum( ranks{[1..cl-1]} );
    return s + [1..ranks[cl]];
end );

    
#############################################################################
##  
#M  LengthOfDescendingSeries  . . . . . . . . length of the descending series
##
InstallMethod( LengthOfDescendingSeries,
    "p-quotient system",
    true,
    [IsPQuotientSystem], 0,
function( qs )
    return Length(RanksOfDescendingSeries(qs));
end );

    
#############################################################################
##  
#M  RanksOfDescendingSeries . . ranks of the factors in the descending series
##
InstallMethod( RanksOfDescendingSeries,
    "p-quotient system",
    true,
    [IsPQuotientSystem], 0,
function( qs )
    return qs!.RanksOfDescendingSeries;
end );

    
#############################################################################
##
#M  CheckConsistencyOfDefinitions . . . . .  check consistency of definitions
##
InstallMethod( CheckConsistencyOfDefinitions,
        "p-quotient system",
        true,
        [IsPQuotientSystem], 0,
function( qs )
    local   g,  h,  def;

    ##  Is each generator marked as defining power contained in .definitions?
    for g in [1..GeneratorNumberOfQuotient(qs)
            -RanksOfDescendingSeries(qs)[LengthOfDescendingSeries(qs)]] do
        if qs!.isDefiningPower[g] and not g in qs!.definitions then
            Print( "#W  Generator number ", g );
            Print( " is marked as a defining power.\n" );
            Print( "#W  There is no corresponding definition.\n" );
            return fail;
        fi;
    od;

    ##  Is each pair of generators marked as defining conjugate contained in
    ##  .definitions? 
    for h in [1..GeneratorNumberOfQuotient(qs)
            -RanksOfDescendingSeries(qs)[LengthOfDescendingSeries(qs)]] do
        for g in [1..Minimum( RanksOfDescendingSeries(qs)[1], h-1 )] do
            if qs!.isDefiningConjugate[ 
                       QuotSysIndexByDefinition( qs, [h,g] ) ] and
               not [h,g] in qs!.definitions then
                Print( "#W  Generator pair ", [h,g] );
                Print( " is marked as a defining conjugate.\n" );
                Print( "#W  There is no corresponding definition.\n" );
                return fail;
            fi;
        od;
    od;
            
    ##  Is each definition marked in .definingPower or .definingConjugate?
    for def in qs!.definitions do
        if IsPosInt( def ) then
            if not qs!.isDefiningPower[ def ] then
                Print( "#W  The power of generator number ", def );
                Print( " defines a generator.\n" );
                Print( "#W  The generator is not marked as defining.\n" );
                return fail;
            fi;
        elif IsInt( def ) then
            ## check defining images
        else
            if not qs!.isDefiningConjugate[ 
                       QuotSysIndexByDefinition( qs, def ) ] then
                Print( "#W  The conjugate pair ", def );
                Print( " defines a generator.\n" );
                Print( "#W  The pair is not marked as defining.\n" );
                return fail;
            fi;
        fi;
    od;

end );

#############################################################################
##  
#F  AbelianPQuotient  . . . . . . . . . . .  initialize an abelian p-quotient
##
InstallGlobalFunction( AbelianPQuotient,
function( qs )
    local   G,  one,  n,  gens,  UTM,  leaders,  d,  
            generators,  i,  r,  l;

    # Setup some variables.
    G    := qs!.preimage;
    one  := One( qs!.field );
    n    := Length( GeneratorsOfGroup( G ) );
    gens := GeneratorsOfRws( qs!.collector );

    UTM := UpperTriangularMatrix( qs!.field );
    for r in RelatorsOfFpGroup( G ) do
        AddVectorUTM( UTM, ExponentSums( r ) * one );
    od;
    RowEchelonFormUTM( UTM );
    leaders := LeadingEntriesUTM( UTM );

    ##  Each row in UTM corresponds to a generator that can be expressed in
    ##  terms of later generators.  The column of the leading entry is the
    ##  generator number.
    qs!.nonDefiningImages := leaders;

    ##  The p-rank.
    d := n - Length( leaders );

    ##  The generator numbers of the p-quotient
    generators := DifferenceLists([1..n],leaders);
    
    ##  Their images are the first d generators.
    qs!.images{ generators } := gens{[1..d]};

    ##  Fix their definitions.
    qs!.definitions{[1..d]} := -generators;

    ##  Now we have to compute the images of the non defining generators.
    l := 0;
    for i in [1..Length(UTM.matrix)] do
        if IsBound( UTM.matrix[i] ) then
            l := l+1;
            r := ShallowCopy(-UTM.matrix[i]);
            r[ leaders[l] ] := 0;
            qs!.images[ leaders[l] ] := 
              ObjByExponents( qs!.collector, List( r{generators}, Int ) );
        fi;
    od;

    qs!.numberOfGenerators := Length( qs!.definitions );
    qs!.RanksOfDescendingSeries[1] := Length( qs!.definitions );

    ##  Update the weight information
    qs!.collector![SCP_CLASS] := 1;
    qs!.collector![SCP_WEIGHTS]{[1..qs!.numberOfGenerators]} := 
      [1..qs!.numberOfGenerators] * 0 + 1;

end );

#############################################################################
##
#F  PQuotient . . . . . . . . . . .  p-quotient of a finitely presented group
##
InstallGlobalFunction( PQuotient,
function( arg )

    local   G,  p,  cl,  ngens,  collector,  qs,  t;


    ##  First we parse the arguments to this function
    if Length( arg ) < 2 or Length( arg ) >= 6 then
        Error( "PQuotient( <G>, <p>, <cl>",
               " [, <ngens>] [, \"single\" | \"combinatorial\" ] )" );
    fi;

    G := arg[1];
    if not IsFpGroup( G ) then
        Error( "The first argument must be a finitely presented group" );
    fi;
    
    p := arg[2];
    if not (IsInt(p) and p > 0 and IsPrime( p )) then
        Error( "The second argument must be a positive prime" );
    fi;

    ##  defaults for the optional parameters
    cl := 666;
    ngens := 256;
    collector := "combinatorial";

    if Length( arg ) >= 3 then
        cl := arg[3];
        if not (IsInt(3) and cl > 0) then
            Error( "The third argument (if present) is the p-class and",
                   " must be a positive integer" );
        fi;
    fi;

    if Length( arg ) >= 4 then
        if IsInt(arg[4]) then
            ngens := arg[4];
            if not ngens > 0 then
                Error( "If the fourth argument is present and an integer,",
                       " then it is the initial number of generators in the",
                       " collector and must be a positive integer" ); 
            fi;
        elif IsString( arg[4] ) then
            collector := arg[4];
            if not (collector = "single" or collector = "combinatorial") then
                Error( "If the fourth argument is present and a string",
                       " then it is the collector that is used during the",
                       " p-quotient algorithm and must be either ",
                       " \"single\" or \"combinatorial\"" );
            fi;
        fi;
    fi;
            
    if Length( arg ) >= 5 then
        collector := arg[5];
        if not (IsString( collector ) and
                (collector = "single" or collector = "combinatorial")) then
                Error( "If the fifth argument is present and a string",
                       " then it is the collector that is used during the",
                       " p-quotient algorithm and must be either ",
                       " \"single\" or \"combinatorial\"" );
        fi;
    fi;


    
    ClearPQuotientStatistics();
    qs := QuotientSystem( G, p, ngens, collector );

    ## First do the abelian p-quotient.  This might later on become a special
    ## case of the general step.
    AbelianPQuotient( qs );

    while LengthOfDescendingSeries(qs) < cl do

        t := Runtime();
        Print( "class ", LengthOfDescendingSeries(qs)+1, " quotient \n" );

        Print( "    Define new generators.\n" );
        DefineNewGenerators( qs );
        Print( "    Compute tails.\n" );
        ComputeTails( qs );

        Print( "    Enforce consistency.\n" );
        EvaluateConsistency( qs );

        Print( "    Lift epimorphism.\n" );
        LiftEpimorphism( qs );

        Print( "    Incorporate relations.\n" );
        IncorporateCentralRelations( qs );
        if qs!.numberOfHighestWeightGenerators > Length(qs!.eliminatedGens) then
            RenumberHighestWeightGenerators( qs );
        else
            qs!.numberOfHighestWeightGenerators := 0;
            qs!.eliminatedGens := [];
            return qs;
        fi;
        
        Print( "        ", 
               RanksOfDescendingSeries(qs)[LengthOfDescendingSeries(qs)],
               " (", Runtime()-t, " msec)\n" );
    od;
    return qs;
end );
#M  ViewObj . . . . . . . . . . . . . . . . . . . .  view a p-quotient system
##
InstallMethod( ViewObj,
        "p-quotient system",
        true,
        [ IsPQuotientSystem ], 0,
function( qs )
    
    Print( "<",
           qs!.prime,
           "-quotient system of ",
           qs!.prime,
           "-class ",
           LengthOfDescendingSeries( qs ),
           " with ",
           GeneratorNumberOfQuotient( qs ),
           " generators>" );
end );
    
#############################################################################
##
#M  EpimorphismQuotientSystem
##  
InstallMethod(EpimorphismQuotientSystem,"for p-quotient systems",true,
  [IsQuotientSystem],0,

function(qs)
local   n,  coll,  i,  H,  l,hom;
  
  # first we form the image group as a pc group:
  # this is code from Werner:
  n := qs!.numberOfGenerators;

  coll := ShallowCopy(qs!.collector);

  coll![ SCP_NUMBER_RWS_GENERATORS ] := n;

  # truncate the collector to the correct number of generators.
  for i in
    [ SCP_RWS_GENERATORS,
      SCP_POWERS,
      SCP_INVERSES,
      SCP_CONJUGATES,
      SCP_AVECTOR,
      SCP_AVECTOR2,
      SCP_RELATIVE_ORDERS,
      SCP_WEIGHTS ] do
    
    if IsBound( coll![ i ] ) and Length( coll![ i ] ) > n then
      coll![ i ] := coll![ i ]{[1..n]};
    fi;
  od;
  H := GroupByRwsNC( coll );

  # now we write the images of the generators of G in H from qs:
  l := List(qs!.images,x->ObjByExtRep(FamilyObj(One(H)),ExtRepOfObj(x)));
  
  hom:=GroupHomomorphismByImagesNC(qs!.preimage,H,
                                     GeneratorsOfGroup(qs!.preimage),l);
  # tell hom about itself
  SetIsSurjective(hom,true);

  return hom;
end );



#############################################################################
##
#E  Emacs . . . . . . . . . . . . . . . . . . . . . . . . . . emacs variables
##  
##  Local Variables:
##  mode:               outline
##  tab-width:          4
##  outline-regexp:     "#[ACEFHMOPRWY]"
##  fill-column:        77
##  fill-prefix:        "##  "
##  eval:               (hide-body)
##  End:
