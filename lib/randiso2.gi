#############################################################################
##
#W  randiso2.gi               GAP library                  Hans Ulrich Besche
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen, Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
Revision.randiso2_gi :=
    "@(#)$Id$";

#############################################################################
##
#F  EvalFpCoc( coc, desc ). . . . . . . . . . . . . . . . . . . . . . . local
##
EvalFpCoc := function( coc, desc )
    local powers, exp, targets, result, i, j, g1, g2, fcd4, pos;

    if desc[ 1 ] = 1 then
        # test, if g^i in cl(g)
        return List( coc[ desc[ 2 ] ],
                     function( x )
                     if x[ 1 ] ^ desc[ 3 ] in x then return 1; fi; return 0;
                     end );

    elif desc[ 1 ] = 2 then
        # test, if cl(g) is root of cl(h)
        exp := QuoInt( Order( coc[ desc[ 2 ] ][ 1 ][ 1 ] ),
                       Order( coc[ desc[ 3 ] ][ 1 ][ 1 ] ) );
        powers := Flat( coc[ desc[ 3 ] ] );
        return List( coc[ desc[ 2 ] ],
                     function(x)
                     if x[ 1 ] ^ exp in powers then return 1; fi; return 0;
                     end );

    elif desc[ 1 ] = 3 then
        # test, if cl(g) is power of cl(h)
        exp := QuoInt( Order( coc[ desc[ 3 ] ][ 1 ][ 1 ] ),
                       Order( coc[ desc[ 2 ] ][ 1 ][ 1 ] ) );
        # just one representative for each class of power-candidates
        powers := List( coc[ desc[ 2 ] ], x -> x[ 1 ] );
        result := List( powers, x -> 0 );
        for i in List( Flat( coc[ desc[ 3 ] ] ), x -> x ^ exp ) do
            for j in [ 1 .. Length( powers ) ] do
                if i = powers[ j ] then
                    result[ j ] := result[ j ] + 1;
                fi;
            od;
        od;
        return result;

    else 
        # test how often the word [ a, b ] * a^2 is hit
        targets := List( coc[ desc[ 2 ] ], x -> x[ 1 ] );
        result := List( targets, x -> 0 );
        fcd4 := Flat( coc[ desc[ 4 ] ] );
        for g1 in Flat( coc[ desc[ 3 ] ] ) do
            for g2 in fcd4 do
                if desc[ 1 ] = 4 then 
                    pos := Position( targets, Comm( g1, g2 ) * g1 ^ 2 );
                else 
                # desc[ 1 ] = 5
                    pos := Position( targets, Comm( g1, g2 ) * g1 ^ 3 );
                fi;
                if not IsBool( pos ) then
                    result[ pos ] := result[ pos ] + 1;
                fi;
            od;
        od;
        return result;
    fi;
end;

#############################################################################
##
#F CocGroup( G ). . . . . . . . . . . . . . . . . . . . . . . . . . . . local
##
CocGroup := function( g )

   local orbs, typs, styps, coc, i, j;

   # compute the conjugacy classes of G as lists of elements and
   # classify them according to representative order and length
   orbs  := Orbits( g, AsList( g ) );
   typs  := List( orbs, x -> [ Order( x[ 1 ] ), Length( x ) ] );
   styps := Set( typs );
   coc   := List( styps, x-> [ ] );
   for i in [ 1 .. Length( styps ) ] do
      for j in [ 1 .. Length( orbs ) ] do
         if styps[ i ] = typs[ j ] then
            Add( coc[ i ], orbs[ j ] );
         fi;
      od;
   od;
   return coc;
end;

#############################################################################
##
#F DiffCoc( coc, pos, finps ) . . . . . . . . . . . . . . . . . . . . . local
##
DiffCoc := function( coc, pos, finps )

   local tmp, sfinps, i, j;

   # split up the pos-th cluster of coc using the fingerprint-values finps
   sfinps := Set( finps );
   tmp := List( sfinps, x -> [ ] );
   for i in [ 1 .. Length( sfinps ) ] do
      for j in [ 1 .. Length( finps ) ] do
         if sfinps[ i ] = finps[ j ] then
            Add( tmp[ i ], coc[ pos ][ j ] );
         fi;
      od;
   od;
   return Concatenation( coc{[1..pos-1]}, tmp, coc{[pos+1..Length(coc)]} );
   end;

#############################################################################
##
#F DiffCocList( <coclist>, <flagwordtest> ) . . . . . . . . . . . . . . local
##
DiffCocList := function( coclist, flagwordtest )

   # coclist is a list of CocGroup's of some groups. DiffCocList tries to
   # find, if necessary recursive, some "tests" which will differentiate
   # the groups, or at least, to differentiate the clusters of the
   # CocGroup's. If flagwordtest is true, then beside the investigation
   # of the powermaps, additionally some words will be evaluated on the
   # classes.

   local i, j, k, ii, jj, kk, pos, word, lencoc,
         fpcand, fpqual, orders, finps, sfinps,
         qual, mqual, qualfp, hits, phits, cphits, poses, leading;

   Info( InfoRandIso, 2, "    DiffCocList starts" );

   # general informations
   orders := List( coclist[ 1 ], x -> Order( x[ 1 ][ 1 ] ) );
   lencoc := Length( coclist[ 1 ] );

   # create a list of usefull tests on the powermap
   fpcand := [ ];
   for i in [ 2 .. lencoc ] do
      for j in Filtered( [ 2..orders[i]-1 ], x -> Gcd( x, orders[i]) = 1 ) do
         # test, if classes in cluster i are invariant under galois-
         # conjugation to the j-th power
         Add( fpcand, [ 1, i, j ] );
      od;
   od;
   for i in [ 2 .. lencoc - 1 ] do
      for j in [ i + 1 .. lencoc ] do
         if orders[ j ] mod orders[ i ] = 0 then
            # 2, j, i: test if classes in cluster i are roots of classes in j
            # 3, i, j: ... powers
            Append( fpcand, [ [ 2, j, i ], [ 3, i, j ] ] );
         fi;
      od;
   od;

   # try the tests and register the number of groups / clusters they split
   fpqual := [ ];
   for i in [ 1 .. Length( fpcand) ] do
      finps := List( coclist, x -> Collected( EvalFpCoc( x, fpcand[i] ) ) );
      sfinps := Set( finps );
      if Length( sfinps ) = Length( coclist ) then
         # fpcand[ i ] will split into lists of length 1
         Info( InfoRandIso, 2, "    DiffCocList split ", Length( coclist ),
                                " groups up" );
         return [ fpcand[ i ] ];
      fi;
      Add( fpqual, [ Length( sfinps ), Length( finps[ 1 ] ) ] );
   od;

   # find the test best spliting the list of groups
   pos := Position( fpqual, Maximum( fpqual ) );
   if fpqual[ pos ][ 1 ] > 1 then
      Info( InfoRandIso, 2, "    DiffCocList split ", Length( coclist ),
                             " groups in ", fpqual[ pos ][ 1 ], " classes" );
      return [ fpcand[ pos ] ];
   fi;

   # find the test best spliting the clusters and call DiffCocList recursive
   if fpqual[ pos ][ 2 ] > 1 then 
      for j in [ 1 .. Length( coclist ) ] do
         coclist[ j ] := DiffCoc( coclist[ j ], fpcand[ pos ][ 2 ],
                                  EvalFpCoc( coclist[ j ], fpcand[ pos ] ) );
      od;
      # storage optimisation in recursive calls
      Unbind( fpqual );
      fpcand := fpcand[ pos ];
      return Concatenation( [fpcand], DiffCocList( coclist, flagwordtest ) );
   fi;

   # the tests concerning the powermap failed all
   if not flagwordtest then
      Info( InfoRandIso, 2, "    DiffCocList failed without wordtest" );
      return [ fail ];
   fi;

   Info( InfoRandIso, 2, "    DiffCocList starts wordtest" );
   mqual := [ 0, 0 ];
   qualfp := [ ];
   leading := List( coclist, x -> List( Concatenation( x ), y -> y [ 1 ] ) );
   poses := [ ];
   i := 0;
   for j in coclist[ 1 ] do
      Add( poses, [ i + 1 .. i + Length ( j ) ] );
      i := i + Length( j );
   od;

   # loop over the sugested words 
   # 4: Comm( g1, g2 ) * a ^ 2
   # 5: Comm( g1, g2 ) * a ^ 3
   for word in [ 4 .. 5 ] do
      for j in [ 2 .. lencoc ] do
         for k in [ 2 .. lencoc ] do

            # check up desc's [ 4 or 5, x, j, k ], count hits
            hits := List( coclist, x -> List( leading[ 1 ], x -> 0 ) );
            for i in [ 1 .. Length( coclist ) ] do
               for jj in Concatenation( coclist[ i ][ j ] ) do
                  for kk in Concatenation( coclist[ i ][ k ] ) do
                     if word = 4 then
                        pos := Position( leading[i], Comm( jj,kk) * jj ^ 2 );
                     elif word = 5 then
                        pos := Position( leading[i], Comm( jj,kk) * jj ^ 3 );
                     fi;
                     if pos <> fail then
                        hits[ i ][ pos ] := hits[ i ][ pos ] + 1;
                     fi;
                  od;
               od;
            od;

            # analyse hits
            for i in [ 1 .. Length( coclist[ 1 ] ) ] do
               phits := hits{[ 1 .. Length( coclist ) ]}{ poses[ i ] };
               cphits := List( phits, Collected );
               qual := [ Length( Set( cphits ) ), Length( cphits[ 1 ] ) ];
               if qual > mqual then

                  # note this test
                  qualfp := [ word, i, j, k ];
                  if qual[ 1 ] = Length( coclist ) then 
                     Info( InfoRandIso, 2, "    DiffCocList split ",
                                 Length( coclist ), " groups in ", qual[ 1 ],
                                 " classes" );
                     return [ qualfp ];
                  fi;
                  mqual := qual;
               fi;
            od;
         od;
      od;
   od;

   if mqual = [ 1, 1 ] then
      Info( InfoRandIso, 2, "    DiffCocList failed after wordtest" );
      return  [ fail ];
   fi;

   if mqual[ 1 ] > 1 then
      Info( InfoRandIso, 2, "    DiffCocList split ", Length( coclist ),
                             " groups in ", mqual[ 1 ], " classes" );
      return [ qualfp ];
   fi;

   # split up clusters
   for j in [ 1 .. Length( coclist ) ] do
      coclist[ j ] := DiffCoc( coclist[ j ], qualfp[ 2 ],
                                  EvalFpCoc( coclist[ j ], qualfp ) );
   od;
   Unbind( fpqual );
   Unbind( fpcand );
   return Concatenation( [ qualfp ], DiffCocList( coclist, true ) );

end;

#############################################################################
##
#F SplitUpSublistsByFpFunc( list ). . . . . . . . . . . . . . . . . . . local
##
SplitUpSublistsByFpFunc := function( list )

   local result, finp, finps, i, g, j;

   result := [ ];
   finps := [ ];
   for i in [ 1 .. Length( list ) ] do
      if list[ i ].isUnique then 
         Add( result, [ list [ i ] ] );
         Add( finps, false );
      else
         g    := PcGroupCodeRec( list[i] );
         finp := FingerprintFF( g );
         j    := Position( finps, finp );
         if IsBool( j ) then
            Add( result, [ list[ i ] ] );
            Add( finps, finp );
            Info( InfoRandIso, 3, "split into ", Length( finps ),
                  " classes within ", i, " of ", Length( list ), " tests" );
         else
            Add( result[ j ], list[ i ] );
            if i mod 50 = 0 then
              Info( InfoRandIso, 3, "still ", Length( finps ),
                    " classes after ", i, " of ", Length( list ), " tests" );
            fi;
         fi;
      fi;
   od;
   for i in [ 1 .. Length( result ) ] do
      if Length( result[ i ] ) = 1 then
         result[ i ] := result[ i ][ 1 ];
         result[ i ].isUnique := true;
      fi;
   od;
   Info( InfoRandIso, 2, "   Iso: found ", Length(result)," classes incl. ",
          Length( Filtered( result, IsRecord ) )," unique groups");
   return result;
end;

#############################################################################
##
#F CodeGenerators( gens, spcgs ). . . . . . . . . . . . . . . . . . . . local
##
CodeGenerators := function( gens, spcgs )

   local  layers, first, one, pcgs, sgrps, dep, lay, 
          numf, pos, e, tpos, found, et, p;

   gens   := ShallowCopy( gens );
   layers := LGLayers( spcgs );
   first  := LGFirst( spcgs );
   one    := OneOfPcgs( spcgs );
   pcgs   := [ ];
   sgrps  := [ ];
   
   numf   := 0;
   pos    := 0;

   while numf < Length( spcgs ) do
      pos := pos + 1;
      e   := gens[ pos ];
      while e <> one do

         dep := DepthOfPcElement( spcgs, e );
         lay := layers[ dep ];
         tpos := first[ lay + 1 ];
         found := false;
         
         while tpos > first[ lay ] and not found and e <> one do
            tpos := tpos - 1;
            if not IsBound( pcgs[ tpos ] ) then
               pcgs[ tpos ] := e;
               sgrps[ tpos ] := GroupByGenerators( Concatenation( [ e ],
                                pcgs{[ tpos + 1 .. first[ lay + 1 ] - 1 ]},
                                spcgs{[ first[lay+1] .. Length(spcgs) ]} ) );
               for p in Set( FactorsInt( Order( e ) ) ) do
                  et := e ^ p;
                  if et <> one and not et in gens then
                     Add( gens, et );
                  fi;
               od;
               for p in Compacted( pcgs ) do
                  et := Comm( e, p );
                  if et <> one and not et in gens then
                     Add( gens, et );
                  fi;
               od;
               e := one;
               numf := numf + 1;
            else
               if e in sgrps[ tpos ] then
                  found := true;
               fi;
            fi;
         od;
         if found then
            while tpos < first[ lay + 1 ] do
               if tpos + 1 = first[ lay + 1 ] then
                  while e <> one and
                        lay = layers[ DepthOfPcElement( spcgs, e ) ] do
                     e := pcgs[ tpos ] ^ -1 * e;
                  od;
               else
                  while not e in sgrps[ tpos + 1 ] do
                     e := pcgs[ tpos ] ^ -1 * e;
                  od;
               fi;
               tpos := tpos + 1;
            od;
         fi;
      od;
   od;
   pcgs := PcgsByPcSequenceNC( ElementsFamily( FamilyObj( spcgs ) ), pcgs );
   SetRelativeOrders( pcgs, RelativeOrders( spcgs ) );
   return rec( pcgs := pcgs, code := CodePcgs( pcgs ) );
end;

#############################################################################
##
#F  PermGensGens( famPcgs, specialPcgs, gens1, gens2 ). . . . . . . . . local
##
PermGensGens := function( fam, spcgs, gens1, gens2 )
    local i, j, perm, l1, l2, elem1, elem2, indices, rel, g;

    gens1 := CodeGenerators( gens1, spcgs ).pcgs;
    gens2 := CodeGenerators( gens2, spcgs ).pcgs;
    l1 := [ gens1[ 1 ] ^ Order( gens1[ 1 ] ) ];
    l2 := [ l1[ 1 ] ];
    rel := RelativeOrders( gens1 );
    for i in Reversed( [ 1 .. Length( gens1 ) ] ) do
        elem1 := ShallowCopy( l1 );
        elem2 := ShallowCopy( l2 );
        for j in [ 1 .. rel[ i ] - 1 ] do
            Append( elem1, gens1[ i ] ^ j * l1 );
            Append( elem2, gens2[ i ] ^ j * l2 );
        od;
        l1 := elem1;
        l2 := elem2;
    od;
    rel := RelativeOrders( fam );
    indices := [];
    indices[ Length( rel ) ] := 1;
    for i in Reversed( [  2 .. Length( rel ) ] ) do
        indices[ i - 1 ] := indices[ i ] * rel[ i ];
    od;

    l1 := [ ]; l2 := [ ];
    for i in [ 1 .. Length( elem1 ) ] do
        Add( l1, ExponentsOfPcElement( fam, elem1[ i ] ) * indices  + 1 );
        Add( l2, ExponentsOfPcElement( fam, elem2[ i ] ) * indices  + 1 );
    od;

    perm := [];
    for i in [ 1 .. Length( l1 ) ] do
        perm[ l1[ i ] ] := l2[ i ];
    od;

    return PermList( perm );
end;

#############################################################################
##
#F DistinguishGroups( list )
##
DistinguishGroups := function( list )

local i, j, cocs, finps;

   i := 1;
   while i <= Length( list ) do
      if IsList( list[ i ] ) then
         cocs := List( list[ i ], x->CocGroup( PcGroupCodeRec( x ) ) );
         finps := DiffCocList( cocs, true );

         if finps[ Length( finps ) ] <> fail then
            # separation was succesful
            finps := finps[ Length( finps ) ];
            finps := List( cocs, x -> Collected( EvalFpCoc( x,finps ) ) );

            list[ i ] := List( Set( finps ), x -> list[ i ]{Filtered(
                    [ 1 .. Length( list[ i ] ) ], y -> finps[ y ] = x ) } );
            Info( InfoRandIso, 1, "   IdentifyGroups splits list  of ", 
                  Length( finps ), " groups in ", Length( list[ i ] ),
                  " sublists" );
            for j in [ 1 .. Length( list[ i ] ) ] do
                if Length( list[ i ][ j ] ) = 1 then
                    list[ i ][ j ][ 1 ].isUnique := true;
                    list[ i ][ j ] := list[ i ][ j ][ 1 ];
                fi;
            od;
            Append( list, list[ i ]{[ 2 .. Length( list[ i ] ) ]} );
            list[ i ] := list[ i ][ 1 ];

            if IsList( list[ i ] ) then 
               # DiffCocList should be started again on block i
               i := i - 1;
            fi;

         else 
            Info( InfoRandIso, 1, "   IdentifyGroups could not seperate" );
         fi;
      fi;
      i := i + 1;
   od;
   return list;
end;
