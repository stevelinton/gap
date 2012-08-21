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
