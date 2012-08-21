#############################################################################
##
#W  idgrp2.g                 GAP group library             Hans Ulrich Besche
##                                               Bettina Eick, Eamonn O'Brien
##
##  This file contains the identification routines for groups of order up to
##  1000 except 512, 768 andsize a product of more then 3 primes
##
Revision.idgrp2_g :=
    "@(#)$Id$";

#############################################################################
##
## tell GAP about the component
##
DeclareComponent("id2","2.0");

#############################################################################
##
#F ID_AVAILABLE_FUNCS[ 2 ]
##
ID_AVAILABLE_FUNCS[ 2 ] := function( size )
    if size > 1000 or size in [ 512, 768 ] then 
        return fail;
    fi;

    return rec( func := 8,
                lib := 2 );
end;

#############################################################################
##
#F  ID_GROUP_FUNCS[ 8 ]( G, inforec, <fpcache>, <lookup> )
##
##  standard lookup in identification tree
##
##  fpcache is a list of 'fp's which will be used first to preselect a branch
##  of the ID_GROUP_TREE
##  if lookup is set, just the information if the specifed branch exists is
##  returned (used to investigate if some situaations are unique in small3)
##
ID_GROUP_FUNCS[ 8 ] := function( arg )
    local level, branch, indices, fp, l, L, i, j, size,
          coc, desc, pos, filename, ldesc, Pack, sfp, newcls, lookup,
          cfp, classes, classtyps, sclasstyps, asList, G, inforec, fpcache;              
    # fingerprint used from compression of lists in the ID_GROUP_TREE
    Pack := function( list )
        local r, i;

        if Length( list ) = 0 then
            return 0;
        fi;                                                                  
        list := Flat( list );                          
        r := list[ 1 ] mod 99661;
        for i in list{[ 2 .. Length( list ) ]} do
            r := ( r * 10 + i ) mod 99661;                  
        od;                       
        return r;
    end;                                                                 

    # set up
    G := arg[ 1 ];
    inforec := arg[ 2 ];
    if Length( arg ) > 2 then 
        fpcache := arg[ 3 ];
        size := fpcache[ 1 ];
    else
        fpcache := [];
        size := Size( G );
    fi;
    if Length( arg ) > 3 then
        lookup := arg[ 4 ];
    else
        lookup := false;
    fi;
    level := 1;
    branch := ID_GROUP_TREE;
    indices := [ ];

    # main loop
    while not IsInt( branch ) do
    
        if IsBound( branch.level ) then
            level := branch.level;
        fi;

        if ( IsBound( branch.desc ) ) or
           ( IsBound( branch.func ) and branch.func in [ 11, 12, 18 ] ) then
            level := 6;
        fi;

        if level >= 4 and ( not IsBound( asList ) ) then
            asList := AttributeValueNotSet( AsList, G );
        fi;

        if level >= 5 and ( not IsBound( coc ) ) then
            classes := Orbits( G, asList );
            classtyps := List( classes,
                               x -> [ Order( x[ 1 ] ), Length( x ) ] );
            sclasstyps := Set( classtyps );
            # coc is   Clusters Of Conjugacy   classes
            coc := List( sclasstyps, x-> [ ] );
            for i in [ 1 .. Length( sclasstyps ) ] do
                for j in [ 1 .. Length( classes ) ] do
                    if sclasstyps[ i ] = classtyps[ j ] then
                        Add( coc[ i ], classes[ j ] );
                    fi;
                od;
            od;
        fi;

        if IsBound( branch.desc ) then
            for desc in branch.desc do
                # reconstruct orignial description list of the test
                ldesc := [ desc mod 1000 ];
                desc := QuoInt( desc, 1000 );
                while desc > 0 do
                    Add( ldesc, desc mod 100 );
                    desc := QuoInt( desc, 100 );
                od;
                desc := Reversed( ldesc );
    
                # evaluate the test
                fp := EvalFpCoc( coc, desc );

                # split up clusters of classes acording to the result of test
                sfp := Set( fp );
                newcls := List( sfp, x-> [ ] );
                for i in [ 1 .. Length( sfp ) ] do
                    for j in [ 1 .. Length( fp ) ] do
                        if sfp[ i ] = fp[ j ] then
                            Add( newcls[ i ], coc[ desc[ 2 ] ][ j ] );
                        fi;
                    od;
                od;
                coc := Concatenation( coc{[ 1 .. desc[ 2 ] -1 ]}, newcls,
                                   coc{[ desc[ 2 ] + 1 .. Length( coc ) ]} );
            od;
        fi;

        if Length( fpcache ) > 0 then
            fp := fpcache[ 1 ];
            fpcache := fpcache{[ 2 .. Length( fpcache ) ]};
            level := 1;

        elif IsBound( branch.func ) then
            inforec.branch := branch;
            if IsBound( coc ) then 
                inforec.coc := coc;
            fi;
            inforec := ID_GROUP_FUNCS[ branch.func ]( G, inforec );
            if IsBound( inforec.id ) then 
                return inforec.id;
            fi;
            fp := inforec.fp;

        elif level = 1 then
            fp := Size( G );

        elif level = 2 then
            fp := Pack( List( DerivedSeriesOfGroup( G ),
                       x -> [ Size( G ), AbelianInvariants( G ) ] ) );

        elif level = 3 then
            if IsSolvable( G ) then
                fp :=  Pack( LGWeights( SpecialPcgs( Pcgs( G ) ) ) );
            else                      
                fp :=  Pack( IdGroup( Centre( G ) ) );
            fi;

        elif level = 4 then
            fp := Pack( Collected( List( asList, Order ) ) );

        elif level = 5 then
            fp := Pack( List( coc{[ 2 .. Length( coc ) ]},
                              x -> [ Length( x[ 1 ] ), Length( x ) ] ) );

        else
            # usuall case for level >= 6
            # make fingerprint calculated above at 'IsBound( desc )' 
            # independ from the rowing of conjugacy-classes
            fp := Pack( Collected( fp ) );
        fi;

        pos := Position( branch.fp, fp );
        if IsBool( pos ) then
            if lookup then
                return fail;
            fi;
            Error( "IdSmallGroup: fatal Error. Please mail group to\n",
                   "Hans-Ulrich.Besche@math.rwth-aachen.de" );
        fi;
        Add( indices, pos );

        # load required branch of 'IdGroupTree' if it is not in memory
        if not IsBound( branch.next[ pos ] ) then
            ReadSmallLib( "id", inforec.lib, size, 
                          indices{[ 2 .. Length( indices ) ]} );
        fi;

        if lookup and fpcache = [ ] then
            if IsBound( branch.desc ) then
                branch.next[ pos ].desc := branch.desc;
            fi;
            if IsBound( branch.pos ) then
                branch.next[ pos ].pos := branch.pos;
            fi;
            return branch.next[ pos ];
        fi;

        branch := branch.next[ pos ];

        level := level + 1;
    od;

    # branch is now a integer
    return branch;
end;

#############################################################################
##
#F ID_GROUP_FUNCS[ 9 ]( G, inforec )
##
##  identification of the isomorphism types of maximal subgroups
##
ID_GROUP_FUNCS[ 9 ] := function( G, inforec )
    local m, id;

    for m in AttributeValueNotSet( MaximalSubgroups, G ) do
        id := IdGroup( m )[ 2 ];
        if id in inforec.branch.fp then
            inforec.fp := id;
            return inforec;
        fi;
    od;
    inforec.fp := fail;
    return inforec;
end;

#############################################################################
##
#F  ID_GROUP_FUNCS[ 10 ]( G, inforec )
##
##  identification of the isomorphism type of a p-sylow-subgrop
##
ID_GROUP_FUNCS[ 10 ] := function( G, inforec )
    inforec.fp := IdGroup( SylowSubgroup( G, inforec.branch.p ) )[ 2 ];
    return inforec;
end;

#############################################################################
##
#F  ID_GROUP_FUNCS[ 11 ]( G, inforec )
##
##  identification of the groups by random presentation trying
##
ID_GROUP_FUNCS[ 11 ] := function( G, inforec )
    local spcgs, flcoc, rand, gens;

    spcgs := SpecialPcgs( G );
    flcoc := List( inforec.coc, Concatenation );
    repeat 
        repeat 
            gens := List( inforec.branch.pos, x-> Random( flcoc[ x ] ) );
        until Size( GroupByGenerators( gens ) ) = Size( G );
        rand := CodeGenerators( gens, spcgs ).code;
        if inforec.branch.func = 18 then
            rand := rand mod 99661;
        fi;
    until rand in inforec.branch.fp;
    inforec.fp := rand;
    return inforec;
end;

#############################################################################
##
#F  ID_GROUP_FUNCS[ 18 ]( G, inforec )
##
ID_GROUP_FUNCS[ 18 ] := ID_GROUP_FUNCS[ 11 ];

#############################################################################
##
#F  ID_GROUP_FUNCS[ 12 ]( G, inforec )
##
##  The fp on level 5 some times is identical, even if the Length of the coc
##  is not.
##
ID_GROUP_FUNCS[ 12 ] := function( G, inforec )
    inforec.fp := Length( inforec.coc );
    return inforec;
end;

#############################################################################
##
#F ID_GROUP_FUNCS[ 14 ]( G, inforec )
##
##  test the Length of a minimal generating set.
##
ID_GROUP_FUNCS[ 14 ] := function( G, inforec )
    local g;

    if IsPcGroup( G ) then 
        g := G;
    else
        g := Image( IsomorphismPcGroup( G ) );
    fi;

    inforec.fp := Length( MinimalGeneratingSet( G ) );
    return inforec;
end;
