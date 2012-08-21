#############################################################################
##
#W  filter.g                    GAP library                     Thomas Breuer
#W                                                             & Frank Celler
#W                                                         & Martin Schoenert
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file deals with filters.
##
Revision.filter_g :=
    "@(#)$Id$";


#############################################################################
##

#V  FILTERS . . . . . . . . . . . . . . . . . . . . . . . list of all filters
##
##  <FILTERS>  and  <RANK_FILTERS> are  lists containing at position <i>  the
##  filter with number <i> resp.  its rank.
##
BIND_GLOBAL( "FILTERS", [] );


#############################################################################
##
#V  RANK_FILTERS  . . . . . . . . . . . . . . . . list of all rank of filters
##
##  <FILTERS>  and  <RANK_FILTERS> are  lists containing at position <i>  the
##  filter with number <i> resp.  its rank.
##
BIND_GLOBAL( "RANK_FILTERS", [] );


#############################################################################
##
#V  INFO_FILTERS  . . . . . . . . . . . . . . . information about all filters
##
##  <INFO_FILTERS> is a lists   containing at position <i> information  about
##  the  <i>.th   filter.  This information   is stored  as  number  with the
##  following meanings:
##
##   0 = no additional information
##   1 = category kernel
##   2 = category
##   3 = representation kernel
##   4 = representation
##   5 = attribute kernel
##   6 = attribute
##   7 = property kernel
##   8 = tester of 7
##   9 = property
##  10 = tester of 9
##
BIND_GLOBAL( "INFO_FILTERS", [] );

BIND_GLOBAL( "FNUM_CATS", [ 1,  2 ] );
BIND_GLOBAL( "FNUM_REPS", [ 3,  4 ] );
BIND_GLOBAL( "FNUM_ATTS", [ 5,  6 ] );
BIND_GLOBAL( "FNUM_PROS", [ 7,  9 ] );
BIND_GLOBAL( "FNUM_TPRS", [ 8, 10 ] );


#############################################################################
##
#V  IMM_FLAGS
##
##  is a flag list.
##  For the filters in `FILTERS{ TRUES_FLAGS( IMM_FLAGS ) }',
##  no immediate method is installed.
##  (The installation of immediate methods changes `IMM_FLAGS'.)
##
IMM_FLAGS := FLAGS_FILTER( IS_OBJECT );
#T EMPTY_FLAGS not yet defined !


#############################################################################
##

#F  Setter( <filter> )  . . . . . . . . . . . . . . . .  setter of a <filter>
##
BIND_GLOBAL( "Setter", SETTER_FILTER );


#############################################################################
##
#F  Tester( <filter> )  . . . . . . . . . . . . . . . .  tester of a <filter>
##
BIND_GLOBAL( "Tester", TESTER_FILTER );


#############################################################################
##

#F  WITH_HIDDEN_IMPS_FLAGS( <flags> )
##
HIDDEN_IMPS := [];
WITH_HIDDEN_IMPS_FLAGS_CACHE      := [];
WITH_HIDDEN_IMPS_FLAGS_COUNT      := 0;
WITH_HIDDEN_IMPS_FLAGS_CACHE_MISS := 0;
WITH_HIDDEN_IMPS_FLAGS_CACHE_HIT  := 0;

BIND_GLOBAL( "CLEAR_HIDDEN_IMP_CACHE", function( filter )
    local   i, flags;

    flags := FLAGS_FILTER(filter);
    for i  in [ 1, 3 .. LEN_LIST(WITH_HIDDEN_IMPS_FLAGS_CACHE)-1 ]  do
        if IsBound(WITH_HIDDEN_IMPS_FLAGS_CACHE[i])  then
          if IS_SUBSET_FLAGS(WITH_HIDDEN_IMPS_FLAGS_CACHE[i+1],flags)  then
            Unbind(WITH_HIDDEN_IMPS_FLAGS_CACHE[i]);
            Unbind(WITH_HIDDEN_IMPS_FLAGS_CACHE[i+1]);
          fi;
      fi;
    od;
end );


# Unbind( WITH_HIDDEN_IMPS_FLAGS );
BIND_GLOBAL( "WITH_HIDDEN_IMPS_FLAGS", function ( flags )
    local   with,  changed,  imp,  hash;

    hash := 2 * ( HASH_FLAGS(flags) mod 1009 ) + 1;
    if IsBound(WITH_HIDDEN_IMPS_FLAGS_CACHE[hash])  then
        if IS_IDENTICAL_OBJ(WITH_HIDDEN_IMPS_FLAGS_CACHE[hash],flags)  then
            WITH_HIDDEN_IMPS_FLAGS_CACHE_HIT :=
              WITH_HIDDEN_IMPS_FLAGS_CACHE_HIT + 1;
            return WITH_HIDDEN_IMPS_FLAGS_CACHE[hash+1];
        fi;
    fi;

    WITH_HIDDEN_IMPS_FLAGS_CACHE_MISS := WITH_HIDDEN_IMPS_FLAGS_CACHE_MISS+1;
    with := flags;
    changed := true;
    while changed  do
        changed := false;
        for imp in HIDDEN_IMPS  do
            if        IS_SUBSET_FLAGS( with, imp[2] )
              and not IS_SUBSET_FLAGS( with, imp[1] )
            then
                with := AND_FLAGS( with, imp[1] );
                changed := true;
            fi;
        od;
    od;

    WITH_HIDDEN_IMPS_FLAGS_CACHE[hash  ] := flags;
    WITH_HIDDEN_IMPS_FLAGS_CACHE[hash+1] := with;
    return with;
end );



#############################################################################
##
#F  InstallHiddenTrueMethod( <filter>, <filters> )
##
BIND_GLOBAL( "InstallHiddenTrueMethod", function ( filter, filters )
    local   imp;

    imp := [];
    imp[1] := FLAGS_FILTER( filter );
    imp[2] := FLAGS_FILTER( filters );
    ADD_LIST( HIDDEN_IMPS, imp );
end );


#############################################################################
##
#F  WITH_IMPS_FLAGS( <flags> )
##
IMPLICATIONS := [];
WITH_IMPS_FLAGS_CACHE      := [];
WITH_IMPS_FLAGS_COUNT      := 0;
WITH_IMPS_FLAGS_CACHE_HIT  := 0;
WITH_IMPS_FLAGS_CACHE_MISS := 0;

BIND_GLOBAL( "CLEAR_IMP_CACHE", function()
    WITH_IMPS_FLAGS_CACHE := [];
end );


BIND_GLOBAL( "WITH_IMPS_FLAGS", function ( flags )
    local   with,  changed,  imp,  hash,  hash2,  i;

    hash := HASH_FLAGS(flags) mod 11001;
    for i  in [ 0 .. 3 ]  do
        hash2 := 2 * ((hash+31*i) mod 11001) + 1;
        if IsBound(WITH_IMPS_FLAGS_CACHE[hash2])  then
            if IS_IDENTICAL_OBJ(WITH_IMPS_FLAGS_CACHE[hash2],flags) then
                WITH_IMPS_FLAGS_CACHE_HIT := WITH_IMPS_FLAGS_CACHE_HIT + 1;
                return WITH_IMPS_FLAGS_CACHE[hash2+1];
            fi;
        else
            break;
        fi;
    od;
    if i = 3  then
        WITH_IMPS_FLAGS_COUNT := ( WITH_IMPS_FLAGS_COUNT + 1 ) mod 4;
        i := WITH_IMPS_FLAGS_COUNT;
        hash2 := 2*((hash+31*i) mod 11001) + 1;
    fi;

    WITH_IMPS_FLAGS_CACHE_MISS := WITH_IMPS_FLAGS_CACHE_MISS + 1;
    with := flags;
    changed := true;
    while changed  do
        changed := false;
        for imp in IMPLICATIONS  do
            if        IS_SUBSET_FLAGS( with, imp[2] )
              and not IS_SUBSET_FLAGS( with, imp[1] )
            then
                with := AND_FLAGS( with, imp[1] );
                changed := true;
            fi;
        od;
    od;

    WITH_IMPS_FLAGS_CACHE[hash2  ] := flags;
    WITH_IMPS_FLAGS_CACHE[hash2+1] := with;
    return with;
end );


#############################################################################
##
#F  InstallTrueMethodNewFilter( <to>, <from> )
##
##  If <from> is a new filter then  it cannot occur in  the cache.  Therefore
##  we do not flush the cache.  <from> should a basic  filter not an `and' of
##  from. This should only be used in the file "type.g".
##
BIND_GLOBAL( "InstallTrueMethodNewFilter", function ( tofilt, from )
    local   imp;

    # Check that no filter implies `IsMutable'.
    # (If this would be allowed then `Immutable' would be able
    # to create paradoxical objects.)
    if     IS_SUBSET_FLAGS( FLAGS_FILTER( tofilt ),
                        FLAGS_FILTER( IS_MUTABLE_OBJ ) )
       and not IS_IDENTICAL_OBJ( from, IS_MUTABLE_OBJ ) then
      Error( "filter <from> must not imply `IsMutable'" );
    fi;

    imp := [];
    imp[1] := FLAGS_FILTER( tofilt );
    imp[2] := FLAGS_FILTER( from );
    ADD_LIST( IMPLICATIONS, imp );
    InstallHiddenTrueMethod( tofilt, from );
end );


#############################################################################
##
#F  InstallTrueMethod( <to>, <from> )
##
BIND_GLOBAL( "InstallTrueMethod", function ( tofilt, from )

    InstallTrueMethodNewFilter( tofilt, from );

    # clear the caches because we do not know if filter <from> is new
    CLEAR_HIDDEN_IMP_CACHE( from );
    CLEAR_IMP_CACHE();
end );


#############################################################################
##
#F  NewFilter( <name>[, <rank>] ) . . . . . . . . . . . . create a new filter
#F  NewFilter( <name>, <implied>[, <rank>] )  . . . . . . create a new filter
##
BIND_GLOBAL( "NewFilter", function( arg )
    local   name,  implied,  rank,  filter;

    if LEN_LIST( arg ) = 3  then
      name    := arg[1];
      implied := arg[2];
      rank    := arg[3];
    elif LEN_LIST( arg ) = 2  then
      if IS_INT( arg[2] ) then
        name    := arg[1];
        implied := 0;
        rank    := arg[2];
      else
        name    := arg[1];
        implied := arg[2];
        rank    := 1;
      fi;
    else
      name    := arg[1];
      implied := 0;
      rank    := 1;
    fi;

    # Create the filter.
    filter := NEW_FILTER( name );
    if implied <> 0 then
      InstallTrueMethodNewFilter( implied, filter );
    fi;

    # Do some administrational work.
    FILTERS[ FLAG1_FILTER( filter ) ] := filter;
    IMM_FLAGS:= AND_FLAGS( IMM_FLAGS, FLAGS_FILTER( filter ) );
    RANK_FILTERS[ FLAG1_FILTER( filter ) ] := rank;
    INFO_FILTERS[ FLAG1_FILTER( filter ) ] := 0;

    # Return the filter.
    return filter;
end );


#############################################################################
##
#F  DeclareFilter( <name> [,<rank>] )
##
BIND_GLOBAL( "DeclareFilter", function( arg )
    BIND_GLOBAL( arg[1], CALL_FUNC_LIST( NewFilter, arg ) );
end );


#############################################################################
##
#F  NamesFilter( <flags> )  . . . . . list of names of the filters in <flags>
##
BIND_GLOBAL( "NamesFilter", function( flags )
    local  bn,  i;

    if IS_FUNCTION(flags)  then
        flags := FLAGS_FILTER(flags);
    fi;
    if IS_LIST(flags)  then
        bn := SHALLOW_COPY_OBJ(flags);
    else
        bn := SHALLOW_COPY_OBJ(TRUES_FLAGS(flags));
    fi;
    for i  in  [ 1 .. LEN_LIST(bn) ]  do
        if not IsBound(FILTERS[ bn[i] ])  then
            bn[i] := STRING_INT( bn[i] );
        else
            bn[i] := NAME_FUNC(FILTERS[ bn[i] ]);
        fi;
    od;
    return bn;

end );


#############################################################################
##
#F  RankFilter( <filter> )  . . . . . . . . . . . . . . . .  rank of a filter
##
##  Compute the rank including the hidden implications.
##
##  (When completion files are used, the precomputed ranks are used.
##  Therefore, `RankFilter' is set in `init.g' to appropriate values;
##  the function that really computes the rank is `RANK_FILTER'.)
##
UNBIND_GLOBAL( "RANK_FILTER" );
BIND_GLOBAL( "RANK_FILTER", function( filter )
    local   rank,  flags,  i;

    rank  := 0;
    if IS_FUNCTION(filter)  then
        flags := FLAGS_FILTER(filter);
    else
        flags := filter;
    fi;
    for i  in TRUES_FLAGS(WITH_HIDDEN_IMPS_FLAGS(flags))  do
        if IsBound(RANK_FILTERS[i])  then
            rank := rank + RANK_FILTERS[i];
        else
            rank := rank + 1;
        fi;
    od;
    return rank;
end );

RankFilter := RANK_FILTER;

UNBIND_GLOBAL( "RANK_FILTER_STORE" );
BIND_GLOBAL( "RANK_FILTER_STORE", function( filter )
    local   hash,  rank,  flags;

    if IS_FUNCTION(filter)  then
        flags := FLAGS_FILTER(filter);
    else
        flags := filter;
    fi;
    hash := HASH_FLAGS(flags);
    rank := RANK_FILTER(flags);
    ADD_LIST( RANK_FILTER_LIST_CURRENT, hash );
    ADD_LIST( RANK_FILTER_LIST_CURRENT, rank );
    return rank;

end );

UNBIND_GLOBAL( "RANK_FILTER_COMPLETION" );
BIND_GLOBAL( "RANK_FILTER_COMPLETION", function( filter )
    local   hash,  flags;

    if IS_FUNCTION(filter)  then
        flags := FLAGS_FILTER(filter);
    else
        flags := filter;
    fi;
    hash := HASH_FLAGS(flags);
    if hash <> RANK_FILTER_LIST[RANK_FILTER_COUNT]  then
        Error( "corrupted completion file" );
    fi;
    RANK_FILTER_COUNT := RANK_FILTER_COUNT+2;
    return RANK_FILTER_LIST[RANK_FILTER_COUNT-1];

end );


#############################################################################
##

#E  filter.g  . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##
