#############################################################################
##
#W  readsml.g                GAP group library             Hans Ulrich Besche
##                                               Bettina Eick, Eamonn O'Brien
##
Revision.readsml_g :=
    "@(#)$Id$";

#############################################################################
##
#V  READ_SMALL_FUNCS[ ]
##
READ_SMALL_FUNCS := [ ];
READ_SMALL_FUNCS[ 2 ] := ReadAndCheckFunc( "small/small2" );
READ_SMALL_FUNCS[ 3 ] := ReadAndCheckFunc( "small/small3" );

#############################################################################
##
#V  READ_IDLIB_FUNCS[ ]
##
READ_IDLIB_FUNCS := [ ];
READ_IDLIB_FUNCS[ 2 ] := ReadAndCheckFunc( "small/id2" );
READ_IDLIB_FUNCS[ 3 ] := ReadAndCheckFunc( "small/id3" );

#############################################################################
##
#X  first read the basic stuff of the small group library and the id-group
##  functions
##
ReadSmall( "small.gd" );
ReadSmall( "small.gi" );

#############################################################################
##
#X  read the 3-primes-order stuff, which is placed in the 'small'-directory
##
ReadSmall( "smlgp1.g" );
ReadSmall( "idgrp1.g" );

#############################################################################
##
#X   read the function-files of the small groups library layers
##
READ_SMALL_FUNCS[ 2 ]( "smlgp2.g", "groups level 2" );
READ_IDLIB_FUNCS[ 2 ]( "idgrp2.g", "idfunctions level 2" );
if IsBound( SMALL_AVAILABLE_FUNCS[ 2 ] ) and
   IsBound( ID_AVAILABLE_FUNCS[ 2 ] ) then
    READ_SMALL_FUNCS[ 3 ]( "smlgp3.g", "groups level 3" );
fi;
if IsBound( SMALL_AVAILABLE_FUNCS[ 3 ] ) then
    READ_IDLIB_FUNCS[ 3 ]( "idgrp3.g", "idfunctions level 3" );
fi;
