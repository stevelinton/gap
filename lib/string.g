#############################################################################
##
#W  string.g                     GAP library                    Thomas Breuer
#W                                                             & Frank Celler
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file deals with strings and characters.
##
Revision.string_g :=
    "@(#)$Id$";


#############################################################################
##
#C  IsChar( <obj> ) . . . . . . . . . . . . . . . . .  category of characters
##
##  is the category of characters.
DeclareCategory( "IsChar", IS_OBJECT );


#############################################################################
##
#C  IsString( <obj> ) . . . . . . . . . . . . . . . . . . category of strings
##
##  A string is a dense list of characters. 
#T  will *not* change the representation. (still true? AH)
##
DeclareCategoryKernel( "IsString", IsDenseList, IS_STRING );

#T  1996/08/23  M.Schoenert this is a hack because `IsString' is a category
Add( CATEGORIES_COLLECTIONS, [ IsChar, IsString ] );


#############################################################################
##
#R  IsStringRep( <obj> )
##
DeclareRepresentationKernel( "IsStringRep",
    IsInternalRep, [], IS_OBJECT, IS_STRING_REP );


#############################################################################
##
#V  CharsFamily . . . . . . . . . . . . . . . . . . . .  family of characters
##
BIND_GLOBAL( "CharsFamily", NewFamily( "CharsFamily", IsChar ) );


#############################################################################
##
#V  TYPE_CHAR . . . . . . . . . . . . . . . . . . . . . . type of a character
##
BIND_GLOBAL( "TYPE_CHAR", NewType( CharsFamily, IsChar and IsInternalRep ) );


#############################################################################
##
#F  IsEmptyString(<str>). . . . . . . . . . . . . . . . . empty string tester
##
##  Note that empty list and empty string have the same type, the only way to
##  distinguish them is via 'TNUM_OBJ_INT'.
##
BIND_GLOBAL( "TNUM_EMPTY_STRING",
             [ TNUM_OBJ_INT( "" ), TNUM_OBJ_INT( Immutable( "" ) ) ] );

BIND_GLOBAL( "IsEmptyString", function( obj )
    return     IsString( obj )
           and IsEmpty( obj )
           and TNUM_OBJ_INT( obj ) in TNUM_EMPTY_STRING;
end );


#############################################################################
##
#F  ConvertToStringRep(<obj>) . . . . . . . . . . . . . .  inplace conversion
##
BIND_GLOBAL( "ConvertToStringRep", CONV_STRING );


############################################################################
##
#M  String( <str> ) . . . . . . . . . . . . . . . . . . . . . .  for a string
##
InstallMethod( String,
    "for a string",
    true,
    [ IsString ], 0,
    IdFunc );


#############################################################################
##
#E
##

