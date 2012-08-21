#############################################################################
##
#W  vecmat.gd                   GAP Library                      Frank Celler
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the basic operations for creating and doing arithmetic
##  with vectors.
##
Revision.vecmat_gd :=
    "@(#)$Id$";


#############################################################################
##
#v  GF2One  . . . . . . . . . . . . . . . . . . . . . . . . . .  one of GF(2)
##
BIND_GLOBAL( "GF2One", Z(2) );


#############################################################################
##
#v  GF2Zero . . . . . . . . . . . . . . . . . . . . . . . . . . zero of GF(2)
##
BIND_GLOBAL( "GF2Zero", 0*Z(2) );


#############################################################################
##
#R  IsGF2VectorRep( <obj> ) . . . . . . . . . . . . . . . . . vector over GF2
##
DeclareRepresentation(
    "IsGF2VectorRep",
    IsDataObjectRep, [],
    IsRowVector );


#############################################################################
##
#V  TYPE_LIST_GF2VEC  . . . . . . . . . . . . . . type of mutable GF2 vectors
##
DeclareGlobalVariable(
    "TYPE_LIST_GF2VEC",
    "type of a packed GF2 vector" );


#############################################################################
##
#V  TYPE_LIST_GF2VEC_IMM  . . . . . . . . . . . type of immutable GF2 vectors
##
DeclareGlobalVariable(
    "TYPE_LIST_GF2VEC_IMM",
    "type of a packed, immutable GF2 vector" );


#############################################################################
##
#F  ConvertToGF2VectorRep( <vector> ) . . . . . . . .  convert representation
##
DeclareSynonym( "ConvertToGF2VectorRep", CONV_GF2VEC );

#############################################################################
##
#F  ConvertToVectorRep( <list> )
##
##  converts <list> to an internal vector representation if possible.
DeclareGlobalFunction( "ConvertToVectorRep");

#############################################################################
##
#F  ConvertToMatrixRep( <list> )
##
##  converts <list> to an internal matrix representation if possible.
DeclareGlobalFunction( "ConvertToMatrixRep");

#############################################################################
##
#F  ImmutableGF2VectorRep( <vector> ) . . . . . . . .  convert representation
##
BIND_GLOBAL( "ImmutableGF2VectorRep", function( vector )
    if ForAny( vector, x -> x <> GF2Zero and x <> GF2One )  then
        return fail;
    fi;
    vector := ShallowCopy(vector);
    CONV_GF2VEC(vector);
    SET_TYPE_DATOBJ( vector, TYPE_LIST_GF2VEC_IMM );
    return vector;
end );


#############################################################################
##

#R  IsGF2MatrixRep( <obj> ) . . . . . . . . . . . . . . . . . matrix over GF2
##
DeclareRepresentation(
    "IsGF2MatrixRep",
    IsPositionalObjectRep, [],
    IsMatrix );


#############################################################################
##
#M  IsOrdinaryMatrix( <obj> )
#M  IsConstantTimeAccessList( <obj> )
#M  IsSmallList( <obj> )
##
##  Lists in `IsGF2VectorRep' and `IsGF2MatrixRep' are (at least) as good
##  as lists in `IsInternalRep' w.r.t.~the above filters.
##
InstallTrueMethod( IsConstantTimeAccessList, IsList and IsGF2VectorRep );
InstallTrueMethod( IsSmallList, IsList and IsGF2VectorRep );

InstallTrueMethod( IsOrdinaryMatrix, IsMatrix and IsGF2MatrixRep );
InstallTrueMethod( IsConstantTimeAccessList, IsList and IsGF2MatrixRep );
InstallTrueMethod( IsSmallList, IsList and IsGF2MatrixRep );


#############################################################################
##
#V  TYPE_LIST_GF2MAT  . . . . . . . . . . . . .  type of mutable GF2 matrices
##
DeclareGlobalVariable(
    "TYPE_LIST_GF2MAT",
    "type of a packed GF2 matrix" );


#############################################################################
##
#V  TYPE_LIST_GF2MAT_IMM  . . . . . . . . . .  type of immutable GF2 matrices
##
DeclareGlobalVariable(
    "TYPE_LIST_GF2MAT_IMM",
    "type of a packed, immutable GF2 matrix" );


#############################################################################
##
#F  SET_LEN_GF2MAT( <list>, <len> ) . . . . .  set the length of a GF2 matrix
##
BIND_GLOBAL( "SET_LEN_GF2MAT", function( list, len )
    list![1] := len;
end );


#############################################################################
##
#F  ConvertToGF2MatrixRep( <matrix> ) . . . . . . . .  convert representation
##
BIND_GLOBAL( "ConvertToGF2MatrixRep", function(matrix)
    local   i;

    if not IsMutable(matrix)  then
        return;
    fi;

    #T 1997/11/3 fceller replace this by `CONV_PLIST'
    if not IsPlistRep(matrix)  then
        return;
    fi;

    # check that we can convert the entries
    for i  in [ 1 .. Length(matrix) ]  do
	if not IsGF2VectorRep(matrix[i])  then
	  ConvertToGF2VectorRep(matrix[i]);
        fi;
        if IsMutable(matrix[i]) then
	  matrix[i]:=Immutable(matrix[i]);
        fi;
    od;

    # put length at position 1
    for i  in [ Length(matrix), Length(matrix)-1 .. 1 ]  do
        matrix[i+1] := matrix[i];
    od;
    matrix[1] := Length(matrix)-1;

    # and convert
    Objectify( TYPE_LIST_GF2MAT, matrix );

end );


#############################################################################
##
#F  ImmutableGF2MatrixRep( <matrix> ) . . . . . . . .  convert representation
##
BIND_GLOBAL( "ImmutableGF2MatrixRep", function(matrix)
    local   new,  i,  row;

    # put length at position 1
    new := [ Length(matrix) ];
    for i  in matrix  do
        row := ImmutableGF2VectorRep(i);
        if row = fail  then
            return fail;
        fi;
        Add( new, row );
    od;

    # convert
    Objectify( TYPE_LIST_GF2MAT_IMM, new );

    # and return new matrix
    return new;

end );


#############################################################################
##
#F  ImmutableMatrix( <field>, <matrix> ) . convert into "best" representation
##
BIND_GLOBAL( "ImmutableMatrix", function( field, matrix )

    # matrix over GF2
    if IsFinite(field) and Size(field) = 2  then
        return ImmutableGF2MatrixRep(matrix);

    # everything else
    else
        return Immutable(matrix);
    fi;
end );

#############################################################################
##
#F  PositionNonZero( <vec> ) . . . . . . . . Position of first non-zero entry
##

DeclareOperation("PositionNonZero", [IsRowVector]);
  

#############################################################################
##
#E
##
