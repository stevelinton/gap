#############################################################################
##
#W  ctblfuns.gi                 GAP library                     Thomas Breuer
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains generic methods for class functions.
##
##  1. class functions as lists
##  2. comparison and arithmetic operations for class functions
##  3. methods for class function specific operations
##  4. methods for auxiliary operations
##  5. vector spaces of class functions
##
Revision.ctblfuns_gi :=
    "@(#)$Id$";


#############################################################################
##
##  1. class functions as lists
##

#############################################################################
##
#M  \[\]( <psi>, <i> )
#M  Length( <psi> )
#M  IsBound\[\]( <psi>, <i> )
#M  Position( <psi>, <obj>, 0 )
##
##  Class functions shall behave as (immutable) lists,
##  we install methods for '\[\]', 'Length', 'IsBound\[\]', 'Position'.
##
InstallMethod( \[\],
    "for class function and positive integer",
    true,
    [ IsClassFunction, IsPosInt ], 0,
    function( chi, i )
    return ValuesOfClassFunction( chi )[i];
    end );

InstallMethod( Length,
    "for class function",
    true,
    [ IsClassFunction ], 0,
    chi -> Length( ValuesOfClassFunction( chi ) ) );

InstallMethod( IsBound\[\],
    "for class function and positive integer",
    true,
    [ IsClassFunction, IsPosInt ], 0,
    function( chi, i )
    return IsBound( ValuesOfClassFunction( chi )[i] );
    end );

InstallMethod( Position,
    "for class function, cyclotomic, and nonnegative integer",
    true,
    [ IsClassFunction, IsCyc, IsInt ], 0,
    function( chi, obj, pos )
    return Position( ValuesOfClassFunction( chi ), obj, pos );
    end );


#############################################################################
##
#M  ValuesOfClassFunction( <list> )
##
##  In order to treat lists as class functions where this makes sense,
##  we define that `ValuesOfClassFunction' returns the list <list> itself.
##
InstallOtherMethod( ValuesOfClassFunction,
    "for a list of cyclotomics",
    true,
    [ IsCyclotomicCollection and IsList ], 0,
    IdFunc );


#############################################################################
##
##  2. comparison and arithmetic operations for class functions
##

#############################################################################
##
#M  \=( <chi>, <psi> )  . . . . . . . . . . . . . equality of class functions
##
##  Two class functions in the same family belong necessarily to the same
##  (identical) character table.
##  If the families differ then we can compare the class functions only
##  if the underlying groups are known, namely we check whether the groups
##  are equal, and if yes then we take the conjugacy classes and compare the
##  values.
##
InstallMethod( \=,
    "for two class functions (same family)",
    IsIdenticalObj,
    [ IsClassFunction, IsClassFunction ], 0,
    function( chi, psi )
    return ValuesOfClassFunction( chi ) = ValuesOfClassFunction( psi );
    end );

InstallMethod( \=,
    "for two class functions (nonidentical families)",
    IsNotIdenticalObj,
    [ IsClassFunction, IsClassFunction ], 0,
    function( chi, psi )
    if    not HasUnderlyingGroup( UnderlyingCharacterTable( chi ) )
       or not HasUnderlyingGroup( UnderlyingCharacterTable( psi ) ) then
      Error( "cannot compare class functions <chi> and <psi>" );
#T try degree or length or so?
    elif UnderlyingGroup( chi ) <> UnderlyingGroup( psi ) then
      return false;
    else
      return ForAll( ConjugacyClasses( UnderlyingGroup( chi ) ),
                     C -> C^chi = C^psi );
    fi;
    end );


#############################################################################
##
#M  \<( <chi>, <psi> )  . . . . . . . . . . . . comparison of class functions
##
InstallMethod( \<,
    "for two class functions",
    IsIdenticalObj,
    [ IsClassFunction, IsClassFunction ], 0,
    function( chi, psi )
    return ValuesOfClassFunction( chi ) < ValuesOfClassFunction( psi );
    end );


#############################################################################
##
#M  \+( <chi>, <psi> )  . . . . . . . . . . . . . . .  sum of class functions
##
InstallMethod( \+,
    "for two class functions",
    IsIdenticalObj,
    [ IsClassFunction, IsClassFunction ], 0,
    function( chi, psi )
    return ClassFunctionByValues( UnderlyingCharacterTable( chi ),
               ValuesOfClassFunction( chi ) + ValuesOfClassFunction( psi ) );
    end );

InstallMethod( \+,
    "for two virtual characters",
    IsIdenticalObj,
    [ IsClassFunction and IsVirtualCharacter,
      IsClassFunction and IsVirtualCharacter ], 0,
    function( chi, psi )
    return VirtualCharacterByValues( UnderlyingCharacterTable( chi ),
               ValuesOfClassFunction( chi ) + ValuesOfClassFunction( psi ) );
    end );

InstallMethod( \+,
    "for two characters",
    IsIdenticalObj,
    [ IsClassFunction and IsCharacter,
      IsClassFunction and IsCharacter ], 0,
    function( chi, psi )
    return CharacterByValues( UnderlyingCharacterTable( chi ),
               ValuesOfClassFunction( chi ) + ValuesOfClassFunction( psi ) );
    end );


#############################################################################
##
#M  AdditiveInverseOp( <psi> )  . . . . . . . . . . . .  for a class function
##
##  The additive inverse of a virtual character is again a virtual character,
##  but the additive inverse of a character is not a character,
##  so  we cannot use `ClassFunctionSameType'.
##
InstallMethod( AdditiveInverseOp,
    "for a class function",
    true,
    [ IsClassFunction ], 0,
    psi -> ClassFunctionByValues( UnderlyingCharacterTable( psi ),
               AdditiveInverse( ValuesOfClassFunction( psi ) ) ) );


InstallMethod( AdditiveInverseOp,
    "for a virtual character",
    true,
    [ IsClassFunction and IsVirtualCharacter ], 0,
    psi -> VirtualCharacterByValues( UnderlyingCharacterTable( psi ),
               AdditiveInverse( ValuesOfClassFunction( psi ) ) ) );


#############################################################################
##
#M  ZeroOp( <psi> ) . . . . . . . . . . . . . . . . . .  for a class function
##
InstallMethod( ZeroOp,
    "for a class function",
    true,
    [ IsClassFunction ], 0,
    psi -> VirtualCharacterByValues( UnderlyingCharacterTable( psi ),
               Zero( ValuesOfClassFunction( psi ) ) ) );


#############################################################################
##
#M  \-( <chi>, <psi> )  . . . . . . . . . . . . difference of class functions
##
InstallMethod( \-,
    "for two class functions",
    IsIdenticalObj,
    [ IsClassFunction, IsClassFunction ], 0,
    function( chi, psi )
    return ClassFunctionByValues( UnderlyingCharacterTable( chi ),
               ValuesOfClassFunction( chi ) - ValuesOfClassFunction( psi ) );
    end );

InstallMethod( \-,
    "for two virtual characters",
    IsIdenticalObj,
    [ IsVirtualCharacter, IsVirtualCharacter ], 0,
    function( chi, psi )
    return VirtualCharacterByValues( UnderlyingCharacterTable( chi ),
               ValuesOfClassFunction( chi ) - ValuesOfClassFunction( psi ) );
    end );


#############################################################################
##
#M  \*( <cyc>, <psi> )  . . . . . . . . . . scalar multiple of class function
##
InstallMethod( \*,
    "for a cyclotomic and a class function",
    true,
    [ IsCyc, IsClassFunction ], 0,
    function( cyc, chi )
    return ClassFunctionByValues( UnderlyingCharacterTable( chi ),
               cyc * ValuesOfClassFunction( chi ) );
    end );

InstallMethod( \*,
    "for an integer and a virtual character",
    true,
    [ IsInt, IsVirtualCharacter ], 0,
    function( cyc, chi )
    return VirtualCharacterByValues( UnderlyingCharacterTable( chi ),
               cyc * ValuesOfClassFunction( chi ) );
    end );

InstallMethod( \*,
    "for a positive integer and a character",
    true,
    [ IsPosInt, IsCharacter ], 0,
    function( cyc, chi )
    return CharacterByValues( UnderlyingCharacterTable( chi ),
               cyc * ValuesOfClassFunction( chi ) );
    end );


#############################################################################
##
#M  \*( <psi>, <cyc> )  . . . . . . . . . . scalar multiple of class function
##
InstallMethod( \*,
    "for class function and cyclotomic",
    true,
    [ IsClassFunction, IsCyc ], 0,
    function( chi, cyc )
    return ClassFunctionByValues( UnderlyingCharacterTable( chi ),
               ValuesOfClassFunction( chi ) * cyc );
    end );

InstallMethod( \*,
    "for virtual character and integer",
    true,
    [ IsVirtualCharacter, IsInt ], 0,
    function( chi, cyc )
    return VirtualCharacterByValues( UnderlyingCharacterTable( chi ),
               ValuesOfClassFunction( chi ) * cyc );
    end );

InstallMethod( \*,
    "for character and positive integer",
    true,
    [ IsCharacter, IsPosInt ], 0,
    function( chi, cyc )
    return CharacterByValues( UnderlyingCharacterTable( chi ),
               ValuesOfClassFunction( chi ) * cyc );
    end );


#############################################################################
##
#M  \/( <chi>, <cyc> )  . . . . . . . . . . . . . . .  divide by a cyclotomic
##
InstallMethod( \/,
    "for class function and cyclotomic",
    true,
    [ IsClassFunction, IsCyc ], 0,
    function( chi, n )
    return ClassFunctionByValues( UnderlyingCharacterTable( chi ),
               ValuesOfClassFunction( chi ) / n );
    end );


#############################################################################
##
#M  OneOp( <psi> )  . . . . . . . . . . . . . . . . . .  for a class function
##
InstallMethod( OneOp,
    "for class function",
    true,
    [ IsClassFunction ], 0,
    psi -> TrivialCharacter( UnderlyingCharacterTable( psi ) ) );


#############################################################################
##
#M  \*( <chi>, <cyc> )  . . . . . . . . . . tensor product of class functions
##
InstallMethod( \*,
    "for two class functions",
    IsIdenticalObj,
    [ IsClassFunction, IsClassFunction ], 0,
    function( chi, psi )
    local valschi, valspsi;
    valschi:= ValuesOfClassFunction( chi );
    valspsi:= ValuesOfClassFunction( psi );
    return ClassFunctionByValues( UnderlyingCharacterTable( chi ),
               List( [ 1 .. Length( valschi ) ],
                     x -> valschi[x] * valspsi[x] ) );
    end );

InstallMethod( \*,
    "for two virtual characters",
    IsIdenticalObj,
    [ IsVirtualCharacter, IsVirtualCharacter ], 0,
    function( chi, psi )
    local valschi, valspsi;
    valschi:= ValuesOfClassFunction( chi );
    valspsi:= ValuesOfClassFunction( psi );
    return VirtualCharacterByValues( UnderlyingCharacterTable( chi ),
               List( [ 1 .. Length( valschi ) ],
                     x -> valschi[x] * valspsi[x] ) );
    end );

InstallMethod( \*,
    "for two characters",
    IsIdenticalObj,
    [ IsCharacter, IsCharacter ], 0,
    function( chi, psi )
    local valschi, valspsi;
    valschi:= ValuesOfClassFunction( chi );
    valspsi:= ValuesOfClassFunction( psi );
    return CharacterByValues( UnderlyingCharacterTable( chi ),
               List( [ 1 .. Length( valschi ) ],
                     x -> valschi[x] * valspsi[x] ) );
    end );


#############################################################################
##
#M  Order( <chi> )  . . . . . . . . . . . . . . . . . . . determinantal order
##
##  Note that we are not allowed to regard the determinantal order of any
##  (virtual) character as order, since nonlinear characters do not have an
##  order as mult. elements.
##
InstallOtherMethod( Order,
    true,
    [ IsCharacter ], 0,
    function( chi )
    local order, values;
    if DegreeOfCharacter( chi ) <> 1 then
      Error( "nonlinear character <chi> has no order" );
    fi;
    values:= ValuesOfClassFunction( chi );
    order:= Lcm( values, Conductor );
    if order mod 2 = 1 and -1 in values then
      order:= 2*order;
    fi;
    return order;
    end );


#############################################################################
##
#M  \^( <chi>, <n> )  . . . . . . . . . . for class function and pos. integer
##
InstallOtherMethod( \^,
    "for class function and positive integer",
    true,
    [ IsClassFunction, IsPosInt ], 0,
    function( chi, n )
    return ClassFunctionSameType( UnderlyingCharacterTable( chi ),
               chi,
               List( ValuesOfClassFunction( chi ), x -> x ^ n ) );
    end );


#############################################################################
##
#M  \^( <chi>, <g> )  . . . . .  conjugate class function under action of <g>
##
InstallMethod( \^,
    "for class function with group, and group element",
    true,
    [ IsClassFunctionWithGroup, IsMultiplicativeElementWithInverse ], 0,
    function( chi, g )
    return ClassFunctionSameType( UnderlyingCharacterTable( chi ), chi,
               Permuted( ValuesOfClassFunction( chi ),
                         CorrespondingPermutations( chi, [ g ] )[1] ) );
    end );


#############################################################################
##
#M  \^( <chi>, <G> )  . . . . . . . . . . . . . . . .  induced class function
#M  \^( <chi>, <tbl> )  . . . . . . . . . . . . . . .  induced class function
##
InstallOtherMethod( \^,
    "for class function with group, and group",
    true,
    [ IsClassFunctionWithGroup, IsGroup ], 0,
    InducedClassFunction );

InstallOtherMethod( \^,
    "for class function and nearly character table",
    true,
    [ IsClassFunction, IsNearlyCharacterTable ], 0,
    InducedClassFunction );


#############################################################################
##
#M  \^( <chi>, <galaut> ) . . . Galois automorphism <galaut> applied to <chi>
##
InstallOtherMethod( \^,
    "for class function and Galois automorphism",
    true,
    [ IsClassFunction, IsGeneralMapping and IsANFAutomorphismRep ], 0,
    function( chi, galaut )
    galaut:= galaut!.galois;
    return ClassFunctionSameType( UnderlyingCharacterTable( chi ), chi,
               List( ValuesOfClassFunction( chi ),
                     x -> GaloisCyc( x, galaut ) ) );
    end );


#############################################################################
##
#M  \^( <g>, <chi> )  . . . . . . . . . . value of <chi> on group element <g>
##
InstallOtherMethod( \^,
    true,
    [ IsMultiplicativeElementWithInverse, IsClassFunctionWithGroup ], 0,
    function( g, chi )
    local ccl, i;
    if g in UnderlyingGroup( chi ) then
      ccl:= ConjugacyClasses( UnderlyingGroup( chi ) );
      for i in [ 1 .. Length( ccl ) ] do
        if g in ccl[i] then
          return ValuesOfClassFunction( chi )[i];
        fi;
      od;
    else
      Error( "<g> must lie in the underlying group of <chi>" );
    fi;
    end );


#############################################################################
##
#M  \^( <psi>, <chi> )  . . . . . . . . . .  conjugation of linear characters
##
InstallOtherMethod( \^,
    "for two class functions (conjugation)",
    IsIdenticalObj,
    [ IsClassFunction, IsClassFunction ], 0,
    function( chi, psi )
    return chi;
    end );


#############################################################################
##
#M  InverseOp( <chi> )  . . . . . . . . . . . . . . . .  for a class function
##
InstallOtherMethod( InverseOp,
    "for a class function",
    true,
    [ IsClassFunction ], 0,
    function( chi )
    local values;
    values:= List( ValuesOfClassFunction( chi ), Inverse );
    if fail in values then
      return fail;
    else
      return ClassFunctionByValues( UnderlyingCharacterTable(chi), values );
    fi;
    end );


#############################################################################
##
##  3. methods for class function specific operations
##

#############################################################################
##
#M  ClassFunctionFamily( <tbl> )
##
InstallMethod( ClassFunctionFamily,
    "for a nearly character table",
    true,
    [ IsNearlyCharacterTable ], 0,
    function( tbl )

    local Fam;      # the family, result

    # Make the family.
    if HasUnderlyingGroup( tbl ) then
      Fam:= NewFamily( "Class functions family", IsClassFunctionWithGroup );
    else
      Fam:= NewFamily( "Class functions family", IsClassFunction );
    fi;

    Fam!.char:= UnderlyingCharacteristic( tbl );
    Fam!.underlyingCharacterTable:= tbl;

    SetCharacteristic( Fam, 0 );

    return Fam;
    end );


#############################################################################
##
#M  One( <Fam> )  . . . . . . . . . . . . . . for a family of class functions
##
InstallOtherMethod( One,
    "for a family of class functions",
    true,
    [ IsClassFunctionFamily ], 0,
    Fam -> TrivialCharacter( Fam!.underlyingCharacterTable ) );


#############################################################################
##
#M  Zero( <Fam> ) . . . . . . . . . . . . . . for a family of class functions
##
InstallOtherMethod( Zero,
    "for a family of class functions",
    true,
    [ IsClassFunctionFamily ], 0,
    Fam -> Zero( One( Fam ) ) );


#############################################################################
##
#M  UnderlyingCharacterTable( <psi> ) . . . . . . . . .  for a class function
##
InstallMethod( UnderlyingCharacterTable,
    "for a class function",
    true,
    [ IsClassFunction ], 0,
    psi -> FamilyObj( psi )!.underlyingCharacterTable );


#############################################################################
##
#M  UnderlyingCharacteristic( <psi> ) . . . . . . . . .  for a class function
##
InstallOtherMethod( UnderlyingCharacteristic,
    "for a class function",
    true,
    [ IsClassFunction ], 0,
    psi -> FamilyObj( psi )!.char );


#############################################################################
##
#M  UnderlyingGroup( <psi> )  . . . . . . . . . . . . .  for a class function
##
InstallOtherMethod( UnderlyingGroup,
    "for a class function",
    true,
    [ IsClassFunction ], 0,
    psi -> UnderlyingGroup( FamilyObj( psi )!.underlyingCharacterTable ) );


#############################################################################
##
#M  PrintObj( <psi> ) . . . . . . . . . . . . . . . .  print a class function
##
InstallMethod( PrintObj,
    "for a class function",
    true,
    [ IsClassFunction ], 0,
    function( psi )
    Print( "ClassFunction( ", UnderlyingCharacterTable( psi ),
           ", ", ValuesOfClassFunction( psi ), " )" );
    end );

InstallMethod( PrintObj,
    "for a class function with group",
    true,
    [ IsClassFunctionWithGroup ], 0,
    function( psi )
    Print( "ClassFunction( ", UnderlyingGroup( psi ),
           ", ", ValuesOfClassFunction( psi ) );
    if UnderlyingCharacteristic( psi ) <> 0 then
      Print( ", ", UnderlyingCharacteristic( psi ) );
    fi;
    Print( " )" );
    end );

InstallMethod( PrintObj,
    "for a virtual character",
    true,
    [ IsClassFunction and IsVirtualCharacter ], 0,
    function( psi )
    Print( "VirtualCharacter( ", UnderlyingCharacterTable( psi ),
           ", ", ValuesOfClassFunction( psi ), " )" );
    end );

InstallMethod( PrintObj,
    "for a virtual character with group",
    true,
    [ IsVirtualCharacter and IsClassFunctionWithGroup ], 0,
    function( psi )
    Print( "VirtualCharacter( ", UnderlyingGroup( psi ),
           ", ", ValuesOfClassFunction( psi ) );
    if UnderlyingCharacteristic( psi ) <> 0 then
      Print( ", ", UnderlyingCharacteristic( psi ) );
    fi;
    Print( " )" );
    end );

InstallMethod( PrintObj,
    "for a character",
    true,
    [ IsClassFunction and IsCharacter ], 0,
    function( psi )
    Print( "Character( ", UnderlyingCharacterTable( psi ),
           ", ", ValuesOfClassFunction( psi ), " )" );
    end );

InstallMethod( PrintObj,
    "for a character with group",
    true,
    [ IsClassFunctionWithGroup and IsCharacter ], 0,
    function( psi )
    Print( "Character( ", UnderlyingGroup( psi ),
           ", ", ValuesOfClassFunction( psi ) );
    if UnderlyingCharacteristic( psi ) <> 0 then
      Print( ", ", UnderlyingCharacteristic( psi ) );
    fi;
    Print( " )" );
    end );


#############################################################################
##
#M  ViewObj( <psi> )  . . . . . . . . . . . . . . . . . view a class function
##
##  Note that class functions are finite lists, so the default `ViewObj'
##  method for finite lists should be avoided.
##
InstallMethod( ViewObj,
    "for a class function",
    true,
    [ IsClassFunction ], 0,
    function( psi )
    Print( "ClassFunction( " );
    View( UnderlyingCharacterTable( psi ) );
    Print( ", " );
    View( ValuesOfClassFunction( psi ) );
    Print( " )" );
    end );

InstallMethod( ViewObj,
    "for a class function with group",
    true,
    [ IsClassFunctionWithGroup ], 0,
    function( psi )
    Print( "ClassFunction( " );
    View( UnderlyingGroup( psi ) );
    Print( ", " );
    View( ValuesOfClassFunction( psi ) );
    if UnderlyingCharacteristic( psi ) <> 0 then
      Print( ", ", UnderlyingCharacteristic( psi ) );
    fi;
    Print( " )" );
    end );

InstallMethod( ViewObj,
    "for a virtual character",
    true,
    [ IsClassFunction and IsVirtualCharacter ], 0,
    function( psi )
    Print( "VirtualCharacter( " );
    View( UnderlyingCharacterTable( psi ) );
    Print( ", " );
    View( ValuesOfClassFunction( psi ) );
    Print( " )" );
    end );

InstallMethod( ViewObj,
    "for a virtual character with group",
    true,
    [ IsVirtualCharacter and IsClassFunctionWithGroup ], 0,
    function( psi )
    Print( "VirtualCharacter( " );
    View( UnderlyingGroup( psi ) );
    Print( ", " );
    View( ValuesOfClassFunction( psi ) );
    if UnderlyingCharacteristic( psi ) <> 0 then
      Print( ", ", UnderlyingCharacteristic( psi ) );
    fi;
    Print( " )" );
    end );

InstallMethod( ViewObj,
    "for a character",
    true,
    [ IsClassFunction and IsCharacter ], 0,
    function( psi )
    Print( "Character( " );
    View( UnderlyingCharacterTable( psi ) );
    Print( ", " );
    View( ValuesOfClassFunction( psi ) );
    Print( " )" );
    end );

InstallMethod( ViewObj,
    "for a character with group",
    true,
    [ IsClassFunctionWithGroup and IsCharacter ], 0,
    function( psi )
    Print( "Character( " );
    View( UnderlyingGroup( psi ) );
    Print( ", " );
    View( ValuesOfClassFunction( psi ) );
    if UnderlyingCharacteristic( psi ) <> 0 then
      Print( ", ", UnderlyingCharacteristic( psi ) );
    fi;
    Print( " )" );
    end );


#############################################################################
##
#M  Display( <chi> )  . . . . . . . . . . . . . . .  display a class function
#M  Display( <chi>, <arec> )
##
InstallOtherMethod( Display,
    "for a class function",
    true,
    [ IsClassFunction ], 0,
    function( chi )
    Display( UnderlyingCharacterTable( chi ), rec( chars:= [ chi ] ) );
    end );

InstallOtherMethod( Display,
    "for a class function, and a record",
    true,
    [ IsClassFunction, IsRecord ], 0,
    function( chi, arec )
    arec:= ShallowCopy( arec );
    arec.chars:= [ chi ];
    Display( UnderlyingCharacterTable( chi ), arec );
    end );


#############################################################################
##
#M  IsVirtualCharacter( <chi> ) . . . . . . . . . . . .  for a class function
##
InstallMethod( IsVirtualCharacter,
    "for a class function",
    true,
    [ IsClassFunction ], 0,
    function( chi )

    local irr,
          psi,
          scpr;

    irr:= Irr( UnderlyingCharacterTable( chi ) );
    for psi in irr do
      scpr:= ScalarProduct( chi, psi );
      if not IsInt( scpr ) then
        return false;
      fi;
#T use NonnegIntScprs!!
    od;
    return true;
    end );


#############################################################################
##
#M  IsCharacter( <obj> )  . . . . . . . . . . . . . . for a virtual character
##
InstallMethod( IsCharacter,
    "for a virtual character",
    true,
    [ IsClassFunction and IsVirtualCharacter ], 0,
    function( obj )

    local chi;

    # Proper characters have positive degree.
    if ValuesOfClassFunction( obj )[1] <= 0 then
      return false;
    fi;

    # Check the scalar products with all irreducibles.
    for chi in Irr( UnderlyingCharacterTable( obj ) ) do
      if ScalarProduct( chi, obj ) < 0 then
        return false;
      fi;
    od;
#T use NonnegIntScprs!
    return true;
    end );

InstallMethod( IsCharacter,
    "for a class function",
    true,
    [ IsClassFunction ], 0,
    function( obj )

    local irr,
          chi,
          scpr,
          foundneg;

    if HasIsVirtualCharacter( obj ) and not IsVirtualCharacter( obj ) then
      return false;
    fi;
#T can disappear when inverse implications are supported!

    # check also for virtual character
    foundneg:= false;
    for chi in Irr( UnderlyingCharacterTable( obj ) ) do
      scpr:= ScalarProduct( chi, obj );
      if not IsInt( scpr ) then
        SetIsVirtualCharacter( obj, false );
        return false;
      elif scpr < 0 then
        return false;
      fi;
    od;
    return true;
    end );


#############################################################################
##
#M  IsIrreducibleCharacter( <chi> )   . . . . . . . . .  for a class function
##
InstallMethod( IsIrreducibleCharacter,
    "for a class function",
    true,
    [ IsClassFunction ], 0,
    chi -> IsCharacter( chi ) and ScalarProduct( chi, chi ) = 1 );


#############################################################################
##
#M  CentreOfCharacter( <chi> )  . . . . . . . . . . . . centre of a character
##
InstallMethod( CentreOfCharacter,
    "for a character with group",
    true,
    [ IsClassFunctionWithGroup and IsCharacter ], 0,
    chi -> NormalSubgroupClasses( UnderlyingCharacterTable( chi ),
                                  CentreChar( chi ) ) );


#############################################################################
##
#M  CentreChar( <chi> )  . . . . . . . . classes in the centre of a character
##
InstallMethod( CentreChar,
    "for a character",
    true,
    [ IsClassFunction and IsCharacter ], 0,
    chi -> CentreChar( ValuesOfClassFunction( chi ) ) );

InstallOtherMethod( CentreChar,
    "for a homogeneous list of cyclotomics",
    true,
    [ IsHomogeneousList and IsCyclotomicCollection ], 0,
    char -> Filtered( [ 1 .. Length( char ) ],
                     i -> char[i] = char[1] or
                          char[i] = - char[1] or
                          IsCyc( char[i] ) and ForAny( COEFFS_CYC( char[i] ),
                                            x -> AbsInt( x ) = char[1] ) ) );


#############################################################################
##
#M  ConstituentsOfCharacter( <chi> )  . . . . .  irred. constituents of <chi>
##
InstallMethod( ConstituentsOfCharacter,
    true,
    [ IsClassFunction ], 0,
    function( chi )

    local irr,    # irreducible characters of underlying table of 'chi'
          const,  # list of constituents, result
          proper, # is 'chi' a proper character
          i,      # loop over 'irr'
          scpr;   # one scalar product

    const:= [];
    proper:= true;
    for i in Irr( UnderlyingCharacterTable( chi ) ) do
      scpr:= ScalarProduct( chi, i );
      if scpr <> 0 then
        Add( const, i );
        proper:= proper and IsInt( scpr ) and ( 0 < scpr );
      fi;
    od;

    # In the case 'proper = true' we know that 'chi' is a character.
    if proper then
      SetIsCharacter( chi, true );
    fi;

    return Set( const );
    end );

InstallMethod( ConstituentsOfCharacter,
    "for a character",
    true,
    [ IsClassFunction and IsCharacter ], 0,
    function( chi )

    local irr,    # irreducible characters of underlying table of 'chi'
          values, # character values
          deg,    # degree of 'chi'
          const,  # list of constituents, result
          i,      # loop over 'irr'
          irrdeg, # degree of an irred. character
          scpr;   # one scalar product

    irr:= Irr( UnderlyingCharacterTable( chi ) );
    values:= ValuesOfClassFunction( chi );
    deg:= values[1];
    const:= [];
    i:= 1;
    while 0 < deg and i <= Length( irr ) do
      irrdeg:= DegreeOfCharacter( irr[i] );
      if irrdeg <= deg then
        scpr:= ScalarProduct( chi, irr[i] );
        if scpr <> 0 then
          deg:= deg - scpr * irrdeg;
          Add( const, irr[i] );
        fi;
      fi;
      i:= i+1;
    od;

    return Set( const );
    end );


#############################################################################
##
#M  DegreeOfCharacter( <chi> )  . . . . . . . . . . . . . . . for a character
##
InstallMethod( DegreeOfCharacter,
    "for a character",
    true,
    [ IsClassFunction and IsCharacter ], 0,
    chi -> ValuesOfClassFunction( chi )[1] );


#############################################################################
##
#M  KernelOfCharacter( <chi> )  . . . . . . . . . . . . . . . for a character
##
InstallMethod( KernelOfCharacter,
    "for a character with group",
    true,
    [ IsClassFunctionWithGroup and IsCharacter ], 0,
    chi -> NormalSubgroupClasses( UnderlyingCharacterTable( chi ),
               KernelChar( ValuesOfClassFunction( chi ) ) ) );


#############################################################################
##
#M  KernelChar( <char> ) . . . . . . .  the set of classes forming the kernel
##
InstallMethod( KernelChar,
    "for a character",
    true,
    [ IsClassFunction and IsCharacter ], 0,
    chi -> KernelChar( ValuesOfClassFunction( chi ) ) );

InstallOtherMethod( KernelChar,
    "for a homogeneous list of cyclotomics",
    true,
    [ IsHomogeneousList and IsCyclotomicCollection], 0,
    function( char )
    local degree;
    degree:= char[1];
    return Filtered( [ 1 .. Length( char ) ], x -> char[x] = degree );
    end );


#############################################################################
##
#M  TrivialCharacter( <G> ) . . . . . . . . . . . . . . . . . . . for a group
##
InstallOtherMethod( TrivialCharacter,
    "for a group (delegate to the table)",
    true,
    [ IsGroup ], 0,
    G -> TrivialCharacter( OrdinaryCharacterTable( G ) ) );


#############################################################################
##
#M  TrivialCharacter( <tbl> ) . . . . . . . . . . . . . for a character table
##
InstallMethod( TrivialCharacter,
    "for a character table",
    true,
    [ IsNearlyCharacterTable ], 0,
    tbl -> CharacterByValues( tbl, List( [ 1 .. NrConjugacyClasses( tbl ) ],
                                         x -> 1 ) ) );


#############################################################################
##
#M  NaturalCharacter( <G> ) . . . . . . . . . . . . . for a permutation group
##
InstallMethod( NaturalCharacter,
    "for a permutation group",
    true,
    [ IsGroup and IsPermCollection ], 0,
    function( G )
    local deg, tbl;
    deg:= NrMovedPoints( G );
    tbl:= OrdinaryCharacterTable( G );
    return CharacterByValues( tbl,
               List( ConjugacyClasses( tbl ),
               C -> deg - NrMovedPointsPerm( Representative( C ) ) ) );
    end );


#############################################################################
##
#M  NaturalCharacter( <G> ) . . . . for a matrix group in characteristic zero
##
InstallMethod( NaturalCharacter,
    "for a matrix group in characteristic zero",
    true,
    [ IsGroup and IsRingElementCollCollColl ], 0,
    function( G )
    local tbl;
    if Characteristic( G ) = 0 then
      tbl:= OrdinaryCharacterTable( G );
      return CharacterByValues( tbl,
                 List( ConjugacyClasses( tbl ),
                       C -> TraceMat( Representative( C ) ) ) );
    else
      TryNextMethod();
    fi;
    end );


#############################################################################
##
#M  PermutationCharacter( <G>, <U> )  . . . . . . . . . . . .  for two groups
##
InstallMethod( PermutationCharacter,
    "for two groups (use double cosets)",
    IsIdenticalObj,
    [ IsGroup, IsGroup ], 0,
    function( G, U )
    local tbl, C, c, s, i;

    tbl:= OrdinaryCharacterTable( G );
    C := ConjugacyClasses( tbl );
    c := [ Index( G, U ) ];
    s := Size( U );

    for i  in [ 2 .. Length(C) ]  do
      c[i]:= Number( DoubleCosets( G, U,
                         SubgroupNC( G, [ Representative( C[i] ) ] ) ),
                     x -> Size( x ) = s );
    od;

    # Return the character.
    return CharacterByValues( tbl, c );
    end );


#############################################################################
##
#M  PermutationCharacter( <G> )  . . . . . . . . . . .  for group action
##
InstallOtherMethod( PermutationCharacter,
#T matches declaration? (installed for right operation at all?)
    "group action on domain",
    true,
    [ IsPermGroup, IsListOrCollection, IsFunction ], 0,
    function( G, dom, opr )
    local tbl;
    tbl:= OrdinaryCharacterTable( G );
    return CharacterByValues( tbl, List( ConjugacyClasses( tbl ),
	       i -> Number( dom, j -> j = opr( j, Representative(i) ) ) ) );
    end);


#T #############################################################################
#T ##
#T #M  PermutationCharacter( <G>, <U> )  . . . . . . . . .  for two small groups
#T ##
#T InstallMethod( PermutationCharacter,
#T     "for two small groups",
#T     IsIdenticalObj,
#T     [ IsGroup and IsSmallGroup, IsGroup and IsSmallGroup ], 0,
#T     function( G, U )
#T     local E, I, tbl;
#T 
#T     E := AsList( U );
#T     I := Size( G ) / Length( E );
#T     tbl:= OrdinaryCharacterTable( G );
#T     return CharacterByValues( tbl,
#T         List( ConjugacyClasses( tbl ),
#T         C -> I * Length( Intersection2( AsList( C ), E ) ) / Size( C ) ) );
#T     end );


#############################################################################
##
#F  CycleStructureClass( <permchar>, <class> )
##
InstallGlobalFunction( CycleStructureClass, function( permchar, class )

    local tbl,         # underlying character table
          n,           # element order of `class'
          divs,        # divisors of `n'
          i, d, j,     # loop over `divs'
          fixed,       # numbers of fixed points
          cycstruct;   # cycle structure, result

    # Check the arguments.
    if not ( IsClassFunction( permchar ) and IsPosInt( class ) ) then
      Error( "<permchar> must be a class function, <class> a position" );
    fi;

    # Compute the numbers of fixed points of powers.
    tbl:= UnderlyingCharacterTable( permchar );
    permchar:= ValuesOfClassFunction(  permchar );
    n:= OrdersClassRepresentatives( tbl )[ class ];
    divs:= DivisorsInt( n );
    fixed:= [];
    for i in [ 1 .. Length( divs ) ] do

      # Compute the number of cycles of the element of order `n / d'.
      d:= divs[i];
      fixed[d]:= permchar[ PowerMap( tbl, d, class ) ];
      for j in [ 1 .. i-1 ] do
        if d mod divs[j] = 0 then

          # Subtract the number of fixed points with stabilizer exactly
          # of order `n / divs[j]'.
          fixed[d]:= fixed[d] - fixed[ divs[j] ];

        fi;
      od;

    od;

    # Convert these numbers into numbers of cycles.
    cycstruct:= [];
    for i in divs do
      if fixed[i] <> 0 and 1 < i then
        cycstruct[ i-1 ]:= fixed[i] / i;
      fi;
    od;

    # Return the cycle structure.
    return cycstruct;
end );


#############################################################################
##
#M  ClassFunctionByValues( <tbl>, <values> )
##
#T change this to return list objects!
##
InstallMethod( ClassFunctionByValues,
    "for nearly character table, and coll. of cyclotomics",
    true,
    [ IsNearlyCharacterTable, IsList and IsCyclotomicCollection ], 0,
    function( tbl, values )
    local chi;

    # Check the no. of classes if known.
    if     HasNrConjugacyClasses( tbl )
       and NrConjugacyClasses( tbl ) <> Length( values ) then
      Error( "no. of classes in <tbl> and <values> must be equal" );
    fi;

    chi:= Objectify( NewType( ClassFunctionFamily( tbl ),
                                  IsClassFunction
                              and IsAttributeStoringRep ),
                     rec() );

    SetValuesOfClassFunction( chi, values );
    return chi;
    end );

InstallMethod( ClassFunctionByValues,
    "for nearly character table with group, and coll. of cyclotomics",
    true,
    [ IsNearlyCharacterTable and HasUnderlyingGroup,
      IsList and IsCyclotomicCollection ], 0,
    function( tbl, values )
    local chi;

    # Check the no. of classes if known.
    if     HasNrConjugacyClasses( tbl )
       and NrConjugacyClasses( tbl ) <> Length( values ) then
      Error( "no. of classes in <tbl> and <values> must be equal" );
    fi;

    chi:= Objectify( NewType( ClassFunctionFamily( tbl ),
                                  IsClassFunctionWithGroup
                              and IsAttributeStoringRep ),
                     rec() );
    SetValuesOfClassFunction( chi, values );
    return chi;
    end );


#############################################################################
##
#M  VirtualCharacterByValues( <tbl>, <values> )
##
InstallMethod( VirtualCharacterByValues,
    "for nearly character table, and coll. of cyclotomics",
    true,
    [ IsNearlyCharacterTable, IsList and IsCyclotomicCollection ], 0,
    function( tbl, values )
    values:= ClassFunctionByValues( tbl, values );
    SetIsVirtualCharacter( values, true );
    return values;
    end );


#############################################################################
##
#M  CharacterByValues( <tbl>, <values> )
##
InstallMethod( CharacterByValues,
    "for nearly character table, and coll. of cyclotomics",
    true,
    [ IsNearlyCharacterTable, IsList and IsCyclotomicCollection ], 0,
    function( tbl, values )
    values:= ClassFunctionByValues( tbl, values );
    SetIsCharacter( values, true );
    return values;
    end );


#############################################################################
##
#F  ClassFunctionSameType( <tbl>, <chi>, <values> )
##
InstallGlobalFunction( ClassFunctionSameType,
    function( tbl, chi, values )
    if not IsClassFunction( chi ) then
      return values;
    elif HasIsCharacter( chi ) and IsCharacter( chi ) then
      return CharacterByValues( tbl, values );
    elif HasIsVirtualCharacter( chi ) and IsVirtualCharacter( chi ) then
      return VirtualCharacterByValues( tbl, values );
    else
      return ClassFunctionByValues( tbl, values );
    fi;
end );


#############################################################################
##
#M  Norm( <chi> )  . . . . . . . . . . . . . . . . . . norm of class function
##
InstallOtherMethod( Norm,
    "for a class function",
    true,
    [ IsClassFunction ], 0,
    chi -> ScalarProduct( chi, chi ) );


#############################################################################
##
#M  CentralCharacter( <chi> ) . . . . . . . . . . . . . . . . for a character
##
InstallMethod( CentralCharacter,
    "for a character",
    true,
    [ IsClassFunction and IsCharacter ], 0,
    chi -> ClassFunctionByValues( UnderlyingCharacterTable( chi ),
               CentralChar( UnderlyingCharacterTable( chi ),
                            ValuesOfClassFunction( chi ) ) ) );


#############################################################################
##
#M  CentralChar( <tbl>, <char> )
##
InstallMethod( CentralChar,
    "for a character table and a character",
    true,
    [ IsCharacterTable, IsClassFunction and IsCharacter ], 0,
    function( tbl, char )
    return CentralChar( tbl, ValuesOfClassFunction( char ) );
    end );

InstallOtherMethod( CentralChar,
    "for a nearly character table and a homogeneous list",
    true,
    [ IsNearlyCharacterTable, IsList and IsCyclotomicCollection ], 0,
    function( tbl, char )
    local classes;
    classes:= SizesConjugacyClasses( tbl );
    if Length( classes ) <> Length( char ) then
      Error( "<classes> and <char> must have same length" );
    fi;
    return List( [ 1 .. Length( char ) ],
                 x -> classes[x] * char[x] / char[1] );
    end );


##############################################################################
##
#M  DeterminantChar( <tbl>, <chi> )
##
##  The determinant is computed as follows.
##  Diagonalize the matrix; the determinant is the product of the diagonal
##  entries, which can be computed by 'Eigenvalues'.
##
##  Note that the determinant of a virtual character $\chi - \psi$ is
##  well-defined as the quotient of the determinants of the characters $\chi$
##  and $\psi$, since the determinant of a sum of characters is the product
##  of the determinants of the summands.
##  
InstallMethod( DeterminantChar,
    "for a nearly character table and a class function",
    true,
    [ IsNearlyCharacterTable, IsClassFunction and IsVirtualCharacter ], 0,
    function( tbl, chi )
    return DeterminantChar( tbl, ValuesOfClassFunction( chi ) );
    end );

InstallOtherMethod( DeterminantChar,
    "for a nearly character table and a homogeneous list",
    true,
    [ IsNearlyCharacterTable, IsList and IsCyclotomicCollection ], 0,
    function( tbl, chi )
    local det,      # result list
          ev,       # eigenvalues
          ord,      # one element order
          i;        # loop over classes

    if chi[1] = 1 then
      return ShallowCopy( chi );
    fi;

    det:= [];

    for i in [ 1 .. Length( chi ) ] do

      ev:= EigenvaluesChar( tbl, chi, i );
      ord:= Length( ev );

      # The determinant is 'E(ord)' to the 'exp'-th power,
      # where $'exp' = \sum_{j=1}^{ord} j 'ev'[j]$.
      # (Note that the $j$-th entry in 'ev' is the multiplicity of
      # 'E(ord)^j' as eigenvalue.)
      det[i]:= E(ord) ^ ( [ 1 .. ord ] * ev );

    od;

    return det;
    end );


##############################################################################
##
#M  DeterminantOfCharacter( <chi> ) . . . . . . . . .  for a virtual character
##
InstallOtherMethod( DeterminantOfCharacter,
    "for a virtual character",
    true,
    [ IsClassFunction and IsVirtualCharacter ], 0,
    chi -> CharacterByValues( UnderlyingCharacterTable( chi ),
               DeterminantChar( UnderlyingCharacterTable( chi ),
                                ValuesOfClassFunction( chi ) ) ) );


#############################################################################
##
#M  EigenvaluesChar( <tbl>, <char>, <class> )
##
InstallMethod( EigenvaluesChar,
    "for a nearly character table, a class function, and a pos.",
    true,
    [ IsNearlyCharacterTable, IsClassFunction and IsCharacter,
      IsPosInt ], 0,
    function( tbl, chi, class )
    return EigenvaluesChar( tbl, ValuesOfClassFunction( chi ), class );
    end );

InstallOtherMethod( EigenvaluesChar,
    "for a nearly character table and a hom. list, and a pos.",
    true,
    [ IsNearlyCharacterTable, IsList and IsCyclotomicCollection,
      IsPosInt ], 0,
    function( tbl, char, class )

    local i, j, n, powers, eigen, e, val;

    n:= OrdersClassRepresentatives( tbl )[ class ];
    if n = 1 then return [ char[ class ] ]; fi;

    # Compute necessary power maps and the restricted character.
    powers:= [];
    powers[n]:= char[1];
    for i in [ 1 .. n-1 ] do
      if not IsBound( powers[i] ) then

        # necessarily 'i' divides 'n', since 'i/Gcd(n,i)' is invertible
        # mod 'n', and thus powering with 'i' is Galois conjugate to
        # powering with 'Gcd(n,i)'
        powers[i]:= char[ PowerMap( tbl, i, class ) ];
#T better approach:
#T only write down values for one representative of each
#T Galois family, and compute traces;
#T for rational characters, this avoids computation with
#T non-rational values at all.
#T (how much does this help?)
        for j in PrimeResidues( n/i ) do

          # Note that the position cannot be 0.
          powers[ ( i*j ) mod n ]:= GaloisCyc( powers[i], j );
        od;
      fi;
    od;

    # compute the scalar products of the characters given by 'E(n)->E(n)^i'
    # with the restriction of <char> to the cyclic group generated by
    # <class>
    eigen:= [];
    for i in [ 1 .. n ] do
      e:= E(n)^(-i);
      val:= 0;
      for j in [ 1 .. n ] do val:= val + e^j * powers[j]; od;
      eigen[i]:= val / n;
    od;

    return eigen;
    end );


#############################################################################
##
#M  EigenvaluesChar( <chi>, <class> )
##
InstallOtherMethod( EigenvaluesChar,
    "for a character and a positive integer",
    true,
    [ IsClassFunction, IsPosInt ], 0,
    function( chi, class )
    if IsCharacter( chi ) then
      return EigenvaluesChar( UnderlyingCharacterTable( chi ),
                              ValuesOfClassFunction( chi ), class );
    else
      Error( "<chi> must be a character" );
    fi;
    end );


#############################################################################
##
#M  ScalarProduct( <chi>, <psi> ) . . . . . . . . . . for two class functions
##
InstallMethod( ScalarProduct,
    "for two class functions",
    IsIdenticalObj,
    [ IsClassFunction, IsClassFunction ], 0,
    function( chi, psi )

    local tbl, i, size, weights, scalarproduct;

    tbl:= UnderlyingCharacterTable( chi );
    size:= Size( tbl );
    weights:= SizesConjugacyClasses( tbl );
    chi:= ValuesOfClassFunction( chi );
    psi:= ValuesOfClassFunction( psi );
    scalarproduct:= 0;
    for i in [ 1 .. Length( weights ) ] do
      scalarproduct:= scalarproduct
                      + weights[i] * chi[i] * GaloisCyc( psi[i], -1 );
    od;

    return scalarproduct / size;
    end );


#############################################################################
##
#M  ScalarProduct( <tbl>, <chi>, <psi> ) .  scalar product of class functions
##
Is2Identical3 := function( F1, F2, F3 ) return IsIdenticalObj( F2, F3 ); end;

InstallOtherMethod( ScalarProduct,
    "for ordinary table and two class functions",
    Is2Identical3,
    [ IsOrdinaryTable, IsClassFunction, IsClassFunction ], 0,
    function( tbl, x1, x2 )

     local i,       # loop variable
           scpr,    # scalar product, result
           weight;  # lengths of conjugacy classes

     weight:= SizesConjugacyClasses( tbl );
     x1:= ValuesOfClassFunction( x1 );
     x2:= ValuesOfClassFunction( x2 );
     scpr:= 0;
     for i in [ 1 .. Length( x1 ) ] do
       scpr:= scpr + x1[i] * GaloisCyc( x2[i], -1 ) * weight[i];
     od;
     return scpr / Size( tbl );
     end );


#############################################################################
##
#M  ScalarProduct( <tbl>, <chivals>, <psivals> )
##
InstallOtherMethod( ScalarProduct,
    "for ordinary table and two values lists",
    true,
    [ IsOrdinaryTable, IsHomogeneousList, IsHomogeneousList ], 0,
    function( tbl, x1, x2 )

     local i,       # loop variable
           scpr,    # scalar product, result
           weight;  # lengths of conjugacy classes

     weight:= SizesConjugacyClasses( tbl );
     scpr:= 0;
     for i in [ 1 .. Length( x1 ) ] do
       scpr:= scpr + x1[i] * GaloisCyc( x2[i], -1 ) * weight[i];
     od;
     return scpr / Size( tbl );
     end );


#############################################################################
##
#M  RestrictedClassFunction( <chi>, <H> )
#M  RestrictedClassFunction( <chi>, <tbl> )
##
InstallMethod( RestrictedClassFunction,
    "for class function with group, and group",
    true,
    [ IsClassFunctionWithGroup, IsGroup ], 0,
    function( chi, H );
    H:= OrdinaryCharacterTable( H );
    return ClassFunctionSameType( H, chi, ValuesOfClassFunction( chi ){ 
               FusionConjugacyClasses( H,
                   UnderlyingCharacterTable( chi ) ) } );
    end );

InstallOtherMethod( RestrictedClassFunction,
    "for class function and nearly character table",
    true,
    [ IsClassFunction, IsNearlyCharacterTable ], 0,
    function( chi, tbl )
    local fus;
    fus:= FusionConjugacyClasses( tbl, UnderlyingCharacterTable( chi ) );
    if fus = fail then
      Error( "class fusion not available" );
    fi;
    return ClassFunctionSameType( tbl, chi,
               ValuesOfClassFunction( chi ){ fus } );
    end );


#############################################################################
##
#M  RestrictedClassFunctions( <chars>, <H> )
#M  RestrictedClassFunctions( <chars>, <tbl> )
##
InstallMethod( RestrictedClassFunctions,
    "for collection of class functions with group, and group",
    true,
    [ IsClassFunctionWithGroupCollection, IsGroup ], 0,
    function( chars, H );
    return List( chars, chi -> RestrictedClassFunction( chi, H ) );
    end );

InstallOtherMethod( RestrictedClassFunctions,
    "for collection of class functions, and nearly character table",
    true,
    [ IsClassFunctionCollection, IsNearlyCharacterTable ], 0,
    function( chars, tbl );
    return List( chars, chi -> RestrictedClassFunction( chi, tbl ) );
    end );


#############################################################################
##
#M  RestrictedClassFunctions( <tbl>, <subtbl>, <chars> )
#M  RestrictedClassFunctions( <tbl>, <subtbl>, <chars>, <specification> )
#M  RestrictedClassFunctions( <chars>, <fusionmap> )
##
InstallOtherMethod( RestrictedClassFunctions,
    "for two nearly character tables, and homogeneous list",
    true,
    [ IsNearlyCharacterTable, IsNearlyCharacterTable, IsHomogeneousList ], 0,
    function( tbl, subtbl, chars )
    local fusion;
    fusion:= FusionConjugacyClasses( subtbl, tbl );
    if fusion = fail then
      return fail;
    fi;
    return List( chars, chi -> chi{ fusion } );
    end );

InstallOtherMethod( RestrictedClassFunctions,
    "for two nearly character tables, homogeneous list, and string",
    true,
    [ IsNearlyCharacterTable, IsNearlyCharacterTable, IsMatrix,
      IsString ], 0,
    function( tbl, subtbl, chars, specification )
    local fusion;
    fusion:= FusionConjugacyClasses( subtbl, tbl, specification );
    if fusion = fail then
      return fail;
    fi;
    return List( chars, chi -> chi{ fusion } );
    end );

InstallOtherMethod( RestrictedClassFunctions,
    "for matrix and list of cyclotomics",
    true,
    [ IsMatrix, IsList and IsCyclotomicCollection ], 0,
    function( chars, fusionmap )
    return List( chars, x -> x{ fusionmap } );
    end );


#############################################################################
##
#F  InducedClassFunctionByFusionMap( <chi>, <tbl> )
##
BindGlobal( "InducedClassFunctionByFusionMap", function( chi, tbl, fus )

    local H,
          values,
          Gcentsizes,
          induced,
          Hclasslengths,
          j,
          size;

    if fus = fail then
      return fail;
    fi;

    H:= UnderlyingCharacterTable( chi );
    values:= ValuesOfClassFunction( chi );

    # initialize zero vector
    Gcentsizes:= SizesCentralizers( tbl );
    induced:= ListWithIdenticalEntries( Length( Gcentsizes ), 0 );

    # add the weighted values
    Hclasslengths:= SizesConjugacyClasses( H );
    for j in [ 1 .. Length( Hclasslengths ) ] do
      if values[j] <> 0 then
        induced[ fus[j] ]:= induced[ fus[j] ] + values[j] * Hclasslengths[j];
      fi;
    od;

    # multiply be the weight
    size:= Size( H );
    for j in [ 1 .. Length( induced ) ] do
      induced[j]:= induced[j] * Gcentsizes[j] / size;
    od;

    return ClassFunctionSameType( tbl, chi, induced );
end );


#############################################################################
##
#M  InducedClassFunction( <chi>, <G> )
#M  InducedClassFunction( <chi>, <tbl> )
##
InstallMethod( InducedClassFunction,
    "for class function with group, and group",
    true,
    [ IsClassFunctionWithGroup, IsGroup ], 0,
    function( chi, G )
    return InducedClassFunctionByFusionMap( chi,
               OrdinaryCharacterTable( G ),
               FusionConjugacyClasses( UnderlyingCharacterTable( chi ),
                   OrdinaryCharacterTable( G ) ) );
    end );


InstallOtherMethod( InducedClassFunction,
    "for class function and nearly character table",
    true,
    [ IsClassFunction, IsNearlyCharacterTable ], 0,
    function( chi, tbl )
    return InducedClassFunctionByFusionMap( chi, tbl,
               FusionConjugacyClasses( UnderlyingCharacterTable( chi ),
                   tbl ) );
    end );


#############################################################################
##
#F  InducedClassFunctionsByFusionMap( <subtbl>, <tbl>, <chars>, <fusionmap> )
##
##  is the list of class function values lists
##
BindGlobal( "InducedClassFunctionsByFusionMap",
    function( subtbl, tbl, chars, fusion )

    local j, im,          # loop variables
          centralizers,   # centralizer orders in hte supergroup
          nccl,           # number of conjugacy classes of the group
          subnccl,        # number of conjugacy classes of the subgroup
          suborder,       # order of the subgroup
          subclasses,     # class lengths in the subgroup
          induced,        # list of induced characters, result
          singleinduced,  # one induced character
          char;           # one character to be induced

    if fusion = fail then
      return fail;
    fi;

    centralizers:= SizesCentralizers( tbl );
    nccl:= Length( centralizers );
    suborder:= Size( subtbl );
    subclasses:= SizesConjugacyClasses( subtbl );
    subnccl:= Length( subclasses );

    induced:= [];

    for char in chars do

      # preset the character with zeros
      singleinduced:= ListWithIdenticalEntries( nccl, 0 );

      # add the contribution of each class of the subgroup
      for j in [ 1 .. subnccl ] do
        if char[j] <> 0 then
          if IsInt( fusion[j] ) then
            singleinduced[ fusion[j] ]:= singleinduced[ fusion[j] ]
                                     + char[j] * subclasses[j];
          else
            for im in fusion[j] do singleinduced[ im ]:= Unknown(); od;
#T only for TableInProgress!
          fi;
        fi;
      od;

      # adjust the values by multiplication
      for j in [ 1 .. nccl ] do
        singleinduced[j]:= singleinduced[j] * centralizers[j] / suborder;
        if not IsCycInt( singleinduced[j] ) then
          singleinduced[j]:= Unknown();
          Info( InfoCharacterTable, 1,
                "Induced: subgroup order not dividing sum in character ",
                Length( induced ) + 1, " at class ", j );
        fi;
      od;

      Add( induced, ClassFunctionSameType( tbl, char, singleinduced ) );

    od;

    # Return the list of induced characters.
    return induced;
end );


#############################################################################
##
#M  InducedClassFunctions( <chars>, <G> )
#M  InducedClassFunctions( <chars>, <tbl> )
##
InstallOtherMethod( InducedClassFunctions,
    "for empty list, and group",
    true,
    [ IsList and IsEmpty, IsGroup ], 0,
    function( empty, G )
    return [];
    end );

InstallMethod( InducedClassFunctions,
    "for collection of class functions with group, and group",
    true,
    [ IsClassFunctionWithGroupCollection, IsGroup ], 0,
    function( chars, G )
    return InducedClassFunctionsByFusionMap( chars,
               OrdinaryCharacterTable( G ),
               FusionConjugacyClasses( UnderlyingCharacterTable( chars[1] ),
                   OrdinaryCharacterTable( G ) ) );
    end );


InstallOtherMethod( InducedClassFunctions,
    "for collection of class functions, and nearly character table",
    true,
    [ IsClassFunctionCollection, IsNearlyCharacterTable ], 0,
    function( chars, tbl )
    return InducedClassFunctionsByFusionMap( chars, tbl,
               FusionConjugacyClasses( UnderlyingCharacterTable( chars[1] ),
                   tbl ) );
    end );


#############################################################################
##
#M  InducedClassFunctions( <subtbl>, <tbl>, <chars> )
#M  InducedClassFunctions( <subtbl>, <tbl>, <chars>, <specification> )
#M  InducedClassFunctions( <subtbl>, <tbl>, <chars>, <fusionmap> )
##
InstallOtherMethod( InducedClassFunctions,
    "for two nearly character tables and homog list",
    true,
    [ IsNearlyCharacterTable, IsNearlyCharacterTable, IsHomogeneousList ], 0,
    function( subtbl, tbl, chars )
    return InducedClassFunctionsByFusionMap( subtbl, tbl, chars,
               FusionConjugacyClasses( subtbl, tbl ) );
    end );

InstallOtherMethod( InducedClassFunctions,
    "for two nearly character tables, homog list, and string",
    true,
    [ IsNearlyCharacterTable, IsNearlyCharacterTable,
      IsHomogeneousList, IsString ], 0,
    function( subtbl, tbl, chars, specification )
    return InducedClassFunctionsByFusionMap( subtbl, tbl, chars, 
               FusionConjugacyClasses( subtbl, tbl, specification ) );
    end );

InstallOtherMethod( InducedClassFunctions,
    "for two nearly character tables and two homog. lists",
    true,
    [ IsNearlyCharacterTable, IsNearlyCharacterTable,
      IsHomogeneousList, IsHomogeneousList and IsCyclotomicCollection ], 0,
    InducedClassFunctionsByFusionMap );


#############################################################################
##
#M  ReducedClassFunctions( <ordtbl>, <constituents>, <reducibles> )
#M  ReducedClassFunctions( <ordtbl>, <reducibles> )
##
InstallMethod( ReducedClassFunctions,
    "for ordinary character table, and two lists of class functions",
    true,
    [ IsOrdinaryTable, IsHomogeneousList , IsHomogeneousList ], 0,
    function( ordtbl, constituents, reducibles )

    local i, j,
          normsquare,
          upper,
          found,          # list of found irreducible characters
          remainders,     # list of reducible remainders after reduction
          single,
          reduced,
          scpr;

    upper:= Length( constituents );
    upper:= List( reducibles, x -> upper );
    normsquare:= List( constituents, x -> ScalarProduct( ordtbl, x, x ) );
    found:= [];
    remainders:= [];

    for i in [ 1 .. Length( reducibles ) ] do
      single:= reducibles[i];
      for j in [ 1 .. upper[i] ] do
        scpr:= ScalarProduct( ordtbl, single, constituents[j] );
        if IsInt( scpr ) then
          scpr:= Int( scpr / normsquare[j] );
          if scpr <> 0 then
            single:= single - scpr * constituents[j];
          fi;
        else
          Info( InfoCharacterTable, 1,
                "ReducedClassFunctions: scalar product of X[", j,
                "] with Y[", i, "] not integral (ignore)" );
        fi;
      od;
      if ForAny( single, x -> x <> 0 ) then
        if single[1] < 0 then single:= - single; fi;
        if ScalarProduct( ordtbl, single, single ) = 1 then
          if not single in found and not single in constituents then
            Info( InfoCharacterTable, 2,
                  "ReducedClassFunctions: irreducible character of degree ",
                  single[1], " found" );
            AddSet( found, single );
          fi;
        else 
          AddSet( remainders, single );
        fi;
      fi;
    od;

    # If no irreducibles were found, return the remainders.
    if IsEmpty( found ) then
      return rec( remainders:= remainders, irreducibles:= [] );
    fi;

    # Try to find new irreducibles by recursively calling the reduction.
    reduced:= ReducedClassFunctions( ordtbl, found, remainders );

    # Return the result.
    return rec( remainders:= reduced.remainders,
                irreducibles:= Union( found, reduced.irreducibles ) );
    end );

InstallOtherMethod( ReducedClassFunctions,
    "for ordinary character table, and list of class functions",
    true,
    [ IsOrdinaryTable, IsHomogeneousList ], 0,
    function( ordtbl, reducibles )

    local upper,
          normsquare,
          found,        # list of found irreducible characters
          remainders,   # list of reducible remainders after reduction
          i, j,
          single,
          reduced,
          scpr;

    upper:= [ 0 .. Length( reducibles ) - 1 ];
    normsquare:= List( reducibles, x -> ScalarProduct( ordtbl, x, x ) );
    found:= [];
    remainders:= [];
  
    for i in [ 1 .. Length( reducibles ) ] do
      if normsquare[i] = 1 then
        if 0 < reducibles[i][1] then
          AddSet( found, reducibles[i] );
        else
          AddSet( found, - reducibles[i] );
        fi;
      fi;
    od;

    for i in [ 1 .. Length( reducibles ) ] do
      single:= reducibles[i];
      for j in [ 1 .. upper[i] ] do
        scpr:= ScalarProduct( ordtbl, single, reducibles[j] );
        if IsInt( scpr ) then
          scpr:= Int( scpr / normsquare[j] );
          if scpr <> 0 then
            single:= single - scpr * reducibles[j];
          fi;
        else
          Info( InfoCharacterTable, 1,
                "ReducedClassFunctions: scalar product of X[", j,
                "] with Y[", i, "] not integral (ignore)" );
        fi;
      od;
      if ForAny( single, x -> x <> 0 ) then
        if single[1] < 0 then single:= - single; fi;
        if ScalarProduct( ordtbl, single, single ) = 1 then
          if not single in found and not single in reducibles then
            Info( InfoCharacterTable, 2,
                  "ReducedClassFunctions: irreducible character of degree ",
                  single[1], " found" );
            AddSet( found, single );
          fi;
        else 
          AddSet( remainders, single );
        fi;
      fi;
    od;

    # If no irreducibles were found, return the remainders.
    if IsEmpty( found ) then
      return rec( remainders:= remainders, irreducibles:= [] );
    fi;

    # Try to find new irreducibles by recursively calling the reduction.
    reduced:= ReducedClassFunctions( ordtbl, found, remainders );

    # Return the result.
    return rec( remainders:= reduced.remainders,
                irreducibles:= Union( found, reduced.irreducibles ) );
    end );


#############################################################################
##
#M  ReducedCharacters( <ordtbl>, <constituents>, <reducibles> )
##
InstallMethod( ReducedCharacters,
    "for ordinary character table, and two lists of characters",
    true,
    [ IsOrdinaryTable, IsHomogeneousList , IsHomogeneousList ], 0,
    function( ordtbl, constituents, reducibles )

    local normsquare,
          found,
          remainders,
          single,
          i, j,
          nchars,
          reduced,
          scpr;

    normsquare:= List( constituents, x -> ScalarProduct( ordtbl, x, x ) );
    found:= [];
    remainders:= [];
    nchars:= Length( constituents );
    for i in [ 1 .. Length( reducibles ) ] do

      single:= reducibles[i];
      for j in [ 1 .. nchars ] do
        if constituents[j][1] <= single[1] then
          scpr:= ScalarProduct( ordtbl, single, constituents[j] );
          if IsInt( scpr ) then
            scpr:= Int( scpr / normsquare[j] );
            if scpr <> 0 then single:= single - scpr * constituents[j]; fi;
          else
            Info( InfoCharacterTable, 1,
                  "ReducedCharacters: scalar product of X[", j, "] with Y[",
                  i, "] not integral (ignore)" );
          fi;
        fi;
      od;

      if ForAny( single, x -> x <> 0 ) then
        if ScalarProduct( ordtbl, single, single ) = 1 then
          if single[1] < 0 then single:= - single; fi;
          if not single in found and not single in constituents then
            Info( InfoCharacterTable, 2,
                  "ReducedCharacters: irreducible character of",
                  " degree ", single[1], " found" );
            AddSet( found, single );
          fi;
        else 
          AddSet( remainders, single );
        fi;
      fi;

    od;

    # If no irreducibles were found, return the remainders.
    if IsEmpty( found ) then
      return rec( remainders:= remainders, irreducibles:= [] );
    fi;

    # Try to find new irreducibles by recursively calling the reduction.
    reduced:= ReducedCharacters( ordtbl, found, remainders );

    # Return the result.
    return rec( remainders:= reduced.remainders,
                irreducibles:= Union( found, reduced.irreducibles ) );
    end );


#############################################################################
##
#F  MatScalarProducts( <ordtbl>, <characters1>, <characters2> )
#F  MatScalarProducts( <ordtbl>, <characters> )
##
InstallGlobalFunction( MatScalarProducts, function( arg )

    local i, j, tbl, chars, chars2, chi, nccl, weight, scprmatrix, order,
          scpr;

    if not ( Length( arg ) in [ 2, 3 ] and IsNearlyCharacterTable( arg[1] )
             and IsList( arg[2] )
             and ( Length( arg ) = 2 or IsList( arg[3] ) ) ) then
      Error( "usage: MatScalarProducts( <tbl>, <chars1>, <chars2> )\n",
             " resp. MatScalarProducts( <tbl>, <chars> )" );
    fi;

    tbl:= arg[1];
    chars:= arg[2];
    if IsEmpty( chars ) then
      return [];
    fi;

    nccl:= NrConjugacyClasses( tbl );
    weight:= SizesConjugacyClasses( tbl );
    order:= Size( tbl );

    scprmatrix:= [];
    if Length( arg ) = 3 then
      chars2:= arg[3];
      for i in [ 1 .. Length( chars2 ) ] do
        scprmatrix[i]:= [];
        chi:= List( ValuesOfClassFunction( chars2[i] ),
                    x -> GaloisCyc(x,-1) );
        for j in [ 1 .. nccl ] do
          chi[j]:= chi[j] * weight[j];
        od;
        for j in chars do
          scpr:= ( chi * j ) / order;
          Add( scprmatrix[i], scpr );
          if not IsInt( scpr ) then
            if IsRat( scpr ) then
              Info( InfoCharacterTable, 2,
                    "MatScalarProducts: sum not divisible by group order" );
            elif IsCyc( scpr ) then
              Info( InfoCharacterTable, 2,
                    "MatScalarProducts: summation not integer valued");
            fi;
          fi;
        od;
      od;
    else
      for i in [ 1 .. Length( chars ) ] do
        scprmatrix[i]:= [];
        chi:= List( chars[i], x -> GaloisCyc( x, -1 ) );
        for j in [ 1 .. nccl ] do
          chi[j]:= chi[j] * weight[j];
        od;
        for j in [ 1 .. i ] do
          scpr:= ( chi * chars[j] ) / order;
          Add( scprmatrix[i], scpr );
          if not IsInt( scpr ) then
            if IsRat( scpr ) then
              Info( InfoCharacterTable, 2,
                    "MatScalarProducts: sum not divisible by group order" );
            elif IsCyc( scpr ) then
              Info( InfoCharacterTable, 2,
                    "MatScalarProducts: summation not integer valued");
            fi;
          fi;
        od;
      od;
    fi;
    return scprmatrix;
end );


#############################################################################
##
##  4. methods for auxiliary operations
##

#############################################################################
##
#M  GaloisMat( <mat> )  . . . . . . . . . . . . for a list of class functions
##
##  Note that we must not mix up plain lists and class functions, since
##  these objects ie in different families.
##
InstallMethod( GaloisMat,
    "for a list of class functions",
    true,
    [ IsMatrix and IsClassFunctionCollection ], 0,
    function( mat ) 

    local gal, lenold, lennew, tbl, i;

    gal:= GaloisMat( List( mat, ValuesOfClassFunction ) );
    lenold:= Length( mat );
    lennew:= Length( gal.mat );

    if lennew <> lenold then

      # There are new rows.
      mat:= ShallowCopy( mat );
      tbl:= UnderlyingCharacterTable( mat[1] );
      for i in [ lenold+1 .. lennew ] do
        Add( mat, ClassFunctionByValues( tbl, gal.mat[i] ) );
#T if the row arises from a character and not only a class function,
#T the Galois conjugate is a character, too!
      od;

    fi;

    return rec( mat        := mat,
                galoisfams := gal.galoisfams,
                generators := gal.generators
               );
    end );


#############################################################################
##
#M  GlobalPartitionOfClasses( <tbl> )
##
InstallMethod( GlobalPartitionOfClasses,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )

    local part,     # partition that has to be respected
          list,     # list of all maps to be respected
          map,      # one map in 'list'
          inv,      # contains number of root classes
          newpart,  #
          values,   #
          j,        # loop over 'orb'
          pt;       # one point to map

    if HasAutomorphismsOfTable( tbl ) then

      # The orbits define the finest possible global partition.
      part:= Orbits( AutomorphismsOfTable( tbl ),
                     [ 1 .. Length( NrConjugacyClasses( tbl ) ) ] );

    else

      # Conjugate classes must have same representative order and
      # same centralizer order.
      list:= [ OrdersClassRepresentatives( tbl ),
               SizesCentralizers( tbl ) ];

      # The number of root classes is by definition invariant under
      # table automorphisms.
      for map in Compacted( ComputedPowerMaps( tbl ) ) do
        inv:= 0 * map;
        for j in map do
          inv[j]:= inv[j] + 1;
        od;
        Add( list, inv );
      od;

      # All elements in `list' must be respected.
      # Transform each of them into a partition,
      # and form the intersection of these partitions.
      part:= Partition( [ [ 1 .. Length( list[1] ) ] ] );
      for map in list do
        newpart := [];
        values  := [];
        for j in [ 1 .. Length( map ) ] do
          pt:= Position( values, map[j] );
          if pt = fail then
            Add( values, map[j] );
            Add( newpart, [ j ] );
          else
            Add( newpart[ pt ], j );
          fi;
        od;
        StratMeetPartition( part, Partition( newpart ) );
      od;
      part:= List( Cells( part ), Set );
#T unfortunately 'Set' necessary ...

    fi;

    return part;
    end );


#############################################################################
##
#M  CorrespondingPermutations( <tbl>, <elms> )  . action on the conj. classes
##
InstallMethod( CorrespondingPermutations,
    "for character table and list of group elements",
    true,
    [ IsOrdinaryTable, IsHomogeneousList ], 0,
    function( tbl, elms )

    local classes,  # list of conjugacy classes
          perms,    # list of permutations, result
          part,     # partition that has to be respected
          base,     # base of aut. group
          g,        # loop over `elms'
          images,   # list of images
          pt,       # one point to map
          im,       # actual image class
          orb,      # possible image points
          len,      # length of 'orb'
          found,    # image point found? (boolean value)
          j,        # loop over 'orb'
          list,     # one list in 'part'
          first,    # first point in orbit of 'g'
          min;      # minimal length of nontrivial orbit of 'g'

    classes:= ConjugacyClasses( tbl );

    perms:= [];

    # If the table automorphisms are known then we only must determine
    # the images of a base of this group.
    if HasAutomorphismsOfTable( tbl ) then

      part:= AutomorphismsOfTable( tbl );

      if IsTrivial( part ) then
        return ListWithIdenticalEntries( Length( elms ), () );
      fi;

      # Compute the images of the base points of this group.
      base:= BaseOfGroup( part );

      for g in elms do

        if IsOne( g ) then

          # If `g' is the identity then nothing is to do.
          Add( perms, () );

        else

          images:= [];
          for pt in base do
    
            im:= Representative( classes[ pt ] ) ^ g;
            found:= false;
            for j in Orbit( part, pt ) do
#T better CanonicalClassElement ??
              if im in classes[j] then
                Add( images, j );
                found:= true;
                break;
              fi;
            od;
    
            # Check that `g' really acts on the set of classes.
            if not found then
              break;
            fi;
    
          od;
    
          # Compute a group element (if possible).
          if found then
            Add( perms,
                 RepresentativeOperation( part, base, images, OnTuples ) );
          else
            Add( perms, fail );
          fi;

        fi;

      od;

    else

      # We can use only a partition into unions of orbits.

      part:= GlobalPartitionOfClasses( tbl );
      if Length( part ) = Length( classes ) then
        return ListWithIdenticalEntries( Length( elms ), () );
      fi;

      for g in elms do

        if IsOne( g ) then

          # If `g' is the identity then nothing is to do.
          Add( perms, () );

        else

          # Compute orbits of `g' on the lists in `part', store the images.
          # Note that if we have taken away a union of orbits such that the
          # number of remaining points is smaller than the smallest prime
          # divisor of the order of `g' then all these points must be fixed.
          min:= FactorsInt( Order( g ) )[1];
          images:= [];
  
          for list in part do
    
            if Length( list ) = 1 then
#T why not `min' ?
    
              # necessarily fixed point
              images[ list[1] ]:= list[1];
    
            else
    
              orb:= ShallowCopy( list );
              while min <= Length( orb ) do
    
                # There may be nontrivial orbits.
                pt:= orb[1];
                first:= pt;
                j:= 1;
    
                while j <= Length( orb ) do
    
                  im:= Representative( classes[ pt ] ) ^ g;
                  found:= false;
                  while j <= Length( orb ) and not found do
#T better CanonicalClassElement ??
                    if im in classes[ orb[j] ] then
                      images[pt]:= orb[j];
                      found:= true;
                    fi;
                    j:= j+1;
                  od;
    
                  # Check that `g' really acts on the set of classes.
                  if not found then
                    break;
                  fi;
    
                  RemoveSet( orb, pt );
    
                  if found then
                    j:= 1;
                    pt:= images[pt];
                  fi;
    
                od;
    
                # Check that `g' really acts on the set of classes.
                if not found then
                  break;
                fi;
  
                # The image must be the first point of the orbit under `g'.
                images[pt]:= first;
  
              od;
    
              # Check that `g' really acts on the set of classes.
              if not found then
                break;
              fi;
  
              # The remaining points of the orbit must be fixed.
              for pt in orb do
                images[pt]:= pt;
              od;
    
            fi;
    
          od;
  
          # Compute a group element (if possible).
          if found then
            Add( perms, PermList( images ) );
          else
            Add( perms, fail );
          fi;

        fi;

      od;

    fi;

    return perms;
    end );


#############################################################################
##
#M  CorrespondingPermutations( <chi>, <elms> )
##
InstallMethod( CorrespondingPermutations,
    "for a class function with group, and list of group elements",
    true,
    [ IsClassFunctionWithGroup, IsHomogeneousList ], 0,
    function( chi, elms )

    local G,        # underlying group
          tbl,      # character table
          values,   # list of class function values
          classes,  # list of conjugacy classes
          perms,    # list of permutations, result
          part,     # partition that has to be respected
          base,     # base of aut. group
          g,        # loop over `elms'
          images,   # list of images
          pt,       # one point to map
          im,       # actual image class
          orb,      # possible image points
          len,      # length of 'orb'
          found,    # image point found? (boolean value)
          j,        # loop over 'orb'
          list,     # one list in 'part'
          first,    # first point in orbit of 'g'
          min;      # minimal length of nontrivial orbit of 'g'

    values:= ValuesOfClassFunction( chi );
    tbl:= UnderlyingCharacterTable( chi );

    classes:= ConjugacyClasses( tbl );
    perms:= [];

    # If the table automorphisms are known then we only must determine
    # the images of a base of this group.
    if HasAutomorphismsOfTable( tbl ) then

      part:= AutomorphismsOfTable( tbl );

      if IsTrivial( part ) then
        return ListWithIdenticalEntries( Length( elms ), () );
      fi;

      # Compute the images of the base points of this group.
      base:= BaseOfGroup( part );

      for g in elms do

        if IsOne( g ) then

          # If `g' is the identity then nothing is to do.
          Add( perms, () );

        else

          images:= [];
          for pt in base do

            im:= Representative( classes[ pt ] ) ^ g;
            found:= false;
            for j in Orbit( part, pt ) do
#T better CanonicalClassElement ??
              if im in classes[j] then
                Add( images, j );
                found:= true;
                break;
              fi;
              j:= j+1;
            od;
    
            # Check that `g' really acts on the set of classes.
            if not found then
              break;
            fi;
    
          od;
    
          # Compute a group element (if possible).
          if found then
            Add( perms,
                 RepresentativeOperation( part, base, images, OnTuples ) );
          else
            Add( perms, fail );
          fi;

        fi;

      od;

    else

      # We can use only a partition into unions of orbits.

      part:= GlobalPartitionOfClasses( tbl );
      if Length( part ) = Length( classes ) then
        return ListWithIdenticalEntries( Length( elms ), () );
      fi;

      for g in elms do

        if IsOne( g ) then

          # If `g' is the identity then nothing is to do.
          Add( perms, () );

        else

          # Compute orbits of `g' on the lists in `part', store the images.
          # Note that if we have taken away a union of orbits such that the
          # number of remaining points is smaller than the smallest prime
          # divisor of the order of `g' then all these points must be fixed.
          min:= FactorsInt( Order( g ) )[1];
          images:= [];
    
          for list in part do
    
            if Length( list ) = 1 then
#T why not `min' ?
    
              # necessarily fixed point
              images[ list[1] ]:= list[1];
    
            elif Length( Set( values{ list } ) ) = 1 then
    
              # We may take any permutation of the orbit.
              for j in list do
                images[j]:= j;
              od;
    
            else
    
              orb:= ShallowCopy( list );
              while Length( orb ) >= min do
#T fishy for S4 acting on V4 !!
    
                # There may be nontrivial orbits.
                pt:= orb[1];
                first:= pt;
                j:= 1;
    
                while j <= Length( orb ) do
    
                  im:= Representative( classes[ pt ] ) ^ g;
                  found:= false;
                  while j <= Length( orb ) and not found do
#T better CanonicalClassElement ??
                    if im in classes[ orb[j] ] then
                      images[pt]:= orb[j];
                      found:= true;
                    fi;
                    j:= j+1;
                  od;
    
                  RemoveSet( orb, pt );
    
                  if found then
                    j:= 1;
                    pt:= images[pt];
                  fi;
    
                od;
    
                # The image must be the first point of the orbit under `g'.
                images[pt]:= first;
    
              od;
    
              # The remaining points of the orbit must be fixed.
              for pt in orb do
                images[pt]:= pt;
              od;
    
            fi;
    
          od;
    
          # Compute a group element (if possible).
          if IsHomogeneousList( images ) then
#T not sufficient
            Add( perms, PermList( images ) );
          else
            Add( perms, fail );
          fi;

        fi;

      od;

    fi;

    return perms;
    end );


#############################################################################
##
#M  InertiaSubgroup( <G>, <chi> ) . . . . . . inertia subgroup of a character
##  
InstallMethod( InertiaSubgroup,
    "for a group, and a class function (character) with group",
    true,
    [ IsGroup, IsClassFunctionWithGroup ], 0,
    function( G, chi )

    local H,          # group of `chi'
          index,      # index of `H' in `G'
          induced,    # induced of `chi' from `H' to `G'
          global,     # global partition of classes
          chi_values, # values of `chi'
          part,       # refined partition
          p,          # one set in `global' and `part'
          val,        # one value in `p'
          values,     # list of character values on `p'
          new,        # list of refinements of `p'
          i,          # loop over stored partitions
          pos,        # position where to store new partition later
          perms,      # permutations corresp. to generators of `G'
          permgrp,    # group generated by `perms'
          stab;       # the inertia subgroup, result

    # `chi' must be a character.
    if not IsCharacter( chi ) then
      Error( "<chi> must be a character" );
    fi;

    # `G' must normalize the group of `chi'.
    H:= UnderlyingGroup( chi );
    if not ( IsSubset( G, H ) and IsNormal( G, H ) ) then
      Error( "<H> must be a normal subgroup in <G>" );
    fi;

    # For prime index, check the norm of the induced character.
    # (We get a decision if `chi' is irreducible.)
    index:= Index( G, H );
    if IsPrimeInt( index ) then
      induced:= InducedClassFunction( chi, G );
      if ScalarProduct( induced, induced ) = 1 then
        return H;
      elif ScalarProduct( chi, chi ) = 1 then
        return G;
      fi;
    fi;

    # Compute the partition that must be stabilized.
#T Why is `StabilizerPartition' no longer available?
#T In GAP 3.5, there was such a function.
    # (We need only those cells where `chi' really yields a refinement.)
    global:= GlobalPartitionOfClasses( UnderlyingCharacterTable( chi ) );
    chi_values:= ValuesOfClassFunction( chi );

    part:= [];
    for p in global do
#T only if `p' has length > 1 !
      val:= chi_values[ p[1] ];
      if ForAny( p, x -> chi_values[x] <> val ) then

        # proper refinement will yield a condition.
        values:= [];
        new:= [];
        for i in p do
          pos:= Position( values, chi_values[i] );
          if pos = fail then
            Add( values, chi_values[i] );
            Add( new, [ i ] );
          else
            Add( new[ pos ], i );
          fi;
        od;
        Append( part, new );

      fi;
    od;

    # If no refinement occurs, the character is necessarily invariant in <G>.
    if IsEmpty( part ) then
      return G;
    fi;

    # Compute the permutations corresponding to the generators of `G'.
    perms:= CorrespondingPermutations( chi, GeneratorsOfGroup( G ) );
    permgrp:= GroupByGenerators( perms );

    # `G' acts on the set of conjugacy classes given by each cell of `part'.
    stab:= permgrp;
    for p in part do
      stab:= Stabilizer( stab, p, OnSets );
#T Better one step (partition stabilizer) ??
    od;

    # Construct and return the result.
    if IsTrivial( stab ) then
      return H;
    elif stab = permgrp then
      return G;
    else
      return PreImagesSet( GroupHomomorphismByImages( G, permgrp,
                               GeneratorsOfGroup( G ), perms ),
                 stab );
    fi;
    end );


##############################################################################
##
#F  OrbitChar( <chi>, <linear> )
##
InstallGlobalFunction( OrbitChar, function( chi, linear )

    local classes,   # range of positions in `chi'
          nofcyc,    # describes the conductor of values of `chi'
          gens,      # generators of Galois automorphism group
          orb,       # the orbit, result
          gen,       # loop over `gens'
          image;     # one image of `chi' under operation

    classes:= [ 1 .. Length( chi ) ];
    nofcyc:= Conductor( chi );

    # Apply Galois automorphisms if necessary.
    orb:= [ chi ];
    if 1 < nofcyc then
      gens:= Flat( GeneratorsPrimeResidues( nofcyc ).generators );
      for chi in orb do
        for gen in gens do
          image:= List( chi, x -> GaloisCyc( x, gen ) );
          if not image in orb then
            Add( orb, image );
          fi;
        od;
      od;
    fi;

    # Apply multiplication with linear characters.
    for chi in orb do
      for gen in linear do
        image:= List( classes, x -> gen[x] * chi[x] );
        if not image in orb then
          Add( orb, image );
        fi;
      od;
    od;
      
    # Return the orbit.
    return orb;
end );


##############################################################################
##
#F  OrbitsCharacters( <irr> )
##
InstallGlobalFunction( OrbitsCharacters, function( irr )

    local irrvals,     # list of value lists
          oldirrvals,  # store original succession
          tbl,         # underlying character table
          linear,      # linear characters of `tbl'
          orbits,      # list of orbits, result
          indices,     # from 1 to number of conjugacy classes of `tbl'
          orb,         # one orbit
          gens,        # generators of the acting group
          chi,         # one irreducible character
          gen,         # one generator of the acting group
          image,       # image of a character
          i,           # loop over one orbit
          pos;         # position of value list in `oldirrvals'

    orbits:= [];

    if not IsEmpty( irr ) then

      if IsClassFunction( irr[1] ) then

        # Replace group characters by their value lists.
        # Store the succession in the original list.
        irrvals:= List( irr, ValuesOfClassFunction );
        oldirrvals:= ShallowCopy( irrvals );
        irrvals:= Set( irrvals );

      else
        irrvals:= Set( irr );
      fi;

      indices:= [ 1 .. Length( irrvals[1] ) ];

      # Compute the orbit of linear characters if there are any.
      linear:= Filtered( irrvals, x -> x[1] = 1 );

      if 0 < Length( linear ) then

        # The linear characters form an orbit.
        # We remove them from the other characters,
        # and remove the trivial character from `linear'.
        orb:= ShallowCopy( linear );
        SubtractSet( irrvals, linear );
        RemoveSet( linear, List( linear[1], x -> 1 ) );

        # Make `linear' closed under Galois automorphisms.
        gens:= Flat( GeneratorsPrimeResidues(
                        Conductor( Flat( linear ) ) ).generators );

        for chi in orb do
          for gen in gens do
            image:= List( chi, x -> GaloisCyc( x, gen ) );
            if not image in orb then
              Add( orb, image );
            fi;
          od;
        od;

        # Make `linear' closed under multiplication with linear characters.
        for chi in orb do
          for gen in linear do
            image:= List( indices, x -> gen[x] * chi[x] );
            if not image in orb then
              Add( orb, image );
            fi;
          od;
        od;

        orbits[1]:= orb;

      fi;

      # Compute the other orbits.
      while Length( irrvals ) > 0 do

        orb:= OrbitChar( irrvals[1], linear );
        Add( orbits, orb );
        SubtractSet( irrvals, orb );

      od;

      # Replace the value lists by the group characters
      # if the input was a list of characters.
      # Be careful not to copy characters if not necessary.
      if IsCharacter( irr[1] ) then
        tbl:= UnderlyingCharacterTable( irr[1] );
        for orb in orbits do
          for i in [ 1 .. Length( orb ) ] do
            pos:= Position( oldirrvals, orb[i] );
            if pos = fail then
              orb[i]:= CharacterByValues( tbl, orb[i] );
            else
              orb[i]:= irr[ pos ];
            fi;
          od;
        od;
      fi;

    fi;

    return orbits;
end );


##############################################################################
##
#F  OrbitRepresentativesCharacters( <irr> )
##
InstallGlobalFunction( OrbitRepresentativesCharacters, function( irr )

    local irrvals,     # list of value lists
          oldirrvals,  # store original succession
          chi,         # loop over `irrvals'
          linear,      # linear characters in `irr'
          nonlin,      # nonlinear characters in `irr'
          repres,      # list of representatives, result
          orb;         # one orbit

    repres:= [];

    if not IsEmpty( irr ) then

      if IsCharacter( irr[1] ) then

        # Replace group characters by their value lists.
        # Store the succession in the original list.
        irrvals:= List( irr, ValuesOfClassFunction );
        oldirrvals:= ShallowCopy( irrvals );
        irrvals:= Set( irrvals );

      else
        irrvals:= Set( irr );
      fi;

      # Get the linear characters.
      linear := [];
      nonlin := [];
      for chi in irrvals do
        if chi[1] = 1 then
          Add( linear, chi );
        else
          Add( nonlin, chi );
        fi;
      od;
      if Length( linear ) > 0 then
        repres[1]:= linear[1];
      fi;

      # Compute orbits and remove them until the set is empty.
      while Length( nonlin ) > 0 do
        Add( repres, nonlin[1] );
        orb:= OrbitChar( nonlin[1], linear );
        SubtractSet( nonlin, orb );
      od;

      # Replace the value lists by the group characters
      # if the input was a list of characters.
      # Do not copy characters!
      if IsCharacter( irr[1] ) then
        repres:= List( repres, x -> irr[ Position( oldirrvals, x ) ] );
      fi;

    fi;

    # Return the representatives.
    return repres;
end );


#############################################################################
##
#M  GroupWithGenerators( <classfuns> )
#M  GroupWithGenerators( <classfuns>, <id> )
##
InstallOtherMethod( GroupWithGenerators,
    "for list of class functions",
    true,
    [ IsHomogeneousList and IsClassFunctionCollection ], 0,
    function( gens )
    local filter,G;

    # Check that the class functions are invertible.
    if ForAny( gens, psi -> Inverse( psi ) = fail ) then
      Error( "class functions in <gens> must be invertible" );
    fi;

    filter:=IsGroup and IsAttributeStoringRep;
    if IsFinite(gens) then
      filter:=filter and IsFinitelyGeneratedGroup;
    fi;

    # Construct the group.
    G:= Objectify( NewType( FamilyObj( gens ),filter), rec() );
    SetGeneratorsOfMagmaWithInverses( G, AsList( gens ) );
    return G;
    end );

InstallOtherMethod( GroupWithGenerators,
    "for list of class functions and identity",
    IsCollsElms,
    [ IsHomogeneousList and IsClassFunctionCollection, IsClassFunction ], 0,
    function( gens, id )
    local filter,G;

    # Check that the class functions are invertible.
    if ForAny( gens, psi -> Inverse( psi ) = fail ) then
      Error( "class functions in <gens> must be invertible" );
    elif not IsOne( id ) then
      Error( "<id> must be an identity" );
    fi;

    filter:=IsGroup and IsAttributeStoringRep;
    if IsFinite(gens) then
      filter:=filter and IsFinitelyGeneratedGroup;
    fi;

    # Construct the group.
    G:= Objectify( NewType( FamilyObj( gens ),filter), rec() );
    SetGeneratorsOfMagmaWithInverses( G, AsList( gens ) );
    SetOne( G, id );
    return G;
    end );

InstallOtherMethod( GroupWithGenerators,
    "for empty list and trivial character",
    true,
    [ IsList and IsEmpty, IsClassFunction ], 0,
    function( empty, id )
    local G;

    # Check that the class functions are invertible.
    if not IsOne( id ) then
      Error( "<id> must be an identity" );
    fi;

    # Construct the group.
    G:= Objectify( NewType( CollectionsFamily( FamilyObj( id ) ),
                            IsGroup and IsAttributeStoringRep and
			    IsFinitelyGeneratedGroup ),
                   rec() );
    SetGeneratorsOfMagmaWithInverses( G, empty );
    SetOne( G, id );
    return G;
    end );


#############################################################################
##
##  5. vector spaces of class functions
##

#############################################################################
##
#R  IsClassFunctionsSpaceRep( <V> )
##
##  Free left modules of class functions are handled by associating to a
##  class function the row vector given by its values.
##
##  Free left modules of class functions contain the component
##
##  \beginitems
##  `elementsunderlying' &
##       the underlying character table of the elements.
##  \enditems
##
DeclareRepresentation( "IsClassFunctionsSpaceRep",
    IsAttributeStoringRep and IsHandledByNiceBasis,
    [ "elementsunderlying" ] );


#############################################################################
##
#M  LeftModuleByGenerators( <F>, <gens> ) . . . . create space of class funs.
#M  LeftModuleByGenerators( <F>, <gens>, <zero> )
#M  LeftModuleByGenerators( <F>, <empty>, <zero> )
##
##  These methods differ from the default methods only by setting the flag
##  `IsClassFunctionsSpaceRep' and the component `elementsunderlying'.
##
InstallMethod( LeftModuleByGenerators,
    "for division ring and collection of class functions",
    true,
    [ IsDivisionRing, IsClassFunctionCollection ] , 0,
    function( F, gens )
    local V;
    V:= Objectify( NewType( FamilyObj( gens ),
                                IsFreeLeftModule
                            and IsLeftActedOnByDivisionRing
                            and IsClassFunctionsSpaceRep ),
                   rec() );
    SetLeftActingDomain( V, F );
    SetGeneratorsOfLeftModule( V, AsList( gens ) );
    V!.elementsunderlying:= UnderlyingCharacterTable(
                                Representative( V ) );
    return V;
    end );

InstallOtherMethod( LeftModuleByGenerators,
    "for division ring, collection of class functions, and zero",
    true,
    [ IsDivisionRing, IsClassFunctionCollection, IsClassFunction ], 0,
    function( F, gens, zero )
    local V;
    V:= Objectify( NewType( CollectionsFamily( FamilyObj( zero ) ),
                                IsFreeLeftModule
                            and IsLeftActedOnByDivisionRing
                            and IsClassFunctionsSpaceRep ),
                   rec() );
    SetLeftActingDomain( V, F );
    SetGeneratorsOfLeftModule( V, AsList( gens ) );
    SetZero( V, zero );
    V!.elementsunderlying:= UnderlyingCharacterTable(
                                Representative( V ) );
    return V;
    end );

InstallOtherMethod( LeftModuleByGenerators,
    "for division ring, empty list, and class function",
    true,
    [ IsDivisionRing, IsList and IsEmpty, IsClassFunction ], 0,
    function( F, empty, zero )
    local V;
    V:= Objectify( NewType( CollectionsFamily( FamilyObj( zero ) ),
                                IsFreeLeftModule
                            and IsLeftActedOnByDivisionRing
                            and IsTrivial
                            and IsClassFunctionsSpaceRep ),
                   rec() );
    SetLeftActingDomain( V, F );
    SetGeneratorsOfLeftModule( V, AsList( empty ) );
    SetZero( V, zero );
    V!.elementsunderlying:= UnderlyingCharacterTable(
                                Representative( V ) );
    return V;
    end );


#############################################################################
##
#M  FLMLORByGenerators( <F>, <gens> )  . . . . . create FLMLOR of class funs.
#M  FLMLORByGenerators( <F>, <gens>, <zero> )
#M  FLMLORByGenerators( <F>, <empty>, <zero> )
##
##  These methods differ from the default methods only by setting the flag
##  `IsClassFunctionsSpaceRep' and the component `elementsunderlying'.
##
InstallMethod( FLMLORByGenerators,
    "for division ring and collection of class functions",
    true,
    [ IsDivisionRing, IsClassFunctionCollection ] , 0,
    function( F, gens )
    local V;
    V:= Objectify( NewType( FamilyObj( gens ),
                                IsFLMLOR
                            and IsLeftActedOnByDivisionRing
                            and IsClassFunctionsSpaceRep ),
                   rec() );
    SetLeftActingDomain( V, F );
    SetGeneratorsOfFLMLOR( V, AsList( gens ) );
    V!.elementsunderlying:= UnderlyingCharacterTable(
                                Representative( V ) );
    return V;
    end );

InstallOtherMethod( FLMLORByGenerators,
    "for division ring, collection of class functions, and zero",
    true,
    [ IsDivisionRing, IsClassFunctionCollection, IsClassFunction ], 0,
    function( F, gens, zero )
    local V;
    V:= Objectify( NewType( CollectionsFamily( FamilyObj( zero ) ),
                                IsFLMLOR
                            and IsLeftActedOnByDivisionRing
                            and IsClassFunctionsSpaceRep ),
                   rec() );
    SetLeftActingDomain( V, F );
    SetGeneratorsOfFLMLOR( V, AsList( gens ) );
    SetZero( V, zero );
    V!.elementsunderlying:= UnderlyingCharacterTable(
                                Representative( V ) );
    return V;
    end );

InstallOtherMethod( FLMLORByGenerators,
    "for division ring, empty list, and class function",
    true,
    [ IsDivisionRing, IsList and IsEmpty, IsClassFunction ], 0,
    function( F, empty, zero )
    local V;
    V:= Objectify( NewType( CollectionsFamily( FamilyObj( zero ) ),
                                IsFLMLOR
                            and IsLeftActedOnByDivisionRing
                            and IsTrivial
                            and IsClassFunctionsSpaceRep ),
                   rec() );
    SetLeftActingDomain( V, F );
    SetGeneratorsOfFLMLOR( V, AsList( empty ) );
    SetZero( V, zero );
    V!.elementsunderlying:= UnderlyingCharacterTable(
                                Representative( V ) );
    return V;
    end );


#############################################################################
##
#M  FLMLORWithOneByGenerators( <F>, <gens> )
#M  FLMLORWithOneByGenerators( <F>, <gens>, <zero> )
#M  FLMLORWithOneByGenerators( <F>, <empty>, <zero> )
##
##  These methods differ from the default methods only by setting the flag
##  `IsClassFunctionsSpaceRep' and the component `elementsunderlying'.
##
InstallMethod( FLMLORWithOneByGenerators,
    "for division ring and collection of class functions",
    true,
    [ IsDivisionRing, IsClassFunctionCollection ] , 0,
    function( F, gens )
    local V;
    V:= Objectify( NewType( FamilyObj( gens ),
                                IsFLMLORWithOne
                            and IsLeftActedOnByDivisionRing
                            and IsClassFunctionsSpaceRep ),
                   rec() );
    SetLeftActingDomain( V, F );
    SetGeneratorsOfFLMLORWithOne( V, AsList( gens ) );
    V!.elementsunderlying:= UnderlyingCharacterTable(
                                Representative( V ) );
    return V;
    end );

InstallOtherMethod( FLMLORWithOneByGenerators,
    "for division ring, collection of class functions, and zero",
    true,
    [ IsDivisionRing, IsClassFunctionCollection, IsClassFunction ], 0,
    function( F, gens, zero )
    local V;
    V:= Objectify( NewType( CollectionsFamily( FamilyObj( zero ) ),
                                IsFLMLORWithOne
                            and IsLeftActedOnByDivisionRing
                            and IsClassFunctionsSpaceRep ),
                   rec() );
    SetLeftActingDomain( V, F );
    SetGeneratorsOfFLMLORWithOne( V, AsList( gens ) );
    SetZero( V, zero );
    V!.elementsunderlying:= UnderlyingCharacterTable(
                                Representative( V ) );
    return V;
    end );

InstallOtherMethod( FLMLORWithOneByGenerators,
    "for division ring, empty list, and class function",
    true,
    [ IsDivisionRing, IsList and IsEmpty, IsClassFunction ], 0,
    function( F, empty, zero )
    local V;
    V:= Objectify( NewType( CollectionsFamily( FamilyObj( zero ) ),
                                IsFLMLORWithOne
                            and IsLeftActedOnByDivisionRing
                            and IsTrivial
                            and IsClassFunctionsSpaceRep ),
                   rec() );
    SetLeftActingDomain( V, F );
    SetGeneratorsOfFLMLORWithOne( V, AsList( empty ) );
    SetZero( V, zero );
    V!.elementsunderlying:= UnderlyingCharacterTable(
                                Representative( V ) );
    return V;
    end );


#############################################################################
##
#M  PrepareNiceFreeLeftModule( <V> )
##
InstallMethod( PrepareNiceFreeLeftModule,
    "for a space of class functions",
    true,
    [ IsFreeLeftModule and IsClassFunctionsSpaceRep ], 0,
    Ignore );


#############################################################################
##
#M  NiceVector( <V>, <v> )
##
InstallMethod( NiceVector,
    "for a free module of class functions",
    IsCollsElms,
    [ IsFreeLeftModule and IsClassFunctionsSpaceRep, IsClassFunction ], 0,
    function( V, v )
    if UnderlyingCharacterTable( v ) = V!.elementsunderlying then
      return ValuesOfClassFunction( v );
    else
      return fail;
    fi;
    end );


#############################################################################
##
#M  UglyVector( <V>, <r> )
##
InstallMethod( UglyVector,
    "for a free module of class functions",
    true,
    [ IsFreeLeftModule and IsClassFunctionsSpaceRep, IsRowVector ], 0,
    function( V, r )
    return ClassFunctionByValues( V!.elementsunderlying, r );
    end );


#############################################################################
##
#M  ScalarProduct( <V>, <chi>, <psi> ) . . . .  for module of class functions
##
##  Left modules of class functions carry the usual bilinear form.
##
InstallOtherMethod( ScalarProduct,
    "for left module of class functions, and two class functions",
    IsCollsElmsElms,
    [ IsFreeLeftModule and IsClassFunctionsSpaceRep,
      IsClassFunction, IsClassFunction ], 0,
    function( V, x1, x2 )

     local tbl,     # character table
           i,       # loop variable
           scpr,    # scalar product, result
           weight;  # lengths of conjugacy classes

     tbl:= V!.elementsunderlying;
     weight:= SizesConjugacyClasses( tbl );
     x1:= ValuesOfClassFunction( x1 );
     x2:= ValuesOfClassFunction( x2 );
     scpr:= 0;
     for i in [ 1 .. Length( x1 ) ] do
       scpr:= scpr + x1[i] * GaloisCyc( x2[i], -1 ) * weight[i];
     od;
     return scpr / Size( tbl );
     end );


#############################################################################
##
#M  ScalarProduct( <V>, <chivals>, <psivals> )  . . for module of class funs.
##
##  Left modules of class functions carry the usual bilinear form.
##
InstallOtherMethod( ScalarProduct,
    "for module of class functions, and two values lists",
    Is2Identical3,
    [ IsFreeLeftModule and IsClassFunctionsSpaceRep,
      IsHomogeneousList, IsHomogeneousList ], 0,
    function( V, x1, x2 )

     local tbl,     # character table
           i,       # loop variable
           scpr,    # scalar product, result
           weight;  # lengths of conjugacy classes

     tbl:= V!.elementsunderlying;
     weight:= SizesConjugacyClasses( tbl );
     scpr:= 0;
     for i in [ 1 .. Length( x1 ) ] do
       scpr:= scpr + x1[i] * GaloisCyc( x2[i], -1 ) * weight[i];
     od;
     return scpr / Size( tbl );
     end );


##############################################################################
##
#M  NormalSubgroupClassesInfo( <tbl> )
##
InstallMethod( NormalSubgroupClassesInfo,
    "default method, initialization",
    true,
    [ IsOrdinaryTable ], 0,
    tbl -> rec( nsg        := [],
                nsgclasses := [],
                nsgfactors := [] ) );


##############################################################################
##
#F  NormalSubgroupClasses( <tbl>, <classes> )
##
InstallGlobalFunction( NormalSubgroupClasses, function( tbl, classes )

    local info,
          pos,        # position of the group in the list of such groups
          G,          # underlying group of `tbl'
          ccl,        # `G'-conjugacy classes in our normal subgroup
          size,       # size of our normal subgroup
          candidates, # bound normal subgroups that possibly are our group
          group,      # the normal subgroup
          repres,     # list of representatives of conjugacy classes
          found,      # normal subgroup already identified
          i;          # loop over normal subgroups

    info:= NormalSubgroupClassesInfo( tbl );

    classes:= Set( classes );
    pos:= Position( info.nsgclasses, classes );
    if pos = fail then

      # The group is not yet stored here, try `NormalSubgroups( G )'.
      G:= UnderlyingGroup( tbl );

      if HasNormalSubgroups( G ) then

        # Identify our normal subgroup.
        ccl:= ConjugacyClasses( tbl ){ classes };
        size:= Sum( ccl, Size, 0 );
        candidates:= Filtered( NormalSubgroups( G ), x -> Size( x ) = size );
        if Length( candidates ) = 1 then
          group:= candidates[1];
        else

          repres:= List( ccl, Representative );
          found:= false;
          i:= 0;
          while not found do
            i:= i+1;
            if ForAll( repres, x -> x in candidates[i] ) then
              found:= true;
            fi;
          od;

          if not found then
            Error( "<classes> does not describe a normal subgroup" );
          fi;

          group:= candidates[i];

        fi;

      elif classes = [ 1 ] then

        group:= TrivialSubgroup( G );

      else

        # The group is not yet stored, we have to construct it.
        repres:= List( ConjugacyClasses( tbl ){ classes }, Representative );
        group := NormalClosure( G, SubgroupNC( G, repres ) );

      fi;

      MakeImmutable( classes );
      Add( info.nsgclasses, classes );
      Add( info.nsg       , group   );
      pos:= Length( info.nsg );

    fi;

    return info.nsg[ pos ];
end );


##############################################################################
##
#M  ClassesOfNormalSubgroup( <tbl>, <N> )
##
InstallGlobalFunction( ClassesOfNormalSubgroup, function( tbl, N )

    local info,
          classes,    # result list
          found,      # `N' already found?
          pos,        # position in `info.nsg'
          G,          # underlying group of `tbl'
          ccl;        # conjugacy classes of `tbl'

    info:= NormalSubgroupClassesInfo( tbl );

    # Search for `N' in `info.nsg'.
    found:= false;
    pos:= 0;
    while ( not found ) and pos < Length( info.nsg ) do
      pos:= pos+1;
      if IsIdenticalObj( N, info.nsg[ pos ] ) then
        found:= true;
      fi;
    od;
    if not found then
      pos:= Position( info.nsg, N );
    fi;

    if pos = fail then

      # The group is not yet stored here, try `NormalSubgroups( G )'.
      G:= UnderlyingGroup( tbl );
      if HasNormalSubgroups( G ) then

        # Identify our normal subgroup.
        N:= NormalSubgroups( G )[ Position( NormalSubgroups( G ), N ) ];

      fi;

      ccl:= ConjugacyClasses( tbl );
      classes:= Filtered( [ 1 .. Length( ccl ) ],
                          x -> Representative( ccl[x] ) in N );

      Add( info.nsgclasses, classes );
      Add( info.nsg       , N       );
      pos:= Length( info.nsg );

    fi;

    return info.nsgclasses[ pos ];
end );


##############################################################################
##
#F  FactorGroupNormalSubgroupClasses( <tbl>, <classes> )
##
InstallGlobalFunction( FactorGroupNormalSubgroupClasses,
    function( tbl, classes )

    local info,
          f,     # the result
          pos;   # position in list of normal subgroups

    info:= NormalSubgroupClassesInfo( tbl );
    pos:= Position( info.nsgclasses, classes );

    if pos = fail then
      f:= UnderlyingGroup( tbl ) / NormalSubgroupClasses( tbl, classes );
      info.nsgfactors[ Length( info.nsgclasses ) ]:= f;
    elif IsBound( info.nsgfactors[ pos ] ) then
      f:= info.nsgfactors[ pos ];
    else
      f:= UnderlyingGroup( tbl ) / info.nsg[ pos ];
      info.nsgfactors[ pos ]:= f;
    fi;

    return f;
end );


#############################################################################
##
#E

