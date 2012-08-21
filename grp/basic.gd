#############################################################################
##
#W  basic.gd                    GAP Library                      Frank Celler
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
##
##  This file contains the operations for the construction of the basic group
##  types.
##
Revision.basic_gd :=
    "@(#)$Id$";


#############################################################################
##
#O  AbelianGroupCons( <filter>, <ints> )
##
DeclareConstructor( "AbelianGroupCons", [ IsGroup, IsList ] );


#############################################################################
##
#F  AbelianGroup( [<cat>,] <ints> ) . . . . . . . . . . . . . . abelian group
##
##  constructs an abelian group in the category <cat> which is of isomorphism
##  type $C_{ints[1]} \*  C_{ints[2]} \* \ldots \* C_{ints[n]}$.
##  <ints> must be a list of positive integers.
##  If <cat> is not given it defaults to `IsPcGroup'.
##
BindGlobal( "AbelianGroup", function ( arg )

  if Length(arg) = 1  then
    return AbelianGroupCons( IsPcGroup, arg[1] );
  elif IsOperation(arg[1]) then

    if Length(arg) = 2  then
      return AbelianGroupCons( arg[1], arg[2] );

    elif Length(arg) = 3  then
      return AbelianGroupCons( arg[1], arg[2], arg[3] );
    fi;
  fi;
  Error( "usage: AbelianGroup( [<category>,]<ints> )" );

end );


#############################################################################
##
#O  AlternatingGroupCons( <filter>, <deg> )
##
DeclareConstructor( "AlternatingGroupCons", [ IsGroup, IsInt ] );


#############################################################################
##
#F  AlternatingGroup( [<cat>,] <deg> )  . . . . . . . . . . alternating group
#F  AlternatingGroup( [<cat>,] <dom> )  . . . . . . . . . . alternating group
##
##  constructs the alternating group of degree <deg> in the category <cat>.
##  If <cat> is not given it defaults to `IsPermGroup'.
##  In the second version, the function constructs the alternating group on
##  the points given in the set <dom> which must be a set of positive
##  integers.
##
BindGlobal( "AlternatingGroup", function ( arg )

  if Length(arg) = 1  then
    return  AlternatingGroupCons( IsPermGroup, arg[1] );
  elif IsOperation(arg[1]) then

    if Length(arg) = 2  then
      return  AlternatingGroupCons( arg[1], arg[2] );
    fi;
  fi;
  Error( "usage:  AlternatingGroup( [<category>,]<deg> )" );

end );


#############################################################################
##
#O  CyclicGroupCons( <filter>, <n> )
##
DeclareConstructor( "CyclicGroupCons", [ IsGroup, IsInt ] );


#############################################################################
##
#F  CyclicGroup( [<cat>,] <n> ) . . . . . . . . . . . . . . . .  cyclic group
##
##  constructs the cyclic group of size <n> in the category <cat>.
##  If <cat> is not given it defaults to `IsPcGroup'.
##
BindGlobal( "CyclicGroup", function ( arg )

  if Length(arg) = 1  then
    if arg[1] = 1 then
      return FreeGroup( 0 );
    fi;
    return CyclicGroupCons( IsPcGroup, arg[1] );
  elif IsOperation(arg[1]) then

    if Length(arg) = 2  then
      return CyclicGroupCons( arg[1], arg[2] );

    elif Length(arg) = 3  then
      return CyclicGroupCons( arg[1], arg[2], arg[3] );
    fi;
  fi;
  Error( "usage: CyclicGroupCons( [<category>,]<size> )" );

end );


#############################################################################
##
#O  DihedralGroupCons( <filter>, <n> )
##
DeclareConstructor( "DihedralGroupCons", [ IsGroup, IsInt ] );


#############################################################################
##
#F  DihedralGroup( [<cat>,] <n> ) . . . . . . . . dihedral groug of order <n>
##
##  constructs the dihedral group of size <n> in the category <cat>.
##  If <cat> is not given it defaults to `IsPcGroup'.
##
BindGlobal( "DihedralGroup", function ( arg )

  if Length(arg) = 1  then
    return DihedralGroupCons( IsPcGroup, arg[1] );
  elif IsOperation(arg[1]) then

    if Length(arg) = 2  then
      return DihedralGroupCons( arg[1], arg[2] );

    elif Length(arg) = 3  then
      return DihedralGroupCons( arg[1], arg[2], arg[3] );
    fi;
  fi;
  Error( "usage: DihedralGroup( [<category>,]<size> )" );

end );


#############################################################################
##
#O  ElementaryAbelianGroupCons( <filter>, <n> )
##
DeclareConstructor( "ElementaryAbelianGroupCons", [ IsGroup, IsInt ] );


#############################################################################
##
#F  ElementaryAbelianGroup( [<cat>,] <n> )  . . . .  elementary abelian group
##
##  constructs the elementary abelian group of size <n> in the category <cat>.
##  If <cat> is not given it defaults to `IsPcGroup'.
##
BindGlobal( "ElementaryAbelianGroup", function ( arg )

  if Length(arg) = 1  then
    return ElementaryAbelianGroupCons( IsPcGroup, arg[1] );
  elif IsOperation(arg[1]) then

    if Length(arg) = 2  then
      return ElementaryAbelianGroupCons( arg[1], arg[2] );

    elif Length(arg) = 3  then
      return ElementaryAbelianGroupCons( arg[1], arg[2], arg[3] );
    fi;
  fi;
  Error( "usage: ElementaryAbelianGroupCons( [<category>,]<size> )" );

end );


#############################################################################
##
#O  ExtraspecialGroupCons( <filter>, <order>, <exponent> )
##
DeclareConstructor( "ExtraspecialGroupCons", [ IsGroup, IsInt, IsObject ] );


#############################################################################
##
#F  ExtraspecialGroup( [<cat>, ]<order>, <exp> )  . . . .  extraspecial group
##
##  Let <order> be of the form $p^{2n+1}$, for a prime integer $p$ and a
##  positive integer $n$.
##  `ExtraspecialGroup' returns the extraspecial group of order <order>
##  that is determined by <exp>, in the category <cat>.
##
##  If $p$ is odd then admissible values of <exp> are the exponent of the
##  group (either $p$ or $p^2$) or one of `{'}+{'}', `\"+\"', `{'}-{'}',
##  `\"-\"'.
##  For $p = 2$, only the above plus or minus signs are admissible.
##
##  If <cat> is not given it defaults to `IsPcGroup'.
##
BindGlobal( "ExtraspecialGroup", function ( arg )

  if Length(arg) = 2  then
    return ExtraspecialGroupCons( IsPcGroup, arg[1],arg[2] );
  elif IsOperation(arg[1]) then

    if Length(arg) = 3  then
      return ExtraspecialGroupCons( arg[1], arg[2],arg[3] );

    elif Length(arg) = 4  then
      return ExtraspecialGroupCons( arg[1], arg[2], arg[3], arg[4] );
    fi;
  fi;
  Error( "usage: ExtraspecialGroup( [<category>,]<order>,<exponent> )" );

end );


#############################################################################
##
#O  GeneralLinearGroupCons( <filter>, <d>, <q> )
##
DeclareConstructor( "GeneralLinearGroupCons", [ IsGroup, IsInt, IsInt ] );


#############################################################################
##
#F  GeneralLinearGroup( [<cat>,] <d>, <q> ) . . . . . .  general linear group
#F  GL( [<cat>,] <d>, <q> )
##
##  constructs a group isomorphic to the general linear group GL( <d>, <q> )
##  of $<d> \times <d>$ matrices over the field with <q> elements,
##  in the category <cat>.
##
##  If <cat> is not given it defaults to `IsMatrixGroup',
##  and the returned group is the general linear group itself.
##
BindGlobal( "GeneralLinearGroup", function ( arg )

  if Length(arg) = 2  then
    return GeneralLinearGroupCons( IsMatrixGroup, arg[1],arg[2] );
  elif IsOperation(arg[1]) then

    if Length(arg) = 3  then
      return GeneralLinearGroupCons( arg[1], arg[2],arg[3] );
    fi;
  fi;
  Error( "usage: GeneralLinearGroup( [<category>,]<d>,<q> )" );

end );

DeclareSynonym( "GL", GeneralLinearGroup );


#############################################################################
##
#O  SpecialLinearGroupCons( <filter>, <d>, <q> )
##
DeclareConstructor( "SpecialLinearGroupCons", [ IsGroup, IsInt, IsInt ] );


#############################################################################
##
#F  SpecialLinearGroup( [<cat>,] <d>, <q> ) . . . . . .  special linear group
#F  SL( [<cat>,] <d>, <q> )
##
##  constructs a group isomorphic to the special linear group SL( <d>, <q> )
##  of those $<d> \times <d>$ matrices over the field with <q> elements
##  whose determinant is the identity of the field,
##  in the category <cat>.
##
##  If <cat> is not given it defaults to `IsMatrixGroup',
##  and the returned group is the special linear group itself.
##
BindGlobal( "SpecialLinearGroup", function ( arg )

  if Length(arg) = 2  then
    return SpecialLinearGroupCons( IsMatrixGroup, arg[1],arg[2] );
  elif IsOperation(arg[1]) then

    if Length(arg) = 3  then
      return SpecialLinearGroupCons( arg[1], arg[2],arg[3] );
    fi;
  fi;
  Error( "usage: SpecialLinearGroup( [<category>,]<d>,<q> )" );

end );

DeclareSynonym( "SL", SpecialLinearGroup );


#############################################################################
##
#O  SymmetricGroupCons( <filter>, <deg> )
##
DeclareConstructor( "SymmetricGroupCons", [ IsGroup, IsInt ] );


#############################################################################
##
#F  SymmetricGroup( [<cat>,] <deg> )
#F  SymmetricGroup( [<cat>,] <dom> )
##
##  constructs the symmetric group of degree <deg> in the category <cat>.
##  If <cat> is not given it defaults to `IsPermGroup'.
##  In the second version, the function constructs the symmetric group on
##  the points given in the set <dom> which must be a set of positive
##  integers.
##
BindGlobal( "SymmetricGroup", function ( arg )

  if Length(arg) = 1  then
    return  SymmetricGroupCons( IsPermGroup, arg[1] );
  elif IsOperation(arg[1]) then

    if Length(arg) = 2  then
      return  SymmetricGroupCons( arg[1], arg[2] );
    fi;
  fi;
  Error( "usage:  SymmetricGroup( [<category>,]<deg> )" );

end );


#############################################################################
##
#E
##

