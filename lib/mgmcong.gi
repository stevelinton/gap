#############################################################################
##
#W  mgmcong.gi              GAP library                     Andrew Solomon
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains generic methods for magma congruences
##
Revision.mgmcong_gi :=
    "@(#)$Id$";


#############################################################################
##
#M  PrintObj( <S> )
##  print a [left, right, two-sided] Magma Congruence
##

##  left

InstallMethod( PrintObj,
    "for a left magma congruence",
    true,
    [ IsLeftMagmaCongruence ], 0,
    function( S )
    Print( "LeftMagmaCongruence( ... )" );
    end );

InstallMethod( PrintObj,
    "for a left magma congruence with known generating pairs",
    true,
    [ IsLeftMagmaCongruence and HasGeneratingPairsOfLeftMagmaCongruence ], 0,
    function( S )
    Print( "LeftMagmaCongruence( ", 
			GeneratingPairsOfLeftMagmaCongruence( S ), " )" );
    end );

##  right

InstallMethod( PrintObj,
    "for a right magma congruence",
    true,
    [ IsRightMagmaCongruence ], 0,
    function( S )
    Print( "RightMagmaCongruence( ... )" );
    end );

InstallMethod( PrintObj,
    "for a right magma congruence with known generating pairs",
    true,
    [ IsRightMagmaCongruence and HasGeneratingPairsOfRightMagmaCongruence ], 0,
    function( S )
    Print( "RightMagmaCongruence( ", 
			GeneratingPairsOfRightMagmaCongruence( S ), " )" );
    end );


##  two sided

InstallMethod( PrintObj,
    "for a magma congruence",
    true,
    [ IsMagmaCongruence ], 0,
    function( S )
    Print( "MagmaCongruence( ... )" );
    end );

InstallMethod( PrintObj,
    "for a magma Congruence with known generating pairs",
    true,
    [ IsMagmaCongruence and HasGeneratingPairsOfMagmaCongruence ], 0,
    function( S )
    Print( "MagmaCongruence( ", 
			GeneratingPairsOfMagmaCongruence( S ), " )" );
    end );

#############################################################################
##
#M  ViewObj( <S> )  
##	view a [left,right,two-sided] magma congruence
##

##  left

InstallMethod( ViewObj,
    "for a LeftMagmaCongruence",
    true,
    [ IsLeftMagmaCongruence ], 0,
    function( S )
    Print( "<LeftMagmaCongruence>" );
    end );

InstallMethod( ViewObj,
    "for a LeftMagmaCongruence with known generating pairs",
    true,
    [ IsLeftMagmaCongruence and HasGeneratingPairsOfLeftMagmaCongruence ], 0,
    function( S )
    Print( "<LeftMagmaCongruence with ", 
			Length( GeneratingPairsOfLeftMagmaCongruence( S ) ), " generating pairs>" );
    end );

##  right


InstallMethod( ViewObj,
    "for a RightMagmaCongruence",
    true,
    [ IsRightMagmaCongruence ], 0,
    function( S )
    Print( "<RightMagmaCongruence>" );
    end );

InstallMethod( ViewObj,
    "for a RightMagmaCongruence with generators",
    true,
    [ IsRightMagmaCongruence and HasGeneratingPairsOfRightMagmaCongruence ], 0,
    function( S )
    Print( "<RightMagmaCongruence with ", 
			Length( GeneratingPairsOfRightMagmaCongruence( S ) ), " generating pairs>" );
    end );


## two sided

InstallMethod( ViewObj,
    "for a magma congruence",
    true,
    [ IsMagmaCongruence ], 0,
    function( S )
    Print( "<MagmaCongruence>" );
    end );

InstallMethod( ViewObj,
    "for a magma congruence with generating pairs",
    true,
    [ IsMagmaCongruence and HasGeneratingPairsOfMagmaCongruence ], 0,
    function( S )
    Print( "<MagmaCongruence with ", 
			Length( GeneratingPairsOfMagmaCongruence( S ) ), " generating pairs>" );
    end );



#############################################################################
##
#M  LR2MagmaCongruenceByGeneratingPairsCAT(<F>,<rels>,<category>) 
##
##  create the magma congruence with generating pairs <rels> as
##  a <category> where <category> is IsLeftMagmaCongruence, 
##  IsRightMagmaCongruence or IsMagmaCongruence.
##
InstallGlobalFunction( LR2MagmaCongruenceByGeneratingPairsCAT, 
function(F, gens, category )

	local r, cong, fam;

	# Check that the relations are all lists of length 2
	for r in gens do
		if Length(r) <> 2 then
			Error("A relation should be a list of length 2");
		fi;
	od;

	# Create the equivalence relation
	fam :=  GeneralMappingsFamily( ElementsFamily(FamilyObj(F)),
    ElementsFamily(FamilyObj(F)) );
    
  # Create the default type for the elements.
  cong :=  Objectify(NewType(fam, 
    category and IsEquivalenceRelationDefaultRep), rec());
  SetSource(cong, F);
  SetRange(cong, F);

	# Add the generators in the appropriate attribute
	if (category = IsMagmaCongruence) or (category = IsSemigroupCongruence) then
		SetGeneratingPairsOfMagmaCongruence(cong, Immutable(gens));
	elif category = IsLeftMagmaCongruence then
		SetGeneratingPairsOfLeftMagmaCongruence(cong, Immutable(gens)); 
	elif category = IsRightMagmaCongruence then
    SetGeneratingPairsOfRightMagmaCongruence(cong, Immutable(gens)); 
	else
		Error("Invalid category ",category," of Magma congruence");
	fi;

	return cong;
end);


#############################################################################
##
#M  LR2MagmaCongruenceByPartitionNCCAT(<F>,<part>,<category>) 
##
##  create the magma congruence with partition <part> as
##  a <category> where <category> is IsLeftMagmaCongruence, 
##  IsRightMagmaCongruence, IsMagmaCongruence or IsSemigroupCongruence.
##
##  <part> is a list of lists containing (at least) all of the non singleton
##  blocks of the partition.  It is not checked that <part> is actually 
##  a congruence in the category specified.
##
InstallGlobalFunction( LR2MagmaCongruenceByPartitionNCCAT, 
function(F, part, category )

	local cong, fam;

	# The only cheap check we can do:
	if not IsElmsColls(FamilyObj(F), FamilyObj(part)) then
		Error("<part> should be a list of lists of elements of the magma");
	fi;

	# Create the equivalence relation
	fam :=  GeneralMappingsFamily( ElementsFamily(FamilyObj(F)),
    ElementsFamily(FamilyObj(F)) );
    
  # Create the default type for the elements.
  cong :=  Objectify(NewType(fam, 
    category and IsEquivalenceRelationDefaultRep), rec());
  SetSource(cong, F);
  SetRange(cong, F);
	SetEquivalenceRelationPartition(cong, part);

	return cong;
end);

#############################################################################
##
#M  LeftMagmaCongruenceByGeneratingPairs( <D>, <gens> )
#M  RightMagmaCongruenceByGeneratingPairs( <D>, <gens> )
#M  MagmaCongruenceByGeneratingPairs( <D>, <gens> )
##
InstallMethod( LeftMagmaCongruenceByGeneratingPairs,
    "for a magma and a list of pairs of its elements",
		IsElmsColls,
    [ IsMagma, IsList ], 0,
function( M, gens )
	return LR2MagmaCongruenceByGeneratingPairsCAT(M, gens, 
		IsLeftMagmaCongruence);
end );

InstallMethod( LeftMagmaCongruenceByGeneratingPairs,
    "for a magma and an empty list",
		true,
    [ IsMagma, IsList and IsEmpty ], 0,
function( M, gens )
	return LR2MagmaCongruenceByGeneratingPairsCAT(M, gens, 
		IsLeftMagmaCongruence);
end );

InstallMethod( RightMagmaCongruenceByGeneratingPairs,
    "for a magma and a list of pairs of its elements",
		IsElmsColls,
    [ IsMagma, IsList ], 0,
function( M, gens )
	return LR2MagmaCongruenceByGeneratingPairsCAT(M, gens, 
		IsRightMagmaCongruence);
end );

InstallMethod( RightMagmaCongruenceByGeneratingPairs,
    "for a magma and an empty list",
		true,
    [ IsMagma, IsList and IsEmpty ], 0,
function( M, gens )
	return LR2MagmaCongruenceByGeneratingPairsCAT(M, gens, 
		IsRightMagmaCongruence);
end );

InstallMethod( MagmaCongruenceByGeneratingPairs,
    "for a magma and a list of pairs of its elements",
		IsElmsColls,
    [ IsMagma, IsList ], 0,
function( M, gens )
	return LR2MagmaCongruenceByGeneratingPairsCAT(M, gens, 
		IsMagmaCongruence);
end );


InstallMethod( MagmaCongruenceByGeneratingPairs,
    "for a magma and an empty list",
		true,
    [ IsMagma, IsList and IsEmpty ], 0,
function( M, gens )
	return LR2MagmaCongruenceByGeneratingPairsCAT(M, gens, 
		IsMagmaCongruence);
end );

#############################################################################
##
#M  EquivalenceClasses( <E> )
##
##  For a MagmaCongruence - fastest to compute the partition
##
InstallMethod(EquivalenceClasses,
  "for magma congruences", true, [IsMagmaCongruence], 0,
function(e)
	local
			part, # the partition of the equivalence relation
			distinctreps; # the reprentatives of distinct cong classes


	part := EquivalenceRelationPartition(e);
	distinctreps := Concatenation(List(part, x->x[1]), 
		Filtered(UnderlyingDomainOfBinaryRelation(e), 
		x-> not x in Concatenation(part)));


	return List(distinctreps, x->EquivalenceClassOfElementNC(e, x));

end);



#############################################################################
##
#E

