#############################################################################
##
#W  semicong.gi                  GAP library    				Andrew Solomon
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains generic methods for semigroup congruences.
##
Revision.semicong_gi :=
    "@(#)$Id$";

######################################################################
##
#O  SemigroupCongruenceByGeneratingPairs(<semigroup>, <pairs>)
##  Special method for the case that the magma is a semigroup
##
######################################################################
InstallMethod( SemigroupCongruenceByGeneratingPairs,
    "for a semigroup and a list of pairs of its elements",
    IsElmsColls,
    [ IsSemigroup, IsList ], 0,
function( M, gens )
  local C;

  C := LR2MagmaCongruenceByGeneratingPairsCAT(M, gens, IsSemigroupCongruence);

  return C;
end );

InstallMethod( SemigroupCongruenceByGeneratingPairs,
    "for a semigroup and an empty list",
    true,
    [ IsSemigroup, IsList and IsEmpty], 0,
function( M, gens )
  local C;

  C := LR2MagmaCongruenceByGeneratingPairsCAT(M, gens, IsSemigroupCongruence);

  return C;
end );


#############################################################################
##
#M  \*( <x1>, <x2> )
##
##  Product of congruence classes. As in fp-semigroups we just
##  multiply without worrying about getting the representative right.
##  Then we check equality when doing < or =.
##
InstallMethod( \*,
    "for two semigroup congruence classes",
    IsIdenticalObj,
    [ IsCongruenceClass, IsCongruenceClass ],
    0,
function( x1, x2 )
  if EquivalenceClassRelation(x1) <> EquivalenceClassRelation(x2) then
    Error("Can only multiply classes of the same congruence");
  fi;
  return EquivalenceClassOfElementNC(EquivalenceClassRelation(x1),
    Representative(x1)*Representative(x2));
end );

############################################################################
##
#M  One(<congruence class>)
##
##  It is installed as 
##  OtherMethod to appease GAP since the selection filters
##  IsCongruenceClass and IsMultiplicativeElementWithOne
##  match two declarations of One - the first filter for domains,
##  the second filter for IsMultiplicativeElementWithOne.
##
InstallOtherMethod(One,
"One(<congruence class>)", true,
[IsCongruenceClass and IsMultiplicativeElementWithOne], 0,
function(x)
  return EquivalenceClassOfElement(EquivalenceClassRelation(x),
    One(Representative(x)));
end);


#############################################################################
##
#P  IsReesCongruence(<c>)
##
##  True precisely when the congruence has at most one
##  nonsingleton congruence class.
##
InstallMethod( IsReesCongruence,
    "for a semigroup congruence",
    true,
    [ IsSemigroupCongruence ], 0,
function( cong )
  # recall - the partition contains only nonsingleton blocks
  return Length(EquivalenceRelationPartition(cong)) in [0,1];
end);

InstallImmediateMethod(IsReesCongruence,
	IsSemigroupCongruence and HasEquivalenceRelationPartition, 0,
	function( c )
		return Size(EquivalenceRelationPartition(c)) = 1;
	end );




######################################################################
##
##  SemigroupCongruenceIteratorData(<cong>)
##
##  Return existing (or create new) iterator data for a 
##  semigroup congruence. 
##
######################################################################
BindGlobal("SemigroupCongruenceIteratorData",
function(cong)
	
	local
		# congruence generating pairs where the sides are distinct
		NontrivialPairs,				

		# elements whose congruence class is known to be nontrivial
		NonsingletonElements,

		Tree,		# The data structure we will store.
		i, 			# index into Tree.elements
		m,			# an actual element
		block;	# a set of elements




	# if it has already been created, return it.

	if IsBound(cong!.enumerator_data) then
		return cong!.enumerator_data;
	fi;

	# check that we know the generators ....
	if not HasGeneratingPairsOfMagmaCongruence(cong) then
		Error("SemigroupCongruenceIteratorData requires GeneratingPairsOfMagmaCongruence");
	fi;

	# if not (HasGeneratorsOfSemigroup(Source(cong)) or 
		# ( HasIsFinite(Source(cong)) and IsFinite(Source(cong)) )) then
		# Error("SemigroupCongruenceIteratorData requires generators for underlying semigroup or list of all elements");
	# fi;

	if not ((HasGeneratorsOfMagma(Source(cong)) or    
					 HasGeneratorsOfMagmaWithInverses(Source(cong))) or
					( HasIsFinite(Source(cong)) and IsFinite(Source(cong)) ))
	then
			Error("SemigroupCongruenceIteratorData requires generators",
						"for underlying semigroup or list of all elements");
	fi;
		

	# Create a new data structure.
	# When the data structure is closed, it will consist of a list of all 
	# elements which aren't in a singleton congruence class, together
	# with a tree consisting of indices (into the list) of elements 
	# which are related as branches.

	NontrivialPairs := 
			Filtered(GeneratingPairsOfMagmaCongruence(cong),
			x->x[1] <> x[2]);

	NonsingletonElements := Set(Concatenation(NontrivialPairs));

	

	
	Tree := rec(
		elts := NonsingletonElements, 
		# first connect every element to itself.
		parents:= [1 .. Length(NonsingletonElements)]);

	#if HasGeneratorsOfSemigroup(Source(cong)) then
		#Tree.generators := Set(GeneratorsOfSemigroup(Source(cong)));
	#else
		#Tree.generators := Elements(Source(cong));
	#fi;

	if HasGeneratorsOfMagma(Source(cong)) or
		 HasGeneratorsOfMagmaWithInverses(Source(cong)) then
			Tree.generators := Set(GeneratorsOfMagma(Source(cong)));
	else
			Tree.generators := Elements(Source(cong));
	fi;



	# Now set the list of unprocessed branches.
  Tree.unprocessed_branches := List(NontrivialPairs, 
			x->[Position(NonsingletonElements, x[1]), 
					Position(NonsingletonElements, x[2])]);

	# store it
	cong!.enumerator_data  := Tree;

	return Tree;
end);


#####################################################################
##
##  SemigroupCongruenceIteratorDataRootIndex(<cong>, <elt>)
##
##  The root index of the tree containing the element <elt>
##  in the tree representation of <cong> which may only be partial
##  at this stage.
##
##	If tree.elts doesn't contain m, then add it to the
##  end, make it its own parent and return that index.
##
####################################################################
BindGlobal("SemigroupCongruenceIteratorDataRootIndex",
function(cong, m)
	local
		tree,		# pointer to the iterator data
		i;			# index

	tree := SemigroupCongruenceIteratorData(cong);


	# return the root of the tree containing m;
	i := PositionProperty(tree.elts, x->x=m);

	if i = fail then
		Add(tree.elts, m);
		tree.parents[Length(tree.elts)] := Length(tree.elts);
		return  Length(tree.elts);
	fi;
	

	while tree.parents[i] <> i do
		i := tree.parents[i];
	od;

	return i;
end);




#####################################################################
##
##  SemigroupCongruenceIteratorDataBlock(<cong>, <elt>)
##
##  Return the block of <cong>  containing the element <elt>.
##  This does not assume the congruence has been closed so it
##  is not stored.
##  
##
####################################################################
BindGlobal("SemigroupCongruenceIteratorDataBlock",
function(cong, m)
	local
		tree,		# the iterator data
		mroot;	# The root of the  element m in tree

	tree := SemigroupCongruenceIteratorData(cong);

	mroot := SemigroupCongruenceIteratorDataRootIndex(cong, m);
	return Set(Filtered(tree.elts,
    x->SemigroupCongruenceIteratorDataRootIndex(cong, x) = mroot));

end);


#####################################################################
##
##  SemigroupCongruenceIteratorDataBlocks
##
##  turn the tree representation of the
##  congruence into a set of blocks of elements.
##
##  This does not assume the congruence has been closed so it
##  is not stored.
##
##  Only the nontrivial congruence classes will be represented
##
####################################################################
BindGlobal("SemigroupCongruenceIteratorDataBlocks",
function(cong)
	local rts, tree;

	tree := SemigroupCongruenceIteratorData(cong);

	# take the tree and write the elements in blocks according
	# to their connected components.

	# rts is the set of all roots
	rts := Set(List(tree.elts, 
		x->SemigroupCongruenceIteratorDataRootIndex(cong, x)));

	# return a list of lists. Each list is the set of elements with
	# this root.
	return List(rts, x->Filtered(tree.elts, 
		y->SemigroupCongruenceIteratorDataRootIndex(cong, y) = x));
end);



######################################################################
##
##  SemigroupCongruenceIteratorDataClosure(<cong>, <cond>)
##
##  <cong> is a semigroup congruence
##  <cond> is a boolean valued function on <cong>
##
##  Computes the partial closure of the congruence until either
##  condition <cond> is satisfied, or the congruence data
##  is completely closed.
##  Returns true iff <cond> becomes true. Otherwise
##  the enumeration is closed and the function returns false.
##
##  To find the full closure of the congruence, just call
##  SemigroupCongruenceIteratorDataClosure(<cong>,x->false);
##
##  The method used is to build a disjoint union of trees 
##  each representing a nontrivial congruence class,
##  by applying the Atkinson orbit algorithm under the action 
##  of the set of generators of the semigroup, or the set
##  of elements of the semigroup if the generators are not known.
##
######################################################################
BindGlobal("SemigroupCongruenceIteratorDataClosure",
function(cong, cond)

	local
		C,							# the unprocessed branches
										# not a copy! changing C changes the enumerator data

		x, y,						# two related elements
		rx, ry,					# the root of the tree containing x (resp. y)
		g,							# one of the generators
		wl, zl,					# x and y times g on left
		wr, zr, 				# x and y times g on right
		rl, sl, rr, sr, # roots of trees
		branch, 				# a pair of semigroup elements
		Tree;						# the enumerator data structure. Again, not a copy.

  ######################################################
  #
  # function proper
  #
	######################################################
	Tree := SemigroupCongruenceIteratorData(cong);
	C := Tree.unprocessed_branches;
	
	# Note: changing C changes the record in place.

  while not (cond(cong) or IsEmpty(C)) do
    branch := C[Length(C)]; # get the last unprocessed branch
    Unbind(C[Length(C)]); # and remove it from the list of unprocessed branches

    x := Tree.elts[branch[1]]; # the child
    y := Tree.elts[branch[2]]; # the parent
		rx := SemigroupCongruenceIteratorDataRootIndex(cong, x);
		ry := SemigroupCongruenceIteratorDataRootIndex(cong, y);

		if rx <> ry then
			Tree.parents[rx] := ry;
			Add(C, [rx, ry]);
		fi;

    for g in Tree.generators do
      wl := g*x; zl := g*y; #left cong
      wr := x*g; zr := y*g; #right cong

      rl := SemigroupCongruenceIteratorDataRootIndex(cong, wl);
      sl := SemigroupCongruenceIteratorDataRootIndex(cong, zl);

      if rl <> sl then
        Tree.parents[rl] := sl;
        Add(C, [rl, sl]);
      fi;

      # These need to be computed *after* the tree is modified
      # otherwise loops may arise.
      rr := SemigroupCongruenceIteratorDataRootIndex(cong, wr);
      sr := SemigroupCongruenceIteratorDataRootIndex(cong, zr);

      if rr <> sr then
        Tree.parents[rr] := sr;
        Add(C, [rr, sr]);
      fi;
    od;
  od;

	# it is possible that we have closed the congruence completely
	if IsEmpty(C) then
		SetEquivalenceRelationPartition(cong, 
			SemigroupCongruenceIteratorDataBlocks(cong));
	fi;


	if cond(cong) then 
		return true;
	else	
		return false;
	fi;
end);

######################################################################
##
##  EquivalenceRelationPartition(<cong>)
##  Calculate the partition attribute of a semigroup congruence
##
######################################################################

InstallMethod(EquivalenceRelationPartition,
    "for a for a two sided  congruence on a semigroup",
    true,
    [IsSemigroupCongruence], 0,
function(cong) # cong a congruence.
	
	# first close the congruence
	SemigroupCongruenceIteratorDataClosure(cong, x->false);

	# the value should now be stored
	return EquivalenceRelationPartition(cong);
end);


#############################################################################
##
#R  IsCongruenceClassEnumeratorRep( <R> )
##
DeclareRepresentation("IsCongruenceClassEnumeratorRep", 
IsAttributeStoringRep and IsComponentObjectRep, ["knownelts"]);


#############################################################################
##
#M  Enumerator( <C> )
##
##	Enumerator for a semigroup congruence class.
##
InstallMethod( Enumerator, "for a semigroup congruence class", true,
[IsCongruenceClass], 0,
function(class)
	local
		cong,		# the congruence of which class is a class
    enum;  # the enumerator

	cong := EquivalenceClassRelation(class);

  if not IsSemigroupCongruence(cong) then
    TryNextMethod();
  fi;

	# if the partition is already known, just go through the 
	# generic equivalence class method
	if HasEquivalenceRelationPartition(EquivalenceClassRelation(class)) then
		TryNextMethod();
	fi;

	enum  :=  Objectify(NewType(FamilyObj(class), IsCongruenceClassEnumeratorRep 
						and IsSemigroupCongruenceClassEnumerator), rec(knownelts :=  
						SemigroupCongruenceIteratorDataBlock(cong, Representative(class))));

	SetUnderlyingCollection( enum, class);

	return enum;
end);


#############################################################################
##
#M  \[\]( <E>, <n> )
##
##  Returns the <n>th element of a semigroup congruence class enumerator.
##  Set AsSSorted list for the collection when all elements have been
##  found.
##
InstallMethod( \[\], 
"for a semigroup congruence class enumerator", true,
	[IsCongruenceClassEnumeratorRep and IsSemigroupCongruenceClassEnumerator, 
        IsPosInt], 0,
function(enum, n)
	if not IsBound(enum[n]) then
		Error("Position ", n, " out of range.");
	fi;

	return enum!.knownelts[n];

end);

#############################################################################
##
#M  ImagesElm( <rel>, <elm> )  . . . for a  semigroup congruence
##  																	assume we can compute the partition
##
InstallMethod( ImagesElm,
    "for semigroup congruence and element",
    FamSourceEqFamElm,
    [ IsSemigroupCongruence, IsObject ], 0,
function( rel, elm )
  return Enumerator(EquivalenceClassOfElement(rel,elm));
end);



#############################################################################
##
#M  IsBound( list[i] ) 
##
##
InstallMethod( IsBound\[\],
"for a semigroup congruence class enumerator", true,
	[IsCongruenceClassEnumeratorRep and IsSemigroupCongruenceClassEnumerator, 
        IsPosInt], 0,
function(enum, n)
	local 
		able,		# are we able to find the nth element?
		class,	# the thing we're enumerating
		newelts,	# the new elements we find.
		cong;		# the congruence one of whose classes we're enumerating

	if n <= Length(enum!.knownelts) then
		return true;
	fi;

	class := UnderlyingCollection(enum);
	cong := EquivalenceClassRelation(class);

  able := SemigroupCongruenceIteratorDataClosure(cong,
    x->Length(SemigroupCongruenceIteratorDataBlock(x,
      Representative(class))) >= n);

	# Add on any new elements and return the 
	# one requested (if the list is now long enough).
	newelts := Set(Filtered(
		SemigroupCongruenceIteratorDataBlock(cong, 
		Representative(class)), x->(not x in enum!.knownelts)));

	Append(enum!.knownelts, newelts);

	if not able then
		# We now know we have the lot
		SetAsSSortedList(class, enum!.knownelts);
		SetAsSSortedList(enum, enum!.knownelts);
		return false;
	fi;


	return true;
end );

#############################################################################
##
#M  PrintObj( <smg cong> ) 
##
InstallMethod( PrintObj,
    "for a semigroup congruence",
    true,
    [ IsSemigroupCongruence ], 0,
    function( S )
    Print( "SemigroupCongruence( ... )" );
    end );

InstallMethod( PrintObj,
    "for a semigroup Congruence with known generating pairs",
    true,
    [ IsSemigroupCongruence and HasGeneratingPairsOfMagmaCongruence ], 0,
    function( S )
    Print( "SemigroupCongruence( ",
      GeneratingPairsOfMagmaCongruence( S ), " )" );
    end );


#############################################################################
##
#M  ViewObj( <smg cong> ) 
##
InstallMethod( ViewObj,
    "for a semigroup congruence",
    true,
    [ IsSemigroupCongruence ], 0,
    function( S )
    Print( "<semigroup congruence>" );
    end );

InstallMethod( ViewObj,
    "for a semigroup Congruence with known generating pairs",
    true,
    [ IsSemigroupCongruence and HasGeneratingPairsOfMagmaCongruence ], 0,
    function( S )
    Print( "<semigroup congruence with ",
      Length(GeneratingPairsOfMagmaCongruence( S )), " generating pairs>" );
    end );




#############################################################################
##
#E

