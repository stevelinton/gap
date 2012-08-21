#############################################################################
##
#W  relation.gi                  GAP library                   Andrew Solomon
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the implementation for binary relations on sets.
##
Revision.relation_gi :=
    "@(#)$Id$";

############################################################################
##
#R  IsBinaryRelationDefaultRep(<obj>)
##
DeclareRepresentation("IsBinaryRelationDefaultRep", 
	IsAttributeStoringRep ,[]);

############################################################################
##
#R  IsEquivalenceRelationDefaultRep(<obj>)
##
DeclareRepresentation("IsEquivalenceRelationDefaultRep", 
	IsAttributeStoringRep ,[]);

############################################################################
##
#M	UnderlyingDomainOfBinaryRelation
##
##	This is simply a synonym for the Source of the relation when
##	considered as a general mapping.
##
DeclareSynonym("UnderlyingDomainOfBinaryRelation",Source);

############################################################################
##
#F  BinaryRelationByListOfImages( <list> )
#F  BinaryRelationByListOfImagesNC( <list> )
##
InstallGlobalFunction(BinaryRelationByListOfImagesNC,
function( l )

    local n, fam, rel;

    n:= Length(l);
    fam:= GeneralMappingsFamily(FamilyObj(1), FamilyObj(1));
    rel:= Objectify(NewType(fam,
        IsBinaryRelation and IsBinaryRelationDefaultRep and
				IsNonSPGeneralMapping), rec());
    SetSource(rel, Domain([1..n]));
    SetRange(rel, Domain([1..n]));
    SetImagesListOfBinaryRelation(rel, List(l,x->AsSSortedList(x)));
    return rel;
end);

InstallGlobalFunction(BinaryRelationByListOfImages,
function( l )

    local n, flat;

    # Check to see if the given list is dense
    if not IsDenseList(l) then
        Error("List, ",l,",must be dense");
    fi;

    # Check to see if the list defines a relation on 1..n
    n:= Length(l);
    flat:= Flat(l);
    if not ForAll(flat,x->x in [1..n]) then
        Error("List ,", l,", does not represent a binary relation on 1 .. n");
    fi;

    return BinaryRelationByListOfImagesNC(l);
end);



#############################################################################
##
#M  ImagesElm( <rel>, <n> )
##
##  For binary relations over [1..n] represented as a list of images
##
InstallMethod(ImagesElm, "for binary relations over [1..n] with images list", 
    true, [IsBinaryRelation and HasImagesListOfBinaryRelation, IsPosInt], 0,
function( rel, n )
    return ImagesListOfBinaryRelation(rel)[n];
end);

#############################################################################
##
#M  PreImagesElm( <rel>, <n> )
##
##  For binary relations over [1..n] represented as a list of images
##
InstallMethod(PreImagesElm, "for binary rels over [1..n] with images list", 
    true, [IsBinaryRelation and HasImagesListOfBinaryRelation, IsPosInt], 0,
function( rel, n )
    local i, imslist, preims;

    imslist:= ImagesListOfBinaryRelation(rel);
    preims:= [];
    for i in [1..Length(imslist)] do
        if n in imslist[i] then
            Add(preims, i);
        fi;
    od;
    return preims;
end);

#############################################################################
##
#M  ImagesListOfBinaryRelation( <rel> )
##
##  Returns the list of images of a binary relation.   If the underlying
##  domain of the relation is not [1..n] then an error is signalled.
##
InstallMethod(ImagesListOfBinaryRelation, "for a generic relation", true,
    [IsGeneralMapping], 0,
function(r)
    local dom, eldom, i, ims;

	if not IsEndoGeneralMapping(r) then
		Error(r, " is not a binary relation!");
	fi;

    dom:= UnderlyingDomainOfBinaryRelation(r);
		eldom := AsSSortedList(dom);
    if not IsRange(eldom) or eldom[1] <> 1 then
        Error("Operation only makes sense for relations over [1..n]");
    fi;

    ims:= [];
    # n:= Length(dom);
    for i in eldom do
        Add(ims, ImagesElm(r, i));
    od;
    return ims;
end);

#############################################################################
##
#M  \= ( <rel1>, <rel2> )
##
##  For binary relations over [1..n] represented as a list of images
##
InstallMethod( \=, "for binary relss over [1..n] with images list", true,
    [IsBinaryRelation and HasImagesListOfBinaryRelation,
    IsBinaryRelation and HasImagesListOfBinaryRelation], 0,
function(rel1, rel2)
    return ImagesListOfBinaryRelation(rel1) 
        = ImagesListOfBinaryRelation(rel2);
end);

#############################################################################
##
#M  \in ( <tup>, <rel> )
##
##  For binary relations over [1..n] represented as a list of images
##
InstallMethod( \in, "for binary rels over [1..n] with images list", true,
    [IsList, IsBinaryRelation and HasImagesListOfBinaryRelation], 0,
function( tup, rel )
    if Length(tup) <> 2 then
        Error("List ", tup, " must be of length 2");
    fi;

    return tup[2] in ImagesListOfBinaryRelation(rel)[tup[1]];
end);

#############################################################################
##
#F  EquivalenceRelationByPartition( <set>, <list> )
##
##
InstallGlobalFunction(EquivalenceRelationByPartition,
function(X, subsX)
	local fam, rel;


	# make sure there are no repititions
	if not IsSet(AsSortedList(Concatenation(subsX))) then
		Error("Input does not describe a partition");
	fi;

  #check that subsX is contained in X
	if not  (IsSubset(X, AsSortedList(Concatenation(subsX)))) then
		Error("Input does not describe a partition");
	fi;
	
	fam :=  GeneralMappingsFamily( ElementsFamily(FamilyObj(X)), 
		ElementsFamily(FamilyObj(X)) );


	# Create the default type for the elements.
  rel :=  Objectify(NewType(fam, 
		IsEquivalenceRelation and IsEquivalenceRelationDefaultRep), rec());
	SetEquivalenceRelationPartition(rel, subsX);
	SetSource(rel, X);
	SetRange(rel, X);

	return rel;
end);


#############################################################################
##
#F  EquivalenceRelationByProperty( <domain>, <property> )
##
##  Create an equivalence relation on <domain> whose only defining
##  data is having the property <property>.
##
InstallGlobalFunction(EquivalenceRelationByProperty,
function(X, property )
	local fam, rel;
	
	fam :=  GeneralMappingsFamily( ElementsFamily(FamilyObj(X)), 
		ElementsFamily(FamilyObj(X)) );

	# Create the default type for the elements.
  rel :=  Objectify(NewType(fam, 
		IsEquivalenceRelation and IsEquivalenceRelationDefaultRep), rec());
	SetSource(rel, X);
	SetRange(rel, X);
	Setter(property)(rel, true);

	return rel;
end);


#############################################################################
##
#F  SetEquivalenceRelationPartition(<equiv>, <part>)
##
##  This establishes a canonical form for EquivalenceRelationPartitions
##  so that if two equivalence relations are equal, they have the same 
##  partition. Also results in \< being consistent for equivalence relations.
##

InstallGlobalFunction(SetEquivalenceRelationPartition,
function(equiv, part)
	if not (IsEquivalenceRelation(equiv) and IsList(part)) then
		Error("usage: SetEquivalenceRelationPartition(<rel>, <list>)");
	fi;

	# first, make each part of the partition a  set
	part := List(part,AsSSortedList);

	# now make all of part a set (strictly order the parts, no duplicates)
	part := AsSSortedList(part);

	# now strip out the singletons and empties
	part := AsSSortedList(Filtered(part, x->Length(x) > 1));

	# finally, set the value
	Setter(EquivalenceRelationPartition)(equiv, part);


	# just strip out the singletons (and empties!)
	# Setter(EquivalenceRelationPartition)(equiv, 
	# 		AsSet(Filtered(part, x->Length(x) > 1)));
	
	
end);


#############################################################################
##
#M      \=	. .      . . . for equivalence relations 
##
InstallMethod(\=, "for eq relations", IsIdenticalObj,
        [IsEquivalenceRelation, IsEquivalenceRelation], 0,
function(x, y)
	if Source(x) <> Source(y) then
		return false;
	fi;
	if (HasEquivalenceRelationPartition(x) and 
		HasEquivalenceRelationPartition(y)) then
			return EquivalenceRelationPartition(x) = EquivalenceRelationPartition(y);
	else
		TryNextMethod();
	fi;
end);

#############################################################################
##
#R	IsEquivalenceClassDefaultRep( <M> )
#M	EquivalenceClassRelation( <C> )
##
##	The default representation for equivalence classes will be to store its
##	underlying relation, and a single canonical element of the class.
##	Representation specific methods are installed here.
##
DeclareRepresentation("IsEquivalenceClassDefaultRep", IsAttributeStoringRep
	and IsComponentObjectRep, rec());


#############################################################################
##
#M	EquivalenceClassOfElement( <R>, <rep> )
#M	EquivalenceClassOfElementNC( <R>, <rep> )
##
##	Returns the equivalence class of an element <rep> with respect to an
##	equivalence relation <R>.   No calculation is performed at this stage.
##	We do not always wish to check that <rep> is in the underlying set
##	of <R>, since we may wish to use equivalence relations to perform
##	membership tests (for example when checking membership of a
##	transformation in a monoid, we use Greens relations and classes).
##
InstallMethod(EquivalenceClassOfElementNC, "no check", true,
	[IsEquivalenceRelation, IsObject], 0,
function(rel, rep)

	local new;

	if IsMagmaCongruence(rel) then
		if IsMultiplicativeElementWithOne(rep) then
			new:= Objectify(NewType(CollectionsFamily(FamilyObj(rep)),
				IsCongruenceClass and IsEquivalenceClassDefaultRep 
				and IsMultiplicativeElementWithOne), rec());
		else
			new:= Objectify(NewType(CollectionsFamily(FamilyObj(rep)),
				IsCongruenceClass and IsEquivalenceClassDefaultRep 
				and IsMultiplicativeElement), rec());
		fi;
	else
		new:= Objectify(NewType(CollectionsFamily(FamilyObj(rep)),
			IsEquivalenceClass and IsEquivalenceClassDefaultRep), rec());
	fi;
	SetEquivalenceClassRelation(new, rel);
	SetRepresentative(new, rep);
	SetParent(new, UnderlyingDomainOfBinaryRelation(rel));
	return new;
end);

InstallMethod(EquivalenceClassOfElement, "with checking", true,
	[IsEquivalenceRelation, IsObject], 0,
function(rel, rep)

	if not rep in UnderlyingDomainOfBinaryRelation(rel) then
		Error("Representative must lie in underlying set of the relation");
	fi;

	return EquivalenceClassOfElementNC(rel, rep);
end);

#############################################################################
##
#M	PrintObj( <C> )
##
##	Display an equivalence class.
##
InstallMethod(PrintObj, "for an eq. class", true,
	[IsEquivalenceClass],0,
function(c)
	Print("{", Representative(c),"}");
end);

#############################################################################
##
#M	\in( <T>, <R> )
##
##	Checks whether a 2-tuple is contained in a relation.   Implementation
##	for an equivalence relation stored as a partition.
##
##  This method should be selected over all others since it assumes
##  that the partition information has already been computed.
##  It has been given a +1 rank which WILL NEED TUNING when  the 
##  other methods are in.
##
InstallMethod(\in, "for eq relation with partition", true,
	[IsList, IsEquivalenceRelation and HasEquivalenceRelationPartition], 1,
function(tup, rel)

	local part, i;

	if Length(tup) <> 2 then 
		Error("Left hand side must be of length 2");
	elif FamilyObj(tup) <> 
			FamilyObj(UnderlyingDomainOfBinaryRelation(rel)) then
		Error("Left hand side must contain elements of relation's domain");
	fi;

	part:= EquivalenceRelationPartition(rel);
	for i in [1..Length(part)] do
		if tup[1] in part[i] then
			if tup[2] in part[i] then
				return true;
			else
				return false;
			fi;
		fi;
	od;
end);

#############################################################################
##
#M  \in( <x>, <C> )
##
##  Checks whether <x> is contained in the equivalence class <C>
##  If <C> is infinite, this will not necessarily terminate.
##
InstallMethod(\in, "for element and equivalence class", true,
  [IsObject, IsEquivalenceClass], 0,
function(x, C)

  local
    iter;       # iterator of the equivalence class


  # first ensure that <x> is in the right family
  if FamilyObj(x) <>
    ElementsFamily(FamilyObj(Source(EquivalenceClassRelation(C)))) then
      Error("incompatible arguments for \in");
  fi;

  # now just enumerate the elements of <C> until we come to <x>
  iter := Iterator(C);
  while not IsDoneIterator(iter) do
    if x = NextIterator(iter) then
      return true;
    fi;
  od;
  return false;
end);

#############################################################################
##
#M  \= ( <C1>, <C2> )
##
##  Equality of equivalence classes
##
InstallMethod(\=, "for two equivalence classes",
IsIdenticalObj,
[IsEquivalenceClass,
IsEquivalenceClass], 0,
function(x, y)
  return Representative(x) in y;
end);

#############################################################################
##
#M  Enumerator( <C> )
##
##  An enumerator for equivalence classes of relations where we have
##  the partition.
##
InstallMethod( Enumerator, "for equivalence classes", true,
  [IsEquivalenceClass], 0,
function( C )

	local
			rel,			# relation for which C is a class
			block, 	# the block where we find rep
			rep;			# an element of C


	rel := EquivalenceClassRelation(C);

	if not HasEquivalenceRelationPartition(rel) then
		TryNextMethod();
	fi;

	rep := Representative(C);

	block := First(EquivalenceRelationPartition(rel), x->rep in x);
	# the singleton case - singleton blocks aren't stored
	if block = fail then
		return [rep];
	fi;
	return Enumerator(block);
end);

#############################################################################
##
#M  \<( <x1>, <x2> )
##
##  The total order on equivalence classes used for creating sets, etc.
##  Relies on the total order of the underlying set. This is a 
##  VERY INEFFICIENT method because it relies on finding the smallest
##  element of an equivalence class. AVOID USING THIS IF POSSIBLE!!
##
##
InstallMethod( \<,
    "for two equivalence classes",
    IsIdenticalObj,
    [ IsEquivalenceClass, IsEquivalenceClass ],
    0,
    function( x1, x2 )
			return RepresentativeSmallest(x1) < RepresentativeSmallest(x2);
    end );

#############################################################################
##
#M  EquivalenceClasses( <E> ) 
##
##	Wraparound function which calls the two-argument method
##
InstallMethod(EquivalenceClasses, 
	"wraparound to call 2-argument version", true, [IsEquivalenceRelation], 0,
		e->EquivalenceClasses(e, UnderlyingDomainOfBinaryRelation(e)));

#############################################################################
##
#M  EquivalenceClasses( <E>, <C> )
##
##	Returns the list of equivalence classes of an equivalence relation.
##	This generic method will not terminate for an equivalence over an
##	infinite set.
##
InstallOtherMethod(EquivalenceClasses, "for a generic equivalence relation", 
	true, [IsEquivalenceRelation, IsCollection], 0,
function(E, D)

	local classes, iter, elm;

	# We iterate over the underlying domain, and build up the list
	# of classes as new ones are found.
	iter:= Iterator(D);

	classes:= [];
	for elm in iter do
		if ForAll(classes, x->not elm in x) then
			Add(classes, EquivalenceClassOfElementNC(E, elm));
		fi;
	od;
	return classes;
end);

#############################################################################
##
#M  ImagesRepresentative( <rel>, <elm> )  . . . for equivalence relations
##
InstallMethod( ImagesRepresentative,
    "equivalence relations",
    FamSourceEqFamElm,
    [ IsEquivalenceRelation, IsObject ], 0,
function( map, elm )
	return elm;
end);



#############################################################################
##
#M  PreImagesRepresentative( <rel>, <elm> )  . . . for equivalence relations
##
InstallMethod( PreImagesRepresentative,
    "equivalence relations",
    FamRangeEqFamElm,
    [ IsEquivalenceRelation, IsObject ], 0,
function( map, elm )
	return elm;
end);

#############################################################################
##
#M  ImagesElm( <rel>, <elm> )  . . . for equivalence relations
##
InstallMethod( ImagesElm,
    "equivalence relations",
    FamSourceEqFamElm,
    [ IsEquivalenceRelation, IsObject ], 0,
function( rel, elm )
	return Enumerator(EquivalenceClassOfElement(rel,elm));
end);


#############################################################################
##
#M  PreImagesElm( <rel>, <elm> )  . . . for equivalence relations
##
InstallMethod( PreImagesElm,
    "equivalence relations",
    FamRangeEqFamElm,
    [ IsEquivalenceRelation, IsObject ], 0,
function( rel, elm )
	return Enumerator(EquivalenceClassOfElement(rel,elm));
end);


#############################################################################
##
#M  PrintObj( <eqr> ) . . . . . . . . . . . . . . . for equivalence relation
##
InstallMethod( PrintObj,
    "for an equivalence relation",
    true,
    [ IsEquivalenceRelation ], 0,
    function( map )
    Print( "<equivalence relation on ", Source( map ), " >" );
    end );




#############################################################################
##
#E
