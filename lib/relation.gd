#############################################################################
##
#W  relation.gd                  GAP library                   Andrew Solomon
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the declarations for binary relations on sets.
##
Revision.relation_gd :=
    "@(#)$Id$";


#############################################################################
#1 
##  Mathematically, a relation on a set <X> is a subset of 
##  $X \times X$. In {\GAP} a *relation*  on <X> is a general mapping 
##  from <X> to itself. In fact, the category `IsBinaryRelation' is
##  the same as the category `IsEndoGeneralMapping'.
##
##  Of course, a binary relation can have the properties:
##  `IsReflexiveBinaryRelation', `IsTransitiveBinaryRelation' and
##  `IsSymmetricBinaryRelation'. When all three are true, we call
##  the relation an *equivalence relation*.
##

##  The hierarchy of concepts around binary relations on a set are:
##
##  IsGeneralMapping > 
## 
##  IsEndoGeneralMapping [ = IsBinaryRelation] >
##
##  [IsEquivalenceRelation] >
##
##  [IsLeftMagmaCongruence], [IsRightMagmaCongruence] >
##
##  [IsTwoSidedMagmaCongruence] =  
## 					IsEquivalenceRelation and RespectsMultiplication
##
##
#############################################################################

#############################################################################
##
## General Binary Relations
##
#############################################################################

#############################################################################
##
#C  IsBinaryRelation( <R> )
##
##  IsBinaryRelation(<R>) is true precisely when 
##  IsEndoGeneralMapping(<R>) is true. 
##  
##  
DeclareSynonym("IsBinaryRelation",IsEndoGeneralMapping);


#############################################################################
##
#F  BinaryRelationByListOfImages( <list> )
#F  BinaryRelationByListOfImagesNC( <list> )
##
##  Given a list of <n> lists, each containing elements in $\{1..\n\}$,
##  this function constructs a binary relation such that $1$ is realated
##  to <list>`[1]', $2$ to <list>`[2]' and so on.
##  By default, checks whether the list supplied is valid, though a NC
##  version exists.
##
DeclareGlobalFunction("BinaryRelationByListOfImages");
DeclareGlobalFunction("BinaryRelationByListOfImagesNC");

###############################################################################
##
#M
#A  ImagesListOfBinaryRelation( <R> )
##
##  Returns the list of images of a binary relation <R>.
##
DeclareAttribute("ImagesListOfBinaryRelation", IsGeneralMapping);


#############################################################################
##
#P  IsSymmetricBinaryRelation(<rel>)
#P  IsTransitiveBinaryRelation(<rel>)
#P  IsReflexiveBinaryRelation(<rel>)
##
##  Properties of binary relations.  Note that a reflexive binary
##  relation is necessarily total.
##
DeclareProperty("IsSymmetricBinaryRelation", IsBinaryRelation);
DeclareProperty("IsTransitiveBinaryRelation", IsBinaryRelation);
DeclareProperty("IsReflexiveBinaryRelation", IsBinaryRelation);
InstallTrueMethod(IsTotal, IsReflexiveBinaryRelation);

#############################################################################
##
## Equivalence Relations
##
#############################################################################

#############################################################################
##
#C  IsEquivalenceRelation( <Relation> )
##
##  An equivalence relation is a symmetric, transitive, reflexive
##  binary relation. 
## 
DeclareCategory("IsEquivalenceRelation", 
	IsTotal and IsBinaryRelation and IsSPGeneralMapping);

InstallTrueMethod(IsBinaryRelation, IsEquivalenceRelation);
InstallTrueMethod(IsReflexiveBinaryRelation, IsEquivalenceRelation);
InstallTrueMethod(IsTransitiveBinaryRelation, IsEquivalenceRelation);
InstallTrueMethod(IsSymmetricBinaryRelation, IsEquivalenceRelation);

#############################################################################
##
#A  EquivalenceRelationPartition(<equiv>)
##
##  EquivalenceRelationPartition returns a list of lists of elements.
##  The lists are precisely the nonsingleton equivalence classes.
##  This allows us to describe ``small'' equivalences on infinite sets.
##

##  This is installed using NewAttribute. 
##  SetEquivalenceRelationPartition is not the attribute setter but
##  a global function which sanitizes the input list, removing singleton
##  and empty lists before calling Setter(EquivalenceRelationPartition).
##  HasEquivalenceRelationPartition is just the tester.
##
BindGlobal("EquivalenceRelationPartition", 
	NewAttribute("EquivalenceRelationPartition", IsEquivalenceRelation));
DeclareGlobalFunction("SetEquivalenceRelationPartition");
BindGlobal("HasEquivalenceRelationPartition", 
	Tester(EquivalenceRelationPartition));


#############################################################################
##
#F  EquivalenceRelationByPartition( <domain>, <list> )
##
##  <domain> is the domain over which the relation is defined, and 
##  <list> is a list of lists, each of these is a list of elements
##  of <domain> which are related to each other.
##  <list> need only contain the nontrivial blocks 
##  and will ignore singletons.
## 
DeclareGlobalFunction("EquivalenceRelationByPartition");

#############################################################################
##
#F  EquivalenceRelationByProperty( <domain>, <property> )
##
##  Create an equivalence relation on <domain> whose only defining
##  data is having the property <property>.
## 
DeclareGlobalFunction("EquivalenceRelationByProperty");

#############################################################################
##
##  Some other creation functions which might be useful in the future
##
##  EquivalenceRelationByRelation( <rel> )
##  EquivalenceRelationByPairs( <set>,<list> )
##  EquivalenceRelationByFunction( <X>, <function> )
##
##  EquivalenceRelationByRelation(<rel>) - form the smallest equivalence 
##  relation containing <rel>.
##
##  EquivalenceRelationByPairs is the smallest equivalence relation 
##  such that every pair in the list is in the relation.
##
##  EquivalenceRelationByFunction - the function goes from 
##  $X  \times X \rightarrow $ {<true>, <false>}.

#############################################################################
##
#C  IsEquivalenceClass( <O> ) 
##
##  An equivalence class is a collection of elements which are mutually
##  related to each other in the associated equivalence relation. Note,
##  this is a special category of object and not just a list of elements.
##
DeclareCategory("IsEquivalenceClass",IsDomain and IsDuplicateFreeCollection); 

#############################################################################
##
#A  EquivalenceClassRelation(<C>) 
##
##  The equivalence relation of which <C> is a class.
##
DeclareAttribute("EquivalenceClassRelation", IsEquivalenceClass);

#############################################################################
##
#A  EquivalenceClasses(<rel>) 
##
##  A list of all equivalence classes of the equivalence relation <rel>.
##  Note, is is possible that different methods will yield the list
##  in a different order, so that for two equivalence relations
##  $c1$ and $c2$ we may have $c1 = c2$ but not 
##  $EquivalenceClasses(c1) = EquivalenceClasses(c2)$.
##
DeclareAttribute("EquivalenceClasses", IsEquivalenceRelation);

#############################################################################
##
#O  EquivalenceClassOfElement(<rel>,<elt>)
#O  EquivalenceClassOfElementNC(<rel>,<elt>)
##
##  The equivalence class of <elt> in <rel>. 
##  In the second form, it is not checked that <elt> is in the domain 
##  over which <rel> is defined.
##

DeclareOperation("EquivalenceClassOfElement", 
				[IsEquivalenceRelation, IsObject]);

DeclareOperation("EquivalenceClassOfElementNC", 
				[IsEquivalenceRelation, IsObject]);



#############################################################################
#E

