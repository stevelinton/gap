#############################################################################
##
#W  ctblfuns.gd                 GAP library                     Thomas Breuer
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the definition of categories of class functions,
##  and the corresponding properties, attributes, and operations.
##
Revision.ctblfuns_gd :=
    "@(#)$Id$";

#T TODO:

#T AsClassFunction( <tbl>, <psi> )
#T (regard as class function of factor group or of a downward extension)


#############################################################################
##
#C  IsClassFunction( <obj> )
##
##  A *class function* (in characteristic $p$) of a finite group $G$ is a map
##  from the set of ($p$-regular) elements in $G$ to the cyclotomics that is
##  constant on conjugacy classes of $G$.
##
##  There are (at least) two reasons why class functions in {\GAP} are *not*
##  implemented as mappings.
##  First, we want to distinguish class functions in different
##  characteristics, for example to be able to define the Frobenius character
##  of a given Brauer character; 
##  viewed as mappings, the trivial characters in all characteristics coprime
##  to the order of $G$ are equal.
##  Second, the product of two class functions shall be again a class
##  function, whereas the product of general mappings is defined as
##  composition.
##
##  Each class function is an immutable list,
##  and also a ring element.
##  (Note that we want to form, e.g., groups of linear characters.)
##  The product of two class functions of the same group in the same
##  characteristic is again a class function;
##  in this respect, class functions behave differently from their
##  values lists.
##
##  Each class function knows its underlying character table.
##
##  Two class functions are equal if they have the same underlying
##  character table and the same class function values.
##
DeclareCategory( "IsClassFunction",
    IsRingElementWithOne and IsCommutativeElement and IsAssociativeElement
        and IsHomogeneousList and IsScalarCollection and IsFinite );


#############################################################################
##
#C  IsClassFunctionWithGroup( <obj> )
##
##  A class function that knows about an underlying group can be asked for
##  its kernel, centre, inertia subgroups etc.
##
##  Note that the class function knows the underlying group only via its
##  character table.
##  
DeclareCategory( "IsClassFunctionWithGroup", IsClassFunction );


#############################################################################
##
#C  IsClassFunctionCollection( <obj> )
##
DeclareCategoryCollections( "IsClassFunction" );


#############################################################################
##
#C  IsClassFunctionWithGroupCollection( <obj> )
##
DeclareCategoryCollections( "IsClassFunctionWithGroup" );


#############################################################################
##
#C  IsClassFunctionFamily( <obj> )
##
DeclareCategoryFamily( "IsClassFunction" );


#############################################################################
##
#A  ClassFunctionFamily( <tbl> )
##
##  is the family of all class functions of the character table <tbl>.
##
DeclareAttribute( "ClassFunctionFamily", IsNearlyCharacterTable );


#############################################################################
##
#A  UnderlyingCharacterTable( <psi> )
##
##  The family of class functions stores the value in its component
##  `underlyingCharacterTable'.
##  (This belongs to the defining data of the class function <psi>.)
##
DeclareAttribute( "UnderlyingCharacterTable", IsClassFunction );


#############################################################################
##
#A  ValuesOfClassFunction( <psi> ) . . . . . . . . . . . . . . list of values
##
##  is the list of values of the class function <psi>, the $i$-th entry
##  being the value on the $i$-th conjugacy class of the underlying
##  character table.
##
##  This belongs to the defining data of the class function <psi>.
##
DeclareAttribute( "ValuesOfClassFunction", IsClassFunction );


#############################################################################
##
#P  IsVirtualCharacter( <chi> )
##
##  A virtual character is a class function that can be written as the
##  difference of proper characters.
##
DeclareProperty( "IsVirtualCharacter", IsClassFunction );


#############################################################################
##
#P  IsCharacter( <chi> )
##
DeclareProperty( "IsCharacter", IsClassFunction );


#############################################################################
##
#P  IsIrreducibleCharacter( <chi> )
##
DeclareProperty( "IsIrreducibleCharacter", IsClassFunction );


#############################################################################
##
#M  IsVirtualCharacter( <chi> ) . . . . . . . . . . . . . . . for a character
##
##  Each character is of course a virtual character.
##
InstallTrueMethod( IsVirtualCharacter, IsCharacter );


#############################################################################
##
#A  CentreOfCharacter( <psi> )
#A  CenterOfCharacter( <psi> )
##
##  is the centre of the character <psi>,
##  as a subgroup of the underlying group of <psi>.
##
DeclareAttribute( "CentreOfCharacter",
    IsClassFunctionWithGroup and IsCharacter );

DeclareSynonym( "CenterOfCharacter", CentreOfCharacter );


#############################################################################
##
#O  CentreChar( <psi> )
##
##  is the list of positions of classes forming the centre of the character
##  <chi> of the ordinary character table <tbl>.
#T  for one argument?
#T  then why not attribute
##
DeclareOperation( "CentreChar", [ IsClassFunction and IsCharacter ] );


#############################################################################
##
#A  ConstituentsOfCharacter( <psi> )
##
##  is the set of irreducible characters that occur in the decomposition of
##  the (virtual) character <psi> with nonzero coefficient.
##
DeclareAttribute( "ConstituentsOfCharacter", IsClassFunction );


#############################################################################
##
#A  DegreeOfCharacter( <psi> )
##
##  is the value of the character <psi> on the identity element.
##
DeclareAttribute( "DegreeOfCharacter", IsClassFunction and IsCharacter );


#############################################################################
##
#O  InertiaSubgroup( <G>, <psi> )
##
##  For a (not necessarily irreducible) character <psi> of the group $H$
##  and a group <G> that contains $H$ as a normal subgroup,
##  `InertiaSubgroup' returns the largest subgroup of <G> that leaves <psi>
##  invariant under conjugation action.
##  In other words, `InertiaSubgroup' returns the group of all those elements
##  <g> in <G> that satisfy `<chi>^<g> = <chi>'.
##
DeclareOperation( "InertiaSubgroup", [ IsGroup, IsClassFunctionWithGroup ] );


#############################################################################
##
#A  KernelOfCharacter( <psi> )
##
##  is the kernel of any representation of the underlying group of the
##  character <psi> affording the character <psi>.
##
DeclareAttribute( "KernelOfCharacter",
    IsClassFunctionWithGroup and IsCharacter );


#############################################################################
##
#A  KernelChar( <psi> )
##
##  is the list of positions of those conjugacy classes that form the kernel
##  of the character <psi>, that is, those positions with character value
##  equal to the character degree.
##
DeclareAttribute( "KernelChar", IsClassFunction and IsCharacter );


#############################################################################
##
#A  TrivialCharacter( <tbl> )
#A  TrivialCharacter( <G> )
##
##  is the trivial character of the group <G> or its character table
##  <tbl>.
##
DeclareAttribute( "TrivialCharacter", IsNearlyCharacterTable );


#############################################################################
##
#A  NaturalCharacter( <G> )
##
##  If <G> is a permutation group then `NaturalCharacter' returns the
##  character of the natural permutation representation of <G> on the set of
##  moved points.
##
##  If <G> is a matrix group in characteristic zero then `NaturalCharacter'
##  returns the character of the natural matrix representation of <G>.
##
DeclareAttribute( "NaturalCharacter", IsGroup );


#############################################################################
##
#O  PermutationCharacter( <G>, <U> )
##
##  is the permutation character of the operation of the group <G> on the
##  cosets of its subgroup <U>.
##  The $i$-th position contains the  value of the permutation character on
##  the $i$-th conjugacy class of <G> (see "ConjugacyClasses").
##  
##  The value of the *permutation character* of <U> in <G> on a class $c$ of
##  <G> is the number of right cosets invariant under the action of an
##  element of $c$.
##
##  To compute the permutation character of a *transitive permutation group*
##  <G> on the cosets of a point stabilizer <U>,
##  the attribute `NaturalCharacter( <G> )' can be used instead of
##  `PermutationCharacter( <G>, <U> )'.
##
DeclareOperation( "PermutationCharacter", [ IsGroup, IsGroup ] );


#T  declare also for other new method !


#############################################################################
##
#F  CycleStructureClass( <permchar>, <class> )
##
##  Let <permchar> be a permutation character, and <class> the position of a
##  conjugacy class of the character table of <permchar>.
##  `CycleStructureClass' returns the cycle structure of the elements in
##  class <class> in the underlying permutation representation.
##
DeclareGlobalFunction( "CycleStructureClass" );


#############################################################################
##
#O  ClassFunctionByValues( <tbl>, <values> )
##
##  Note that the characteristic of the class function is determined by
##  <tbl>.
##
DeclareOperation( "ClassFunctionByValues",
    [ IsNearlyCharacterTable, IsHomogeneousList ] );


#############################################################################
##
#O  VirtualCharacterByValues( <tbl>, <values> )
##
DeclareOperation( "VirtualCharacterByValues",
    [ IsNearlyCharacterTable, IsHomogeneousList ] );


#############################################################################
##
#O  CharacterByValues( <tbl>, <values> )
##
DeclareOperation( "CharacterByValues",
    [ IsNearlyCharacterTable, IsHomogeneousList ] );


#############################################################################
##
#F  ClassFunctionSameType( <tbl>, <chi>, <values> )
##
##  is the class function $\psi$ of the table <tbl>
##  (in particular of same characteristic as <tbl>)
##  with values list <values>.
##
##  If <chi> is a virtual character then $\psi$ is a virtual character,
##  if <chi> is a character then $\psi$ is a character.
##
##  (<chi> need *not* be a class function of <tbl>.)
##
DeclareGlobalFunction( "ClassFunctionSameType" );


#############################################################################
##
#A  CentralCharacter( <psi> )
##
DeclareAttribute( "CentralCharacter", IsClassFunction and IsCharacter );


#############################################################################
##
#O  CentralChar( <tbl>, <psi> )
##
##  is the list of values of the central character corresp. to the character
##  <chi> of the ordinary character table <tbl>.
##
DeclareOperation( "CentralChar", [ IsNearlyCharacterTable, IsCharacter ] );


#############################################################################
##
#A  DeterminantOfCharacter( <psi> )
##
DeclareAttribute( "DeterminantOfCharacter",
    IsClassFunction and IsCharacter );


##############################################################################
##
#O  DeterminantChar( <tbl>, <chi> )
##
##  is the list of values of the determinant of the character <chi>
##  of the ordinary character table <tbl>.
##  This is defined to be the character obtained on taking the determinant of
##  representing matrices of a representation affording <chi>.
##
DeclareOperation( "DeterminantChar",
    [ IsNearlyCharacterTable, IsVirtualCharacter ] );


#############################################################################
##
#O  EigenvaluesChar( <tbl>, <char>, <class> )
##
##  Let $M$ be a matrix of a representation affording the character <char>,
##  for a group element in the <class>-th conjugacy class of <tbl>.
##
##  `EigenvaluesChar( <tbl>, <char>, <class> )' is the list of length
##  `$n$ = orders[ <class> ]' where at position `k' the multiplicity
##  of `E(n)^k = $e^{\frac{2\pi i k}{n}$' as eigenvalue of $M$ is stored.
##
##  We have `<char>[ <class> ] = List( [ 1 .. <n> ], k -> E(n)^k )
##                               * EigenvaluesChar( <tbl>, <char>, <class> ).
##
DeclareOperation( "EigenvaluesChar",
    [ IsNearlyCharacterTable, IsCharacter, IsPosInt ] );


#############################################################################
##
#O  RestrictedClassFunction( <chi>, <H> )
#O  RestrictedClassFunction( <chi>, <tbl> )
##
##  is the restriction of the $G$-class function <chi> to the subgroup
##  or downward extension <H> of $G$. 
##
DeclareOperation( "RestrictedClassFunction",
    [ IsClassFunction, IsGroup ] );


DeclareSynonym( "InflatedClassFunction", RestrictedClassFunction );


#############################################################################
##
#O  RestrictedClassFunctions( <chars>, <H> )
#O  RestrictedClassFunctions( <chars>, <tbl> )
##
##  is the restrictions of the $G$-class functions <chars> to the
##  subgroup or downward extension <H> of $G$. 
##
#O  RestrictedClassFunctions( <tbl>, <subtbl>, <chars> )
#O  RestrictedClassFunctions( <tbl>, <subtbl>, <chars>, <specification> )
#O  RestrictedClassFunctions( <chars>, <fusionmap> )
##
##  is the list of indirections of <chars> from <tbl> to <subtbl> by a fusion
##  map.  This map can either be entered directly as <fusionmap>, or it must
##  be stored on the table <subtbl>; in the latter case the value of the
##  `specification' field may be specified.
##
DeclareOperation( "RestrictedClassFunctions",
    [ IsClassFunctionCollection, IsGroup ] );


DeclareSynonym( "InflatedClassFunctions", RestrictedClassFunctions );


#############################################################################
##
#O  InducedClassFunction( <chi>, <G> )
#O  InducedClassFunction( <chi>, <tbl> )
##
##  is the class function obtained on induction of <chi> to <G>.
##
DeclareOperation( "InducedClassFunction", [ IsClassFunction, IsGroup ] );


#############################################################################
##
#O  InducedClassFunctions( <chars>, <G> )
#O  InducedClassFunctions( <chars>, <tbl> )
##
##  is the list of class function obtained on induction of the class
##  functions in the list <chars> to <G>.
##
#O  InducedClassFunctions( <subtbl>, <tbl>, <chars> )
#O  InducedClassFunctions( <subtbl>, <tbl>, <chars>, <specification> )
#O  InducedClassFunctions( <subtbl>, <tbl>, <chars>, <fusionmap> )
##
##  induces <chars> from <subtbl> to <tbl>.
##  The fusion map can either be entered directly as <fusionmap>,
##  or it must be stored on the table <subtbl>;
##  in the latter case the value of the `specification' field may be
##  specified.
##
##  Note that <specification> must not be a list!
##
DeclareOperation( "InducedClassFunctions",
    [ IsClassFunctionCollection, IsGroup ] );


#############################################################################
##
#O  ReducedClassFunctions( <ordtbl>, <constituents>, <reducibles> )
#O  ReducedClassFunctions( <ordtbl>, <reducibles> )
##
##  is a record with components `remainders' and `irreducibles', both lists
##
##  Let `rems' be the set of nonzero characters obtained from <reducibles>
##  by subtraction of
##  $\sum_{j}
##   \frac{'ScalarProduct( <ordtbl>, <reducibles>[i], <constituents>[j]}
##        {'ScalarProduct( <ordtbl>, <constituents>[j], <constituents>[j]}
##            \cdot <constituents>[j]$
##  from `<reducibles>[i]'.
##
##  Let `irrs' be the list of irreducible characters in `rems'.
##
##  We reduce `rems' with `irrs' and all found irreducibles until no new
##  irreducibles are found.
##  Then `irreducibles' is the set of all found irreducible characters,
##  `remainders' is the set of all nonzero remainders.
##
##  The class functions in <constituents> and <reducibles> are assumed to
##  be virtual characters.
##
#T why not to allow a projection into the orthogonal space of <constituents>?
#T (<constituents> would have to be irreducibles then)
##  
DeclareOperation( "ReducedClassFunctions",
    [ IsOrdinaryTable, IsHomogeneousList, IsHomogeneousList ] );

DeclareSynonym( "Reduced", ReducedClassFunctions );
#T compatibility with GAP-3


#############################################################################
##
#O  ReducedCharacters( <ordtbl>, <constituents>, <reducibles> )
##
##  like `Reduced', but <constituents> and <reducibles> are known to be
##  proper characters of <ordtbl>, so only those scalar products must be
##  formed where the degree of the constituent is not bigger than the
##  degree of the reducibles character.
##
DeclareOperation( "ReducedCharacters",
    [ IsOrdinaryTable, IsHomogeneousList, IsHomogeneousList ] );

DeclareSynonym( "ReducedOrdinary", ReducedCharacters );
#T compatibility with GAP-3


#############################################################################
##
##  auxiliary operations
##

#############################################################################
##
#A  GlobalPartitionOfClasses( <tbl> )
##
##  Let <n> be the number of conjugacy classes of the character table <tbl>.
##  `GlobalPartitionOfClasses( <tbl> )' is a list of subsets of the range
##  `[ 1 .. <n> ]' that forms a partition of `[ 1 .. <n> ]'.
##  This partition is respected by each table automorphism of <tbl>
##  (see~"AutomorphismsOfTable");
##  *note* that also fixed points occur.
##
##  This is useful for the computation of table automorphisms.
##
##  Since group automorphisms induce table automorphisms, the partition is
##  also respected by the permutation group that occurs in the computation
##  of inertia groups and conjugate class functions.
##
##  If the group of table automorphisms is already known then its orbits
##  form the finest possible global partition.
##
##  Otherwise the subsets in the partition are the sets of classes with
##  same centralizer order and same element order,
##  and --if more about the character table is known-- also with the same
##  number of $p$-th root classes, for all $p$ for which the power maps
##  are stored.
##
DeclareAttribute( "GlobalPartitionOfClasses", IsNearlyCharacterTable );


#############################################################################
##
#O  CorrespondingPermutations( <tbl>, <elms> )
#O  CorrespondingPermutations( <chi>, <elms> )
##
##  If the first argument is a character table <tbl> then the list of
##  permutations of conjugacy classes of <tbl> is returned
##  that are induced by the group elements in the list <elms>;
##  If an element of <elms> does *not* act on the classes of <tbl> then
##  either `fail' or a (meaningless) permutation is returned.
##
##  If the first argument is a class function <chi> then the returned
##  permutations will at least yield the same conjugate class functions as
##  the permutations induced by <elms>,
##  that is, the images are not necessarily computed for orbits on which
##  <chi> is constant.
##
DeclareOperation( "CorrespondingPermutations",
    [ IsOrdinaryTable, IsHomogeneousList ] );
DeclareOperation( "CorrespondingPermutations",
    [ IsClassFunction, IsHomogeneousList ] );


##############################################################################
##
#A  NormalSubgroupClassesInfo( <tbl> )
##
##  Let <tbl> be the ordinary character table of the group $G$.
##  Many computations for group characters of $G$ involve computations
##  in normal subgroups or factor groups of $G$.
##
##  In some cases the character table <tbl> is sufficient;
##  for example questions about a normal subgroup $N$ of $G$ can be answered
##  if one knows the conjugacy classes that form $N$,
##  e.g., the question whether a character of $G$ restricts
##  irreducibly to $N$.
##  But other questions require the computation of $N$ or
##  even more information, like the character table of $N$.
##
##  In order to do these computations only once, one stores in the group a
##  record with components to store normal subgroups, the corresponding lists
##  of conjugacy classes, and (if necessary) the factor groups, namely
##
##  \beginitems
##  `nsg': &
##      list of normal subgroups of $G$, may be incomplete,
##
##  `nsgclasses': &
##      at position $i$, the list of positions of conjugacy
##      classes of <tbl> forming the $i$-th entry of the `nsg' component,
##
##  `nsgfactors': &
##      at position $i$, if bound, the factor group
##      modulo the $i$-th entry of the `nsg' component.
##  \enditems
##
##  The functions
##
##     `NormalSubgroupClasses',
##     `FactorGroupNormalSubgroupClasses', and
##     `ClassesOfNormalSubgroup'
##
##  use these components, and they are the only functions that do this.
##
##  So if you need information about a normal subgroup for that you know the
##  conjugacy classes, you should get it using `NormalSubgroupClasses'.  If
##  the normal subgroup was already used it is just returned, with all the
##  knowledge it contains.  Otherwise the normal subgroup is added to the
##  lists, and will be available for the next call.
##
##  For example, if you are dealing with kernels of characters using the
##  `KernelOfCharacter' function you make use of this feature
##  because `KernelOfCharacter' calls `NormalSubgroupClasses'.
##
DeclareAttribute( "NormalSubgroupClassesInfo", IsOrdinaryTable, "mutable" );


##############################################################################
##
#F  ClassesOfNormalSubgroup( <tbl>, <N> )
##
##  is the list of positions of conjugacy classes of the character table
##  <tbl> that are contained in the normal subgroup <N>
##  of the underlying group of <tbl>.
##
DeclareGlobalFunction( "ClassesOfNormalSubgroup" );


##############################################################################
##
#F  NormalSubgroupClasses( <tbl>, <classes> )
##
##  returns the normal subgroup of the underlying group $G$ of the ordinary
##  character table <tbl>
##  that consists of those conjugacy classes of <tbl> whose positions are in
##  the list <classes>.
##
##  If `NormalSubgroupClassesInfo( <tbl> ).nsg' does not yet contain
##  the required normal subgroup,
##  and if `NormalSubgroupClassesInfo( <tbl> ).normalSubgroups' is bound then
##  the result will be identical to the group in
##  `NormalSubgroupClassesInfo( <tbl> ).normalSubgroups'.
##
DeclareGlobalFunction( "NormalSubgroupClasses" );


##############################################################################
##
#F  FactorGroupNormalSubgroupClasses( <tbl>, <classes> )
##
##  is the factor group of the underlying group $G$ of the ordinary character
##  table <tbl> modulo the normal subgroup of $G$ that consists of those
##  conjugacy classes of <tbl> whose positions are in the list <classes>.
##
DeclareGlobalFunction( "FactorGroupNormalSubgroupClasses" );


#############################################################################
##
#O  MatScalarProducts( <tbl>, <characters1>, <characters2> )
#O  MatScalarProducts( <tbl>, <characters> )
##
##  The first form returns the matrix of scalar products:
##
##  $'MatScalarProducts( <tbl>, <characters1>, <characters2> )[i][j]' =
##  `ScalarProduct( <tbl>, <characters1>[j], <characters2>[i] )'$,
##
##  the second form returns a lower triangular matrix of scalar products:
##
##  $'MatScalarProducts( <tbl>, <characters> )[i][j]' =
##  `ScalarProduct( <tbl>, <characters>[j], <characters>[i] )'$ for
##  $ j \leq i $.
##  
DeclareGlobalFunction( "MatScalarProducts" );


##############################################################################
##
#F  OrbitChar( <chi>, <linear> )
##
##  is the orbit of the character values list <chi> under the action of
##  Galois automorphisms and multiplication with the linear characters in
##  the list <linear>.
##
##  It is assumed that <linear> is closed under Galois automorphisms and
##  tensoring.
##  (This means that we can first form the orbit under Galois action, and
##  then apply the linear characters to all Galois conjugates.)
##
DeclareGlobalFunction( "OrbitChar" );


##############################################################################
##
#F  OrbitsCharacters( <irr> )
##
##  is a list of orbits of the characters <irr> under the action of
##  Galois automorphisms and multiplication with linear characters.
##
DeclareGlobalFunction( "OrbitsCharacters" );


##############################################################################
##
#F  OrbitRepresentativesCharacters( <irr> )
##
##  is a list of representatives of the orbits of the characters <irr>
##  under the action of Galois automorphisms and multiplication with linear
##  characters.
##
DeclareGlobalFunction( "OrbitRepresentativesCharacters" );


#############################################################################
##
#M  IsFiniteDimensional( <classfuns> )
##
##  Spaces of class functions are always finite dimensional.
##
InstallTrueMethod( IsFiniteDimensional,
    IsFreeLeftModule and IsClassFunctionCollection );


#############################################################################
##
#E

