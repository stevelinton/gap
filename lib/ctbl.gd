#############################################################################
##
#W  ctbl.gd                     GAP library                     Thomas Breuer
#W                                                           & Goetz Pfeiffer
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the definition of categories of character table like
##  objects, and their properties, attributes, operations, and functions.

#1
##  It seems to be necessary to state some basic facts --and maybe warnings--
##  at the beginning of the character theory  package.  This holds for people
##  who  are  familiar  with  character theory  because there  is  no  global
##  reference on  computational  character  theory,  although  there are many
##  papers  on  this  topic,  like~\cite{NPP84}  or~\cite{LP91}.   It  holds,
##  however, also for people who are familiar with {\GAP} because the general
##  concept of domains (see Chapter~"Domains") plays no  important  role here
##  --we  will justify this later in this section.
##
##  Intuitively, *characters* (or more generally, *class functions*) of a
##  finite group $G$ can be thought of as certain mappings defined on $G$,
##  with values in the complex number field;
##  the set of all characters of $G$ forms a semiring, with both addition
##  and multiplication defined pointwise, which is naturally embedded into
##  the ring of *generalized* (or *virtual*) *characters* in the natural way.
##  A {\Z}--basis of this ring, and also a vector space basis of the complex
##  vector space of class functions, is given by the irreducible characters.
##
##  At this stage one could ask where there is a problem, since all these
##  algebraic structures are supported by {\GAP}.
##  But in practice, these structures are of minor importance,
##  compared to individual characters and the *character tables* themselves
##  (which are not domains in the sense of {\GAP}).
##
##  For computations with characters of a finite group $G$ with $n$ conjugacy
##  classes, say, we fix an ordering of the classes, and then identify each
##  class with its position according to this ordering.
##  Each character of $G$ can be represented by a list of length $n$ where at
##  the $i$--th position the character value for elements of the $i$--th
##  class is stored.
##  Note that we do not need to know the conjugacy classes of $G$ physically,
##  even our knowledge of $G$ may be implicit in the sense that, e.g.,
##  we know how many classes of involutions $G$ has, and which length these
##  classes have, but we never have seen an element of $G$, or a presentation
##  or representation of $G$.
##  This allows us to work with the character tables of very large groups,
##  e.g., of the so--called monster, where {\GAP} has (currently) no chance
##  to deal with the group.
##
##  As a consequence, also other information involving characters is given
##  implicitly.  For example, we can talk about the kernel of a character not
##  as a group but as a list of classes (more exactly: a list of their
##  positions according to the chosen ordering of classes) forming this
##  kernel; we can deduce the group order, the contained cyclic subgroups
##  and so on, but we do not get the group itself.
##
##  So typical calculations with characters and character tables involve
##  loops over the lists of character values.
##  For  example, the scalar product of two characters $\chi$, $\psi$ of $G$
##  given by
##  $$
##     [\chi,\psi] = \frac{1}{|G|} \sum_{g\in G} \chi(g) \psi(g^{-1})
##  $$
##  can be written as
##  \begintt
##      Sum( [ 1 .. n ], i -> SizesConjugacyClasses( t )[i] * chi[i]
##                                * ComplexConjugate( psi[i] ) );
##  \endtt
##  where `t' is the character table of $G$, and `chi', `psi' are the lists
##  of values of $\chi$, $\psi$, respectively.
##
##  It is one of the advantages of character theory that after one has
##  translated a problem concerning groups into a problem concerning
##  only characters, the necessary calculations are mostly simple.
##  For example, one can often prove that a group is a Galois group over the
##  rationals using calculations with structure constants that can be
##  computed from the character table,
##  and informations on (the character tables of) maximal subgroups.
##  When one deals with such questions,
##  the translation back to groups is just an interpretation by the user,
##  it does not take place in {\GAP}.
##
##  {\GAP} uses character tables to store information such as class
##  lengths, element orders, the irreducible characters of $G$ etc.~in a
##  consistent way; note that the values of these attributes rely on the
##  chosen ordering of conjugacy classes.
##
##  Two more important instances of such information are *power maps* and
##  *fusion maps*, both are represented as lists of integers in {\GAP}.
##  The $k$--th power map maps each class to the class of $k$--th powers
##  of its elements, the corresponding list contains at each position the
##  position of the image.
##  A subgroup fusion map between the classes of a subgroup $H$ of $G$ and
##  the classes of $G$ maps each class $c$ of $H$ to that class of $G$ that
##  contains $c$, the corresponding list contains again the positions of
##  image classes.
##  (If we know only the character tables of the two groups then
##  in general the class fusion depends on the embedding of $H$ into $G$.)
##
##  So class functions, power maps, and fusion maps are represented by lists
##  in {\GAP}, they are regarded as class functions etc.~of an appropriate
##  character table when they are passed to {\GAP} functions that expect
##  class functions etc.
##  For example, a list with all entries equal to 1 is regarded as the
##  trivial character if it is passed to a function that expects a character.
##  Note that class functions need not be plain lists,
##  for the sake of elegance and efficiency one can construct class functions
##  that store their underlying character table and other attribute values
##  (see~"Class Functions").
##
##

#2
##  (about incomplete tables!)
##
##  For character tables that do *not* store an underlying group,
##  there is no notion of generation, contrary to all {\GAP} domains.
##  Consequently, the correctness or even the consistency of such a character
##  table is hard to decide.
##  Nevertheless, one may want to work with incomplete character tables or
##  hypothetical tables which are, strictly speaking, not character tables
##  but shall be handled like character tables.
##  In such cases, one often has to set attribute values by hand;
##  no need to say that one must be very careful then.

#3
##  For a character table with underlying group,
##  the interface between table and group consists of two parts,
##  namely the *conjugacy classes* stored in the table
##  and the *identification* of the conjugacy classes of table and group.
##
##  The former is the value of the attribute `ConjugacyClasses' for the
##  character table,
##  the ordering of all those lists stored in the table that are related to
##  the orderering of conjugacy classes (such as sizes of centralizers and
##  conjugacy classes, orders of representatives, power maps,
##  and all class functions)
##  refer to the ordering of this list, *not* to the ordering of conjugacy
##  classes in the underlying group.
##
##  The latter is a list ...
##  
##
Revision.ctbl_gd :=
    "@(#)$Id$";


#############################################################################
##
#T TODO:
##
#T introduce fusion objects!
##
#T `CharTable' produces HUGE amounts of garbage
#T (e.g., for `SolvableGroup( "Q8+Q8" )' compute all tables for normal
#T subgroups; it is a big difference with what initial workspace GAP was
#T started ...)


#############################################################################
##
#V  InfoCharacterTable
##
DeclareInfoClass( "InfoCharacterTable" );


#############################################################################
##
##  1. categories and families of character tables
##

#############################################################################
##
#C  IsNearlyCharacterTable( <obj> )
#C  IsCharacterTable( <obj> )
#C  IsOrdinaryTable( <obj> )
#C  IsBrauerTable( <obj> )
#C  IsCharacterTableInProgress( <obj> )
##
##  Every ``character table like object'' in {\GAP} lies in the category
##  `IsNearlyCharacterTable'.
##  There are four important subcategories,
##  namely the *ordinary* tables in `IsOrdinaryTable',
##  the *Brauer* tables in `IsBrauerTable',
##  the union of these two, in `IsCharacterTable',
##  and the *incomplete ordinary* tables in `IsCharacterTableInProgress'.
##
##  We want to distinguish ordinary and Brauer tables because Brauer tables
##  may delegate tasks to the underlying ordinary table, for example the
##  computation of power maps.
##
##  Furthermore, `IsOrdinaryTable' and `IsBrauerTable' denote
##  tables that provide enough information to compute all power maps
##  and irreducible characters (and in the case of Brauer tables to get the
##  ordinary table), for example because the underlying group is known
##  or because the table is a library table.
##  We want to distinguish these tables from those of partially known
##  ordinary tables that cannot be asked for all power maps or all
##  irreducible characters.
##
##  The latter ``table like objects'' are in `IsCharacterTableInProgress'.
##  These are first of all *mutable* objects.
##  So *nothing is stored automatically* on such a table,
##  since otherwise one has no control of side-effects when
##  a hypothesis is changed.
##  Operations for such tables may return more general values than for
##  other tables, for example a power map may be a multi-valued mapping.
##
##  Several attributes for groups are valid also for their character tables.
##  These are on one hand those that have the same meaning and can be read
##  off respectively computed from the character table (think of tables or
##  incomplete tables that have no access to a group), such as `Size',
##  `Irr', `IsAbelian'.
##
##  On the other hand, there are attributes whose meaning for character
##  tables is different from the meaning for groups, such as
##  `SizesCentralizers', `SizesConjugacyClasses', and
##  `OrdersClassRepresentatives'.

##  @change here!@

# Let us discuss the example `OrdersClassRepresentatives',
# although there are a few other instances of the problem.
# 
# This attribute is useful for character tables,
# since library tables need not know the conjugacy classes themselves.
# Introducing the attribute for groups seemed natural.
# Moreover, this fits into the method selection process in the sense that
# a known `OrdersClassRepresentatives' value for a group
# (which might be caused by the fact that the user has stored the
# library table of the group, and the `OrdersClassRepresentatives' value
# of the table has been transferred to the group)
# may be used in a call of `ConjugacyClasses'.
# It does *not* fit into the method selection process in the sense
# that the values of `OrdersClassRepresentatives' and `ConjugacyClasses'
# *must* be compatible.
# 
# Solution 1 would be possible for groups but not for character tables,
# since for example the columns of ATLAS tables of central extensions
# and automorphism groups are not ordered w.r.t. increasing element order.
# Solution 2 would indeed make `OrdersClassRepresentatives' useless,
# at least using it for `ConjugacyClasses' would not be possible.
# 
# Solution 3 would be clean, but probably not easy to understand;
# I suppose we would need to make `ConjugacyClasses' a plain function
# that does the necessary consistency manipulations, to add an
# attribute for the final value, and to have an operation whose methods
# are allowed to return the classes in any ordering -- is this desirable?
# And do we really want to force/guarantee `ConjugacyClasses' to obey
# certain consistency rules?
# 
# One way out would be to define `OrdersClassRepresentatives' only for
# character tables,
# and to declare the attribute `ConjugacyClasses' for character tables
# in such a way that the value is consistent with other attribute values
# of the tables.
# When `ConjugacyClasses' for a group wants to take advantage from
# information in the known character table, only `HasCharacterTable'
# can be used by some method, and this method has to return if no
# useful information is stored there.
# 
# This would leave the situation for groups as flexible as it is now;
# for example, currently it may happen that the identity element does
# not lie in the first class of the `ConjugacyClasses' list,
# which is explicitly forbidden for character tables.

##  In the case of ordinary character tables, these attributes mean
##  information relative to the *conjugacy classes stored in the table*,
##  in the case of Brauer tables in characteristic $p$ they refer to the
##  $p$-regular conjugacy classes.
##
##  It should be emphasized that the value of the attribute
##  `ConjugacyClasses' for a character table and its underlying group may
##  be different w.r.t. ordering of the classes.
##  One reason for this is that otherwise we would not be allowed to
##  use a library table as character table of a group for which the
##  conjugacy classes are known already.
##  (Another, less important reason is that we can use the same group as
##  underlying group of tables that differ only w.r.t. the ordering of
##  classes.)
##
##  Attributes and properties that are *defined* for groups but are valid
##  also for tables:
##
##  For an ordinary character table with underlying group, the group has
##  priority over the table, i.e., if the table is asked for `Irr( <tbl> )',
##  say, it may delegate this task to the group, but if the group is asked
##  for `Irr( <G> )', it must not ask its table.

#T no!!

##  Only if a group knows its ordinary table and if this table knows the
##  value of an attribute then the group may fetch this value from its
##  ordinary character table.
##
##  The same principle holds for the data that refer to each other in the
##  group and in the table.
##
#T problem:
#T if the table knows already class lengths etc.,
#T the group may fetch them;
#T but if the conjugacy classes of the group are not yet computed,
#T how do we guarantee that the classes are in the right succession
#T when they are computed later???
#T Note that the classes computation may take advantage of the known
#T distribution of orders, power maps etc.
#T (Or shall such a notification of a known table for a group be handled
#T more restrictive, e.g., only via explicit assignments?)
##
##  Conversely, if an attribute is defined for character tables but is valid
##  also for groups (for example `TrivialCharacter'), the group may ask the
##  table but the table must not ask the group.
##  The same holds also for operations, e.g., `InducedClassFunction'.
##
DeclareCategory( "IsNearlyCharacterTable", IsObject );
DeclareCategory( "IsCharacterTable", IsNearlyCharacterTable );
DeclareCategory( "IsOrdinaryTable", IsCharacterTable );
DeclareCategory( "IsBrauerTable", IsCharacterTable );
DeclareCategory( "IsCharacterTableInProgress", IsNearlyCharacterTable );
#T was: and IsMutable !!


#############################################################################
##
#V  NearlyCharacterTablesFamily
##
##  All character table like objects belong to the same family.
##
BindGlobal( "NearlyCharacterTablesFamily",
    NewFamily( "NearlyCharacterTablesFamily", IsNearlyCharacterTable ) );


#############################################################################
##
#P  IsSimpleCharacterTable( <tbl> )
##
##  is `true' if the underlying group of the character table <tbl> is
##  simple.
##
DeclareProperty( "IsSimpleCharacterTable", IsNearlyCharacterTable );


#############################################################################
##
#P  IsSolvableCharacterTable( <tbl> )
##
##  is `true' if the underlying group of the character table <tbl> is
##  solvable.
##
DeclareProperty( "IsSolvableCharacterTable", IsNearlyCharacterTable );


#############################################################################
##
#F  IsPSolvableCharacterTable( <tbl>, <p> )
#o  IsPSolvableCharacterTableOp( <tbl>, <p> )
#a  ComputedIsPSolvableCharacterTables( <tbl> )
##
KeyDependentFOA( "IsPSolvableCharacterTable",
    IsNearlyCharacterTable, IsPosInt, "prime" );


#############################################################################
##
#V  SupportedOrdinaryTableInfo
#V  SupportedBrauerTableInfo
##
##  are used to create ordinary or Brauer character tables from records.
##  The most important applications are the construction of library tables
##  and the construction of derived tables (direct products, factors etc.)
##  by library functions.
##
##  `SupportedOrdinaryTableInfo' is a list that contains at position $2i-1$
##  an attribute getter function, and at position $2i$ the name of this
##  attribute.
##  This allows one to set components with these names as attribute values.
##
##  Supported attributes that are not contained in the list as initialized
##  below must be created using `DeclareAttributeSuppCT'.
##
BindGlobal( "SupportedOrdinaryTableInfo", [
    IsSimpleCharacterTable,       "IsSimpleCharacterTable", # is a property
    ] );
#T what about classtext?

BindGlobal( "SupportedBrauerTableInfo",
    ShallowCopy( SupportedOrdinaryTableInfo ) );


#############################################################################
##
#F  DeclareAttributeSuppCT( <name>, <filter> )
#F  DeclareAttributeSuppCT( <name>, <filter>, "mutable" )
##
BindGlobal( "DeclareAttributeSuppCT", function( arg )
    local attr, name, nname;

    # Make the attribute as `DeclareAttribute' does.
    attr:= CallFuncList( NewAttribute, arg );
    name:= arg[1];
    BIND_GLOBAL( name, attr );
    nname:= "Set"; APPEND_LIST_INTR( nname, name );
    BIND_GLOBAL( nname, SETTER_FILTER( attr ) );
    nname:= "Has"; APPEND_LIST_INTR( nname, name );
    BIND_GLOBAL( nname, TESTER_FILTER( attr ) );

    # Do the additional magic.
    Append( SupportedOrdinaryTableInfo, [ attr, arg[1] ] );
    Append( SupportedBrauerTableInfo, [ attr, arg[1] ] );
end );


#############################################################################
##
##  2. operations for groups that concern characters and character tables
##

#############################################################################
##
#F  CharacterDegrees( <G>, <p> )
#F  CharacterDegrees( <G> )
#F  CharacterDegrees( <tbl> )
##
##  In the first two forms, `CharacterDegrees' returns a collected list of
##  the degrees of the absolutely irreducible characters of the group <G>,
##  in characteristic <p> respectively zero.
##
##  In the third form, `CharacterDegrees' returns a collected list of the
##  degrees of the absolutely irreducible characters of the (ordinary or
##  Brauer) character table <tbl>.
##
DeclareGlobalFunction( "CharacterDegrees" );


#############################################################################
##
#A  CharacterDegreesAttr( <G> )
#A  CharacterDegreesAttr( <tbl> )
##
##  `CharacterDegreesAttr' is the attribute for storing the character degrees
##  computed by `CharacterDegrees'.
##
#O  CharacterDegreesOp( <G>, <p> )
##
##  is the operation called by `CharacterDegrees' for that methods can be
##  installed.
##

DeclareAttribute( "CharacterDegreesAttr", IsGroup );

InstallIsomorphismMaintenance( CharacterDegreesAttr,
    IsGroup and HasCharacterDegreesAttr, IsGroup );

DeclareOperation( "CharacterDegreesOp", [ IsGroup, IsInt ] );


#############################################################################
##
#O  CharacterTable( <G> ) . . . . . . . . . . ordinary char. table of a group
#O  CharacterTable( <G>, <p> )  . . . . . characteristic <p> table of a group
#O  CharacterTable( <ordtbl>, <p> )
#O  CharacterTable( <name> )  . . . . . . . . . library table with given name
##
##  Called with a group <G>, `CharacterTable' calls the attribute
##  `OrdinaryCharacterTable'.
##  Called with first argument a group <G> or an ordinary character table
##  <ordtbl>, and second argument a prime <p>, `CharacterTable' calls
##  the operation `BrauerCharacterTable'.
##  Called with a string <name>, `CharacterTable' delegates to
##  `CharacterTableFromLibrary'.
##
DeclareOperation( "CharacterTable", [ IsGroup, IsInt ] );


#############################################################################
##
#A  OrdinaryCharacterTable( <G> ) . . . . . . . . . . . . . . . . for a group
#A  OrdinaryCharacterTable( <modtbl> )  . . . .  for a Brauer character table
##
##  `OrdinaryCharacterTable' returns the ordinary character table of the
##  group <G> respectively of the Brauer character table <modtbl>.
##  If <modtbl> has no underlying group stored then the value of
##  `OrdinaryCharacterTable' must be stored already.)
##
DeclareAttribute( "OrdinaryCharacterTable", IsGroup );

Append( SupportedBrauerTableInfo, [
    OrdinaryCharacterTable, "OrdinaryCharacterTable",
    ] );


#############################################################################
##
#F  BrauerCharacterTable( <ordtbl>, <p> )
#O  BrauerCharacterTableOp( <ordtbl>, <p> )
#A  ComputedBrauerCharacterTables( <ordtbl> ) . . . . . . known Brauer tables
##
#F  BrauerCharacterTable( <G>, <p> )
##
##  `BrauerCharacterTable' returns the <p>-modular character table of the
##  ordinary character table <ordtbl>.
##  If the first argument is a group <G>, `BrauerCharacterTable' delegates
##  to the ordinary character table of <G>.
##
##  The Brauer tables that are computed already by `BrauerCharacterTable'
##  are stored using the attribute `ComputedBrauerCharacterTables'.
##  Methods for the computation of Brauer tables can be installed for
##  the operation `BrauerCharacterTableOp'.
##
##  The `\\mod' operator for a character table and a prime is defined to
##  delegate to `BrauerCharacterTable'.
##
DeclareGlobalFunction( "BrauerCharacterTable" );

DeclareOperation( "BrauerCharacterTableOp", [ IsOrdinaryTable, IsPosInt ] );

DeclareAttribute( "ComputedBrauerCharacterTables",
    IsOrdinaryTable, "mutable" );

#T candidate for FOA ?


#############################################################################
##
#F  CharacterTableRegular( <tbl>, <p> ) .  table consist. of <p>-reg. classes
##
##  preconstructor for the <p>-modular Brauer table of the ordinary character
##  table <tbl>,
##  used by the operation `BrauerCharacterTableOp' that should be called by
##  the user.
##
DeclareGlobalFunction( "CharacterTableRegular" );


#############################################################################
##
#A  Irr( <ordtbl> )
#A  Irr( <modtbl> )
#A  Irr( <G> )
##
##  In the first two forms, `Irr' returns the list of all complex ordinary
##  absolutely irreducible characters of the finite group <G>, respectively
##  of the ordinary character table <ordtbl>.
##
##  In the third form, `Irr' returns the absolutely irreducible Brauer
##  characters of the Brauer character table <modtbl>.
##  (Note that `IBr' is just a function that is defined for two arguments,
##  a group and a prime;
##  Called with a Brauer table, `IBr' calls `Irr'.)
#T  no longer necessary!!
##
##  (`Irr' may delegate back to the group <G>.)
#T  no!
##
DeclareAttributeSuppCT( "Irr", IsGroup );


#############################################################################
##
#F  IBr( <G>, <p> )
#F  IBr( <modtbl> )
##
##  `IBr' returns the list of <p>-modular absolutely irreducible Brauer
##  characters of the group <G>.
##  (This is done by delegation to `Irr' for the Brauer table in question.)
##
##  If the only argument is a Brauer character table <modtbl>,
##  `IBr' calls `Irr( <modtbl> )'.
##  (`Irr' may delegate back to <G>.)
##
DeclareGlobalFunction( "IBr" );


#############################################################################
##
##  3. ...
##


#############################################################################
##
#A  UnderlyingCharacteristic( <tbl> )
#A  UnderlyingCharacteristic( <psi> )
##
##  For a character table or Brauer table <tbl>, ...
##
##  For a class function <psi>, this belongs to the defining data, and is
##  stored in the family of class functions.
##  (We cannot use the attribute `Characteristic' to denote this, since
##  of course each Brauer character is an element of characteristic zero
##  in the sense of {\GAP}.)
##
DeclareAttributeSuppCT( "UnderlyingCharacteristic",
    IsNearlyCharacterTable );


#############################################################################
##
#A  OrdersClassRepresentatives( <tbl> )
##
##  is a list of orders of representatives of conjugacy classes of the
##  character table <tbl>,
##  in the same ordering as the conjugacy classes of <tbl>.
##
DeclareAttributeSuppCT( "OrdersClassRepresentatives",
    IsNearlyCharacterTable );


#############################################################################
##
#A  SizesCentralizers( <tbl> )
##
##  is a list that stores at position $i$ the size of the centralizer of any
##  element in the $i$-th conjugacy class of the character table <tbl>.
##
DeclareAttributeSuppCT( "SizesCentralizers", IsNearlyCharacterTable );


#############################################################################
##
#A  SizesConjugacyClasses( <tbl> )
##
##  is a list that stores at position $i$ the size of the $i$-th conjugacy
##  class of the character table <tbl>.
##
DeclareAttributeSuppCT( "SizesConjugacyClasses", IsNearlyCharacterTable );


#############################################################################
##
#A  BlocksInfo( <modtbl> )
##
##  If <modtbl> is a Brauer character table then the value of `BlocksInfo'
##  is a list of (mutable) records, the $i$-th entry containing information
##  about the $i$-th block.
##  Each record has the following components.
##  \beginitems
##  `defect': &
##       the defect of the block,
##
##  `ordchars': &
##       the list of positions of the ordinary characters that belong to the
##       block, relative to `Irr( OrdinaryCharacterTable( <modtbl> ) )',
##
##  `modchars': &
##       the list of positions of the Brauer characters that belong to the
##       block, relative to `IBr( <modtbl> )'.
##  \enditems
##  Optional components are
##  \beginitems
##  `basicset': &
##       a list of positions of ordinary characters in the block whose
##       restriction to <modtbl> is maximally linearly independent,
##       relative to `Irr( OrdinaryCharacterTable( <modtbl> ) )',
##
##  `decmat': &
##       the decomposition matrix of the block,
##
##  `decinv': &
##       inverse of the decomposition matrix of the block, restricted to the
##       ordinary characters described by `basicset',
##
##  `brauertree': &
##       a list that describes the Brauer tree of the block,
##       in the case that the block is of defect $1$.
##  \enditems
##  The `decmat' components can be computed using `AddDecMats'.
##
#T  If <tbl> is an ordinary character table then ...
#T  (store `PrimeBlocks' info??
#T  operation with two arguments?)
##
DeclareAttributeSuppCT( "BlocksInfo", IsNearlyCharacterTable, "mutable" );


#############################################################################
##
#F  AddDecMats( <modtbl> )
##
##  stores decomposition matrices of all blocks in the `decmat' component
##  of each record in the `BlocksInfo' list of the Brauer table <modtbl>.
##
DeclareGlobalFunction( "AddDecMats" );


#############################################################################
##
#A  ClassPositionsOfNormalSubgroups( <ordtbl> )
#A  ClassPositionsOfMaximalNormalSubgroups( <ordtbl> )
##
##  Let <ordtbl> be the ordinary character table of the group $G$.
##  Every normal subgroup of $G$ is a union of conjugacy classes.
##
##  `ClassPositionsOfNormalSubgroups' returns the list of all position lists
##  of the normal subgroups of $G$,
##  `ClassPositionsOfMaximalNormalSubgroups' returns a list describing the
##  maximal normal subgroups of $G$.
##
##  The entries of the result lists are sorted according to increasing
##  length.
##
DeclareAttribute( "ClassPositionsOfNormalSubgroups", IsOrdinaryTable );

DeclareAttribute( "ClassPositionsOfMaximalNormalSubgroups",
    IsOrdinaryTable );


#############################################################################
##
#A  ClassesOfDerivedSubgroup( <ordtbl> )
##
DeclareAttribute( "ClassesOfDerivedSubgroup", IsOrdinaryTable );


#############################################################################
##
#O  ClassesOfNormalClosure( <ordtbl>, <classes> )
##
DeclareOperation( "ClassesOfNormalClosure",
    [ IsOrdinaryTable, IsHomogeneousList and IsCyclotomicCollection ] );


#############################################################################
##
#A  IrredInfo( <tbl> )
##
##  a list of records, the $i$-th entry belonging to the $i$-th irreducible
##  character.
##
##  Usual entries are
##  `classparam'
##
#T remove this, better store the info in the irred. characters themselves
#T (`IrredInfo' is used in `Display' and `\*' methods)
##
DeclareAttributeSuppCT( "IrredInfo", IsNearlyCharacterTable, "mutable" );


#############################################################################
##
#A  ClassParameters( <tbl> )
##
DeclareAttributeSuppCT( "ClassParameters", IsNearlyCharacterTable );


#############################################################################
##
#A  ClassPermutation( <tbl> )
##
##  is a permutation $\pi$ of classes of <tbl>.
##  Its meaning is that class fusions into <tbl> that are stored on other
##  tables must be followed by $\pi$ in order to describe the correct
##  fusion.
##
##  This attribute is bound only if <tbl> was obtained from another table
##  by permuting the classes (commands `CharacterTableWithSortedClasses' or
##  `SortedCharacterTable').
##  It is necessary because the original table and the sorted table have the
##  same identifier, and hence the same fusions are valid for the two tables.
##
DeclareAttributeSuppCT( "ClassPermutation", IsNearlyCharacterTable );


#############################################################################
##
#A  ClassNames( <tbl> )
##
#T allow class names (optional) such as in the ATLAS ?
##
DeclareAttribute( "ClassNames", IsNearlyCharacterTable );


#############################################################################
##
#A  DisplayOptions( <tbl> )
##
#T is a more general attribute?
##
DeclareAttribute( "DisplayOptions", IsNearlyCharacterTable );


#############################################################################
##
#A  Identifier( <tbl> )
##
##  is a string that identifies the character table <tbl> in the current
##  {\GAP} session.
##  It is used mainly for class fusions into <tbl> that are stored on other
##  character tables.
##  For character tables without group,
##  the identifier is also used to print the table;
##  this is the case for library tables,
##  but also for tables that are constructed as direct products, factors
##  etc.~involving tables that may store their groups.
##
DeclareAttributeSuppCT( "Identifier", IsNearlyCharacterTable );


#############################################################################
##
#V  LARGEST_IDENTIFIER_NUMBER
##
##  Character table identifiers computed by {\GAP} are strings of the form
##  `\"CT#<n>\"', where <n> is a positive integer.
##  `LARGEST_IDENTIFIER_NUMBER' is the largest integer <n> used in the
##  current {\GAP} session.
##
#T  Note that one must be very careful when it becomes possible to read
#T  character tables from files!!
#T  (signal warnings then?)
##
BindGlobal( "LARGEST_IDENTIFIER_NUMBER", 1 );


#############################################################################
##
#A  InfoText( <tbl> )
##
##  is a string with information about <tbl>.
##
DeclareAttributeSuppCT( "InfoText", IsNearlyCharacterTable );


#############################################################################
##
#A  InverseClasses( <tbl> )
##
DeclareAttribute( "InverseClasses", IsNearlyCharacterTable );


#############################################################################
##
#A  Maxes( <tbl> )
##
##  is a list of identifiers of the tables of all maximal subgroups of <tbl>.
##  This is known usually only for library tables.
#T meaningful also for tables with group?
##
DeclareAttributeSuppCT( "Maxes", IsNearlyCharacterTable );


#############################################################################
##
#A  NamesOfFusionSources( <tbl> )
##
##  is the list of identifiers of all those tables that are known to have
##  fusions into <tbl> stored.
##
DeclareAttributeSuppCT( "NamesOfFusionSources",
    IsNearlyCharacterTable, "mutable" );


#############################################################################
##
#A  AutomorphismsOfTable( <tbl> )
##
DeclareAttributeSuppCT( "AutomorphismsOfTable", IsNearlyCharacterTable );
#T use `GlobalPartitionClasses' in `TableAutomorphisms' ?
#T AutomorphismGroup( <tbl> ) ??


#############################################################################
##
#O  Indicator( <tbl>, <n> )
#O  Indicator( <tbl>, <characters>, <n> )
#O  Indicator( <modtbl>, 2 )
##
##  If <tbl> is an ordinary character table then `Indicator' returns the
##  list of <n>-th Frobenius-Schur indicators of <characters>
##  or `Irr( <tbl> )'.
##
##  If <tbl> is a Brauer table in characteristic $\not= 2$, and $<n> = 2$
##  then `Indicator' returns the second indicator.
##
DeclareOperation( "Indicator", [ IsNearlyCharacterTable, IsPosInt ] );


#############################################################################
##
#O  InducedCyclic( <tbl> )
#O  InducedCyclic( <tbl>, \"all\" )
#O  InducedCyclic( <tbl>, <classes> )
#O  InducedCyclic( <tbl>, <classes>, \"all\" )
##
##  `InducedCyclic' calculates characters induced up from cyclic subgroups
##  of the character table <tbl> to <tbl>.
##
##  If `"all"` is specified, all irreducible characters of those subgroups
##  are induced, otherwise only the permutation characters are calculated.
##
##  If a list <classes> is specified, only those cyclic subgroups generated
##  by these classes are considered, otherwise all classes of <tbl> are
##  considered.
##
##  `InducedCyclic' returns a set of characters.
##
DeclareOperation( "InducedCyclic", [ IsNearlyCharacterTable ] );


#############################################################################
##
#A  UnderlyingGroup( <ordtbl> )
##
##  Note that only the ordinary character table stores the underlying group,
##  the class functions can notify knowledge of the group via the
##  category `IsClassFunctionWithGroup'.
##
DeclareAttributeSuppCT( "UnderlyingGroup", IsOrdinaryTable );


#############################################################################
##
#A  ConjugacyClasses( <tbl> )
##
##  For a character table <tbl> with known underlying group <G>,
##  the `ConjugacyClasses' value of <tbl> is defined to be consistent with the
##  values of `OrdersClassRepresentatives', `SizesCentralizers',
##  `SizesConjugacyClasses', and with each class function of <tbl>,

##  need not coincide with the ordering in <G>,

##  class of the identity element is always the first one

##  
#T one more word about the relation to the `ConjugacyClasses' value
#T of the group!!
#T (and a word about sorting ...)
##
DeclareAttribute( "ConjugacyClasses", IsOrdinaryTable );


#############################################################################
##
#A  IdentificationOfConjugacyClasses( <tbl> )
##
##  For a character table <tbl> with known underlying group <G>,
##  `IdentificationOfConjugacyClasses' returns a list that contains at
##  position $i$ the position of the $i$-th conjugacy class of <tbl>
##  in the list `ConjugacyClasses( <G> )'.
##
DeclareAttribute( "IdentificationOfConjugacyClasses", IsOrdinaryTable );


#############################################################################
##
#O  CharacterTableDirectProduct( <tbl1>, <tbl2> )
##
##  is the table of the direct product of the character tables <tbl1>
##  and <tbl2>.
##
##  We allow products of ordinary and Brauer character tables.
##
##  In general, the result will not know an underlying group,
##  so the power maps and irreducibles of <tbl1> and <tbl2> may be computed
##  in order to construct the direct product.
##
##  The embeddings of <tbl1> and <tbl2> into the direct product are stored,
##  they can be fetched with `GetFusionMap' (see~"GetFusionMap");
##  if <tbl1> is equal to <tbl2> then the two embeddings are distinguished
##  by their `specification' components `"1"' and `"2"', respectively.
##
##  Analogously, the projections from the direct product onto <tbl1> and
##  <tbl2> are stored, and can be distinguished by the `specification'
##  compoenents.
##
DeclareOperation( "CharacterTableDirectProduct",
    [ IsNearlyCharacterTable, IsNearlyCharacterTable ] );


#############################################################################
##
#O  CharacterTableFactorGroup( <tbl>, <classes> )
##
##  is the table of the factor group of <tbl> by the intersection of kernels
##  of those irreducible characters of <tbl> that contain <classes> in their
##  kernel.
##
DeclareOperation( "CharacterTableFactorGroup",
    [ IsNearlyCharacterTable, IsHomogeneousList ] );


#############################################################################
##
#O  CharacterTableIsoclinic( <tbl> )
#O  CharacterTableIsoclinic( <tbl>, <classes_of_normal_subgp> )
#O  CharacterTableIsoclinic( <tbl>, <classes_of_normal_subgp>, <centrepos> )
##
##  for table of groups $2.G.2$, the character table of the isoclinic group
##  (see ATLAS, Chapter~6, Section~7)
#T needed: unique centre of order 2 in side the normal subgroup;
#T table arises  from mult. char. values in the outer corner with `E(4)';
#T generalized in order to admit 4.HS.2 (< HN.2) --> works?
##
#T meaning for Brauer tables?
##
DeclareOperation( "CharacterTableIsoclinic", [ IsNearlyCharacterTable ] );
DeclareOperation( "CharacterTableIsoclinic",
    [ IsNearlyCharacterTable, IsList and IsCyclotomicCollection ] );
DeclareOperation( "CharacterTableIsoclinic",
    [ IsNearlyCharacterTable, IsList and IsCyclotomicCollection, IsPosInt ]);


#############################################################################
##
#O  CharacterTableOfNormalSubgroup( <ordtbl>, <classes> )
##
##  returns the restriction of the ordinary character table <ordtbl>
##  to the classes in the list <classes>.
##
##  In most cases, this table is only an approximation of the character table
##  of this normal subgroup, and some classes of the normal subgroup must be
##  split, see "CharTableSplitClasses".
##  The result is only a table in progress then.
##
##  If the classes in <classes> need not to be split then the result is a
##  proper character table.
##
DeclareGlobalFunction( "CharacterTableOfNormalSubgroup" );


#############################################################################
##
#F  CharacterTableQuaternionic( <4n> )
##
##  is the character table of the quaternionic group of order <4n>
##
DeclareGlobalFunction( "CharacterTableQuaternionic" );


#############################################################################
##
#O  PossibleClassFusions( <subtbl>, <tbl> )
#O  PossibleClassFusions( <subtbl>, <tbl>, <options> )
##
##  returns the list of all possible class fusions from <subtbl> into <tbl>.
##
##  The optional record <options> may have the following components:
##
##  `chars':\\
##       a list of characters of <tbl> which will be restricted to <subtbl>,
##       (see "FusionsAllowedByRestrictions");
##       the default is `<tbl>.irreducibles'
##
##  `subchars':\\
##       a list of characters of <subtbl> which are constituents of the
##       retrictions of `chars', the default is `<subtbl>.irreducibles'
##
##  `fusionmap':\\
##       a (parametrized) map which is an approximation of the desired map
##
##  `decompose':\\
##       a boolean; if `true', the restrictions of `chars' must have all
##       constituents in `subchars', that will be used in the algorithm;
##       if `subchars' is not bound and `<subtbl>.irreducibles' is complete,
##       the default value of `decompose' is `true', otherwise `false'
##
##  `permchar':\\
##       a permutaion character; only those fusions are computed which
##       afford that permutation character
##
##  `quick':\\
##       a boolean; if `true', the subroutines are called with the option
##       `\"quick\"'; especially, a unique map will be returned immediately
##       without checking all symmetrisations; the default value is `false'
##
##  `parameters':\\
##       a record with fields `maxamb', `minamb' and `maxlen' which control
##       the subroutine `FusionsAllowedByRestrictions':
##       It only uses characters with actual indeterminateness up to
##       `maxamb', tests decomposability only for characters with actual
##       indeterminateness at least `minamb' and admits a branch only
##       according to a character if there is one with at most `maxlen'
##       possible restrictions.
##
DeclareOperation( "PossibleClassFusions",
    [ IsOrdinaryTable, IsOrdinaryTable, IsRecord ] );


#############################################################################
##
#O  PossiblePowerMaps( <tbl>, <prime> )
#O  PossiblePowerMaps( <tbl>, <prime>, <options> )
##
##  is a list of possibilities for the <prime>-th power map of the
##  character table <tbl>.
##  If <tbl> is a Brauer table, the map is computed from the power map
##  of the ordinary table.
##
##  The optional record <options> may have the following components:
##
##  \beginitems
##  `chars': &
##       a list of characters which are used for the check of kernels
##       (see "ConsiderKernels"), the test of congruences (see "Congruences")
##       and the test of scalar products of symmetrisations
##       (see "PowerMapsAllowedBySymmetrisations");
##       the default is `<tbl>.irreducibles'
##
##  `powermap': &
##       a (parametrized) map which is an approximation of the desired map
##
##  `decompose': &
##       a boolean; if `true', the symmetrisations of `chars' must have all
##       constituents in `chars', that will be used in the algorithm;
##       if `chars' is not bound and `Irr( <tbl> )' is known,
##       the default value of `decompose' is `true', otherwise `false'
##
##  `quick': &
##       a boolean; if `true', the subroutines are called with the option
##       `\"quick\"'; especially, a unique map will be returned immediately
##       without checking all symmetrisations; the default value is `false'
##
##  `parameters': &
##       a record with fields `maxamb', `minamb' and `maxlen' which control
##       the subroutine `PowerMapsAllowedBySymmetrisations':
##       It only uses characters with actual indeterminateness up to
##       `maxamb', tests decomposability only for characters with actual
##       indeterminateness at least `minamb' and admits a branch only
##       according to a character if there is one with at most `maxlen'
##       possible minus-characters.
##  \enditems
##
DeclareOperation( "PossiblePowerMaps",
    [ IsCharacterTable, IsInt, IsRecord ] );


#############################################################################
##
#F  FusionConjugacyClasses( <tbl1>, <tbl2> )
#F  FusionConjugacyClasses( <H>, <G> )
#F  FusionConjugacyClasses( <hom> )
##
##  In the first form, `FusionConjugacyClasses' returns the fusion of
##  conjugacy classes between the character tables <tbl1> and <tbl2>.
##  (If one of the tables is a Brauer table,
##  it may delegate this task to its ordinary table.)
##
##  In the second form, `FusionConjugacyClasses' returns the fusion of
##  conjugacy classes between the group <H> and its supergroup <G>;
##  this is done by delegating to the ordinary character tables of <H> and
##  <G>,
##  since class fusions are stored only for character tables and not for
##  groups.
#T  We need this facility mainly for compatibility with {\GAP}~3.
##  Note that the returned fusion refers to the ordering of conjugacy
##  classes in the character tables if the arguments are character tables
##  and to the ordering of conjugacy classes in the groups if the arguments
##  are groups (see~"ConjugacyClasses!for character tables").
##
##  In the third form, `FusionConjugacyClasses' returns the fusion of
##  conjugacy classes between source and range of the group homomorphism
##  <hom>; contrary to the second form, also factor fusions can be handled
##  this way.
##
##  If no class fusion exists, `fail' is returned.
##  If the class fusion is not uniquely determined then an error is
##  signalled.
##
#O  FusionConjugacyClassesOp( <tbl1>, <tbl2> )
#A  FusionConjugacyClassesOp( <hom> )
#A  ComputedClassFusions( <tbl> )
##
##  The class fusions to <tbl2> that have been computed already by
##  `FusionConjugacyClasses' are stored in the list
##  `ComputedClassFusions( <tbl2> )'
##
##  Methods for the computation of class fusions can be installed for
##  the operation `FusionConjugacyClassesOp'.
##
##  (see also~"GetFusionMap", "StoreFusion")
##
DeclareGlobalFunction( "FusionConjugacyClasses" );

DeclareAttribute( "FusionConjugacyClassesOp", IsGroupHomomorphism );

DeclareOperation( "FusionConjugacyClassesOp",
    [ IsNearlyCharacterTable, IsNearlyCharacterTable ] );

DeclareAttributeSuppCT( "ComputedClassFusions",
    IsNearlyCharacterTable, "mutable" );


#############################################################################
##
#F  GetFusionMap( <source>, <destination> )
#F  GetFusionMap( <source>, <destination>, <specification> )
##
##  For ordinary character tables <source> and <destination>,
##  `GetFusionMap( <source>, <destination> )' returns the `map' component of
##  the fusion stored on the table <source> that has the `name' component
##  <destination>,
##  and `GetFusionMap( <source>, <destination>, <specification> )' fetches
##  that fusion that additionally has the `specification' component
##  <specification>.
##
##  If <source> and <destination> are Brauer tables,
##  `GetFusionMap' looks whether a fusion map between the ordinary tables
##  is stored; if so then the fusion map between <source> and <destination>
##  is stored on <source>, and then returned.
##
##  If no appropriate fusion is found, `fail' is returned.
##  If several fusions to <destination> are stored on <source>,
##  the two-argument version returns one such fusion,
##  and an info statement is printed if the level of `InfoCharacterTable'
##  is at least 1.
##
##  (For the computation of class fusions, see~"FusionConjugacyClasses".)
##
##  Note that the stored fusion map may differ from the entered map if the
##  table <destination> has a `ClassPermutation'.
##  So one should *not* fetch fusion maps directly via access to
##  `ComputedFusionMaps'.
##
DeclareGlobalFunction( "GetFusionMap" );


#############################################################################
##
#F  StoreFusion( <source>, <fusion>, <destination> )
#F  StoreFusion( <source>, <fusionmap>, <destination> )
##
##  The record <fusion> is stored on <source> if no ambiguity arises.
##  `Identifier( <source> )' is added to the list
##  `NamesOfFusionSources( <destination> )'.
##
##  If a list <fusionmap> is entered, the same holds for
##  `<fusion> = rec( map:= <fusionmap> )'.
##
##  If fusions to <destination> are already stored on <source> then
##  another fusion can be stored only if it has a record component
##  `specification' that distinguishes it from the stored fusions.
##
##  Note that the stored fusion map may differ from the entered map if the
##  table <destination> has a `ClassPermutation'.
##  So one should not fetch fusion maps directly via access to
##  `ComputedFusionMaps'.
##
DeclareGlobalFunction( "StoreFusion" );


#############################################################################
##
#F  PowerMapByComposition( <tbl>, <n> ) . .  for char. table and pos. integer
##
##  <n> must be a positive integer, and <tbl> a nearly character table.
##  If the power maps for all prime divisors of <n> are stored in
##  `ComputedPowerMaps' of <tbl> then `PowerMapByComposition' returns the
##  <n>-th power map of <tbl>.
##  Otherwise `fail' is returned.
##
DeclareGlobalFunction( "PowerMapByComposition" );


#############################################################################
##
#F  PowerMap( <tbl>, <n> )
#F  PowerMap( <G>, <n> )
#F  PowerMap( <tbl>, <n>, <class> )
#F  PowerMap( <G>, <n>, <class> )
#O  PowerMapOp( <tbl>, <n> )
#O  PowerMapOp( <tbl>, <n>, <class> )
#A  ComputedPowerMaps( <tbl> )
##
##  In the first form, `PowerMap' returns the <n>-th power map of the
##  character table <tbl>.
##  In the second form, `PowerMap' returns the <n>-th power map of the
##  group <G>; this is done by delegating to the ordinary character table
##  of <G>.
##
##  The power maps that were computed already by `PowerMap'
##  are stored as value of the attribute `ComputedPowerMaps'
##  (the $n$-th power map at position $n$).
##  Methods for the computation of power maps can be installed for
##  the operation `PowerMapOp'.
##
DeclareGlobalFunction( "PowerMap" );

DeclareOperation( "PowerMapOp", [ IsNearlyCharacterTable, IsInt ] );

DeclareAttributeSuppCT( "ComputedPowerMaps",
    IsNearlyCharacterTable, "mutable" );


#############################################################################
##
#F  InverseMap( <paramap> ) . . . . . . . . . . inverse of a parametrized map
##
##  `InverseMap( <paramap> )[i]' is the unique preimage or the set of all
##  preimages of `i' under <paramap>, if there are any;
##  otherwise it is unbound.
##
##  We have `CompositionMaps( <paramap>, InverseMap( <paramap> ) )'
##  the identity map.
##
DeclareGlobalFunction( "InverseMap" );


#############################################################################
##
#F  NrPolyhedralSubgroups( <tbl>, <c1>, <c2>, <c3>)  . # polyhedral subgroups
##
DeclareGlobalFunction( "NrPolyhedralSubgroups" );


#############################################################################
##
#F  ConvertToOrdinaryTable( <record> )  . . . . create character table object
#F  ConvertToOrdinaryTableNC( <record> )  . . . create character table object
##
##  The components listed in `SupportedOrdinaryTableInfo' are used to set
##  properties and attributes.
##  All other components will simply become components of the record object.
##
DeclareGlobalFunction( "ConvertToOrdinaryTable" );

DeclareGlobalFunction( "ConvertToOrdinaryTableNC" );


#############################################################################
##
#F  ConvertToBrauerTable( <record> ) . . . . . . . create Brauer table object
#F  ConvertToBrauerTableNC( <record> ) . . . . . . create Brauer table object
##
##  The components listed in `SupportedBrauerTableInfo' are used to set
##  properties and attributes.
##  All other components will simply become components of the record object.
##
DeclareGlobalFunction( "ConvertToBrauerTable" );

DeclareGlobalFunction( "ConvertToBrauerTableNC" );


#T ConvertToTableInProgress ???


#############################################################################
##
#F  ConvertToLibraryCharacterTableNC( <record> )
##
##  converts the record <record> into a library character table (ordinary or
##  modular).
##  No consistency checks are made, and <record> is not copied.
##
##  <record> must have one of the components `isGenericTable' or
##  `underlyingCharacteristic'.
##
##  The components listed in `SupportedOrdinaryTableInfo' are used to set
##  properties and attributes.
##  All other components will simply become components of the record object.
##
DeclareGlobalFunction( "ConvertToLibraryCharacterTableNC" );


#############################################################################
##
#F  PrintCharacterTable( <tbl>, <varname> )
##
##  Let <tbl> be a nearly character table, and <varname> a string.
##  `PrintCharacterTable' prints those values of the supported attributes
##  (see~"SupportedOrdinaryTableInfo") that are known for <tbl>;
##  If <tbl> is a library table then also the known values of supported
##  components (see~"SupportedLibraryTableComponents") are printed.
##
##  The output of `PrintCharacterTable' is {\GAP} readable;
##  actually reading it into {\GAP} will bind the variable with name
##  <varname> to a character table that is equivalent to <tbl>.
##
DeclareGlobalFunction( "PrintCharacterTable" );


#############################################################################
##
#F  ClassStructureCharTable(<tbl>,<classes>)  . gener. class mult. coefficent
##
DeclareGlobalFunction( "ClassStructureCharTable" );


#############################################################################
##
#F  MatClassMultCoeffsCharTable( <tbl>, <class> )
#F                                     . . . matrix of class mult coefficents
##
##  is a matrix <M> of structure constants where
##  `<M>[j][k] = ClassMultiplicationCoefficient( <tbl>, <class>, j, k )'
##
DeclareGlobalFunction( "MatClassMultCoeffsCharTable" );


#############################################################################
##
#F  RealClassesCharTable( <tbl> ) . . . .  the real-valued classes of a table
##
##  An element $x$ is real iff it is conjugate to its inverse
##  $x^-1 = x^{o(x)-1}$.
##
DeclareGlobalFunction( "RealClassesCharTable" );


#############################################################################
##
#O  CharacterTableWithSortedCharacters( <tbl> )
#O  CharacterTableWithSortedCharacters( <tbl>, <perm> )
##
##  is a character table that differs from <tbl> only by the succession of
##  its irreducible characters.
##  This affects at most the value of the attributes `Irr' and `IrredInfo',
##  namely these lists are permuted by the permutation <perm>.
##
##  If no second argument is given then a permutation is used that yields
##  irreducible characters of increasing degree for the result.
##  For the succession of characters in the result, see "SortedCharacters".
##
##  The result has all those attributes and properties of <tbl> that are
##  stored in `SupportedOrdinaryTableInfo'.
##
##  The result will *not* be a library table, even if <tbl> is,
##  and it will *not* have an underlying group.
##
DeclareOperation( "CharacterTableWithSortedCharacters",
    [ IsNearlyCharacterTable ] );


#############################################################################
##
#O  SortedCharacters( <tbl>, <chars> )\\
#O  SortedCharacters( <tbl>, <chars>, \"norm\" )\\
#O  SortedCharacters( <tbl>, <chars>, \"degree\" )
##
##  is a list containing the characters <chars>, in a succession specified
##  by the other arguments.
##
##  There are three possibilities to sort characters:\ 
##  They can be sorted according to ascending norms (parameter `\"norm\"'),
##  to ascending degree (parameter `\"degree\"'),
##  or both (no third parameter),
##  i.e., characters with same norm are sorted according to ascending degree,
##  and characters with smaller norm precede those with bigger norm.
##
##  Rational characters always will precede other ones with same norm
##  respectively same degree afterwards.
##
##  The trivial character, if contained in <chars>, will always be sorted to
##  the first position.
##
DeclareOperation( "SortedCharacters",
    [ IsNearlyCharacterTable, IsHomogeneousList ] );


#############################################################################
##
#O  CharacterTableWithSortedClasses( <tbl> )
#O  CharacterTableWithSortedClasses( <tbl>, \"centralizers\" )
#O  CharacterTableWithSortedClasses( <tbl>, \"representatives\" )
#O  CharacterTableWithSortedClasses( <tbl>, <permutation> )
##
##  is a character table obtained on permutation of the classes of <tbl>.
##  If the second argument is the string `"centralizers"' then the classes
##  of the result are sorted according to descending centralizer orders.
##  If the second argument is the string `"representatives"' then the classes
##  of the result are sorted according to ascending representative orders.
##  If no second argument is given, then the classes
##  of the result are sorted according to ascending representative orders,
##  and classes with equal representative orders are sorted according to
##  descending centralizer orders.
##
##  If the second argument is a permutation then the classes of the
##  result are sorted by application of this permutation.
##
##  The result has all those attributes and properties of <tbl> that are
##  stored in `SupportedOrdinaryTableInfo'.
##
##  The result will *not* be a library table, even if <tbl> is,
##  and it will *not* have an underlying group.
##
DeclareOperation( "CharacterTableWithSortedClasses",
    [ IsNearlyCharacterTable ] );


#############################################################################
##
#F  SortedCharacterTable( <tbl>, <kernel> )
#F  SortedCharacterTable( <tbl>, <normalseries> )
#F  SortedCharacterTable( <tbl>, <facttbl>, <kernel> )
##
##  is a character table obtained on permutation of the classes and the
##  irreducibles characters of <tbl>.
##
##  The first form sorts the classes at positions contained in the list
##  <kernel> to the beginning, and sorts all characters in
##  `Irr( <tbl> )' such that the first characters are those that contain
##  <kernel> in their kernel.
##
##  The second form does the same successively for all kernels $k_i$ in
##  the list $'normalseries' = [ k_1, k_2, \ldots, k_n ]$ where
##  $k_i$ must be a sublist of $k_{i+1}$ for $1 \leq i \leq n-1$.
##
##  The third form computes the table <F> of the factor group of <tbl>
##  modulo the normal subgroup formed by the classes whose positions are
##  contained in the list <kernel>;
##  <F> must be permutation equivalent to the table <facttbl> (in the
##  sense of "TransformingPermutationsCharacterTables"), otherwise `fail' is
##  returned.  The classes of <tbl> are sorted such that the preimages
##  of a class of <F> are consecutive, and that the succession of
##  preimages is that of <facttbl>.
##  `Irr( <tbl> )' is sorted as by `SortCharTable( <tbl>, <kernel> )'.
##
##  (*Note* that the transformation is only unique up to table automorphisms
##  of <F>, and this need not be unique up to table automorphisms of <tbl>.)
##
##  All rearrangements of classes and characters are stable, i.e., the
##  relative positions of classes and characters that are not distinguished
##  by any relevant property is not changed.
##
##  The result has at most those attributes and properties of <tbl> that are
##  stored in `SupportedOrdinaryTableInfo'.
##  If <tbl> is a library table then the components of <tbl> that are stored
##  in `SupportedLibraryTableComponents' are components of <tbl>.
##
##  The `ClassPermutation' value of <tbl> is changed if necessary,
##  see "Conventions for Character Tables".
##
DeclareGlobalFunction( "SortedCharacterTable" );


#############################################################################
##
#F  CASString( <tbl> )
##
##  is a string that encodes the {\sf CAS} library format of the character
##  table <tbl>.
##  This string can be printed to a file which then can be read into the
##  {\sf CAS} system using its `get'-command (see~\cite{NPP84}).
##
##  The used line length is `SizeScreen()[1]' (see~"SizeScreen").
##
##  Only the values of the following attributes of <tbl> are used.
##  `ClassParameters' (for partitions only), `ComputedClassFusions',
##  `ComputedPowerMaps', `Identifier', `InfoText', `Irr', `IrredInfo',
##  `OrdersClassRepresentatives', `Size', `SizesCentralizers'.
##
DeclareGlobalFunction( "CASString" );


#############################################################################
##
#F  IrrConlon( <G> )
##
##  compute the irreducible characters of a supersolvable group using
##  Conlon's algorithm.
##  The monomiality information (attribute `TestMonomial') for each
##  irreducible character is known.
##
DeclareGlobalFunction( "IrrConlon" );


#############################################################################
##
##  The following representation is used for the character table library.
##  As the library refers to it, it has to be given in a library file not
##  to enforce installing the character tables library.

#############################################################################
##
#V  SupportedLibraryTableComponents
#R  IsLibraryCharacterTableRep( <tbl> )
##
##  Ordinary library tables may have some components that are meaningless for
##  character tables that know their underlying group.
##  These components do not justify the introduction of operations to fetch
##  them.
##
##  Library tables are always complete character tables.
##  Note that in spite of the name, `IsLibraryCharacterTableRep' is used
##  *not* only for library tables; for example, the direct product of two
##  tables with underlying groups or a factor table of a character table with
##  underlying group may be in `IsLibraryCharacterTableRep'.
##
BindGlobal( "SupportedLibraryTableComponents", [
     "basicset",
     "brauertree",
     "CAS",
     "cliffordTable",
     "construction",
     "decinv",
     "defect",
     "extInfo",
     "factorblocks",
     "factors",
     "indicator",
     "isSimple",
     "projectives",
     "tomfusion",
     "tomidentifier",
    ] );

DeclareRepresentation( "IsLibraryCharacterTableRep", IsAttributeStoringRep,
    SupportedLibraryTableComponents );


#############################################################################
##
#R  IsGenericCharacterTableRep( <tbl> )
##
##  generic character tables are a special representation of objects since
##  they provide just some record components.
##  It might be useful to treat them similar to character table like objects,
##  for example to display them.
##  So they belong to the category of nearly character tables.
##
DeclareRepresentation( "IsGenericCharacterTableRep", IsNearlyCharacterTable,
     [
     "domain",
     "wholetable",
     "classparam",
     "charparam",
     "specializedname",
     "size",
     "centralizers",
     "orders",
     "powermap",
     "classtext",
     "matrix",
     "irreducibles",
     "text",
     ] );


#############################################################################
##
#F  BlanklessPrintTo( <stream>, <obj> )
##
##  appends <obj> to the output stream <stream>,
##  thereby trying to avoid unnecessary blanks.
##  For the subobjects of <obj>, the function `PrintTo' is used.
##  (So the subobjects are appended only if <stream> is of the appropriate
##  type, see~"PrintTo".)
##
##  If <obj> is a record then the component `text' and strings in an `irr'
##  list are *not* treated in a special way!
##
##  This function is used by the libraries of character tables and of tables
##  of marks.
##
DeclareGlobalFunction( "BlanklessPrintTo" );


#############################################################################
##
#E

