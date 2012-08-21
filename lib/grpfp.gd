#############################################################################
##
#W  grpfp.gd                    GAP library                    Volkmar Felsch
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the declarations for finitely presented groups
##  (fp groups).
##
Revision.grpfp_gd :=
    "@(#)$Id$";


#############################################################################
##
#V  CosetTableDefaultLimit
##
##  is the default number of cosets with which any coset table is
##  initialized before doing a coset enumeration.
##
##  The function performing this coset enumeration will automatically extend
##  the table whenever necessary (as long as the number of cosets does not
##  exceed the value of `CosetTableDefaultMaxLimit'), but this is an
##  expensive operation. Thus, if you change the value of
##  `CosetTableDefaultLimit', you should set it to a number of cosets
##  that you expect to be sufficient for your subsequent coset enumerations.
##  On the other hand, if you make it too large, your job will unnecessarily
##  waste a lot of space.
##
##  The default value of `CosetTableDefaultLimit' is 1000.
##
CosetTableDefaultLimit := 1000;


#############################################################################
##
#V  CosetTableDefaultMaxLimit
##
##  is the default limit for the number of cosets allowed in a coset
##  enumeration.
##
##  A coset enumeration will not finish if the subgroup does not have finite
##  index, and even if it has it may take many more intermediate cosets than
##  the actual index of the subgroup is. To avoid a coset enumeration
##  ``running away'' therefore {\GAP} has a ``safety stop'' built in. This
##  is controlled by the global variable `CosetTableDefaultMaxLimit'.

##  If this number of cosets is reached, {\GAP} will issue an error message
##  and prompt the user to either continue the calculation or to stop it.
##  The default value is 64000.
##
CosetTableDefaultMaxLimit := 64000;


#############################################################################
##
#V  InfoFpGroup
##
##  The info class for functions dealing with finitely presented groups is
##  `InfoFpGroup'.
DeclareInfoClass( "InfoFpGroup" );


#############################################################################
##
#C  IsSubgroupFpGroup( <H> )
##
##  returns `true' if <H> is a finitely presented group or a subgroup of a
##  finitely presented group.
##
DeclareCategory( "IsSubgroupFpGroup", IsGroup );


#############################################################################
##
#C  IsElementOfFpGroup
##
DeclareCategory( "IsElementOfFpGroup",
    IsMultiplicativeElementWithInverse and IsAssociativeElement );

#############################################################################
##
#F  IsFpGroup(<G>)
##
##  is a synonym for `IsSubgroupFpGroup(<G>)' and `IsGroupOfFamily(<G>)'.
##
DeclareSynonym( "IsFpGroup", IsSubgroupFpGroup and IsGroupOfFamily );

#############################################################################
##
#C  IsElementOfFpGroupCollection
##
DeclareCategoryCollections( "IsElementOfFpGroup" );


#############################################################################
##
#m  IsSubgroupFpGroup
##
InstallTrueMethod( IsSubgroupFpGroup,
    IsGroup and IsElementOfFpGroupCollection );


#############################################################################
##
#C  IsElementOfFpGroupFamily
##
DeclareCategoryFamily( "IsElementOfFpGroup" );


#############################################################################
##
#A  FpElmComparisonMethod(<fam>)
##
##  If <fam> is the elements family of a finitely presented group this
##  attribute returns a function `smaller(<left>, <right>)' that will be
##  used to compare elements in <fam>.
##
DeclareAttribute( "FpElmComparisonMethod",IsElementOfFpGroupFamily);


#############################################################################
##
#O  ElementOfFpGroup( <fam>, <word> )
##
##  If <fam> is the elements family of a finitely presented group and <word>
##  is a word in the free generators underlying this finitely presented
##  group, this operation creates the element with the representative <word>
##  in the free group.
##
DeclareOperation( "ElementOfFpGroup",
    [ IsElementOfFpGroupFamily, IsAssocWordWithInverse ] );


#############################################################################
##
#V  TCENUM
#V  GAPTCENUM
##
##  TCENUM is a global record variable whose components contain functions
##  used for coset enumeration. By default `TCENUM' is assigned to
##  `GAPTCENUM', which contains the coset enumeration functions provided by
##  the GAP library.
BindGlobal("GAPTCENUM",rec(name:="GAP Felsch-type enumerator"));
TCENUM:=GAPTCENUM;

#############################################################################
##
#F  CosetTableFromGensAndRels( <fgens>, <grels>, <fsgens> )
##
##  is an internal function which is called by the functions `CosetTable',
##  `CosetTableInWholeGroup' and others. It is, in fact, the proper working
##  horse that performs a Todd-Coxeter coset
##  enumeration. <fgens> must be a set of free generators and <grels> a set
##  of relators in these generators. <fsgens> are subgroup generators
##  expressed as words in these generators. The function returns a coset
##  table with respect to <fgens>.
##
##  `CosetTableFromGensAndRels' will call
##  `TCENUM.CosetTableFromGensAndRels'. This allows to switch the built-in
##  coset enumerator for another one by assigning `TCENUM' to another
##  record.
## 
##  The library version which is used by default performs a standard Felsch
##  strategy coset enumeration. You can call this function explicitly as
##  `GAPTCENUM.CosetTableFromGensAndRels' even if other coset enumerators
##  are installed.
##
DeclareGlobalFunction("CosetTableFromGensAndRels");


#############################################################################
##
#A  CosetTableInWholeGroup(< H >)
##
##  is equivalent to `CosetTable(<G>,<H>)' where <G> is the (unique) 
##  finitely presented group such that <H> is a subgroup of <G>.
##
DeclareAttribute( "CosetTableInWholeGroup", IsGroup );

#############################################################################
##
#F  SubgroupOfWholeGroupByCosetTable(<fpfam>,<tab>)
##
##  takes a family of an fp group and a coset table <tab> and returns
##  the subgroup of fam!.wholeGroup defined by this coset table.
##
DeclareGlobalFunction("SubgroupOfWholeGroupByCosetTable");


#############################################################################
##
#M  SubgroupOfWholeGroupByQuotientSubgroup(<fpfam>,<Q>,<U>)
##
##  takes a fp group family <fpfam>, a finitely generated group <Q> such that
##  the fp generators of <fam> can be mapped by an epimorphism <phi> onto
##  `GeneratorsOfGroup(<Q>)' and a subgroup <U> of <Q>.
##  It returns the subgroup of `<fam>!.wholeGroup' which is the full
##  preimage of <U> under <phi>.
DeclareGlobalFunction("SubgroupOfWholeGroupByQuotientSubgroup");

#############################################################################
##
#R  IsSubgroupOfWholeGroupByQuotientRep(<G>)
##
##  is the representation for subgroups of an fp group, given by a quotient
##  subgroup. The components `<G>!.quot' and `<G>!.sub' hold quotient,
##  respectively subgroup.
DeclareRepresentation("IsSubgroupOfWholeGroupByQuotientRep",
  IsSubgroupFpGroup,["quot","sub"]);

############################################################################
##
#R  IsFromFpGroupGeneralMappingByImages . . . General mapping from Fp group,
##
DeclareRepresentation( "IsFromFpGroupGeneralMappingByImages",
      IsGroupGeneralMappingByImages, [ "generators", "genimages" ] );
IsFromFpGroupHomomorphismByImages :=
  IsFromFpGroupGeneralMappingByImages and IsMapping;

############################################################################
##
#R  IsFromFpGroupStdGensGeneralMappingByImages . . . General mapping from
##                      fp group, just mapping the standard generators
##
DeclareRepresentation( "IsFromFpGroupStdGensGeneralMappingByImages",
      IsFromFpGroupGeneralMappingByImages, [ "generators", "genimages" ] );
IsFromFpGroupStdGensHomomorphismByImages :=
  IsFromFpGroupStdGensGeneralMappingByImages and IsMapping;


############################################################################
##
#F  IsToFpGroupGeneralMappingByImages
##
DeclareRepresentation( "IsToFpGroupGeneralMappingByImages",
      IsGroupGeneralMappingByImages,
      [ "generators", "genimages" ] );
IsToFpGroupHomomorphismByImages := IsToFpGroupGeneralMappingByImages
                               and IsMapping;


############################################################################
##
#O  LowIndexSubgroupsFpGroup(<G>,<H>,<index>[,<excluded>])
##
##  returns a list of representatives of the conjugacy classes of subgroups
##  of the finitely presented group <G> that contain the subgroup <H> of <G>
##  and that have index less than or equal to <index>.
##
##  If the optional argument <excluded> has been specified, then it is
##  expected to be a list of words in the free generators of the underlying
##  free group of <G>, and `LowIndexSubgroupsFpGroup' returns only those
##  subgroups of index at most <index> that contain <H>, but do not contain
##  any conjugate of any of the group elements defined by these words.
##
##  The function `LowIndexSubgroupsFpGroup' finds the requested subgroups
##  by systematically running through a tree of all potential coset tables
##  of <G> of length at most <index> (where it skips all branches of that
##  tree for which it knows in advance that they cannot provide new classes
##  of such subgroups). The time required to do this depends, of course, on
##  the presentation of <G>, but in general it will grow exponentially with
##  the value of <index>. So you should be careful with the choice of
##  <index>.
##
DeclareOperation("LowIndexSubgroupsFpGroup",
  [IsSubgroupFpGroup,IsSubgroupFpGroup,IsPosInt]);


############################################################################
##
#F  MostFrequentGeneratorFpGroup( <G> )
##
##  is an internal function which is used in some applications of coset
##  table methods. It returns the first of those generators of the given
##  finitely presented group <G> which occur most frequently in the
##  relators.
##
DeclareGlobalFunction("MostFrequentGeneratorFpGroup");


#############################################################################
##
#A  FreeGeneratorsOfFpGroup( <G> )
##
##  returns the underlying free generators corresponding to the generators
##  of the finitely presented group <G>.
##
DeclareAttribute( "FreeGeneratorsOfFpGroup",
     IsSubgroupFpGroup and IsGroupOfFamily  );

############################################################################
##
#A  RelatorsOfFpGroup(<G>)
##
##  returns the relators of the finitely presented group <G> as words in the
##  free generators provided by `FreeGeneratorsOfFpGroup(<G>)'.
##
DeclareAttribute("RelatorsOfFpGroup",IsSubgroupFpGroup and IsGroupOfFamily);

#############################################################################
##
#A  FreeGroupOfFpGroup(<G>)
##
##  returns the underlying free group for the finitely presented group <G>.
##  This is the group generated by the free generators provided by
##  `FreeGeneratorsOfFpGroup(<G>)'.
##
DeclareAttribute("FreeGroupOfFpGroup",IsSubgroupFpGroup and IsGroupOfFamily);

#############################################################################
##
#A  IndicesInvolutaryGenerators( <G> )
##
##  returns the indices of those generators of the finitely presented group
##  <G> which are known to be involutions. This knowledge is used by
##  internal functions to improve the performance of coset enumerations.
##
DeclareAttribute("IndicesInvolutaryGenerators",
  IsSubgroupFpGroup and IsGroupOfFamily);

############################################################################
##
#F  RelatorRepresentatives(<rels>)
##
##  returns a set of  relators,  that  contains for each relator in the list
##  <rels> its minimal cyclical  permutation (which is automatically
##  cyclically reduced).
DeclareGlobalFunction("RelatorRepresentatives");


#############################################################################
##
#F  RelsSortedByStartGen( <gens>, <rels>, <table> )
##
##  is a  subroutine of the  Felsch Todd-Coxeter and the  Reduced
##  Reidemeister-Schreier  routines. It returns a list which for each
##  generator or  inverse generator in <gens> contains a list  of all
##  cyclically reduced relators,  starting  with that element,  which can be
##  obtained by conjugating or inverting the given relators <rels>.  The
##  relators are represented as lists of the coset table columns from the
##  table <table> corresponding to the generators and, in addition, as lists
##  of the respective column numbers.
##
DeclareGlobalFunction("RelsSortedByStartGen");


#############################################################################
##
#F  SubgroupGeneratorsCosetTable(<freegens>,<fprels>,<table>)
##
##  determinates subgroup generators for the subgroup given by the coset
##  table <table> from the free generators <freegens>,
##  the  relators <fprels> (as words in <freegens>).
##  It returns words in <freegens>.
##
DeclareGlobalFunction( "SubgroupGeneratorsCosetTable" );


#############################################################################
##
#E  grpfp.gd  . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here

