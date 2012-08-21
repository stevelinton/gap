#############################################################################
##
#W  csetgrp.gd                      GAP library              Alexander Hulpke
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the declarations of operations for cosets.
##
Revision.csetgrp_gd:=
  "@(#)$Id$";

#############################################################################
##
#V  InfoCoset
##
##  The information function for coset and double coset operations is
##  `InfoCoset'.
DeclareInfoClass("InfoCoset");

#############################################################################
##
#F  AscendingChain(<G>,<U>) . . . . . . .  chain of subgroups G=G_1>...>G_n=U
##
##  This function computes an ascending chain of subgroups from <U> to <G>.
##  This chain is given as a list whose first entry is <U> and the last entry
##  is <G>. The function tries to make the links in this chain small.
##
DeclareGlobalFunction("AscendingChain");

#############################################################################
##
#O  AscendingChainOp(<G>,<U>)  chain of subgroups
##
##  This operation does the actual work of computing ascending chains. It
##  gets called from `AscendingChain' if no chain is found stored in
##  `ComputedAscendingChains'.
##
DeclareOperation("AscendingChainOp",[IsGroup,IsGroup]);

#############################################################################
##
#A  ComputedAscendingChains(<U>)    list of already computed ascending chains
##
##  This attribute stores ascending chains. It is a list whose entries are
##  of the form [<G>,<chain>] where <chain> is an ascending chain from <U> up
##  to <G>. This storage is used by `AscendingChain' to avoid duplicate
##  calculations.
DeclareAttribute("ComputedAscendingChains",IsGroup,
                                        "mutable");

#############################################################################
##
#O  CanonicalRightCosetElement(U,g)    canonical representative of U*g 
##                                  (Representation dependent!)
##
##  returns an element of the coset <Ug> which is independent of the given
##  representative <g>. This can be used to compare cosets by comparing
##  their canonical representatives. The representative chosen to be the
##  canonical one is representation dependent and only guaranteed to remain the
##  same within one {\GAP} session.
##
DeclareOperation("CanonicalRightCosetElement",
  [IsGroup,IsObject]);

#############################################################################
##
#C  IsDoubleCoset(<obj>)
##
##  The category of double cosets.
DeclareCategory("IsDoubleCoset",
    IsDomain and IsExtLSet and IsExtRSet);

#############################################################################
##
#A  LeftActingGroup(<obj>)
#A  RightActingGroup(<obj>)
##
DeclareAttribute("LeftActingGroup",IsDoubleCoset);
DeclareAttribute("RightActingGroup",IsDoubleCoset);

#############################################################################
##
#O  DoubleCoset(<U>,<g>,<V>)
##
##  The groups <U> and <V> must be subgroups of a common supergroup <G> of which
##  <g> is an element. This command constructs the double coset <UgV> which is
##  the set of all elements of the form $ugv$ for any $u\in<U>$, $v\in<V>$.
##  For element operations like `in' a double coset behaves like a set of group
##  elements. The double doset stores <U> in the attribute
##  `LeftActingGroup', <g> as `Representative' and <V> as
##  `RightActingGroup'.
DeclareOperation("DoubleCoset",[IsGroup,IsObject,IsGroup]);

#############################################################################
##
#O  DoubleCosets(<G>,<U>,<V>)
#O  DoubleCosetsNC(<G>,<U>,<V>)
##
##  computes a duplicate free list of all double cosets <UgV> for $<g>\in<G>$.
##  <U> and <V> must be subgroups of the group <G>.
##  The NC version does not check whether <U> and <V> are both subgroups
##  of <G>.
##
DeclareGlobalFunction("DoubleCosets");
DeclareOperation("DoubleCosetsNC",[IsGroup,IsGroup,IsGroup]);

#############################################################################
##
#A  RepresentativesContainedRightCosets(<D>)
##
##  A double coset <UgV> can be considered as an union of right cosets
##  $<U>h_i$.  (it is the union of the orbit of $<Ug>$ under right
##  multiplication by $V$.) For a double coset <D>=<UgV> this returns a set
##  of representatives $h_i$ such that $<D>=\bigcup_{h_i}<U>h_i$. The
##  representatives returned are canonical for <U> (see
##  "CanonicalRightCosetElement") and form a set.
DeclareAttribute( "RepresentativesContainedRightCosets", IsDoubleCoset );

#############################################################################
##
#C  IsRightCoset(<obj>)
##
##  The category of right cosets.
DeclareCategory("IsRightCoset",
    IsDomain and IsExternalSet);

#############################################################################
##
#O  RightCoset(<U>,<g>)
##
##  returns the right coset of <U> with representative <g>, which is 
##  the set of all elements of the form $ug$ for any $u\in<U>$.
##  <g> must be an element of a larger group <G> which contains <U>.
##  Right cosets are external orbits for the action of <U> which acts via
##  `OnLeftInverse'.
##  For element operations like `in' a right coset behaves like a set of group
##  elements.
DeclareOperation("RightCoset",[IsGroup,IsObject]);


#############################################################################
##
#O  RightCosets(<G>,<U>)
#O  RightCosetsNC(<G>,<U>)
##
##  computes a duplicate free list of right cosets $Ug$ for $g\in<G>$. A set
##  of representatives for the elements in this list forms a right transversal
##  of <U> in <G>. (By inverting the representatives one obtains a list
##  of left cosets.) The NC version does not check the parameters.
DeclareGlobalFunction("RightCosets");
DeclareOperation("RightCosetsNC",[IsGroup,IsGroup]);

#############################################################################
##
#F  IntermediateGroup(<G>,<U>)  . . . . . . . . . subgroup of G containing U
##
##  This routine tries to find a subgroup <E> of <G>, such that $G>E>U$. If
##  $U$ is
##  maximal, it returns false. This is done by finding minimal blocks for
##  the operation of <G> on the right cosets of <U>.
##
DeclareGlobalFunction("IntermediateGroup");

#############################################################################
##
#E  csetgrp.gd  . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##
