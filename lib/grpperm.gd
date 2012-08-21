#############################################################################
##
#W  grpperm.gd                  GAP library                    Heiko Thei"sen
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
Revision.grpperm_gd :=
    "@(#)$Id$";


#############################################################################
##
#C  IsPermGroup( <obj> )
##
##  A permutation group is a  group of permutations on  a finite set
##  $\Omega$ of  positive integers. {\GAP} does *not*  require the user to
##  specify the operation domain  $\Omega$ when a permutation  group is
##  defined.
##
DeclareSynonym( "IsPermGroup", IsGroup and IsPermCollection );


#############################################################################
##
#M  IsSubsetLocallyFiniteGroup( <G> ) . . . . . .  for magmas of permutations
##
#T  Here we assume implicitly that all permutations are finitary!
#T  (What would be a permutation with unbounded largest moved point?
#T  Perhaps a permutation of possibly infinite order?)
##
InstallTrueMethod( IsSubsetLocallyFiniteGroup, IsPermCollection );


#############################################################################
##
#M  KnowsHowToDecompose( <G> )  . . . . . . . .  always true for perm. groups
##
InstallTrueMethod( KnowsHowToDecompose, IsPermGroup );


#############################################################################
##
#F  MinimizeExplicitTransversal
##
DeclareGlobalFunction( "MinimizeExplicitTransversal" );


#############################################################################
##
#F  AddCosetInfoStabChain
##
DeclareGlobalFunction( "AddCosetInfoStabChain" );


#############################################################################
##
#F  NumberCoset
#F  CosetNumber
##
DeclareGlobalFunction( "NumberCoset" );

DeclareGlobalFunction( "CosetNumber" );


#############################################################################
##
#F  IndependentGeneratorsAbelianPPermGroup
##
DeclareGlobalFunction( "IndependentGeneratorsAbelianPPermGroup" );


#############################################################################
##
#F  OrbitPerms
##
DeclareGlobalFunction( "OrbitPerms" );


#############################################################################
##
#F  OrbitsPerms
##
DeclareGlobalFunction( "OrbitsPerms" );


#############################################################################
##
#F  SmallestMovedPointPerms( <list> )
##
##  returns the smallest integer which is moved by at least one permutation
##  in the nonempty list <list> of permutations.
##
DeclareGlobalFunction( "SmallestMovedPointPerms" );


#############################################################################
##
#F  LargestMovedPointPerms( <list> )
##
##  returns the largest integer which is moved by at least one permutation
##  in <list>. If <list> contains no nontrivial permutation, 0 is returned.
##
DeclareGlobalFunction( "LargestMovedPointPerms" );


#############################################################################
##
#F  MovedPointsPerms( <list> )
##
##  returns a list of the points which are moved by at least one of the
##  permutations in <list>.
##
DeclareGlobalFunction( "MovedPointsPerms" );


#############################################################################
##
#F  NrMovedPointsPerms( <list> )
##
##  returns the number of the points which are moved by at least one of the
##  permutations in <list>.
##
DeclareGlobalFunction( "NrMovedPointsPerms" );


#############################################################################
##
#A  LargestMovedPoint( <G> )
##
##  returns the largest positive integer which is moved by at least one
##  element of the permutation group <G>.
##
DeclareAttribute( "LargestMovedPoint", IsPermGroup );


#############################################################################
##
#A  SmallestMovedPoint( <G> )
##
##  returns the smallest positive integer which is moved by at least one
##  element of the permutation group <G>.
##
DeclareAttribute( "SmallestMovedPoint", IsPermGroup );


#############################################################################
##
#A  NrMovedPoints( <G> )
##
##  returns the number of positive integers which are moved by at least one
##  element of the permutation group <G>.
##
DeclareAttribute( "NrMovedPoints", IsPermGroup );


#############################################################################
##
#F  SylowSubgroupPermGroup
##
DeclareGlobalFunction( "SylowSubgroupPermGroup" );


#############################################################################
##
#F  SignPermGroup
##
DeclareGlobalFunction( "SignPermGroup" );


#############################################################################
##
#F  CycleStructuresGroup
##
DeclareGlobalFunction( "CycleStructuresGroup" );


#############################################################################
##
#F  ApproximateSuborbitsStabilizerPermGroup( <G>, <pnt> )
##
##  returns an approximation of the orbits of Stab${}_G$(<pnt>) on all
##  points of the orbit $<pnt>^G$. (As not all schreier generators are used,
##  the results may be the orbits of a subgroup.)
##
DeclareGlobalFunction("ApproximateSuborbitsStabilizerPermGroup");


#############################################################################
##
#A  AllBlocks( <G> )
##
##  computes a list of representatives of all block systems for a
##  permutation group <G> acting transitively on the points moved by the
##  group.
##
DeclareAttribute( "AllBlocks", IsPermGroup );


#############################################################################
##
#A  TransitiveIdentification( <G> )
##
##  Let <G> be a permutation group, acting transitively on a set  of up to 23
##  points.  Then `TransitiveIdentification' will return the position of this
##  group in the transitive  groups library.  This means,  if <G> operates on
##  $m$ points and    `TransitiveIdentification'  returns $n$,  then <G>   is
##  permutation isomorphic to the group `TransitiveGroup(m,n)'.
##
DeclareAttribute( "TransitiveIdentification", IsPermGroup );


#############################################################################
##
#E

