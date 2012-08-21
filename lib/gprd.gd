#############################################################################
##
#W  gprd.gd                     GAP library                    Heiko Thei"sen
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen, Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
Revision.gprd_gd :=
    "@(#)$Id$";


#############################################################################
##
#F  DirectProduct( <G>{, <H>} )
#O  DirectProductOp( <list>, <expl> )
##
##  These functions construct the direct product of the groups given as
##  arguments.
##  `DirectProduct' takes an arbitrary positive number of arguments
##  and calls the operation `DirectProductOp', which takes exactly two
##  arguments, namely a nonempty list of groups and one of these groups.
##  (This somewhat strange syntax allows the method selection to choose
##  a reasonable method for special cases, e.g., if all groups are
##  permutation groups or pc groups.)
##
DeclareGlobalFunction( "DirectProduct" );
DeclareOperation( "DirectProductOp", [ IsList, IsGroup ] );


#############################################################################
##
#O  SubdirectProduct(<G> ,<H>, <Ghom>, <Hhom> )
##
##  constructs the subdirect product of <G> and <H> with respect to the
##  epimorphisms <Ghom> from <G> onto a group <A> and <Hhom> from <H> onto
##  the same group <A>.
DeclareOperation( "SubdirectProduct",
    [ IsGroup, IsGroup, IsGroupHomomorphism, IsGroupHomomorphism ] );

#############################################################################
##
#O  SemidirectProduct(<G>, <alpha>, <N> )
##
##  constructs the semidirect product of <N> with <G> acting via <alpha>.
DeclareOperation( "SemidirectProduct",
    [ IsGroup, IsGroupHomomorphism, IsGroup ] );


#############################################################################
##
#O  WreathProduct(<G>, <P> )
#O  WreathProduct(<G>, <H> [,<hom>] )
##
##  constructs the wreath product of <G> with the permutation group <P>
##  (acting on its `MovedPoints'). The
##  second usage constructs the wreath product of <G> with the image of <H>
##  under <hom> where <hom> must be a homomorphism from <H> into a
##  permutation group. If <hom> is not given, the regular representation of
##  <H> is taken.
## * Currently only the first usage is supported !*
DeclareOperation( "WreathProduct", [ IsObject, IsObject ] );

#############################################################################
##
#F  WreathProductProductAction(<G>, <H> )
##
##  for two permutation groups <G> and <H> this function constructs the
##  wreath product in product action.
DeclareGlobalFunction( "WreathProductProductAction" );

DeclareGlobalFunction( "InnerSubdirectProducts" );
DeclareGlobalFunction( "InnerSubdirectProducts2" );
DeclareGlobalFunction( "SubdirectProducts" );

#############################################################################
##
#A  DirectProductInfo( <G> )
##
DeclareAttribute( "DirectProductInfo", IsGroup, "mutable" );

#############################################################################
##
#A  SubdirectProductInfo( <G> )
##
DeclareAttribute( "SubdirectProductInfo", IsGroup, "mutable" );

#############################################################################
##
#A  SemidirectProductInfo( <G> )
##
DeclareAttribute( "SemidirectProductInfo", IsGroup, "mutable" );

#############################################################################
##
#A  WreathProductInfo( <G> )
##
DeclareAttribute( "WreathProductInfo", IsGroup, "mutable" );

#############################################################################
##
#E

