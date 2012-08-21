#############################################################################
##  
#W  pquot.gd                    GAP Library                     Werner Nickel
##
#H  $Id$
##
#Y  Copyright (C) 1998, . . . . . . . . .  University of St Andrews, Scotland
##
Revision.pquot_gd :=
    "$Id$";

#############################################################################
##  
#F  AbelianPQuotient  . . . . . . . . . . .  initialize an abelian p-quotient
##
DeclareGlobalFunction( "AbelianPQuotient" );

#############################################################################
##
#F  PQuotient(<fpgrp>,<p>,<n>)  . .  p-quotient of a finitely presented group
##
DeclareGlobalFunction( "PQuotient" );

#############################################################################
##
#O  EpimorphismQuotientSystem(<quotsys>)
##
##  If <quotsys> is a quotient system as obtained from the PQuotient
##  algorithm, this operation returns an epimorphism $<F>\to<P>$ where $<F>$
##  is the finitely presented group of which <quotsys> is a quotient system
##  and $<P>$ is a `PcGroup' isomorphic to the quotient of <F> determined by
##  <quotsys>.
##
##  Different calls to this operation will create nifferent groups <P>, each
##  with its own family.
##  
DeclareOperation( "EpimorphismQuotientSystem", [IsQuotientSystem] );

#############################################################################
##
#E  Emacs . . . . . . . . . . . . . . . . . . . . . . . . . . emacs variables
##  
##  Local Variables:
##  mode:               outline
##  tab-width:          4
##  outline-regexp:     "#[ACEFHMOPRWY]"
##  fill-column:        77
##  fill-prefix:        "##  "
##  End:

