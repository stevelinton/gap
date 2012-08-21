#############################################################################
##
#W  pcgsmodu.gd                 GAP Library                      Frank Celler
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the operations for polycylic generating systems modulo
##  another such system.
##
Revision.pcgsmodu_gd :=
    "@(#)$Id$";

#############################################################################
##
#O  ModuloPcgsByPcSequenceNC( <home>, <pcs>, <modulo> )
##
DeclareOperation(
    "ModuloPcgsByPcSequenceNC",
    [ IsPcgs, IsList, IsPcgs ] );


#############################################################################
##
#O  ModuloPcgsByPcSequence( <home>, <pcs>, <modulo> )
##
DeclareOperation(
    "ModuloPcgsByPcSequence",
    [ IsPcgs, IsList, IsPcgs ] );

#############################################################################
##
#O  ModuloPcgs( <G>, <N> )
##
DeclareOperation( "ModuloPcgs", [ IsGroup, IsGroup ] );


#############################################################################
##
#A  ModuloParentPcgs( <pcgs> )
##
DeclareAttribute(
    "ModuloParentPcgs",
    IsPcgs );



#############################################################################
##
#A  DenominatorOfModuloPcgs( <pcgs> )
##
##  returns a generating set for the denominator of the modulo pcgs <pcgs>. 
DeclareAttribute( "DenominatorOfModuloPcgs", IsModuloPcgs );



#############################################################################
##
#A  NumeratorOfModuloPcgs( <pcgs> )
##
##  returns a generating set for the numerator of the modulo pcgs <pcgs>.
DeclareAttribute( "NumeratorOfModuloPcgs", IsModuloPcgs );

#############################################################################
##
#P  IsNumeratorParentPcgsFamilyPcgs( <mpcgs> )
##
##  This property indicates that the numerator of the modulo pcgs <mpcgs> is
##  induced with respect to a family pcgs.
DeclareProperty( "IsNumeratorParentPcgsFamilyPcgs", IsModuloPcgs );


#############################################################################
##
#E  pcgsmodu.gd . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##
