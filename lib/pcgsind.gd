#############################################################################
##
#W  pcgsind.gd                  GAP Library                      Frank Celler
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This  file  contains  the operations   for  induced polycylic  generating
##  systems.
##
Revision.pcgsind_gd :=
    "@(#)$Id$";

#############################################################################
##
#C  IsInducedPcgs(<pcgs>)
##
##  The category of induced pcgs. This a subcategory of pcgs.
DeclareCategory( "IsInducedPcgs", IsPcgs );


#############################################################################
##
#O  InducedPcgsByPcSequence( <pcgs>, <pcs> )
#O  InducedPcgsByPcSequenceNC( <pcgs>, <pcs> )
##
##  If <pcs> is a list of elements that form an induced pcgs with respect to
##  <pcgs> this operation returns an induced pcgs with these elements.
DeclareOperation( "InducedPcgsByPcSequence", [ IsPcgs, IsList ] );
DeclareOperation( "InducedPcgsByPcSequenceNC", [ IsPcgs, IsList ] );

#############################################################################
##
#A  LeadCoeffsIGS( <igs> )
##
##  this attribute is used to store leading coefficients wrt. the parent
##  pcgs. (It cannot be assigned to a component in
##  `InducedPcgsByPcSequenceNC' as the permutation group methods call it
##  with postprocessing, before this postprocessing however no coefficients
##  may be computed.)
DeclareAttribute( "LeadCoeffsIGS", IsInducedPcgs );


#############################################################################
##
#O  InducedPcgsByPcSequenceAndGenerators( <pcgs>, <ind>, <gens> )
##
##  returns an induced pcgs with respect to <pcgs> of the subgroup generated 
##  by <ind> and <gens>. Here <ind> must be an induced pcgs with respect to
##  <pcgs> and it will be used as initial sequence for the compuation.
DeclareOperation(
    "InducedPcgsByPcSequenceAndGenerators",
    [ IsPcgs, IsList, IsList ] );


#############################################################################
##
#O  InducedPcgsByGenerators( <pcgs>, <gens> )
#O  InducedPcgsByGeneratorsNC( <pcgs>, <gens> )
##
##  returns an induced pcgs with respect to <pcgs> for the subgroup generated
##  by <gens>.
DeclareOperation( "InducedPcgsByGenerators", [ IsPcgs, IsCollection ] );
DeclareOperation( "InducedPcgsByGeneratorsNC", [ IsPcgs, IsCollection ] );


#############################################################################
##
#O  InducedPcgsByGeneratorsWithImages( <pcgs>, <gens>, <imgs> )
##
DeclareOperation(
    "InducedPcgsByGeneratorsWithImages",
    [ IsPcgs, IsCollection, IsCollection ] );

#############################################################################
##
#O  CanonicalPcgsByGeneratorsWithImages( <pcgs>, <gens>, <imgs> )
##
DeclareOperation(
    "CanonicalPcgsByGeneratorsWithImages",
    [ IsPcgs, IsCollection, IsCollection ] );


#############################################################################
##
#O  AsInducedPcgs( <parent>, <pcs> )
##
##  Obsolete function, potentially erraneous. DO NOT USE!
##  returns an induced pcgs with <parent> as parent pcgs and to the
##  sequence of elements <pcs>.
DeclareOperation(
    "AsInducedPcgs",
    [ IsPcgs, IsList ] );


#############################################################################
##
#A  ParentPcgs( <pcgs> )
##
##  returns the pcgs by which <pcgs> was induced. If <pcgs> was not induced,
##  it simply returns <pcgs>.
DeclareAttribute( "ParentPcgs", IsInducedPcgs );


#############################################################################
##
#A  CanonicalPcgs( <pcgs> )
##
##  returns the canonical pcgs corresponding to the induced pcgs <pcgs>.
DeclareAttribute( "CanonicalPcgs", IsInducedPcgs );


#############################################################################
##
#P  IsCanonicalPcgs( <pcgs> )
##
##  An induced pcgs is canonical if the matrix of the exponent vectors of
##  the elements of <pcgs> with respect to `ParentPcgs(<pcgs>)' is in
##  Hermite normal form
##  (see \cite{SOGOS}). While a subgroup can have various
##  induced pcgs with respect to a parent pcgs a canonical pcgs is unique.
DeclareProperty( "IsCanonicalPcgs", IsInducedPcgs );

#############################################################################
##
#P  IsParentPcgsFamilyPcgs( <pcgs> )
##
##  This property indicates that the pcgs <pcgs> is induced with respect to
##  a family pcgs.
DeclareProperty( "IsParentPcgsFamilyPcgs", IsInducedPcgs );

#############################################################################
##
#A  ElementaryAbelianSubseries( <pcgs> )
##
DeclareAttribute(
    "ElementaryAbelianSubseries",
    IsPcgs );



#############################################################################
##
#O  CanonicalPcElement( <ipcgs>, <elm> )
##
##  reduces <elm> at the induces pcgs <ipcgs> such that the exponents of the
##  reduced result <r> are zero at the depths for which there are generators
##  in <ipcgs>. Elements, whose quotient lies in the group generated by
##  <ipcgs> yield the same canonical element.
DeclareOperation( "CanonicalPcElement", [ IsInducedPcgs, IsObject ] );


#############################################################################
##
#O  SiftedPcElement( <pcgs>, <elm> )
##
##  sifts <elm> through <pcgs>, reducing it if the depth is the same as the
##  depth of one of the generators in <pcgs>. Thus the identity is returned
##  if <elm> lies in the group generated by <pcgs>.
DeclareOperation(
    "SiftedPcElement",
    [ IsInducedPcgs, IsObject ] );


#############################################################################
##
#O  HomomorphicCanonicalPcgs( <pcgs>, <imgs> )
##
##  It  is important that  <imgs>  are the images of  in  induced  generating
##  system  in their natural order, ie.  they must not be sorted according to
##  their  depths in the new group,  they must be  sorted according to  their
##  depths in the old group.
##
DeclareOperation(
    "HomomorphicCanonicalPcgs",
    [ IsPcgs, IsList ] );


#############################################################################
##
#O  HomomorphicInducedPcgs( <pcgs>, <imgs> )
##
##  It  is important that  <imgs>  are the images of  in  induced  generating
##  system  in their natural order, ie.  they must not be sorted according to
##  their  depths in the new group,  they must be  sorted according to  their
##  depths in the old group.
##
DeclareOperation(
    "HomomorphicInducedPcgs",
    [ IsPcgs, IsList ] );

#############################################################################
##
#O  CorrespondingGeneratorsByModuloPcgs( <mpcgs>, <imgs> )
##
##  computes a list of elements in the span of <imgs> that form a canonical
##  pcgs with
##  respect to <mpcgs> (The calculation of induced generating sets is not
##  possible for some modulo pcgs).
DeclareGlobalFunction("CorrespondingGeneratorsByModuloPcgs");

#############################################################################
##
#F  NORMALIZE_IGS( <pcgs>, <list> )
##
##  Obsolete function, potentially erraneous. DO NOT USE!
DeclareGlobalFunction("NORMALIZE_IGS");

#############################################################################
##
#E  pcgsind.gd 	. . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##
