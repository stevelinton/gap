#############################################################################
##
#W  grpmat.gd                   GAP Library                      Frank Celler
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the operations for matrix groups.
##
Revision.grpmat_gd :=
    "@(#)$Id$";


#############################################################################
##
#C  IsMatrixGroup(<grp>)
##
DeclareSynonym( "IsMatrixGroup", IsRingElementCollCollColl and IsGroup );

InstallTrueMethod( IsHandledByNiceMonomorphism, IsMatrixGroup and IsFinite );

#############################################################################
##
#A  DefaultFieldOfMatrixGroup( <mat-grp> )
##
##  Is a field containing all the matrix entries. It is not guaranteed to be
##  the smallest field with this property.
##
DeclareAttribute(
    "DefaultFieldOfMatrixGroup",
    IsMatrixGroup );

InstallSubsetMaintenance( DefaultFieldOfMatrixGroup,
        IsMatrixGroup and HasDefaultFieldOfMatrixGroup, IsMatrixGroup );

#############################################################################
##
#A  DimensionOfMatrixGroup( <mat-grp> )
##
##  The dimension of the matrix group.
##
DeclareAttribute(
    "DimensionOfMatrixGroup",
    IsMatrixGroup );


InstallSubsetMaintenance( DimensionOfMatrixGroup,
        IsMatrixGroup and HasDimensionOfMatrixGroup, IsMatrixGroup );


#############################################################################
##
#A  FieldOfMatrixGroup( <mat-grp> )
##
##  The smallest  field containing all the  matrix entries.  As the
##  calculation of this can be hard, this should only be used        if  one
##  *really*   needs     the    smallest   field,  use
##  `DefaultFieldOfMatrixGroup' to get (for example) the characteristic.
##
DeclareAttribute(
    "FieldOfMatrixGroup",
    IsMatrixGroup );


#############################################################################
##
#P  IsGeneralLinearGroup( <grp> )
#P  IsGL(<grp>)
##
##  The General Linear group is the group of all invertible matrices over a
##  ring. This property tests, whether a group is isomorphic to a General
##  Linear group.
DeclareProperty( "IsGeneralLinearGroup", IsGroup );
DeclareSynonym( "IsGL", IsGeneralLinearGroup );


#############################################################################
##
#P  IsNaturalGL( <matgrp> )
##
##  This property tests, whether a matrix group is the General Linear group
##  in the right dimension over the (smallest) ring which contains all
##  entries of its elements.
DeclareProperty( "IsNaturalGL", IsMatrixGroup );
InstallTrueMethod(IsGeneralLinearGroup,IsNaturalGL);

#############################################################################
##
#P  IsSpecialLinearGroup( <grp> )
#P  IsSL(<grp>)
##
##  The Special Linear group is the group of all invertible matrices over a
##  ring. This property tests, whether a group is isomorphic to a Special  
##  Linear group.
DeclareProperty( "IsSpecialLinearGroup", IsGroup );
DeclareSynonym( "IsSL", IsSpecialLinearGroup );

#############################################################################
##
#P  IsNaturalSL( <matgrp> )
##
##  This property tests, whether a matrix group is the Special Linear group
##  in the right dimension over the (smallest) ring which contains all
##  entries of its elements.
DeclareProperty( "IsNaturalSL", IsMatrixGroup );
InstallTrueMethod(IsSpecialLinearGroup,IsNaturalSL);

#############################################################################
##
#P  IsSubgroupSL( <matgrp> )
##
##  This property tests, whether a matrix group is a subgroup of the Special
##  Linear group in the right dimension over the (smallest) ring which
##  contains all entries of its elements.
DeclareProperty( "IsSubgroupSL", IsMatrixGroup );
InstallTrueMethod(IsSubgroupSL,IsNaturalSL);

#############################################################################
##
#A  InvariantBilinearForm(<matgrp>)
##
##  This attribute contains a bilinear form that is invariant under
##  <matgrp>. The form is given by a record with the component `matrix'
##  which is a matrix <m> such that for every generator <g> of
##  <m> the equation $<g>\cdot<m>\cdot<g>^{tr}$ holds.
DeclareAttribute( "InvariantBilinearForm", IsMatrixGroup );

#############################################################################
##
#P  IsFullSubgroupGLorSLRespectingBilinearForm(<matgrp>)
##
##  This property tests, whether a matrix group <matgrp> is the full
##  subgroup of GL or SL (the property `IsSubgroupSL' determines which it
##  is) respecting the `InvariantBilinearForm' of <matgrp>.
DeclareProperty( "IsFullSubgroupGLorSLRespectingBilinearForm", IsMatrixGroup );

#############################################################################
##
#A  InvariantSesquilinearForm(<matgrp>)
##
##  This attribute contains a sesquilinear form that is invariant under
##  <matgrp>. The form is given by a record with the component `matrix'
##  which is is a matrix <m> such that for every generator <g> of <m> the
##  equation $<g>\cdot<m>\cdot(<g>^{tr})^F$ holds, where <F> is the
##  `FrobeniusAutomorphism' of the `FieldOfMatrixGroup' of <G>.
DeclareAttribute( "InvariantSesquilinearForm", IsMatrixGroup );

#############################################################################
##
#P  IsFullSubgroupGLorSLRespectingSesquilinearForm(<matgrp>)
##
##  This property tests, whether a matrix group <matgrp> is the full
##  subgroup of GL or SL (the property `IsSubgroupSL' determines which it
##  is) respecting the `InvariantSesquilinearForm' of <matgrp>.
DeclareProperty( "IsFullSubgroupGLorSLRespectingSesquilinearForm",
  IsMatrixGroup );

#############################################################################
##
#E  grpmat.gd . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##
