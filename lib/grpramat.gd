#############################################################################
##
#W  grpramat.gd                 GAP Library                     Franz G"ahler
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the declarations for matrix groups over the rationals
##
Revision.grpramat_gd :=
    "@(#)$Id$";

#############################################################################
##
#P  IsCyclotomicMatrixGroup( <G> )
##
##  tests whether all matrices in <G> have cyclotomic entries.
IsCyclotomicMatrixGroup := IsCyclotomicCollCollColl and IsMatrixGroup;

#############################################################################
##
#P  IsRationalMatrixGroup( <G> )
##
##  tests whether all matrices in <G> have rational entries.
DeclareProperty("IsRationalMatrixGroup", IsCyclotomicMatrixGroup);

#############################################################################
##
#P  IsIntegerMatrixGroup( <G> )
##
##  tests whether all matrices in <G> have integer entries.
#T  Not `IsIntegralMatrixGroup' to avoid confusion with matrix groups of
#T  integral cyclotomic numbers.  
DeclareProperty("IsIntegerMatrixGroup", IsCyclotomicMatrixGroup);

#############################################################################
##
#P  IsNaturalGLnZ( <G> )
##
##  tests whether <G> is $GL_n(\Z)$ in its natural representation by
##  $n\times n$ integer matrices. (The dimension $n$ will be read off the
##  generating matrices.)
IsNaturalGLnZ := IsNaturalGL and IsIntegerMatrixGroup;

#############################################################################
##
#A  ZClassRepsQClass( G ) . . . . . . . . . . .  Z-class reps in Q-class of G
##
##  The conjugacy class in $GL_n(\Q)$ of the finite integer matrix 
##  group <G> splits into finitely many conjugacy classes in $GL_n(\Z)$.
##  `ZClassRepsQClass( <G> )' returns representative groups for these.
DeclareAttribute( "ZClassRepsQClass", IsCyclotomicMatrixGroup );

#############################################################################
##
#A  NormalizerInGLnZ( G ) . . . . . . . . . . . . . . . . .  NormalizerInGLnZ
##
##  is an attribute used to store the normalizer of <G> in $GL_n(\Z)$,
##  where <G> is an integer matrix group of dimension <n>. This attribute
##  is used by `Normalizer( GL( n, Integers ), G )'. 
DeclareAttribute( "NormalizerInGLnZ", IsCyclotomicMatrixGroup );

#############################################################################
##
#A  CentralizerInGLnZ( G ) . . . . . . . . . . . . . . . . .CentralizerInGLnZ
##
##  is an attribute used to store the centralizer of <G> in $GL_n(\Z)$,
##  where <G> is an integer matrix group of dimension <n>. This attribute
##  is used by `Centralizer( GL( n, Integers ), G )'. 
DeclareAttribute( "CentralizerInGLnZ", IsCyclotomicMatrixGroup );

#############################################################################
##
##  RightAction or LeftAction
##
##  In {\GAP}, matrices by convention act on row vectors from the right,
##  whereas in crystallography the convention is to act on column vectors
##  from the left. The definition of certain algebraic objects important
##  in crystallography implicitly depends on which action is assumed.
##  This holds true in particular for the Bravais groups and related
##  concepts. The Bravais group of a group <G> is the full invariance 
##  group of a space of quadratic forms left invariant by <G>. This
##  definition implicitly contains an assumption on how <G> acts on
##  quadratic forms. For this reason, a number of functions which are 
##  important in crystallography and whose result depends on which action 
##  is assumed, are provided in two versions, one for the usual action 
##  from the right, and one for the crystallographic action from the left. 
##
##  For every such function, this fact is explicitly mentioned. 
##  The naming scheme is as follows: If `SomeThing' is such a function, 
##  there will be functions `SomeThingOnRight' and `SomeThingOnLeft', 
##  assuming action from the right and from the left, repectively. 
##  In addition, there is a generic function `SomeThing', which returns 
##  either the result of `SomeThingOnRight' or `SomeThingOnLeft', 
##  depending on the global variable `CrystGroupDefaultAction'.

#############################################################################
##
#V  CrystGroupDefaultAction
##
##  can have either of the two values `RightAction' and `LeftAction'. 
##  The initial value is `RightAction'. For functions described in the
##  following, which have variants OnRight and OnLeft, this variable
##  determines which variant is returned by the generic form.
##  The value of `CrystGroupDefaultAction' can be changed with with the 
##  function `SetCrystGroupDefaultAction'.
##
DeclareGlobalVariable( "CrystGroupDefaultAction" );

BindGlobal( "LeftAction",  Immutable( "LeftAction"  ) );
BindGlobal( "RightAction", Immutable( "RightAction" ) );

#############################################################################
##
#F  SetCrystGroupDefaultAction( <action> ) . . . . .RightAction or LeftAction
##
##  allows to set the value of the global variable `CrystGroupDefaultAction'.
##  Only the arguments `RightAction' and `LeftAction' are allowed.
##  Initially, the value of `CrystGroupDefaultAction' is `RightAction'
DeclareGlobalFunction( "SetCrystGroupDefaultAction" );

#############################################################################
##
#P  IsBravaisGroupOnRight( <G> ) . . . . . . . . . . . .IsBravaisGroupOnRight
##
##  test whether <G> coincides with its right Bravais group
##  (see "BravaisGroupOnRight").
DeclareProperty( "IsBravaisGroupOnRight", IsCyclotomicMatrixGroup );

#############################################################################
##
#P  IsBravaisGroupOnLeft( <G> ) . . . . . . . . . . . . .IsBravaisGroupOnLeft
##
##  test whether <G> coincides with its left Bravais group
##  (see "BravaisGroupOnLeft").
DeclareProperty( "IsBravaisGroupOnLeft",  IsCyclotomicMatrixGroup );

#############################################################################
##
#F  IsBravaisGroup( <G> ) . . . . . . . . . . . . . . . . . .  IsBravaisGroup
##
##  returns either IsBravaisGroupOnRight(<G>) or IsBravaisGroupOnLeft(<G>),
##  depending on the value of `CrystGroupDefaultAction'.
DeclareGlobalFunction( "IsBravaisGroup" );

#############################################################################
##
#A  BravaisGroupOnRight( <G> ) .  right Bravais group of integer matrix group
##
##  returns the right Bravais group of a finite integer matrix group
##  <G>. If <C> is the cone of positive definite quadratic forms <Q>
##  invariant under $g \to g^{tr}*Q*g$ for all $g \in G$, then the
##  right Bravais group of <G> is the maximal subgroup of $GL_n(\Z)$ 
##  leaving the same cone invariant.
DeclareAttribute( "BravaisGroupOnRight", IsCyclotomicMatrixGroup );

#############################################################################
##
#A  BravaisGroupOnLeft( <G> ) . .  left Bravais group of integer matrix group
##
##  returns the left Bravais group of a finite integer matrix group
##  <G>. If <C> is the cone of positive definite quadratic forms <Q>
##  invariant under $g \to g*Q*g^{tr}$ for all $g \in G$, then the
##  left Bravais group of <G> is the maximal subgroup of $GL_n(\Z)$ 
##  leaving the same cone invariant.
DeclareAttribute( "BravaisGroupOnLeft",  IsCyclotomicMatrixGroup );

#############################################################################
##
#F  BravaisGroup( <G> ) . . . . . . . . . . . . . . . . . . . .  BravaisGroup
##
##  returns either BravaisGroupOnRight(<G>) or BravaisGroupOnLeft(<G>),
##  depending on the value of `CrystGroupDefaultAction'.
DeclareGlobalFunction( "BravaisGroup" );

#############################################################################
##
#A  BravaisSubgroupsOnRight( <G> ) . Bravais subgroups of right Bravais group
##
##  returns the subgroups of the right Bravais group of <G> which are 
##  themselves right Bravais groups.
DeclareAttribute( "BravaisSubgroupsOnRight", IsCyclotomicMatrixGroup );

#############################################################################
##
#A  BravaisSubgroupsOnLeft( <G> ) . . Bravais subgroups of left Bravais group
##
##  returns the subgroups of the left Bravais group of <G> which are 
##  themselves left Bravais groups.
DeclareAttribute( "BravaisSubgroupsOnLeft",  IsCyclotomicMatrixGroup );

#############################################################################
##
#A  BravaisSubgroups( <G> ) . . . . . . .  Bravais subgroups of Bravais group
##
##  returns either BravaisSubgroupsOnRight(<G>) or BravaisSubgroupsOnLeft(<G>),
##  depending on the value of `CrystGroupDefaultAction'.
DeclareGlobalFunction( "BravaisSubgroups" );

#############################################################################
##
#A  BravaisSupergroupsOnRight( <G> )  Bravais supergr. of right Bravais group
##
##  returns the subgroups of $GL_n(\Z)$ that contain the right Bravais group 
##  of <G> and are right Bravais groups themselves.
DeclareAttribute( "BravaisSupergroupsOnRight", IsCyclotomicMatrixGroup );

#############################################################################
##
#A  BravaisSupergroupsOnLeft( <G> ) .  Bravais supergr. of left Bravais group
##
##  returns the subgroups of $GL_n(\Z)$ that contain the left Bravais group 
##  of <G> and are left Bravais groups themselves.
DeclareAttribute( "BravaisSupergroupsOnLeft",  IsCyclotomicMatrixGroup );

#############################################################################
##
#A  BravaisSupergroups( <G> ) . . . . .  Bravais supergroups of Bravais group
##
##  returns either BravaisSupergroupsOnRight(<G>) or 
##  BravaisSupergroupsOnLeft(<G>), depending on the value of 
##  `CrystGroupDefaultAction'.
DeclareGlobalFunction( "BravaisSupergroups" );

#############################################################################
##
#A  BravaisNormalizerInGLnZOnRight( <G> ) . normalizer of right Bravais group
##                                                               of G in GLnZ
##
##  returns the normalizer of the right Bravais group of <G> in the 
##  appropriate $GL_n(\Z)$.
DeclareAttribute( "BravaisNormalizerInGLnZOnRight", IsCyclotomicMatrixGroup );

#############################################################################
##
#A  BravaisNormalizerInGLnZOnLeft( <G> ) . . normalizer of left Bravais group 
##                                                               of G in GLnZ
##
##  returns the normalizer of the left Bravais group of <G> in the 
##  appropriate $GL_n(\Z)$.
DeclareAttribute( "BravaisNormalizerInGLnZOnLeft",  IsCyclotomicMatrixGroup );

#############################################################################
##
#A  BravaisNormalizerInGLnZ( <G> ) . . . . . . .  normalizer of Bravais group 
##                                                               of G in GLnZ
##
##  returns either BravaisNormalizerInGLnZOnRight(<G>) or 
##  BravaisNormalizerInGLnZOnLeft(<G>), depending on the value of 
##  `CrystGroupDefaultAction'.
DeclareGlobalFunction( "BravaisNormalizerInGLnZ" );

#############################################################################
##
#A  InvariantLatticeOnRight( G )
##
##  returns a basis of the $\Z$-lattice that is invariant under the 
##  rational matrix group <G> acting from the right. It returns `fail' 
##  if the group is not unimodular.
DeclareAttribute( "InvariantLatticeOnRight", IsCyclotomicMatrixGroup );

#############################################################################
##
#A  InvariantLatticeOnLeft( G )
##
##  returns a basis of the $\Z$-lattice that is invariant under the 
##  rational matrix group <G> acting from the left. It returns `fail' 
##  if the group is not unimodular.
DeclareAttribute( "InvariantLatticeOnLeft",  IsCyclotomicMatrixGroup );

#############################################################################
##
#A  InvariantLattice( G )
##
##  returns either InvariantLatticeOnRight(<G>) or 
##  InvariantLatticeOnLeft(<G>), depending on the value of 
##  `CrystGroupDefaultAction'.
DeclareGlobalFunction( "InvariantLattice" );

#############################################################################
##
#E  grpramat.gd . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##

