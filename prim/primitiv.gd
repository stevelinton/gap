#############################################################################
##
#W  primitiv.gd              GAP group library  Dixon,Mortimer,Short,Thei"sen
##
#H  @(#)$Id$
##
##
Revision.primitiv_gd :=
    "@(#)$Id$";

#############################################################################
##
## tell GAP about the component
##
DeclareComponent("prim","1.0");

#############################################################################
##
#F  PrimitiveGroup(<deg>,<nr>)
##
##  returns the primitive permutation  group of degree <deg> with number <nr>
##  from the list. 
##
##  *The library of primitive groups (as given in \cite{Theissen97}) currently
##  does not store all the groups, but computes them ``on the fly''. Therefore
##  it cannot be guaranteed that the arrangement of the groups will remain the
##  same between different versions of {\GAP} or after making further methods
##  available! Therefore when using or quoting primitive groups in a context
##  that leaves one {\GAP} session it is not sufficient to talk about group
##  number <nr> of degree <deg>, but actual generators must be given!*
##
##  The groups are sorted in the following way: For $<deg>\le
##  255$ first  come affine groups. If <deg> is a prime <p> it starts with the
##  one-dimensional affine  groups over the field $F_p$, that is Frobenius
##  groups of the  form $ F_p{:}A$ for a  subgroup $A\le{\rm Aut}(F_p)$.  Then
##  come the other solvable  affine groups, in the same order as in the list of
##  M.~Short (who did not include the Frobenius groups).  Next  in the list
##  come the insolvable affine primitive  permutation groups.
##
##  Then come the   non-affine primitive permutation  groups  of degree <deg>.
##  They have been  classified  into cohorts in  \cite{DixonMortimer88},  and
##  {\GAP}    represents a     cohort   as a     homomorphism   $\kappa\colon
##  N=N_{S_{<deg>}}(S)\to A$ whose kernel $S$  is the socle  of $N$ and every
##  primitive group in that cohort is the preimage of a subgroup of $A$ (only
##  one from   each conjugacy  class)  under $\kappa$.   For the  degrees  in
##  question,  $A$ is solvable. All  primitive groups in  the cohort $\kappa$
##  have the same socle, namely~$S$. The groups  of each cohort appear in the
##  list consecutively.
##
##  (The functions `NrAffinePrimitiveGroups and `NrSolvablePrimitiveGroups' can
##  be used to determine where the different parts of the lists start.)
##
##  This arrangement *differs* from the arrangement of primitive groups in the
##  list of C.~Sims, which was used in {\GAP}~3. See `PrimitiveGroupSims'
##  ("PrimitiveGroupSims").

UnbindGlobal( "PrimitiveGroup" );
DeclareGlobalFunction( "PrimitiveGroup" );

#############################################################################
##
#F  NrPrimitiveGroups(<deg>)
##
##  returns the number of primitive permutation groups of degree <deg> in the
##  library.
DeclareGlobalFunction( "NrPrimitiveGroups" );

#############################################################################
##
#F  NrAffinePrimitiveGroups(<deg>)
##
##  returns the number of affine primitive permutation groups of degree <deg>
##  in the library.
UnbindGlobal( "NrAffinePrimitiveGroups" );
DeclareGlobalFunction( "NrAffinePrimitiveGroups" );

#############################################################################
##
#F  NrSolvableAffinePrimitiveGroups(<deg>)
##
##  returns the number of solvable affine primitive permutation groups of
##  degree <deg> in the library.
UnbindGlobal( "NrSolvableAffinePrimitiveGroups" );
DeclareGlobalFunction( "NrSolvableAffinePrimitiveGroups" );

#############################################################################
##
#F  PrimitiveGroupSims(<deg>,<nr>)
##
##  For  compatibility with earlier versions  of {\GAP}, the original list of
##  Sims, with the same numbers and the names given by Buekenhout and Leemans
##  \cite{BuekenhoutLeemans96},  is also   included.  It is accessed  by  the
##  function  `PrimitiveGroupSims'.
DeclareGlobalFunction( "PrimitiveGroupSims" );

#############################################################################
##
#A  SimsNo(<G>)
##
##  If <G> is a primitive group obtained by `PrimitiveGroup' (respectively one
##  of the selection functions) this attribute contains the number of the
##  isomorphic group in the original list of Sims.
DeclareAttribute( "SimsNo", IsPermGroup );

#############################################################################
##
#A  SimsName(<G>)
##
##  If <G> is a primitive group obtained by `PrimitiveGroup' (respectively one
##  of the selection functions) this attribute contains the name of the
##  isomorphic group in the original list of Sims.
DeclareAttribute( "SimsName", IsPermGroup );


#############################################################################
##
#F  IrreducibleSolvableGroup( <n>, <p>, <i> )
##
## returns  the   <i>-th  irreducible  solvable subgroup  of GL(  <n>,  <p> ).
## The  irreducible  solvable subgroups of GL(n,p) are ordered with respect to
## the following criteria:
##  \beginlist
##  \item{-} increasing size;
##  \item{-} increasing guardian number.
##  \endlist
##  If two groups have the same size and guardian, they  are in no particular
##  order.  (See the library documentation   or  \cite{Sho92} for the meaning
##  of guardian.)
DeclareGlobalFunction( "IrreducibleSolvableGroup" );

#############################################################################
##
#F  AffinePermGroupByMatrixGroup( <M> )
##
##  takes a matrix group <M> and constructs a affine permutation group $V{:}M$
##  from this with $V$ being the vector space for the natural action of <M>.
DeclareGlobalFunction( "AffinePermGroupByMatrixGroup" );

#############################################################################
##
#F  PrimitiveAffinePermGroupByMatrixGroup( <M> )
##
##  works as `AffinePermGroupByMatrixGroup' but assumes that <M> acts
##  irreducibly. (This reduces the number of generators.)
DeclareGlobalFunction( "PrimitiveAffinePermGroupByMatrixGroup" );

coh := "2b defined";

DeclareGlobalFunction( "RepOpSuborbits" );
DeclareGlobalFunction( "OnSuborbits" );
DeclareGlobalFunction( "ConstructCohort" );
DeclareGlobalFunction( "CohortOfGroup" );
DeclareGlobalFunction( "MakeCohort" );
DeclareGlobalFunction( "AlternatingCohortOnSets" );
DeclareGlobalFunction( "LinearCohortOnProjectivePoints" );
DeclareGlobalFunction( "SymplecticCohortOnProjectivePoints" );
DeclareGlobalFunction( "UnitaryCohortOnProjectivePoints" );
DeclareGlobalFunction( "CohortProductAction" );
DeclareGlobalFunction( "CohortPowerAlternating" );
DeclareGlobalFunction( "CohortPowerLinear" );
DeclareGlobalFunction( "CohortDiagonalAction" );
DeclareGlobalFunction( "GLnbylqtolInGLnq" );
DeclareGlobalFunction( "FrobInGLnq" );
DeclareGlobalFunction( "StabFldExt" );

DeclareGlobalFunction( "AlmostDerivedSubgroup" );

DeclareGlobalVariable( "AFFINE_NON_SOLVABLE_GROUPS", "..." );

DeclareGlobalFunction( "BOOT_AFFINE_NON_SOLVABLE_GROUPS" );
DeclareGlobalFunction( "Cohort" );
DeclareGlobalFunction( "MakePrimitiveGroup" );

COHORTS := [  ];
COHORTS_DONE := [  ];
SIMS_NUMBERS := [  ];
SIMS_NAMES := [  ];

#############################################################################
##
#F  ReadCohorts( <name> ) . . . . . . . . . . . . .  primitive groups
##
BIND_GLOBAL("ReadCohorts",ReadAndCheckFunc("prim/cohorts"));
BIND_GLOBAL("RereadCohorts",RereadAndCheckFunc("prim/cohorts"));

#############################################################################
##
#E  primitiv.gd . . . . . . . . . . . . . . . . . . . . . . . . . . ends here

