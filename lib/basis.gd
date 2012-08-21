#############################################################################
##
#W  basis.gd                    GAP library                     Thomas Breuer
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file declares the operations for bases of free left modules.
#1
##  A *basis* of a free left $F$-module $V$ of dimension $n$, say,
##  is an ordered list of vectors $B = [ v_1, v_2, \ldots, v_n ]$ in $V$
##  such that $V$ is generated as a left module by these vectors.
##  In {\GAP} bases behave like lists, i.e., their elements can be accessed
##  via [ ], and they have a length:
##  \beginexample
##  gap> V:= Rationals^3;
##  ( Rationals^3 )
##  gap> B:= Basis( V );
##  CanonicalBasis( ( Rationals^3 ) )
##  gap> B[1];
##  [ 1, 0, 0 ]
##  gap> Length( B );
##  3
##  \endexample
##
##  Besides the basic operations for lists
##  (see~"Basic Operations for Lists"),
##  the basic operations for bases are `BasisVectors', `Coefficients',
##  and `LinearCombination'.
##
##  {\GAP} supports three types of bases, namely
##  \beginlist
##  \item{1.}
##    *relative bases* that delegate the work to another basis of the same
##    left module (via a basechange matrix), 
##
##  \item{2.}
##    *bases handled by nice bases* that delegate the work to a basis
##    of an isomorphic left module over the same left acting domain, and
##
##  \item{3.}
##    bases that really do the work.
##  \endlist
##
##  *Constructors* for bases are `RelativeBasis' resp. `RelativeBasisNC'
##  in the case of relative bases, and `NewBasis' in the other cases.
##  Note that the left module knows whether its bases use nice bases or bases
##  that do the work, so appropriate methods of `NewBasis' can be installed.
##  `RelativeBasis' does only need one method.
##  
##  Examples:
##  \beginlist
##  \item{-}
##    In the case of Gaussian row and matrix spaces, 
##    `Basis( <V> )'
##    computes a semi-echelonized basis that uses Gaussian elimination.
##    A basis constructed with user supplied vectors is either
##    semi-echelonized or is a relative basis.
##
##  \item{-}
##    In the case of handling by nice bases, *no* basechange matrix is used
##    (the nice basis, however, is allowed to use a basechange matrix).
##
##  \item{-}
##    Non-Gaussian row and matrix spaces are handled via nice bases.
##
##  \item{-}
##    Field element spaces occur in two situations.
##    For the fields themselves and subfields special bases are used.
##    For a subspace of a field the nice basis is constructed
##    relative to a basis of the enveloping field.
##  \endlist
##
Revision.basis_gd :=
    "@(#)$Id$";


#############################################################################
##
#C  IsBasis( <obj> )
##
##  A basis of a free left module is an object that knows
##  how to compute coefficients w.r.t.~its basis vectors.
##  A basis is an immutable list,
##  the $i$-th entry being the $i$-th basis vector.
##
##  (See `IsMutableBasis' ("ref:ismutablebasis") for mutable bases.)
##
DeclareCategory( "IsBasis", IsHomogeneousList and IsDuplicateFreeList );


#############################################################################
##
#P  IsCanonicalBasis( <B> )
##
##  If the underlying free left module $V$ of the basis <B> supports a
##  canonical basis (see "CanonicalBasis") then `IsCanonicalBasis' returns
##  `true' if <B> is equal to the canonical basis of $V$,
##  and `false' otherwise.
##
DeclareProperty( "IsCanonicalBasis", IsBasis );


#############################################################################
##
#P  IsCanonicalBasisFullRowModule( <B> )
##
##  is `true' if the underlying free left module of the basis <B> is a full
##  row module and <B> is equal to its canonical basis,
##  and `false' otherwise.
##
DeclareProperty( "IsCanonicalBasisFullRowModule", IsBasis );

InstallTrueMethod( IsCanonicalBasis, IsCanonicalBasisFullRowModule );

InstallTrueMethod( IsSmallList,
    IsList and IsCanonicalBasisFullRowModule );


#############################################################################
##
#P  IsCanonicalBasisFullMatrixModule( <B> )
##
##  is `true' if the underlying free left module of the basis <B> is a full
##  matrix module and <B> is equal to its canonical basis,
##  and `false' otherwise.
##
DeclareProperty( "IsCanonicalBasisFullMatrixModule", IsBasis );

InstallTrueMethod( IsCanonicalBasis, IsCanonicalBasisFullMatrixModule );

InstallTrueMethod( IsSmallList,                               
    IsList and IsCanonicalBasisFullMatrixModule );


#############################################################################
##
#P  IsIntegralBasis( <B> )
##
##  is `true' if <B> is a basis for the ring of integers in the underlying
##  left module of <B>, which must be a field.
##
DeclareProperty( "IsIntegralBasis", IsBasis );


#############################################################################
##
#P  IsNormalBasis( <B> )
##
##  is `true' if <B> is invariant under the Galois group of the underlying
##  left module of <B>, which must be a field.
##
DeclareProperty( "IsNormalBasis", IsBasis );


#############################################################################
##
#P  IsSemiEchelonized( <B> )
##
##  is used for Gaussian row and matrix vector spaces. A basis is 
##  semi-echelonized if its basis vectors form an upper triangular matrix
##  with $1$-s on the diagonal.
##
DeclareProperty( "IsSemiEchelonized", IsBasis );


#############################################################################
##
#A  BasisVectors( <B> )
##
##  is the (immutable) list of basis vectors of the basis <B>.
##
DeclareAttribute( "BasisVectors", IsBasis );


#############################################################################
##
#A  EnumeratorByBasis( <B> )
##
##  is an enumerator for the underlying left module of the basis <B> w.r.t.
##  this basis.
##
DeclareAttribute( "EnumeratorByBasis", IsBasis );


#############################################################################
##
#A  StructureConstantsTable( <B> )
##
##  is defined only if the underlying left module of the basis <B> is also
##  a ring.
##
##  In this case `StructureConstantsTable' returns a structure constants
##  table $T$ in sparse representation, as used for structure constants
##  algebras (see Section "tut:algebras" of the user's tutorial).
## 
##  The coefficients of the product $b_i b_j$ of basis vectors are stored in
##  $T[i][j]$ as a list of length 2; its first entry is the list of positions
##  of nonzero coefficients, the second entry is the list of the coefficients
##  themselves.
##
##  The multiplication in an algebra $A$ with vector space basis <B>
##  with basis vectors $( v_1, \ldots, v_n )$ is determined by the so-called
##  structure matrices $M_k = [ m_{ijk} ]_{ij}, 1 \leq i \leq n$.
##  The $M_k$ are defined by $v_i v_j = \sum_k m_{i,j,k} v_k$.
##  Let $a = [ a_1, \ldots, a_n ], b = [ b_1, \ldots, b_n ]$.  Then
##  $$ ( \sum_i a_i v_i ) ( \sum_j b_j v_j )
##     = \sum_{i,j} a_i b_j ( v_i v_j )
##     = \sum_k ( \sum_j ( \sum_i a_i m_{i,j,k} ) b_j ) v_k
##     = \sum_k ( a M_k b^{tr} ) v_k \ . $$
##
DeclareAttribute( "StructureConstantsTable", IsBasis );


#############################################################################
##
#A  UnderlyingLeftModule( <B> )
##
##  Is the left module of which <B> is a basis.
##
DeclareAttribute( "UnderlyingLeftModule", IsBasis );


#############################################################################
##
#O  Coefficients( <B>, <v> )  . . . coefficients of <v> w.r. to the basis <B>
##
##  Let $V$ be the underlying left module of the basis <B>, and <v> a vector
##  such that the family of <v> is the elements family of the family of <V>.
##  Then `Coefficients( <B>, <v> )' is the list of coefficients of <v> w.r.t.
##  <B> if <v> lies in $V$, and `fail' otherwise.
##
DeclareOperation( "Coefficients", [ IsBasis, IsVector ] );


#############################################################################
##
#O  LinearCombination( <B>, <coeff> ) . . . . linear combination w. r. to <B>
#O  LinearCombination( <vectors>, <coeff> )
##
##  is the vector $\sum_{i=1}^n <coeff>[i] \* `BasisVectors( <B> )'[i]$.
##
DeclareOperation( "LinearCombination", [ IsBasis, IsHomogeneousList ] );


#############################################################################
##
#O  SiftedVector( <B>, <v> ) . . . . .  residuum of <v> w.r. to the basis <B>
##
##  Is the residuum of the vector <v> with respect to the basis <B>.
##  So `SiftedVector( <B>, <v> ) = 0' if and only if <v> lies in the
##  underlying left module of <B>.
##  This operation is defined only for semi-echelonized bases 
##  (or mutable bases) of Gaussian row and matrix vector spaces.
##  If the scalars in the vector <v> are not all contained in the base field
##  of the underlying left module of <B> then `fail' is returned.
##
DeclareOperation( "SiftedVector", [ IsBasis, IsVector ] );
#T more restrictive (SEB)?


#############################################################################
##
#O  IteratorByBasis( <B> )
##
##  is an iterator for the underlying left module of the basis <B> w.r.t.
##  this basis.
##
DeclareOperation( "IteratorByBasis", [ IsBasis ] );


#############################################################################
##
#A  Basis( <V> )
#O  Basis( <V>, <vectors> )
#O  BasisNC( <V>, <vectors> )
##
##  Called with a free left module <V> as the only argument,
##  `Basis' returns an arbitrary basis of <V>.
##
##  If additionally a list <vectors> of vectors in <V> is given
##  that forms a basis of <V> then `Basis' returns this basis;
##  if <vectors> are not linearly independent or do not generate <V>
##  as a free left module over the left acting domain of <V>
##  then `fail' is returned.
##
##  `BasisNC' does the same as `Basis' for two arguments,
##  except that it is not checked whether <vectors> form a basis.
##
DeclareAttribute( "Basis", IsFreeLeftModule );
DeclareOperation( "Basis", [ IsFreeLeftModule, IsHomogeneousList ] );

DeclareOperation( "BasisNC", [ IsFreeLeftModule, IsHomogeneousList ] );


#############################################################################
##
#A  SemiEchelonBasis( <V> )
#O  SemiEchelonBasis( <V>, <vectors> )
#O  SemiEchelonBasisNC( <V>, <vectors> )
##
##  Let <V> be a Gaussian row or matrix vector space over the field $F$.
##  A basis of <V> is called *semi-echelonized* if its basis vectors form
##  a semi-echelonized matrix (see~"SemiEchelonMat").
##
##  Called with <V> as the only argument,
##  `SemiEchelonBasis' returns an arbitrary semi-echelonized basis of <V>.
##
##  If additionally a list <vectors> of vectors in <V> is given
##  that forms a semi-echelonized basis of <V> then `SemiEchelonBasis'
##  returns this basis;
##  if <vectors> do not form a basis of <V> then `fail' is returned.
##
##  `SemiEchelonBasisNC' does the same as `SemiEchelonBasis' for two
##  arguments,
##  except that it is not checked whether <vectors> form
##  a semi-echelonized basis.
##
DeclareAttribute( "SemiEchelonBasis", IsFreeLeftModule );
DeclareOperation( "SemiEchelonBasis",
    [ IsFreeLeftModule, IsHomogeneousList ] );

DeclareOperation( "SemiEchelonBasisNC",
    [ IsFreeLeftModule, IsHomogeneousList ] );
#T In fact they should be declared for `IsGaussianSpace', or at least for
#T `IsVectorSpace', but the files containing these categories are read later ..
#T (Change this!)


#############################################################################
##
#O  NewBasis( <V> )
#O  NewBasis( <V>, <gens> )
##
##  Note that `Basis' cannot be a basis constructor
##  (i.e., an operations whose methods have to call `Objectify'),
##  since one must be able to install methods for these operations,
##  depending on the free module in question.
##  (And there is a default method for `Basis' with two arguments,
##  using `Basis' as an attribute and the construction of a relative basis.)
##
DeclareOperation( "NewBasis", [ IsFreeLeftModule, IsCollection ] );


#############################################################################
##
#O  RelativeBasis( <B>, <vectors> )
#O  RelativeBasisNC( <B>, <vectors> )
##
##  A relative basis is a basis of the free left module <V> that delegates
##  the computation of coefficients etc. to another basis of <V> via
##  a basechange matrix.
##
##  Let <B> be a basis of the free left module <V>,
##  and <vectors> a list of vectors in <V>.
##
##  `RelativeBasis' checks whether <vectors> form a basis of <V>,
##  and in this case a basis is returned in which <vectors> are
##  the basis vectors; otherwise `fail' is returned.
##
##  `RelativeBasisNC' does the same, except that it omits the check.
##
DeclareOperation( "RelativeBasis", [ IsBasis, IsHomogeneousList ] );
DeclareOperation( "RelativeBasisNC", [ IsBasis, IsHomogeneousList ] );


#############################################################################
##
#C  IsBasisByNiceBasis( <B> )
##
##  Let $B$ be a basis of the free left $F$-module $V$.
##  Computations in $V$ may be easy as long as no basis dependent
##  calculations occur, but usually there is a canonical way to delegate the
##  computation of basis vectors, coefficients w.r.t. $B$ etc.
##  to a basis $C$ of an isomorphic ``nicer'' left $F$-module,
##  which usually is a row vector space or a matrix vector space,
##  and thus allows one to apply Gaussian elimination. 
##  $C$ is called the {\it nice basis} of $B$, its underlying space $W$
##  is called the {\it nice vector space} of $V$.
##  (It is *not* required that the nice vector space is a coefficient space.)
##
##  $B$ stores $C$ as value of the attribute `NiceBasis', and $B$ knows how
##  to convert elements of $V$ to the corresponding elements of $W$,
##  and vice versa.
##
##  Any object in `IsBasisByNiceBasis' must be a small list in the sense of
##  `IsSmallList'.
##
##  If left module generators for $V$ are known then the usual process is as
##  follows.
##  \beginlist
##  \item{1.}
##     `B:= Basis( <V> )'
##           computes a basis for <V>, without basis vectors.
##  \item{2.}
##     `PrepareNiceFreeLeftModule( <V> )'
##           computes the necessary data for the bijections
##  \item{3.}
##     `W:= NiceFreeLeftModule( <V> )'
##           computes the left module generated by the images of
##           left module generators of <V> under the homomorphism mentioned
##           above.
##           (There are two generic methods for this, namely for the cases
##           that either left module generators of <V> are known or that
##           <V> is a FLMLOR(-with-one) with known left operator
##           ring(-with-one) generators.)
##  \item{3.}
##     `C:= Basis( W )'
##           computes a basis of the nice module `W' (That this is possible
##           is a problem of `W' and must of course be assumed!).
##  \item{4.}
##     `BasisVectors( B )'
##           computes the preimages of `BasisVectors( C )' under the
##           homomorphism.
##  \endlist
##
##  The default of `NiceBasis( <B> )' is
##  `Basis( NiceFreeLeftModule( <V> ) )' if no basis vectors are bound in
##  <B>, and this will usually be a semi-echelonized basis;
##  thus such a basis will be chosen in the call `Basis( <V> )'.
##  If basis vectors are stored in <B> then the nice vectors of
##  these vectors are taken as basis vectors.
##  `NiceBasisNC( <B> )' does not check whether the basis vectors of
##  <B> really form a basis.
##
##  (The only situation where the `NC' version is not used is in the
##  construction of bases with prescribed vectors.)
##
##  If left module generators of <V> are known, and if <V> is finite
##  then there is a default method to compute a nice free left module,
##  namely computing all elements of the left module,
##  and in parallel computing a basis.
##
##  Details of the implementation.
##
##  To install a new type of free left modules that uses the mechanism of
##  nice bases means
##  1. to create a new representation of free left modules in the category
##     `IsHandledByNiceBasis';
##     for that, one has to install methods for `LeftModuleByGenerators'
##     (and in the case of FLMLORs also for `FLMLORByGenerators')
##  2. to install methods for the operations
##     `PrepareNiceFreeLeftModule( <V> )' : \\
##       This function has to provide the necessary information (if any)
##       for calls of `NiceVector' and `UglyVector'.
##
##     `NiceVector( <V>, <v> )' : \\
##       is the nice vector $r \in W$ associated to the vector <v> of $V$,
##       or `fail'.
##       It can be assumed that `PrepareNiceFreeLeftModule( <V> )'
##       has been called before.
##
##     `UglyVector( <V>, <r> )' : \\
##       is the vector $v \in V$ associated to the nice vector
##       $r \in W$, or `fail'.
##
##  *Note* that `NiceVector' and `UglyVector' may yield
##  incorrect results if <v> resp. <r> is not an element of $V$ resp. $W$.
##
##  The computation of a basis of $V$ does *not* necessarily cause the
##  computation of basis vectors.  For that, the computation of the
##  nice module, its basis, its basis vectors,
##  and then the ugly vectors in $V$ may be necessary.
##  (example: spaces of polynomials)
##
DeclareCategory( "IsBasisByNiceBasis", IsBasis and IsSmallList );


#############################################################################
##
#A  NiceBasis( <B> )
##
##  Let <B> be a basis of a free left module <V> that is handled via
##  nice bases.
##  If <B> has no basis vectors then `NiceBasis( <B> )' is a basis of
##  `NiceFreeLeftModule( <V> )'.
##  Otherwise `NiceBasis( <B> )' is the result of the call of
##  `Basis' with arguments `NiceFreeLeftModule( <V> )'
##  and the nice vectors of the basis vectors;
##  note that this result is either the desired basis $C$, say, or `fail',
##  where the latter case occurs if and only if the prescribed
##  ``basis vectors'' are in fact not basis vectors.
##
##  The attributes `GeneratorsOfLeftModule' of the underlying left modules
##  of <B> and $C$ correspond via `NiceVector' and `UglyVector'.
##
DeclareAttribute( "NiceBasis", IsBasisByNiceBasis );


#############################################################################
##
#O  NiceBasisNC( <B> )
##
##  If the basis <B> has basis vectors bound then the attribute `NiceBasis'
##  of <B> is set to `BasisNC( <W>, <nice> )'
##  where <W> is the value of `NiceFreeLeftModule' for the underlying
##  free left module of <B>.
##  This means that it is *not* checked whether <B> really is a basis.
##
DeclareOperation( "NiceBasisNC", [ IsBasisByNiceBasis ] );


#############################################################################
##
#A  NiceFreeLeftModule( <V> ) . . . . nice free left module isomorphic to <V>
##
DeclareAttribute( "NiceFreeLeftModule", IsFreeLeftModule );


#############################################################################
##
#O  PrepareNiceFreeLeftModule( <V> )
##
##  stores the data in <V> that are needed to compute `NiceVector' and
##  `UglyVector'.
##
DeclareOperation( "PrepareNiceFreeLeftModule",
    [ IsFreeLeftModule and IsHandledByNiceBasis ] );


#############################################################################
##
#O  NiceVector( <V>, <v> )
#O  UglyVector( <V>, <r> )
##
##  `NiceVector' and `UglyVector' provide the linear bijection between the
##  free left module <V> and `<W>:= NiceFreeLeftModule( <V> )'.
##
##  If <v> lies in the elements family of the family of <V> then
##  `NiceVector( <v> )' is either `fail' or an element in the elements family
##  of the family of <W>.
##
##  If <r> lies in the elements family of the family of <W> then
##  `UglyVector( <r> )' is either `fail' or an element in the elements family
##  of the family of <V>.
##
##  If <v> lies in <V> (which usually cannot be checked without using <W>)
##  then `UglyVector( <V>, NiceVector( <V>, <v> ) ) = <v>'.
##  If <r> lies in <W> (which usually can be checked)
##  then `NiceVector( <V>, UglyVector( <V>, <r> ) ) = <r>'.
##
##  (This allows one for example to implement a membership test for <V>
##  using the membership test in <W>.)
##
##  Note that `NiceVector' and `UglyVector' may fail if <V> is a free module
##  for that `PrepareNiceFreeLeftModule' was not yet called.
##
DeclareOperation( "NiceVector",
    [ IsFreeLeftModule and IsHandledByNiceBasis, IsVector ] );

DeclareOperation( "UglyVector",
    [ IsFreeLeftModule and IsHandledByNiceBasis, IsVector ] );


#############################################################################
##
#F  BasisWithReplacedLeftModule( <B>, <V> )
##
##  For a basis <B> and a left module <V> that is equal to the underlying
##  left module of <B>,
##  `BasisWithReplacedLeftModule' returns a basis equal to <B> except that
##  the underlying left module of this basis is <V>.
##
DeclareGlobalFunction( "BasisWithReplacedLeftModule" );


#############################################################################
##
#E

#############################################################################
##
#A  BasisOfDomain( <V> )
#O  BasisByGenerators( <V>, <vectors> )
#O  BasisByGeneratorsNC( <V>, <vectors> )
#A  SemiEchelonBasisOfDomain( <V> )
#O  SemiEchelonBasisByGenerators( <V>, <vectors> )
#O  SemiEchelonBasisByGeneratorsNC( <V>, <vectors> )
##
DeclareSynonymAttr( "BasisOfDomain", Basis );
DeclareSynonym( "BasisByGenerators", Basis );
DeclareSynonym( "BasisByGeneratorsNC", BasisNC );
DeclareSynonymAttr( "SemiEchelonBasisOfDomain", SemiEchelonBasis );
DeclareSynonym( "SemiEchelonBasisByGenerators", SemiEchelonBasis );
DeclareSynonym( "SemiEchelonBasisByGeneratorsNC", SemiEchelonBasisNC );
#T obsolete!


