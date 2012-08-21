#############################################################################
##
#W  ctblpope.gd                 GAP library                     Thomas Breuer
#W                                                           & Goetz Pfeiffer
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the declaration of those functions  that are needed to
##  compute and test possible permutation characters.
##
#N  TODO:
#N  - `IsPermChar( <tbl>, <pc> )'
#N    (check whether <pc> can be a permutation character of <tbl>;
#N     use also the kernel of <pc>, i.e., check whether the kernel factor
#N     of <pc> can be a permutation character of the factor of <tbl> by the
#N     kernel; one example where this helps is the sum of characters of S3
#N     in O8+(2).3.2)
#N  - `Constituent' und `Maxdeg' - Optionen in `PermComb'
#T  - option to compute only multiplicity free candidates?

#1
##  For groups $H$ and $G$ with $H \leq G$,
##  the induced character $(1_G)^H$ is called the *permutation character*
##  of the operation of $G$ on the right cosets of $H$.
##  If only the character table of $G$ is available and not the group $G$
##  itself, one can try to get informations about possible subgroups of $G$
##  by inspection of those $G$-class functions that might be
##  permutation characters, using that such a class function $\pi$ must have
##  at least the following properties.
##  (For a proof, see~\cite{Isa76}, Theorem~5.18.)
##  \beginlist
##  \item{(a)}
##      $\pi$ is a character of $G$,
##  \item{(b)}
##      $\pi(g)$ is a nonnegative integer for all $g \in G$,
##  \item{(c)}
##      $\pi(1)$ divides $|G|$,
##  \item{(d)}
##      $\pi(g^n) \geq \pi(g)$ for $g \in G$ and integers $n$,
##  \item{(e)}
##      $[\pi,1_G] = 1$,
##  \item{(f)}
##      the multiplicity of any rational irreducible $G$-character $\psi$
##      as a constituent of $\pi$ is at most $\psi(1)/[\psi,\psi]$,
##  \item{(g)}
##      $\pi(g) = 0$ if the order of $g$ does not divide $|G|/\pi(1)$,
##  \item{(h)}
##      $\pi(1) |N_G(g)|$ divides $\pi(g) |G|$ for all $g \in G$,
##  \item{(i)}
##      $\pi(g) \leq (|G| - \pi(1)) / (|g^G| |Gal_G(g)|)$ for all nonidentity
##      $g \in G$, where $|Gal_G(g)|$ denotes the number of conjugacy classes
##      of $G$ that contain generators of the group $\langle g \rangle$,
##  \item{(j)}
##      if $p$ is a prime that divides $|G|/\pi(1)$ only once then $s/(p-1)$
##      divides $|G|/\pi(1)$ and is congruent to $1$ modulo $p$,
##      where $s$ is the number of elements of order $p$ in the
##      (hypothetical) subgroup $H$ for which $\pi = (1_H)^G$ holds.
##      (Note that $s/(p-1)$ equals the number of Sylow $p$ subgroups in
##      $H$.)
##  \endlist
##  Any $G$-class function with these properties is called a
##  *possible permutation character* in {\GAP}.
##
##  (Condition (d) is checked only for those power maps that are stored in
##  the character table of $G$;
##  clearly (d) holds for all integers if it holds for all prime divisors of
##  the group order $|G|$.)
##  
##  {\GAP} provides some algorithms to compute
##  possible permutation characters, see~"PermChars".
##  Some information about the subgroup $U$ can be computed from the
##  permutation character $(1_U)^G$ using `PermCharInfo'
##  (see~"PermCharInfo").
##
Revision.ctblpope_gd :=
    "@(#)$Id$";


#############################################################################
##
#F  PermCharInfo( <tbl>, <permchars> )
##
##  Let <tbl> be the ordinary character table of the group $G$,
##  and `permchars' either the permutation character $(1_U)^G$,
##  for a subgroup $U$ of $G$, or a list of such permutation characters.
##  `PermCharInfo' returns a record with components
##
##  \beginitems
##  `contained': &
##    a list containing, for each character $\psi = (1_U)^G$ in <permchars>,
##    a list containing at position $i$ the number
##    $\psi[i] |U| / `SizesCentralizers( <tbl> )'[i]$,
##    which equals the number of those elements of $U$
##    that are contained in class $i$ of <tbl>,
##    
##  `bound': &
##    a list containing, for each character $\psi = (1_U)^G$ in <permchars>,
##    a list containing at position $i$ the number
##    $|U| / \gcd( |U|, `SizesCentralizers( <tbl> )'[i] )$,
##    which divides the class length in $U$ of an element in class $i$
##    of <tbl>,
##
##  `display': &
##    a record that can be used as second argument of `Display'
##    to display each permutation character in <permchars> and the
##    corresponding components `contained' and `bound',
##    for those classes where at least one character of <permchars> is
##    nonzero,
##
##  `ATLAS': &
##    a list of strings describing the decomposition of the permutation
##    characters in <permchars> into the irreducible characters of <tbl>,
##    given in an {\ATLAS}-like notation.
##    This means that the irreducible constituents are indicated by their
##    degrees followed by lower case letters `a', `b', `c', \ldots,
##    which indicate the successive irreducible characters of <tbl>
##    of that degree, in the order in which they appear in `Irr( <tbl> )'.
##    A sequence of small letters (not necessarily distinct) after a single
##    number indicates a sum of irreducible constituents all of the same
##    degree, an exponent of the form `<lett>^{<n>}' means the letter <lett>
##    is repeated <n> times.
##  \enditems
##
DeclareGlobalFunction( "PermCharInfo" );


#############################################################################
##
#F  TestPerm1( <tbl>, <char> ) . . . . . . . . . . . . . . . .  test permchar
#F  TestPerm2( <tbl>, <char> ) . . . . . . . . . . . . . . . .  test permchar
#F  TestPerm3( <tbl>, <chars> )  . . . . . . . . . . . . . . . test permchars
#F  TestPerm4( <tbl>, <permch>, <modtbl> ) . . . . . . . . . .  test permchar
##
##  These functions implement tests of the properties of possible permutation
##  characters listed in Section~"Possible Permutation Characters".
##  Let <tbl> be an ordinary character table, <char> a rational character of
##  <tbl>, and <chars> a list of rational characters of <tbl>.
##
##  The return values of the functions were chosen parallel to the tests
##  listed in~\cite{NPP84}.
##
##  `TestPerm1' return `1' or `2' if <char> fails because of (T1) or (T2),
##  respectively; this corresponds to the criteria (b) and (d).
##  Note that only those power maps are considered that are stored on <tbl>.
##  If <char> satisfies the conditions, `0' is returned.
##
##  `TestPerm2' returns `1' if <char> fails because of the criterion (c),
##  it returns `3', `4', or `5' if <char> fails because of (T3), (T4),
##  or (T5), respectively;
##  these tests correspond to (g), a weaker form of (h), and (j).
##  If <char> satisfies the conditions, `0' is returned.
##
##  `TestPerm3' returns the list of all those class functions in <chars>
##  that satisfy criterion (h); this is a stronger version of (T6).
##
##  `TestPerm4' returns the list of all those class functions in <permch>
##  that fail because of (T9), with respect to the modular character table
##  <modtbl>.
##
#T say a word about (T7) and (T8)?
##
DeclareGlobalFunction( "TestPerm1" );
DeclareGlobalFunction( "TestPerm2" );
DeclareGlobalFunction( "TestPerm3" );
DeclareGlobalFunction( "TestPerm4" );
#T implementation of TestPerm4 is missing!!


#############################################################################
##
#F  PermChars( <tbl> )
#F  PermChars( <tbl>, <degree> )
#F  PermChars( <tbl>, <arec> )
##
##  {\GAP} provides several algorithms to determine
##  possible permutation characters from a given character table.
##  They are described in detail in~\cite{BP98}.
##  The algorithm is selected from the choice of the record components of the
##  optional argument record <arec>.
##  The user is encouraged to try different approaches,
##  especially if one choice fails to come to an end.
##  
##  Regardless of the algorithm used in a specific case,
##  `PermChars' returns a list of *all* possible permutation characters
##  with the properties described by <arec>.
##  There is no guarantee that a character of this list is in fact
##  a permutation character.
##  But an empty list always means there is no permutation character
##  with these properties (e.g., of a certain degree).
##  
##  In the first form `PermChars' returns the list of all
##  possible permutation characters of the group with character table <tbl>.
##  This list might be rather long for big groups,
##  and its computation might take much time.
##  The algorithm is described in Section~3.2 in~\cite{BP98};
##  it depends on a preprocessing step, where the inequalities
##  arising from the condition $\pi(g) \geq 0$ are transformed into
##  a system of inequalities that guides the search (see~"Inequalities").
##  So the following commands compute the list of 39 possible permutation
##  characters of the Mathieu group $M_{11}$.
##  \beginexample
##  gap> m11:= CharacterTable( "M11" );;
##  gap> SetName( m11, "m11" );
##  gap> perms:= PermChars( m11 );;
##  gap> Length( perms );
##  39
##  \endexample
##  There are two different search strategies for this algorithm.
##  The default strategy simply constructs all characters with nonnegative
##  values and then tests for each such character whether its degree
##  is a divisor of the order of the group.
##  The other strategy uses the inequalities to predict
##  whether a character of a certain degree can lie
##  in the currently searched part of the search tree.
##  To choose this strategy, use the third form of `PermChars'
##  and set the component `degree' to the range of degrees
##  (which might also be a range containing all divisors of the group order)
##  you want to look for;
##  additionally, the record component `ineq' can take the inequalities
##  computed by `Inequalities' if they are needed more than once.
##  
##  In the second form `PermChars' returns the list of all
##  possible permutation characters of <tbl> that have degree <degree>.
##  For that purpose, a preprocessing step is performed where
##  essentially the rational character table is inverted
##  in order to determine boundary points for the simplex
##  in which the possible permutation characters of the given degree
##  must lie (see~"PermBounds").
##  The algorithm is described at the end of Section~3.2 in~\cite{BP98};
##  Note that inverting big integer matrices needs a lot of time and space.
##  So this preprocessing is restricted to groups with less than 100 classes,
##  say.
##  \beginexample
##  gap> deg220:= PermChars( m11, 220 );
##  [ Character( m11 ), [ 220, 4, 4, 0, 0, 4, 0, 0, 0, 0 ] ),
##    Character( m11 ), [ 220, 12, 4, 4, 0, 0, 0, 0, 0, 0 ] ),
##    Character( m11 ), [ 220, 20, 4, 0, 0, 2, 0, 0, 0, 0 ] ) ]
##  \endexample
##  
##  In the third form `PermChars' returns the list of all
##  possible permutation characters that have the properties described by
##  the argument record <arec>.
##  One such situation has been mentioned above.
##  If <arec> contains a degree as value of the record component `degree'
##  then `PermChars' will behave exactly as in the second form.
##  \beginexample
##  gap> deg220 = PermChars( m11, rec( degree:= 220 ) );
##  true
##  \endexample
##  For the meaning of additional components of <arec> besides `degree',
##  see~"PermComb".
##
##  Instead of `degree', <arec> may have the component `torso' bound
##  to a list that contains some known values of the required characters
##  at the right positions;
##  at least the degree `<arec>.torso[1]' must be an integer.
##  In this case, the algorithm described in Section~3.3 in~\cite{BP98}
##  is chosen.
##  The component `chars', if present, holds a list of all those *rational*
##  irreducible characters of <tbl> that might be constituents of the
##  required characters.
##  (*Note*: If `<arec>.chars' is bound and does not contain *all* rational
##  irreducible characters of <tbl>, {\GAP} checks whether the scalar
##  products of all class functions in the result list with the omitted
##  rational irreducible characters of <tbl> are nonnegative;
##  so there should be nontrivial reasons for excluding a character
##  that is known to be not a constituent of the desired possible permutation
##  characters.
##  \beginexample
##  gap> PermChars( m11, rec( torso:= [ 220 ] ) );
##  [ Character( m11 ), [ 220, 4, 4, 0, 0, 4, 0, 0, 0, 0 ] ),
##    Character( m11 ), [ 220, 20, 4, 0, 0, 2, 0, 0, 0, 0 ] ),
##    Character( m11 ), [ 220, 12, 4, 4, 0, 0, 0, 0, 0, 0 ] ) ]
##  gap> PermChars( m11, rec( torso:= [ 220,,,,, 2 ] ) );
##  [ Character( m11, [ 220, 20, 4, 0, 0, 2, 0, 0, 0, 0 ] ) ]
##  \endexample
##
##  The class functions returned by `PermChars' have the properties tested by
##  `TestPerm1', `TestPerm2', and `TestPerm3'.
##  So they are possible permutation characters.
##  Note that `TestPerm4' may be used to prove that certain possible
##  permutation characters are in fact not permutation characters.
##
DeclareGlobalFunction( "PermChars" );


#############################################################################
##
#F  ClassOrbitCharTable( <tbl>, <cc> )  . . . .  classes of a cyclic subgroup
##
##  is the list of positions of those conjugacy classes
##  of the character table <tbl> that are Galois conjugate to the <cc>-th
##  class.
##  That is, exactly the classes at positions given by the list returned by
##  `ClassOrbitCharTable' contain generators of the cyclic group generated
##  by an element in the <cc>-th class.
##
##  This information is computed from the power maps of <tbl>.
##
DeclareGlobalFunction( "ClassOrbitCharTable" );


#############################################################################
##
#F  ClassRootsCharTable( <tbl> )  . . . . . . . . nontrivial root of elements
##
##  For a character table <tbl>, `ClassRootsCharTable' returns a list
##  containing at position $i$ the list of positions of the classes
##  of all nontrivial $p$-th roots, where $p$ runs over the prime divisors  
##  of `Size( <tbl> )'.
##
##  This information is computed from the power maps of <tbl>.
##
DeclareGlobalFunction( "ClassRootsCharTable" );


#############################################################################
##
#F  Inequalities( <tbl>, <chars>[, <option>] )
##
##  Let <tbl> be the ordinary character table of a group $G$.
##  The condition $\pi(g) \geq 0$ for every possible permutation character
##  $\pi$ of $G$ places restrictions on the multiplicities $a_i$
##  of the irreducible constituents $\chi_i$
##  of $\pi = \sum_{i=1}^r a_i \chi_i$.
##  For every element $g \in G$, we have $\sum_{i=1}^r a_i \chi_i(g) \geq 0$.
##  The power maps provide even stronger conditions.
##
##  This system of inequalities is kind of diagonalized,
##  resulting in a system of inequalities restricting $a_i$
##  in terms of $a_j$, $j \< i$.
##  These inequalities are used to construct characters with nonnegative
##  values (see~"PermChars").
##  `PermChars' either calls `Inequalities' or takes this information
##  from the `ineq' component of its argument record.
##
##  The number of inequalities arising in the process of diagonalization may
##  grow very strong.
##
##  There are two ways to organize the projection.
##  The first, which is chosen if no <option> argument is present,
##  is the straight approach which takes the rational irreducible
##  characters in their original order and by this guarantees the character
##  with the smallest degree to be considered first.
##  The other way, which is chosen if the string `\"small\"' is entered as
##  third argument, tries to keep the number of intermediate inequalities
##  small by eventually changing the order of characters.
##
DeclareGlobalFunction( "Inequalities" );


#############################################################################
##
#F  Permut( <tbl>, <arec> )
##
##  `Permut' computes possible permutation characters of the character table
##  <tbl> by the algorithm that
##  solves a system of inequalities.
##  This is described in Section~3.2 in~\cite{BP98}.
#T what about <arec> ?
##
DeclareGlobalFunction( "Permut" );


#############################################################################
##
#F  PermBounds( <tbl>, <d> ) . . . . . . . . . .  boundary points for simplex 
##
##  Let <tbl> be the ordinary character table of the group $G$.
##  All $G$-characters $\pi$ satisfying $\pi(g) > 0$ and $\pi(1) = <d>$,
##  for a given degree <d>, lie in a simplex described by these conditions.
##  `PermBounds' computes the boundary points of this simplex for  $d = 0$,
##  from which the boundary points for any other <d> are easily derived.
##  (Some conditions from the power maps of <tbl> are also involved.)
##  For this purpose, a matrix similar to the rational character table of $G$
##  has to be inverted.
##  These boundary points are used by `PermChars' (see~"PermChars")
##  to construct all possible permutation characters
##  (see~"Possible Permutation Characters") of a given degree.
##  `PermChars' either calls `PermBounds' or takes this information from the
##  `bounds' component of its argument record.
##
DeclareGlobalFunction( "PermBounds" );


#############################################################################
##
#F  PermComb( <tbl>, <arec> ) . . . . . . . . . . . .  permutation characters
##
##  `PermComb' computes possible permutation characters of the character
##  table <tbl> by the improved combinatorial approach
##  described at the end of Section~3.2 in~\cite{BP98}.
##
##  For computing the possible linear combinations *without* prescribing
##  better bounds (i.e., when the computation of bounds shall be suppressed),
##  enter `<arec>:= rec( degree := <degree>, bounds := false )',
##  where <degree> is the character degree;
##  this is useful if the multiplicities are expected to be small,
##  and if this is forced by high irreducible degrees.
##
##  Upper bounds on the multiplicities of the constituents can be explicitly
##  prescribed via a `maxmult' component in <arec>.
##
DeclareGlobalFunction( "PermComb" );


#############################################################################
##
#F  PermCandidates( <tbl>, <characters>, <torso> )
##
##  `PermCandidates' computes possible permutation characters of the
##  character table <tbl> with the strategy using Gaussian elimination,
##  which is described in Section~3.3 in~\cite{BP98}.
##
##  The class functions in the result have the additional properties that
##  only the (necessarily rational) characters <characters> occur as
##  constituents, and that they are all completions of <torso>.
##  (Note that scalar products with rational irreducible characters of <tbl>
##  that are omitted in <characters> may be negative,
##  so not all class functions in the result list are necessarily characters
##  if <characters> does not contain all rational irreducible characters of
##  <tbl>.)
##
##  Known values of the candidates must be nonnegative integers in <torso>,
##  the other positions of <torso> are unbound;
##  at least the degree `<torso>[1]' must be an integer.
#T what about choice lists ??
##
DeclareGlobalFunction( "PermCandidates" );


#############################################################################
##
#F  PermCandidatesFaithful( <tbl>, <chars>, <norm_subgrp>, <nonfaithful>,
#F                          <lower>, <upper>, <torso> )
##
##  computes certain possible permutation characters of the character table
##  <tbl> with a generalization of the strategy using Gaussian elimination
##  (see~"PermCandidates").
##  These characters are all with the following properties.
##  \beginlist
##  \item{1.}
##     Only the (necessarily rational) characters <chars> occur as
##     constituents,
##
##  \item{2.}
##     they are completions of <torso>, and
##
##  \item{3.}
##     have the character <nonfaithful> as maximal constituent with kernel
##     <norm_subgrp>.
##
##  Known values of the candidates must be nonnegative integers in <torso>,
##  the other positions of <torso> are unbound;
##  at least the degree `<torso>[1]' must be an integer.
##
DeclareGlobalFunction( "PermCandidatesFaithful" );


#############################################################################
##
#E

