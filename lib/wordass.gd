#############################################################################
##
#W  wordass.gd                  GAP library                     Thomas Breuer
#W                                                             & Frank Celler
##
#H  @(#)$Id$
##
#Y  Copyright 1997,    Lehrstuhl D fuer Mathematik,   RWTH Aachen,    Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file declares the operations for associative words.
##
##  An *associative word* in {\GAP} is a word formed from generators under an
##  associative multiplication.
##
Revision.wordass_gd :=
    "@(#)$Id$";

#1
##  Two associative words are equal if they are words over the same alphabet
##  and if they are a sequence of the same letters.
##  There is no ``universal'' empty word,
##  every alphabet (that is every family of words) has its own empty word.

#2
##  The ordering of associative words is defined by length and lexicography,
##  that is, shorter words are smaller than longer words,
##  and words of the same length are compared w.r.t~the lexicographical
##  ordering induced by the ordering of generators.
##  Generators are sorted according to the order in which they were created,
##  If the generators are invertible then each generator <g> is larger than
##  its inverse `<g>^-1',
##  and `<g>^-1' is larger than every generator that is smaller than <g>.
##  \beginexample
##  gap> f:= FreeGroup( 2 );;  gens:= GeneratorsOfGroup( f );;
##  gap> a:= gens[1];;  b:= gens[2];;
##  gap> One(f) < a^-1;  a^-1 < a;  a < b^-1;  b^-1 < b; b < a^2;  a^2 < a*b;
##  true
##  true
##  true
##  true
##  true
##  true
##  \endexample

#3
##  There is an external representation of the category of associative words,
##  a list of generators and exponents.
##  For example, the word $w = g_1^4 * g_2^3 * g_1$
##  has external representation `[ 1, 4, 2, 3, 1, 1 ]', where $g_i$ means
##  the $i$-th generator of the family of $w$.
##  The empty list describes the identity element (if exists) of the family.
##  Exponents may be negative if the family allows inverses.
##  The external representation of a word is guaranteed to be freely reduced.
##  For example, $g_1 * g_2 * g_2^{-1} * g_1$ has the external representation
##  `[ 1, 2 ]'.


#############################################################################
##
#C  IsAssocWord( <obj> )
##
##  is the category of associative words in free semigroups.
##
DeclareSynonym( "IsAssocWord", IsWord and IsAssociativeElement );


#############################################################################
##
#C  IsAssocWordWithOne( <obj> )
##
##  is the category of associative words in free monoids (which have an
##  identity).
##
DeclareSynonym( "IsAssocWordWithOne", IsAssocWord and IsWordWithOne );


#############################################################################
##
#C  IsAssocWordWithInverse( <obj> )
##
##  is the category of associative words in free groups (which have an
##  inverse).
##
DeclareSynonym( "IsAssocWordWithInverse",
    IsAssocWord and IsWordWithInverse );


#############################################################################
##
#C  IsAssocWordCollection( <obj> )
#C  IsAssocWordWithOneCollection( <obj> )
#C  IsAssocWordWithInverseCollection( <obj> )
##
DeclareCategoryCollections( "IsAssocWord" );
DeclareCategoryCollections( "IsAssocWordWithOne" );
DeclareCategoryCollections( "IsAssocWordWithInverse" );

DeclareCategoryFamily( "IsAssocWord" );
DeclareCategoryFamily( "IsAssocWordWithOne" );
DeclareCategoryFamily( "IsAssocWordWithInverse" );


#############################################################################
##
#C  Is8BitsFamily
#C  Is16BitsFamily
#C  Is32BitsFamily
#C  IsInfBitsFamily
##
DeclareCategory( "Is8BitsFamily", IsFamily );
DeclareCategory( "Is16BitsFamily", IsFamily );
DeclareCategory( "Is32BitsFamily", IsFamily );
DeclareCategory( "IsInfBitsFamily", IsFamily );


#############################################################################
##
#T  IsFreeSemigroup( <obj> )
#T  IsFreeMonoid( <obj> )
#C  IsFreeGroup( <obj> )
##
#T  Note that we cannot define `IsFreeMonoid' as
#T  `IsAssocWordWithOneCollection and IsMonoid' because then
#T  every free group would be a free monoid, which is not true!
#T  Instead we just make it a property and set it at creation
##
DeclareProperty("IsFreeSemigroup", IsAssocWordCollection and IsSemigroup);
DeclareProperty("IsFreeMonoid", IsAssocWordWithOneCollection and IsMonoid);
DeclareSynonym( "IsFreeGroup",
    IsAssocWordWithInverseCollection and IsGroup );


#############################################################################
##
#M  IsGeneratorsOfMagmaWithInverses( <coll> )
##
InstallTrueMethod( IsGeneratorsOfMagmaWithInverses,
    IsAssocWordWithInverseCollection );


#############################################################################
##
#A  NumberSyllables( <w> )
##
##  Let <w> be an associative word of the form
##  $x_1^{n_1} x_2^{n_2} \cdots x_k^{n_k}$,
##  such that $x_i \not= x_{i+1}^{\pm 1}$ for $1 \leq i \leq k-1$.
##  Then `NumberSyllables( <w> )' is $k$.
##
DeclareAttribute( "NumberSyllables", IsAssocWord );
DeclareSynonymAttr( "NrSyllables", NumberSyllables );


#############################################################################
##
#O  ExponentSums( <w> )
#O  ExponentSums( <w>, <?>, <?> )
##
##  ???
##
DeclareOperation( "ExponentSums", [ IsAssocWord ] );


#############################################################################
##
#O  ExponentSumWord( <w>, <gen> )
##
##  is the number of times the generator <gen> appears in the associative
##  word <w> minus the number of times its inverse appears in <w>.
##  If <gen> and its inverse do not occur in <w>, 0 is returned.
##  <gen> may also be the inverse of a generator.
##
DeclareOperation( "ExponentSumWord", [ IsAssocWord, IsAssocWord ] );


#############################################################################
##
#O  Subword( <w>, <from>, <to> )
##
##  is the subword of the associative word <w> that begins at position <from>
##  and ends at position <to>.
##  <from> and <to> must be positive integers.
##  Indexing is done with origin 1.
##
DeclareOperation( "Subword", [ IsAssocWord, IsPosInt, IsPosInt ] );


#############################################################################
##
#O  SubSyllables( <w>, <from>, <to> )
##
##  is the subword of the associative word <w> that consists of the
##  syllables from positions <from> to <to>.
##  <from> and <to> must be positive integers.
##  Indexing is done with origin 1.
##
DeclareOperation( "SubSyllables", [ IsAssocWord, IsPosInt, IsPosInt ] );


#############################################################################
##
#O  PositionWord( <w>, <sub>, <from> )
##
##  is the position of the first occurrence of the associative word <sub>
##  in the associative word <w> starting at position <from>.
##  If there is no such occurrence, `fail' is returned.
##  <from> must be a positive integer.
##  Indexing is done with origin 1.
##
##  In other words, `PositionWord(<w>,<sub>,<from>)' is the smallest
##  integer <i> larger than or equal to <from> such that
##  `Subword( <w>, <i>, <i>+Length(<sub>)-1 ) = <sub>' (see~"Subword").
##
DeclareOperation( "PositionWord", [ IsAssocWord, IsAssocWord, IsPosInt ] );


#############################################################################
##
#O  SubstitutedWord( <w>, <from>, <to>, <by> )
##
##  is a new associative word where the subword of the associative word <w>
##  that begins at position <from> and ends at position <to> is replaced by
##  the associative word <by>.
##  <from> and <to> must be positive integers.
##  Indexing is done with origin 1.
##
##  In other words `SubstitutedWord(<w>,<from>,<to>,<by>) =
##  Subword(<w>,1,<from>-1)\*<by>\*Subword(<w>,<to>+1,Length(<w>)'
##  (see~"Subword").
##
DeclareOperation( "SubstitutedWord",
    [ IsAssocWord, IsPosInt, IsPosInt, IsAssocWord ] );


#############################################################################
##
#O  EliminatedWord( <word>, <gen>, <by> )
##
##  is a new associative word where each occurrence of the generator <gen>
##  in the associative word <word> is replaced by the associative word <by>.
##
DeclareOperation( "EliminatedWord",
    [ IsAssocWord, IsAssocWord, IsAssocWord ] );


#############################################################################
##
#O  RenumberedWord( <word>, <renumber> )  . . . renumber generators of a word
##
##  accepts an associative word <word> and a list <renumber> of positive
##  integers.  The result is a new word obtained from <word> by replacing
##  each occurrence of generator number $g$ by <renumber>[g].  The list
##  <renumber> need not be dense, but it must have a positive integer for
##  each  generator number occurring in <word>.  That integer must not exceed
##  the number of generators in the elements family of <word>.
##
DeclareOperation( "RenumberedWord", [IsAssocWord, IsList] );


#############################################################################
##
#O  ExponentSyllable( <w>, <i> )
##
##  is the exponent of the <i>-th syllable of the associative word <w>.
##
DeclareOperation( "ExponentSyllable", [ IsAssocWord, IsPosInt ] );


#############################################################################
##
#O  GeneratorSyllable( <w>, <i> )
##
##  is the generator of the <i>-th syllable of the associative word <w>.
##
DeclareOperation( "GeneratorSyllable", [ IsAssocWord, IsInt ] );


#############################################################################
##
#O  AssocWord( <Fam>, <extrep> )  . . . .  construct word from external repr.
#O  AssocWord( <Type>, <extrep> ) . . . .  construct word from external repr.
##
DeclareGlobalFunction( "AssocWord" );
#T maybe this will become a constructor of `TypeArg1' type again


#############################################################################
##
#O  ObjByVector( <Fam>, <exponents> )
#O  ObjByVector( <Type>, <exponents> )
##
##  is the associative word in the family <Fam> that has exponents vector
##  <exponents>.
##
DeclareGlobalFunction( "ObjByVector" );
#T maybe this will become a constructor of `TypeArg1' type again


#############################################################################
##
#O  CyclicReducedWordList( <word>, <gens> )
##
DeclareOperation( "CyclicReducedWordList", [ IsAssocWord, IsList ] );


#############################################################################
##

#F  StoreInfoFreeMagma( <F>, <names>, <req> )
##
##  does the administrative work in the construction of free semigroups,
##  free monoids, and free groups.
##
##  <F> is the family of objects, <names> is a list of generators names,
##  and <req> is the required category for the elements, that is,
##  `IsAssocWord', `IsAssocWordWithOne', or `IsAssocWordWithInverse'.
##
DeclareGlobalFunction( "StoreInfoFreeMagma" );


#############################################################################
##
#F  InfiniteListOfNames( <string>[, <initnames>] )
##
##  If the only argument is a string <string> then `InfiniteListOfNames'
##  returns an infinite list with the string $<string>i$ at position $i$.
##  If a finite list <initnames> of length $n$, say,
##  is given as second argument, 
##  the $i$-th entry of the returned infinite list is equal to
##  `<initnames>[$i$]' if $i \leq n$, and equal to $<string>i$ if $i > n$.
##
DeclareGlobalFunction( "InfiniteListOfNames" );


#############################################################################
##
#F  InfiniteListOfGenerators( <F>[, <init>] )
##
##  If the only argument is a family <Fam> then `InfiniteListOfGenerators'
##  returns an infinite list containing at position $i$ the element in <Fam>
##  obtained as `ObjByExtRep( <Fam>, [ $i$, 1 ] )'.
##  If a finite list <init> of length $n$, say, is given as second argument, 
##  the $i$-th entry of the returned infinite list is equal to
##  `<init>[$i$]' if $i \leq n$, and equal to `ObjByExtRep( <Fam>, $i$ )'
##  if $i > n$.
##
DeclareGlobalFunction( "InfiniteListOfGenerators" );

#############################################################################
##
#F  IsBasicWreathLessThanOrEqual( <u>, <v> )
##
##	for two associative words <u> and <v>.
##	It returns true if <u> is less than or equal to <v>, with
##	respect to the basic wreath product ordering.
##
DeclareGlobalFunction( "IsBasicWreathLessThanOrEqual" );

#############################################################################
##

#E
##

