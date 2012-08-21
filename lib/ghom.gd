#############################################################################
##
#W  ghom.gd                     GAP library                    Heiko Thei"sen
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen, Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
Revision.ghom_gd :=
    "@(#)$Id$";


#############################################################################
##
#O  GroupGeneralMappingByImages( <G>, <H>, <gensG>, <gensH> )
##
DeclareOperation( "GroupGeneralMappingByImages",
    [ IsGroup, IsGroup, IsList, IsList ] );


#############################################################################
##
#F  GroupHomomorphismByImages( <G>, <H>, <gens>, <imgs> )
##
##  `GroupHomomorphismByImages' returns the group homomorphism with
##  source <G> and range <H> that is defined by mapping the list <gens> of
##  generators of <G> to the list <imgs> of images in <H>.
##
##  If <gens> does not generate <G> or if the homomorphism does not exist
##  (i.e., if mapping the generators describes only a multi-valued mapping)
##  then `fail' is returned.
##
##  One can avoid the checks by calling `GroupHomomorphismByImagesNC',
##  and one can construct multi-valued mappings with
##  `GroupGeneralMappingByImages'.
##
DeclareGlobalFunction( "GroupHomomorphismByImages" );


#############################################################################
##
#O  GroupHomomorphismByImagesNC( <G>, <H>, <gensG>, <gensH> )
##
##  `GroupHomomorphismByImagesNC' is the operation that is called by the
##  function `GroupHomomorphismByImages'.
##  Its methods may assume that <gens> generates <G> and that the mapping of
##  <gens> to <imgs> defines a group homomorphism.
##  Results are unpredictable if these conditions do not hold.
##
##  For creating a possibly multi-valued mapping from <G> to <H> that
##  respects multiplication and inverses,
##  `GroupGeneralMappingByImages' can be used.
##
#T If we could guarantee that it does not matter whether we construct the
#T homomorphism directly or whether we construct first a general mapping
#T and ask it for  being a homomorphism,
#T then this operation would be obsolete,
#T and `GroupHomomorphismByImages' would be allowed to return the general
#T mapping itself after the checks.
#T (See also the declarations of `AlgebraHomomorphismByImagesNC',
#T `AlgebraWithOneHomomorphismByImagesNC',
#T `LeftModuleHomomorphismByImagesNC'.)
##
DeclareOperation( "GroupHomomorphismByImagesNC",
    [ IsGroup, IsGroup, IsList, IsList ] );


#############################################################################
##
#O  NaturalHomomorphismByNormalSubgroup( <G>, <N> )
#O  NaturalHomomorphismByNormalSubgroupNC(<G>,<N> )
##
##  returns a homomorphism from <G> to another group whose kernel is <N>.
##  {\GAP} will try to select the image group as to make computations in it
##  as efficient as possible. As the factor group $<G>/<N>$ can be identified 
##  with the image of <G> this permits efficient computations in the factor
##  group. The homomorphism returned is not necessarily surjective, so
##  `ImagesSource' should be used insteadf of `Range' to get a group
##  isomorphic to the factor group.
##  The `NC' variant does not check whether <N> is normal in <G>.
##
InParentFOA( "NaturalHomomorphismByNormalSubgroup", IsGroup, IsGroup,
              NewAttribute );
BindGlobal( "NaturalHomomorphismByNormalSubgroupNC",
    NaturalHomomorphismByNormalSubgroup );
MakeReadWriteGlobal( "NaturalHomomorphismByNormalSubgroup" );
UnbindGlobal( "NaturalHomomorphismByNormalSubgroup" );

DeclareGlobalFunction("NaturalHomomorphismByNormalSubgroup");

#############################################################################
##
#R  IsGroupGeneralMappingByImages(<obj>)
##
DeclareRepresentation( "IsGroupGeneralMappingByImages",
      IsGroupGeneralMapping and IsSPGeneralMapping and IsAttributeStoringRep,
      [ "generators", "genimages", "elements", "images" ] );

#############################################################################
##
#R  IsGroupGeneralMappingByPcgs(<obj>)
##
DeclareRepresentation( "IsGroupGeneralMappingByPcgs",
      IsGroupGeneralMappingByImages, [ "pcgs", "generators", "genimages" ] );

#############################################################################
##
#R  IsPreimagesByAsGroupGeneralMappingByImages(<obj>)
##
##  Representation for mappings that delegate work for preimages to a
##  GroupHomomorphismByImages.
DeclareRepresentation( "IsPreimagesByAsGroupGeneralMappingByImages",
      IsGroupGeneralMapping and IsSPGeneralMapping and IsAttributeStoringRep,
      [  ] );

#############################################################################
##
#R  IsGroupGeneralMappingByAsGroupGeneralMappingByImages(<obj>)
##  Representation for mappings that delegate work on a
##  GroupHomomorphismByImages.
DeclareRepresentation( "IsGroupGeneralMappingByAsGroupGeneralMappingByImages",
      IsPreimagesByAsGroupGeneralMappingByImages, [  ] );

#############################################################################
##
#A   AsGroupGeneralMappingByImages(<map>)
##
##   If <map> is a mapping from one group to another this attribute returns
##   a group general mapping that which implements the same abstract
##   mapping. (Some operations may be quicker for MappingByImages.)
DeclareAttribute( "AsGroupGeneralMappingByImages",
    IsGroupGeneralMapping );

InstallAttributeMethodByGroupGeneralMappingByImages :=
  function( attr, value_filter )
    InstallMethod( attr, "via `AsGroupGeneralMappingByImages'", true,
            [ IsGroupGeneralMappingByAsGroupGeneralMappingByImages ], 0,
            hom -> attr( AsGroupGeneralMappingByImages( hom ) ) );
    InstallMethod( Setter( attr ),
            "also for `AsGroupGeneralMappingByImages'", true,
            [ HasAsGroupGeneralMappingByImages, value_filter ], SUM_FLAGS,
            function( hom, value )
                local    asggmbi;

                asggmbi := AsGroupGeneralMappingByImages( hom );
                if not HasAsGroupGeneralMappingByImages( asggmbi )  then
                    Setter( attr )( asggmbi, value );
                fi;
                TryNextMethod();
            end );
end;
    
#############################################################################
##
#O  ConjugatorAutomorphism( <G>, <g> )
##
##  creates for $<g>$ in the same Family as the elemnts of <G> the
##  automorphism of <G> defined by $<h>\mapsto<h>^{<elm>}$ for all
##  $<h>\in<G>$.
DeclareOperation( "ConjugatorAutomorphism",
    [ IsGroup, IsMultiplicativeElementWithInverse ] );
    
#############################################################################
##
#O  InnerAutomorphism( <G>, <g> )
##
##  creates for $<g>\in<G>$ the inner automorphism of <G>
##  defined by $<h>\mapsto<h>^{<elm>}$ for all $<h>\in<G>$.
DeclareOperation( "InnerAutomorphism",
    [ IsGroup, IsMultiplicativeElementWithInverse ] );

#############################################################################
##
#P  IsConjugatorAutomorphism( <hom> )
##
##  If <hom> is an bijective endomorphism of a group <G> this property
##  tests, whether <hom> can be induced by conjugation with an element of
##  <G> or another group which naturally contains <G> (if <G> is a
##  permutation group).  If this is the case, the attribute
##  `ConjugatorInnerAutomorphism' contains this element which induces the
##  same conjugation action as <hom> does.
##
##  To avoid problems with `IsInnerAutomorphism' it is guaranteed that the
##  conjugator is taken from <G> if possible.
DeclareProperty("IsConjugatorAutomorphism",IsGroupGeneralMappingByImages);

#############################################################################
##
#P  IsInnerAutomorphism( <hom> )
##
##  If <hom> is an bijective endomorphism of a group <G> this property tests,
##  whether <hom> is an inner automorphism of <G>. If this is the case, the
##  attribute `ConjugatorInnerAutomorphism' contains an element of <G> which
##  induces the same conjugation action as <hom> does.
##
##  An automorphism is an inner automorphism if it is a conjugator
##  automorphism and if the conjugating element can be found in <G>.
DeclareProperty("IsInnerAutomorphism",IsConjugatorAutomorphism);

#############################################################################
##
#A  ConjugatorInnerAutomorphism( <hom> )
##
##  For an inner automorphism <hom> this attribute returns an element that
##  induces the same conjugation action.
DeclareAttribute("ConjugatorInnerAutomorphism",IsConjugatorAutomorphism);

DeclareRepresentation( "IsConjugatorAutomorphismRep",
    IsGroupHomomorphism and IsConjugatorAutomorphism and IsBijective 
    and IsAttributeStoringRep and IsSPGeneralMapping, [ ] );


#############################################################################
##
#R  IsNaturalHomomorphismPcGroupRep . . . . . . . . natural hom in a pc group
##
DeclareRepresentation( "IsNaturalHomomorphismPcGroupRep",
      IsGroupHomomorphism and IsSurjective and IsSPGeneralMapping and
      IsAttributeStoringRep,
      [ "pcgsSource", "pcgsRange" ] );

DeclareGlobalFunction( "MakeMapping" );

#############################################################################
##
#F  GroupHomomorphismByFunction( <S>, <R>, <fun> )
#F  GroupHomomorphismByFunction( <S>, <R>, <fun>, <invfun> )
##
##  `GroupHomomorphismByFunction' returns a group homomorphism <hom> with
##  source <S> and range <R>, such that each element <s> of <S> is mapped to
##  the element `<fun>( <s> )', where <fun> is a {\GAP} function.
##
##  If the argument <invfun> is bound then <hom> is a bijection between <S>
##  and <R>, and the preimage of each element <r> of <R> is given by
##  `<invfun>( <r> )', where <invfun> is a {\GAP}  function.
##
##  No test is performed on whether the functions actually give an
##  isomorphism between both groups.
##
##  `GroupHomomorphismByFunction' creates a mapping which
##  `IsSPGeneralMapping'.
##              
DeclareGlobalFunction("GroupHomomorphismByFunction");

#############################################################################
##
#F  ImagesRepresentativeGMBIByElementsList( <hom>, <elm> )
##
##  This is the method for `ImagesRepresentative' which calls `MakeMapping'
##  and uses element lists to evaluate the image. It is used by
##  `Factorization'.
DeclareGlobalFunction("ImagesRepresentativeGMBIByElementsList");

#############################################################################
##
#E  ghom.gd . . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
