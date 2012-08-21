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
##  returns a generalized mapping defined by extending the mapping from
##  <gensG> to <gensH> homomorphically. 
##  (`GroupHomomorphismByImages' creates a `GroupGeneralMappingByImages' and
##  tests whether it `IsMapping'.)
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
##  If <gens> does not generate <G> or if the mapping of the generators does
##  not extend to a homomorphism
##  (i.e., if mapping the generators describes only a multi-valued mapping)
##  then `fail' is returned.
##
##  This test can be quite expensive. If one is certain that the mapping of
##  the generators extends to a homomorphism,
##  one can avoid the checks by calling `GroupHomomorphismByImagesNC'.
##  (There also is the possibility to
##  construct potentially multi-valued mappings with
##  `GroupGeneralMappingByImages' and to test with `IsMapping' that
##  they are indeed homomorphisms.)
##
DeclareGlobalFunction( "GroupHomomorphismByImages" );


#############################################################################
##
#O  GroupHomomorphismByImagesNC( <G>, <H>, <gensG>, <gensH> )
##
##  `GroupHomomorphismByImagesNC' creates a homomorphism as
##  `GroupHomomorphismByImages' does, however it does not test whether
##  <gens> generates <G> and that the mapping of
##  <gens> to <imgs> indeed defines a group homomorphism.
##  Because these tests can be expensive it can be substantially faster than
##  `GroupHomomorphismByImages'.
##  Results are unpredictable if the conditions do not hold.
##
##  (For creating a possibly multi-valued mapping from <G> to <H> that
##  respects multiplication and inverses,
##  `GroupGeneralMappingByImages' can be used.)
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
##  `ImagesSource' should be used instead of `Range' to get a group
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
#R  IsGroupGeneralMappingByImages(<map>)
##
##  Representation for mappings from one group to another that are defined
##  by extending a mapping of group generators homomorphically. 
DeclareRepresentation( "IsGroupGeneralMappingByImages",
      IsGroupGeneralMapping and IsSPGeneralMapping and IsAttributeStoringRep,
      [ "generators", "genimages" ] );

#############################################################################
##
#R  IsPreimagesByAsGroupGeneralMappingByImages(<map>)
##
##  Representation for mappings that delegate work for preimages to a
##  GroupHomomorphismByImages.
DeclareRepresentation( "IsPreimagesByAsGroupGeneralMappingByImages",
      IsGroupGeneralMapping and IsSPGeneralMapping and IsAttributeStoringRep,
      [  ] );

#############################################################################
##
#R  IsGroupGeneralMappingByAsGroupGeneralMappingByImages(<map>)
##
##  Representation for mappings that delegate work on a
##  `GroupHomomorphismByImages'.
DeclareRepresentation( "IsGroupGeneralMappingByAsGroupGeneralMappingByImages",
      IsPreimagesByAsGroupGeneralMappingByImages, [  ] );

#############################################################################
##
#A   AsGroupGeneralMappingByImages(<map>)
##
##   If <map> is a mapping from one group to another this attribute returns
##   a group general mapping that which implements the same abstract
##   mapping. (Some operations can be performed more effective in this
##   representation, see
##   also~"IsGroupGeneralMappingByAsGroupGeneralMappingByImages".)
DeclareAttribute( "AsGroupGeneralMappingByImages", IsGroupGeneralMapping );

#############################################################################
##
#A   MappingOfWhichItIsAsGGMBI(<map>)
##
##   If <map> is `AsGroupGeneralMappingByImages(<map2>)' then
##   <map2> is `MappingOfWhichItIsAsGGMBI(<map>)'. This attribute is used to
##   transfer attribute values which were set later.
DeclareAttribute( "MappingOfWhichItIsAsGGMBI", IsGroupGeneralMapping );

InstallAttributeMethodByGroupGeneralMappingByImages :=
  function( attr, value_filter )
    InstallMethod( attr, "via `AsGroupGeneralMappingByImages'", true,
            [ IsGroupGeneralMappingByAsGroupGeneralMappingByImages ], 0,
            hom -> attr( AsGroupGeneralMappingByImages( hom ) ) );
    InstallMethod( attr, "get delayed set attribute values", true,
            [ HasMappingOfWhichItIsAsGGMBI ], 
	    SUM_FLAGS-1, # we want to do this before doing any calculations
	    function(hom)
              hom:=MappingOfWhichItIsAsGGMBI( hom );
	      if Tester(attr)(hom) then
	        return attr(hom);
	      else
	        TryNextMethod();
	      fi;
	    end);
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
##  homomorphism between both groups because this would require testing the
##  full multiplication table.
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
#A   ImagesSmallestGenerators(<map>)
##
##   returns the list of images of `GeneratorsSmallest(Source(<map>))'. This
##   list can be used to compare group homomorphisms.  (The standard
##   comparison is to compare the image lists on the set of elements of the
##   source. If however x and y have the same images under a and b,
##   certainly all their products have. Therefore it is sufficient to test
##   this on the images of the smallest generators.)
DeclareAttribute( "ImagesSmallestGenerators",
    IsGroupGeneralMapping );

#############################################################################
##
#E  ghom.gd . . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
