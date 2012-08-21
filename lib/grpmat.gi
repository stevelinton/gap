#############################################################################
##
#W  grpmat.gi                   GAP Library                      Frank Celler
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the methods for matrix groups.
##
Revision.grpmat_gi :=
    "@(#)$Id$";


InstallMethod( KnowsHowToDecompose, "matrix groups", true,
        [ IsMatrixGroup, IsList ], 0, ReturnFalse );


#############################################################################
##
#M  DefaultFieldOfMatrixGroup( <mat-grp> )
##
InstallMethod( DefaultFieldOfMatrixGroup,
    "using 'FieldOfMatrixGroup'",
    true,
    [ IsMatrixGroup ],
    0,
    FieldOfMatrixGroup );

InstallMethod( DefaultFieldOfMatrixGroup,
    "for matrix group over the cyclotomics",
    true,
    [ IsMatrixGroup and IsCyclotomicCollCollColl ], 0,
    grp -> Cyclotomics );

InstallOtherMethod( DefaultFieldOfMatrixGroup,
        "from source of nice monomorphism", true,
        [ IsMatrixGroup and HasNiceMonomorphism ], 0,
    grp -> DefaultFieldOfMatrixGroup( Source( NiceMonomorphism( grp ) ) ) );


#############################################################################
##
#M  FieldOfMatrixGroup( <mat-grp> )
##
InstallMethod( FieldOfMatrixGroup,
    "for a matrix group",
    true,
    [ IsMatrixGroup ],
    0,
    function( grp )
    local gens,  deg,  i,  j,  char;

    gens:= GeneratorsOfGroup( grp );
    if IsEmpty( gens ) then
      return Field( One( grp )[1][1] );
    else
      return Field( Flat( gens ) );
    fi;
    end );


#############################################################################
##
#M  DimensionOfMatrixGroup( <mat-grp> )
##
InstallMethod( DimensionOfMatrixGroup, "from generators", true,
    [ IsMatrixGroup and HasGeneratorsOfGroup ], 0,
    function( grp )
    if not IsEmpty( GeneratorsOfGroup( grp ) )  then
        return Length( GeneratorsOfGroup( grp )[ 1 ] );
    else
        TryNextMethod();
    fi;
end );

InstallMethod( DimensionOfMatrixGroup, "from one", true,
    [ IsMatrixGroup and HasOne ], 1,
    grp -> Length( One( grp ) ) );

InstallOtherMethod( DimensionOfMatrixGroup,
        "from source of nice monomorphism", true,
        [ IsMatrixGroup and HasNiceMonomorphism ], 0,
    grp -> DimensionOfMatrixGroup( Source( NiceMonomorphism( grp ) ) ) );


#############################################################################
##
#M  One( <mat-grp> )
##
InstallOtherMethod( One,
    "for matrix group, call `IdentityMat'",
    true, [ IsMatrixGroup ], 0,
    grp -> IdentityMat( DimensionOfMatrixGroup( grp ),
                        DefaultFieldOfMatrixGroup( grp ) ) );

#############################################################################
##
#M  IsomorphismPermGroup( <mat-grp> )
##
BindGlobal( "NicomorphismOfGeneralMatrixGroup", function( grp )
  local   nice;
  nice:=SortedSparseOperationHomomorphism( grp, One( grp ) );
  SetRange( nice, Image( nice ) );
  SetIsBijective( nice, true );
  # base to get point sorting compatible with lexicographic
  # vector arrangement
  SetBaseOfGroup( UnderlyingExternalSet( nice ), One( grp ) );
  SetFilterObj( nice, IsOperationHomomorphismByBase );
  SetIsCanonicalNiceMonomorphism(nice,true);
  return nice;
end );

InstallMethod( IsomorphismPermGroup, true, [ IsMatrixGroup and IsFinite ], 0,
  NicomorphismOfGeneralMatrixGroup);

#############################################################################
##
#M  NiceMonomorphism( <mat-grp> )
##
InstallMethod( NiceMonomorphism, true, [ IsMatrixGroup and IsFinite ], 0,
  NicomorphismOfGeneralMatrixGroup);

#    function( grp )
#    local   nice;
#    
#    nice := IsomorphismPermGroup( grp );
#    SetNiceMonomorphism( grp, nice );
#    if IsSolvableGroup( Image( nice ) )  then
#        nice := nice * IsomorphismPcGroup( Image( nice ) );
#        SetNiceMonomorphism( grp, nice );
#    fi;
#    return nice;
#end );

#############################################################################
##
#M  GeneratorsSmallest(<finite matrix group>)
##
##  This algorithm takes <bas>:=the points corresponding to the standard basis
##  and then computes a minimal generating system for the permutation group
##  wrt. this base <bas>. As lexicographical comparison of matrices is
##  compatible with comparison of base images wrt. the standard base this
##  also is the smallest (irredundant) generating set of the matrix group!
InstallMethod(GeneratorsSmallest,"matrix group via niceo",true,
  [IsMatrixGroup and IsFinite],0,
function(G)
local gens,s,dom;
  dom:=UnderlyingExternalSet(NiceMonomorphism(G));
  s:=StabChainOp(NiceObject(G),rec(base:=List(BaseOfGroup(dom),
				      i->Position(HomeEnumerator(dom),i))));
  # call the recursive function to do the work
  gens:=SCMinSmaGens(NiceObject(G),s,[],(),true).gens;
  SetMinimalStabChain(G,s);
  return List(gens,i->PreImagesRepresentative(NiceMonomorphism(G),i));
end);

#############################################################################
##
#M  MinimalStabChain(<finite matrix group>)
##
##  used for cosets where we probably won't need the smallest generators
InstallOtherMethod(MinimalStabChain,"matrix group via niceo",true,
  [IsMatrixGroup and IsFinite],0,
function(G)
local s,dom;
  dom:=UnderlyingExternalSet(NiceMonomorphism(G));
  s:=StabChainOp(NiceObject(G),rec(base:=List(BaseOfGroup(dom),
				      i->Position(HomeEnumerator(dom),i))));
  # call the recursive function to do the work
  SCMinSmaGens(NiceObject(G),s,[],(),false);
  return s;
end);

#############################################################################
##
#M  LargestElementGroup(<finite matrix group>)
##
InstallOtherMethod(LargestElementGroup,"matrix group via niceo",true,
  [IsMatrixGroup and IsFinite],0,
function(G)
local s,dom;
  dom:=UnderlyingExternalSet(NiceMonomorphism(G));
  s:=StabChainOp(NiceObject(G),rec(base:=List(BaseOfGroup(dom),
				      i->Position(HomeEnumerator(dom),i))));
  # call the recursive function to do the work
  s:=LargestElementStabChain(s,());
  return PreImagesRepresentative(NiceMonomorphism(G),s);
end);

#############################################################################
##
#M  CanonicalRightCosetElement(<finite matrix group>,<rep>)
##
InstallMethod(CanonicalRightCosetElement,"finite matric group",IsCollsElms,
  [IsMatrixGroup and IsFinite,IsMatrix],0,
function(U,e)
local mon,dom,S,o,oimgs,p,i,g;
  mon:=NiceMonomorphism(U);
  dom:=UnderlyingExternalSet(mon);
  S:=StabChainOp(NiceObject(U),rec(base:=List(BaseOfGroup(dom),
				      i->Position(HomeEnumerator(dom),i))));
  dom:=HomeEnumerator(dom);

  while not IsEmpty(S.generators) do
    o:=dom{S.orbit}; # the relevant vectors
    oimgs:=List(o,i->i*e); #their images

    # find the smallest image
    p:=1;
    for i in [2..Length(oimgs)] do
      if oimgs[i]<oimgs[p] then
        p:=i;
      fi;
    od;

    # the point corresponding to the preimage
    p:=S.orbit[p];

    # now find an element that maps S.orbit[1] to p;
    g:=S.identity;
    while S.orbit[1]^g<>p do
      g:=LeftQuotient(S.transversal[p/g],g);
    od;

    # change by corresponding matrix element
    e:=PreImagesRepresentative(mon,g)*e;

    S:=S.stabilizer;
  od;

  return e;
end);

#############################################################################
##
#M  ViewObj(<G>)
##
InstallMethod(ViewObj,"matrix group",true,[IsMatrixGroup],0,
function(G)
local gens;
  gens:=GeneratorsOfGroup(G);
  if Length(gens)>0 and Length(gens)*Length(gens[1])^2/VIEWLEN>8 then
    Print("<matrix group");
    if HasSize(G) then
      Print(" of size ",Size(G));
    fi;
    Print(" with ",Length(GeneratorsOfGroup(G)),
          " generators>");
  else
    Print("Group(");
    ViewObj(GeneratorsOfGroup(G));
    Print(")");
  fi;
end);

#############################################################################
##
#M  IsGeneralLinearGroup(<G>)
##
InstallMethod(IsGeneralLinearGroup,"try natural",true,[IsMatrixGroup],0,
function(G)
  if IsNaturalGL(G) then 
    return true;
  else
    TryNextMethod();
  fi;
end);

#############################################################################
##
#M  IsSubgroupSL
##
InstallMethod(IsSubgroupSL,"determinant test for generators",true,
  [IsMatrixGroup and HasGeneratorsOfGroup],0,
function(G)
  return ForAll(GeneratorsOfGroup(G),i->IsOne(DeterminantMat(i)));
end);

#############################################################################
##
#M  <mat> in <G>  . . . . . . . . . . . . . . . . . . . .  is form invariant?
##
InstallMethod( \in, "respecting bilinear form", IsElmsColls,
        [ IsMatrix, IsFullSubgroupGLorSLRespectingBilinearForm ], 0,
function( mat, G )
  if IsSubgroupSL(G) and not IsOne(DeterminantMat(mat)) then return false;fi;
  return mat * InvariantBilinearForm(G).matrix * TransposedMat( mat ) =
	       InvariantBilinearForm(G).matrix;
end );

InstallMethod( \in, "respecting sesquilinear form", IsElmsColls,
        [ IsMatrix, IsFullSubgroupGLorSLRespectingSesquilinearForm ], 0,
function( mat, G )
local   f;
  if IsSubgroupSL(G) and not IsOne(DeterminantMat(mat)) then return false;fi;
  f := FrobeniusAutomorphism( FieldOfMatrixGroup( G ) );
  return mat * InvariantSesquilinearForm(G).matrix * List( TransposedMat( mat ),
		  row -> OnTuples(row,f)) = InvariantSesquilinearForm(G).matrix;
end );

#############################################################################
##
#E  grpmat.gi . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##
