#############################################################################
##
#W  pcgspcg.gi                  GAP Library                      Frank Celler
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file   contains the methods  for polycylic  generating systems of pc
##  groups.
##
Revision.pcgspcg_gi :=
    "@(#)$Id$";


#############################################################################
##

#R  IsUnsortedPcgsRep
##
DeclareRepresentation(
    "IsUnsortedPcgsRep",
    IsPcgsDefaultRep, [] );


#############################################################################
##

#M  PcgsByPcSequenceNC( <fam>, <pcs> )
##


#############################################################################
InstallMethod( PcgsByPcSequenceNC,
    "elements family by rws with defining pcgs",
    true,
    [ IsElementsFamilyByRws and HasDefiningPcgs,
      IsHomogeneousList ],
    0,

function( efam, pcs )
    local   rws,  pfa,  pcgs,  pag,  id,  g,  dg,  i,  new,
    ord,codepths,pagpow,sorco;

    # quick check
    if not IsIdenticalObj( efam, ElementsFamily(FamilyObj(pcs)) )  then
        Error( "elements family of <pcs> does not match <efam>" );
    fi;

    # check if it is the defining sequence
    rws := efam!.rewritingSystem;
    pfa := DefiningPcgs(efam);
    if List( pcs, UnderlyingElement ) = GeneratorsOfRws(rws)  then
        pcgs := PcgsByPcSequenceCons(
                    IsPcgsDefaultRep,
                    IsPcgs,
                    efam,
                    pcs );
        SetIsFamilyPcgs( pcgs, true );
        SetRelativeOrders( pcgs, RelativeOrders(rws) );


#T We should not use `InducedPcgs' because `PcgsByPcSequence' is guaranteed
#T to return a new, noninduced pcgs each time! AH
    # otherwise check if we can used an induced system
#    elif IsSSortedList( List( pcs, x -> DepthOfPcElement(pfa,x) ) )  then
#        pcgs := InducedPcgsByPcSequenceNC( pfa, pcs );


    # make an unsorted pcgs
    else
        pcgs := PcgsByPcSequenceCons(
                    IsPcgsDefaultRep,
                    IsPcgs and IsUnsortedPcgsRep,
                    efam,
                    pcs );

        # sort the elements according to the depth wrt pfa
        pag := [];
        new := [];
        ord := [];
        id  := One(pcs[1]);
     	for i  in [ Length(pcs), Length(pcs)-1 .. 1 ]  do
            g  := pcs[i];
      	    dg := DepthOfPcElement( pfa, g );
            while g <> id and IsBound(pag[dg])  do
          	g  := ReducedPcElement( pfa, g, pag[dg] );
     	    	dg := DepthOfPcElement( pfa, g );
            od;
            if g <> id  then
           	pag[dg] := g;
                new[dg] := i;
                ord[i]  := RelativeOrderOfPcElement( pfa, g );
            fi;
     	od;
	if not IsHomogeneousList(ord) then
	  Error("not all relative orders given");
	fi;
        pcgs!.sortedPcSequence := pag;
        pcgs!.newDepths        := new;
        pcgs!.sortingPcgs      := pfa;

	# Precompute the leading coeffs and the powers of pag up to the
	# relative order
        pagpow:=[];
	sorco:=[];
	for i in [1..Length(pag)] do
	  if IsBound(pag[i]) then
	    pagpow[i]:=
	      List([1..RelativeOrderOfPcElement(pfa,pag[i])-1],j->pag[i]^j);
	    sorco[i]:=LeadingExponentOfPcElement(pfa,pag[i]);
	  fi;
	od;
	pcgs!.sortedPcSeqPowers:=pagpow;
        pcgs!.sortedPcSequenceLeadCoeff:=sorco;

	# codepths[i]: the minimum pcgs-depth that can be implied by pag-depth i
	codepths:=[];
	for dg in [1..Length(new)] do
	  g:=Length(new)+1;
	  for i in [dg..Length(new)] do
	    if IsBound(new[i]) and new[i]<g then
	      g:=new[i];
	    fi;
	  od;
	  codepths[dg]:=g;
	od;
	pcgs!.minimumCodepths:=codepths;
        SetRelativeOrders( pcgs, ord );

    fi;

    # that it
    return pcgs;

end );


#############################################################################
InstallMethod( PcgsByPcSequenceNC,
    "elements family by rws",
    true,
    [ IsElementsFamilyByRws,
      IsHomogeneousList ],
    0,

function( efam, pcs )
    local   pcgs,  rws;

    # quick check
    if not IsIdenticalObj( efam, ElementsFamily(FamilyObj(pcs)) )  then
        Error( "elements family of <pcs> does not match <efam>" );
    fi;

    # check if it is the defining sequence
    rws := efam!.rewritingSystem;
    if List( pcs, UnderlyingElement ) = GeneratorsOfRws(rws)  then
        pcgs := PcgsByPcSequenceCons(
                    IsPcgsDefaultRep,
                    IsPcgs,
                    efam,
                    pcs );
        SetIsFamilyPcgs( pcgs, true );
        SetRelativeOrders( pcgs, RelativeOrders(rws) );

    # make an ordinary pcgs
    else
        pcgs := PcgsByPcSequenceCons(
                    IsPcgsDefaultRep,
                    IsPcgs,
                    efam,
                    pcs );
    fi;

    # that it
    return pcgs;

end );


#############################################################################
InstallMethod( PcgsByPcSequenceNC,
    "elements family by rws, empty sequence",
    true,
    [ IsElementsFamilyByRws,
      IsList and IsEmpty ],
    0,

function( efam, pcs )
    local   pcgs,  rws;

    # construct a pcgs
    pcgs := PcgsByPcSequenceCons(
                IsPcgsDefaultRep,
                IsPcgs,
                efam,
                pcs );

    # check if it is the defining sequence
    rws := efam!.rewritingSystem;
    if 0 = NumberGeneratorsOfRws(rws)  then
        SetIsFamilyPcgs( pcgs, true );
        SetRelativeOrders( pcgs, []   );
    fi;

    # that it
    return pcgs;

end );


#############################################################################
##
#M  PcgsByPcSequence( <fam>, <pcs> )
##


#############################################################################
InstallMethod( PcgsByPcSequence,
    true,
    [ IsElementsFamilyByRws,
      IsHomogeneousList ],
    0,

function( efam, pcs )
    #T  96/09/26 fceller  do some checks
    return PcgsByPcSequenceNC( efam, pcs );
end );
    

#############################################################################
InstallMethod( PcgsByPcSequence,
    true,
    [ IsElementsFamilyByRws,
      IsList and IsEmpty ],
    0,

function( efam, pcs )
    #T  96/09/26 fceller  do some checks
    return PcgsByPcSequenceNC( efam, pcs );
end );


#############################################################################
##
#M  DepthOfPcElement( <fam-pcgs>, <elm> )
##
InstallMethod( DepthOfPcElement,
    "family pcgs",
    IsCollsElms,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws ],
    100,

function( pcgs, elm )
    local   rep;

    rep := ExtRepOfObj( UnderlyingElement(elm) );
    if 0 = Length(rep)  then
        return Length(pcgs)+1;
    else
        return rep[1];
    fi;

end );


#############################################################################
##
#M  ExponentsOfPcElement( <fam-pcgs>, <elm> )
##
InstallMethod( ExponentsOfPcElement,
    "family pcgs",
    IsCollsElms,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws ],
    100,

function( pcgs, elm )
    local   exp,  rep,  i;

    exp := ListWithIdenticalEntries( Length( pcgs ), 0 );
    rep := ExtRepOfObj( UnderlyingElement(elm) );
    for i  in [ 1, 3 .. Length(rep)-1 ]  do
        exp[rep[i]] := rep[i+1];
    od;
    return exp;

end );


#############################################################################
##
#M  LeadingExponentOfPcElement( <fam-pcgs>, <elm> )
##
InstallMethod( LeadingExponentOfPcElement,
    "family pcgs",
    IsCollsElms,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws ],
    100,

function( pcgs, elm )
    local   rep;

    rep := ExtRepOfObj( UnderlyingElement(elm) );
    if 0 = Length(rep)  then
        return fail;
    else
        return rep[2];
    fi;

end );

# methods for `PcElementByExponent' that use the family pcgs directly
#############################################################################
##
#M  PcElementByExponentsNC( <family pcgs>, <list> )
##
InstallMethod( PcElementByExponentsNC,
    "family pcgs",
    true,
    [ IsPcgs and IsFamilyPcgs,
      IsRowVector and IsCyclotomicCollection ],
    0,

function( pcgs, list )
local i;
  for i in list do if i<0 then Error("wrong exponents");fi;od;
  return ObjByVector(TypeObj(OneOfPcgs(pcgs)),list);
end );

InstallMethod( PcElementByExponentsNC,
    "family pcgs, FFE",
    true,
    [ IsPcgs and IsFamilyPcgs,
      IsRowVector and IsFFECollection ],
    0,

function( pcgs, list )
  list:=IntVecFFE(list);
  return ObjByVector(TypeObj(OneOfPcgs(pcgs)),list);
end );

#############################################################################
##
#M  PcElementByExponentsNC( <family pcgs induced>, <list> )
##
InstallMethod( PcElementByExponentsNC,
    "subset induced wrt family pcgs",
    true,
    [ IsPcgs and IsParentPcgsFamilyPcgs and IsSubsetInducedPcgsRep
      and IsPrimeOrdersPcgs, IsRowVector and IsCyclotomicCollection ],
    0,

function( pcgs, list )
local exp;
  for exp in list do if exp<0 then Error("wrong exponents");fi;od;
  exp:=ShallowCopy(pcgs!.parentZeroVector);
  exp{pcgs!.depthsInParent}:=list;
  return ObjByVector(TypeObj(OneOfPcgs(pcgs)),exp);
end);

#############################################################################
##
#M  PcElementByExponentsNC( <family pcgs induced>, <list> )
##
InstallMethod( PcElementByExponentsNC,
    "subset induced wrt family pcgs, FFE",
    true,
    [ IsPcgs and IsParentPcgsFamilyPcgs and IsSubsetInducedPcgsRep
      and IsPrimeOrdersPcgs, IsRowVector and IsFFECollection ],
    0,

function( pcgs, list )
local exp;
  list:=IntVecFFE(list);
  exp:=ShallowCopy(pcgs!.parentZeroVector);
  exp{pcgs!.depthsInParent}:=list;
  return ObjByVector(TypeObj(OneOfPcgs(pcgs)),exp);
end);

#############################################################################
##
#M  PcElementByExponentsNC( <family pcgs modulo>, <list> )
##
InstallMethod( PcElementByExponentsNC,
    "modulo subset induced wrt family pcgs",
    true,
    [ IsModuloPcgs and IsModuloTailPcgsRep and
      IsSubsetInducedNumeratorModuloTailPcgsRep and IsPrimeOrdersPcgs
      and IsNumeratorParentPcgsFamilyPcgs,
      IsRowVector and IsCyclotomicCollection ],
    0,

function( pcgs, list )
local exp;
  for exp in list do if exp<0 then Error("wrong exponents");fi;od;
  exp:=ShallowCopy(pcgs!.parentZeroVector);
  exp{pcgs!.parentSubmap}:=list;
  return ObjByVector(TypeObj(OneOfPcgs(pcgs)),exp);
end);

#############################################################################
##
#M  PcElementByExponentsNC( <family pcgs modulo>, <list> )
##
InstallMethod( PcElementByExponentsNC,
    "modulo subset induced wrt family pcgs, FFE",
    true,
    [ IsModuloPcgs and IsModuloTailPcgsRep and
      IsSubsetInducedNumeratorModuloTailPcgsRep and IsPrimeOrdersPcgs
      and IsNumeratorParentPcgsFamilyPcgs,
      IsRowVector and IsFFECollection ],
    0,

function( pcgs, list )
local exp;
  list:=IntVecFFE(list);
  exp:=ShallowCopy(pcgs!.parentZeroVector);
  exp{pcgs!.parentSubmap}:=list;
  return ObjByVector(TypeObj(OneOfPcgs(pcgs)),exp);
end);

#############################################################################
##
#M  CanonicalPcElement( <igs>, <8bits-word> )
##
InstallMethod( CanonicalPcElement,
    "tail induced pcgs, 8bits word",
    IsCollsElms,
    [ IsInducedPcgs and IsTailInducedPcgsRep and IsParentPcgsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is8BitsPcWordRep ],
    100,

function( pcgs, elm )
    return 8Bits_HeadByNumber( elm, pcgs!.tailStart );
end );


#############################################################################
##
#M  DepthOfPcElement( <8bits-pcgs>, <elm> )
##
InstallMethod( DepthOfPcElement,
    "family pcgs (8 bits)",
    IsCollsElms,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is8BitsPcWordRep ],
    100,
    8Bits_DepthOfPcElement );


#############################################################################
##
#M  ExponentOfPcElement( <8bits-pcgs>, <elm> )
##
InstallMethod( ExponentOfPcElement,
    "family pcgs (8bits)",IsCollsElmsX,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is8BitsPcWordRep,
      IsPosInt ],
    100,
    8Bits_ExponentOfPcElement );

#############################################################################
##
#M  ExponentsOfPcElement( <8bits-pcgs>, <elm> )
##
InstallMethod( ExponentsOfPcElement, "family pcgs/8 bit",IsCollsElms,
     [ IsPcgs and IsFamilyPcgs, Is8BitsPcWordRep ], 
     # in `pcgspcg' there is a value 100 method that is worse than we are
     200,
function ( pcgs, elm )
    local  exp, rep, i;
    exp := ListWithIdenticalEntries( Length( pcgs ), 0 );
    rep := 8Bits_ExtRepOfObj( elm );
    for i  in [ 1, 3 .. Length( rep ) - 1 ]  do
        exp[rep[i]] := rep[i + 1];
    od;
    return exp;
end);

#############################################################################
##
#M  ExponentsOfPcElement( <8bits-pcgs>, <elm>,<range> )
##
InstallOtherMethod( ExponentsOfPcElement, "family pcgs/8 bit",IsCollsElmsX,
     [ IsPcgs and IsFamilyPcgs, Is8BitsPcWordRep,IsList ], 
     # in `pcgspcg' there is a value 100 method that is worse than we are
     200,
function( pcgs, elm,range )
local   exp,  rep,  i,rp,lr;
    lr:=Length(range);
    exp := ListWithIdenticalEntries( lr, 0 );
    rep := 8Bits_ExtRepOfObj(elm);
    rp:=1; # position in range
    # assume the ext rep is always ordered.
    for i  in [ 1, 3 .. Length(rep)-1 ]  do
      # do we have to get up through the range?
      while rp<=lr and range[rp]<rep[i] do
        rp:=rp+1;
      od;
      if rp>lr then
        break; # we have reached the end of the range
      fi;
      if rep[i]=range[rp] then
        exp[rp] := rep[i+1];
        rp:=rp+1;
        fi;
    od;
    return exp;
end );

#############################################################################
##
#M  HeadPcElementByNumber( <8bits-pcgs>, <8bits-word>, <num> )
##
InstallMethod( HeadPcElementByNumber,
    "family pcgs (8bits)",
    IsCollsElmsX,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is8BitsPcWordRep,
      IsInt ],
    100,

function( pcgs, elm, pos )
    return 8Bits_HeadByNumber( elm, pos );
end );


#############################################################################
##
#M  LeadingExponentOfPcElement( <8bits-pcgs>, <elm> )
##
InstallMethod( LeadingExponentOfPcElement,
    "family pcgs (8 bits)",
    IsCollsElms,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is8BitsPcWordRep ],
    100,
    8Bits_LeadingExponentOfPcElement );


#############################################################################
##
#M  CanonicalPcElement( <igs>, <16bits-word> )
##
InstallMethod( CanonicalPcElement,
    "tail induced pcgs, 16bits word",
    IsCollsElms,
    [ IsInducedPcgs and IsTailInducedPcgsRep and IsParentPcgsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is16BitsPcWordRep ],
    100,

function( pcgs, elm )
    return 16Bits_HeadByNumber( elm, pcgs!.tailStart );
end );


#############################################################################
##
#M  DepthOfPcElement( <16bits-pcgs>, <elm> )
##
InstallMethod( DepthOfPcElement,
    "family pcgs (16 bits)",
    IsCollsElms,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is16BitsPcWordRep ],
    100,
    16Bits_DepthOfPcElement );


#############################################################################
##
#M  ExponentOfPcElement( <16bits-pcgs>, <elm> )
##
InstallMethod( ExponentOfPcElement,
    "family pcgs (16bits)",IsCollsElmsX,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is16BitsPcWordRep,
      IsPosInt ],
    100,
    16Bits_ExponentOfPcElement );

#############################################################################
##
#M  ExponentsOfPcElement( <16bits-pcgs>, <elm> )
##
InstallMethod( ExponentsOfPcElement, "family pcgs/16 bit",IsCollsElms,
     [ IsPcgs and IsFamilyPcgs, Is16BitsPcWordRep ], 
     # in `pcgspcg' there is a value 100 method that is worse than we are
     200,
function ( pcgs, elm )
    local  exp, rep, i;
    exp := ListWithIdenticalEntries( Length( pcgs ), 0 );
    rep := 16Bits_ExtRepOfObj( elm );
    for i  in [ 1, 3 .. Length( rep ) - 1 ]  do
        exp[rep[i]] := rep[i + 1];
    od;
    return exp;
end);

#############################################################################
##
#M  ExponentsOfPcElement( <16bits-pcgs>, <elm>,<range> )
##
InstallOtherMethod( ExponentsOfPcElement, "family pcgs/16 bit",IsCollsElmsX,
     [ IsPcgs and IsFamilyPcgs, Is16BitsPcWordRep,IsList ], 
     # in `pcgspcg' there is a value 100 method that is worse than we are
     200,
function( pcgs, elm,range )
local   exp,  rep,  i,rp,lr;
    lr:=Length(range);
    exp := ListWithIdenticalEntries( lr, 0 );
    rep := 16Bits_ExtRepOfObj(elm);
    rp:=1; # position in range
    # assume the ext rep is always ordered.
    for i  in [ 1, 3 .. Length(rep)-1 ]  do
      # do we have to get up through the range?
      while rp<=lr and range[rp]<rep[i] do
        rp:=rp+1;
      od;
      if rp>lr then
        break; # we have reached the end of the range
      fi;
      if rep[i]=range[rp] then
        exp[rp] := rep[i+1];
        rp:=rp+1;
        fi;
    od;
    return exp;
end );

#############################################################################
##
#M  HeadPcElementByNumber( <16bits-pcgs>, <16bits-word>, <num> )
##
InstallMethod( HeadPcElementByNumber,
    "family pcgs (16bits)",
    IsCollsElmsX,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is16BitsPcWordRep,
      IsInt ],
    100,

function( pcgs, elm, pos )
    return 16Bits_HeadByNumber( elm, pos );
end );


#############################################################################
##
#M  LeadingExponentOfPcElement( <16bits-pcgs>, <elm> )
##
InstallMethod( LeadingExponentOfPcElement,
    "family pcgs (16 bits)",
    IsCollsElms,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is16BitsPcWordRep ],
    100,
    16Bits_LeadingExponentOfPcElement );


#############################################################################
##

#M  CanonicalPcElement( <igs>, <32bits-word> )
##
InstallMethod( CanonicalPcElement,
    "tail induced pcgs, 32bits word",
    IsCollsElms,
    [ IsInducedPcgs and IsTailInducedPcgsRep and IsParentPcgsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is32BitsPcWordRep ],
    100,

function( pcgs, elm )
    return 32Bits_HeadByNumber( elm, pcgs!.tailStart-1 );
end );


#############################################################################
##
#M  DepthOfPcElement( <32bits-pcgs>, <elm> )
##
InstallMethod( DepthOfPcElement,
    "family pcgs (32 bits)",
    IsCollsElms,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is32BitsPcWordRep ],
    100,
    32Bits_DepthOfPcElement );


#############################################################################
##
#M  ExponentOfPcElement( <32bits-pcgs>, <elm> )
##
InstallMethod( ExponentOfPcElement,
    "family pcgs (32bits)",
    IsCollsElmsX,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is32BitsPcWordRep,
      IsPosInt ],
    100,
    32Bits_ExponentOfPcElement );

#############################################################################
##
#M  ExponentsOfPcElement( <32bits-pcgs>, <elm> )
##
InstallMethod( ExponentsOfPcElement, "family pcgs/32 bit",IsCollsElms,
     [ IsPcgs and IsFamilyPcgs, Is32BitsPcWordRep ], 
     # in `pcgspcg' there is a value 100 method that is worse than we are
     200,
function ( pcgs, elm )
    local  exp, rep, i;
    exp := ListWithIdenticalEntries( Length( pcgs ), 0 );
    rep := 32Bits_ExtRepOfObj( elm );
    for i  in [ 1, 3 .. Length( rep ) - 1 ]  do
        exp[rep[i]] := rep[i + 1];
    od;
    return exp;
end);

#############################################################################
##
#M  ExponentsOfPcElement( <32bits-pcgs>, <elm>,<range> )
##
InstallOtherMethod( ExponentsOfPcElement, "family pcgs/32 bit",IsCollsElmsX,
     [ IsPcgs and IsFamilyPcgs, Is32BitsPcWordRep,IsList ], 
     # in `pcgspcg' there is a value 100 method that is worse than we are
     200,
function( pcgs, elm,range )
local   exp,  rep,  i,rp,lr;
    lr:=Length(range);
    exp := ListWithIdenticalEntries( lr, 0 );
    rep := 32Bits_ExtRepOfObj(elm);
    rp:=1; # position in range
    # assume the ext rep is always ordered.
    for i  in [ 1, 3 .. Length(rep)-1 ]  do
      # do we have to get up through the range?
      while rp<=lr and range[rp]<rep[i] do
        rp:=rp+1;
      od;
      if rp>lr then
        break; # we have reached the end of the range
      fi;
      if rep[i]=range[rp] then
        exp[rp] := rep[i+1];
        rp:=rp+1;
        fi;
    od;
    return exp;
end );


#############################################################################
##
#M  HeadPcElementByNumber( <32bits-pcgs>, <32bits-word>, <num> )
##
InstallMethod( HeadPcElementByNumber,
    "family pcgs (32bits)",
    IsCollsElmsX,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is32BitsPcWordRep,
      IsInt ],
    100,

function( pcgs, elm, pos )
    return 32Bits_HeadByNumber( elm, pos );
end );


#############################################################################
##
#M  LeadingExponentOfPcElement( <32bits-pcgs>, <elm> )
##
InstallMethod( LeadingExponentOfPcElement,
    "family pcgs (32 bits)",
    IsCollsElms,
    [ IsPcgs and IsFamilyPcgs,
      IsMultiplicativeElementWithInverseByRws and Is32BitsPcWordRep ],
    100,
    32Bits_LeadingExponentOfPcElement );


#############################################################################
##
#M  DepthOfPcElement( <unsorted-pcgs>, <elm> )
##
InstallMethod( DepthOfPcElement,
    "unsorted pcgs",
    IsCollsElms,
    [ IsPcgs and IsUnsortedPcgsRep,
      IsObject ],
    0,

function( pcgs, elm )
    local   pfa,  pcs,  new,  dep,  id,  dg;

    pfa := pcgs!.sortingPcgs;
    pcs := pcgs!.sortedPcSequence;
    new := pcgs!.newDepths;
    dep := Length(pcgs)+1;
    id  := OneOfPcgs(pcgs);

    # if <elm> is the identity return the composition length plus one
    if elm = id  then
        return Length(pcgs)+1;
    fi;
        
    # sift element through the sorted system
    while elm <> id  do
        dg := DepthOfPcElement( pfa, elm );
        if IsBound(pcs[dg])  then
            elm := ReducedPcElement( pfa, elm, pcs[dg] );
            if new[dg] < dep  then
                dep := new[dg];
            fi;
        else
            Error( "<elm> must lie in group defined by <pcgs>" );
        fi;
    od;
    return dep;
end );


#############################################################################
##
#M  ExponentOfPcElement( <unsorted-pcgs>, <elm>, <pos> )
##
InstallMethod( ExponentOfPcElement,
    "unsorted pcgs",
    IsCollsElmsX,
    [ IsPcgs and IsUnsortedPcgsRep,
      IsObject,
      IsPosInt ],
    0,

function( pcgs, elm, pos )
    local   pfa,  pcs,  new,  dep,  id,  g,  dg,  ll,  lr,  ord,
            led,pcsl,relords,pcspow,codepths,step;

    id  := OneOfPcgs(pcgs);
    # if <elm> is the identity return the null
    if elm = id  then
        return 0;
    fi;

    pfa := pcgs!.sortingPcgs;
    relords:=RelativeOrders(pfa);
    pcs := pcgs!.sortedPcSequence;
    pcsl:= pcgs!.sortedPcSequenceLeadCoeff;
    pcspow := pcgs!.sortedPcSeqPowers;
    new := pcgs!.newDepths;
    codepths:=pcgs!.minimumCodepths;
        
    # sift element through the sorted system
    step:=0; # the index in pcgs up to which we have already computed exponents
    while elm <> id  do
	#compute the next depth `dep' at which we have an exponent in pcgs.
        g   := elm;
        dep := Length(pcgs)+1;
        while g <> id  do
	    # do this by stepping down in pag
            dg := DepthOfPcElement( pfa, g );

	    if codepths[dg]>dep then
	      # once we have reached pfa-depth dg, we cannot acchieve `dep'
	      # any longer. So we may stop the descent through pfa here
	      g:=id;
            elif IsBound(pcs[dg])  then
                ll  := LeadingExponentOfPcElement( pfa, g );
                #lr  := LeadingExponentOfPcElement( pfa, pcs[dg]);
                lr  := pcsl[dg]; # precomputed value
                #ord := RelativeOrderOfPcElement( pfa, g );
		# the relative order is of course the rel. ord. in pfa
		# at depth dg.
		ord:=relords[dg];
                ll  := (ll/lr mod ord);
                #g   := LeftQuotient( pcs[dg]^ll, g ); 
                g   := LeftQuotient( pcspow[dg][ll], g ); #precomputed

                if new[dg] < dep  then
                    dep := new[dg];
                    led := ll;
		    if dep<=step+1 then
		      # this is the minimum possible pcgs-depth at this
		      # point
		      g:=id;
		    fi;
                fi;
            else
                Error( "<elm> must lie in group defined by <pcgs>" );
            fi;
        od;
	step:=dep;
        if dep = pos  then
            return led;
        fi;
        elm := LeftQuotient( pcgs[dep]^led, elm );
    od;
    return 0;
end );


#############################################################################
##
#M  ExponentsOfPcElement( <unsorted-pcgs>, <elm> )
##
InstallMethod( ExponentsOfPcElement,
    "unsorted pcgs",
    IsCollsElms,
    [ IsPcgs and IsUnsortedPcgsRep,
      IsObject ],
    0,

function( pcgs, elm )
    local   pfa,  pcs,  new,  dep,  id,  exp,  g,  dg,  ll,  lr,  ord,  
            led,pcsl,relords,pcspow,codepths,step;

    id  := OneOfPcgs(pcgs);
    exp := ListWithIdenticalEntries(Length(pcgs),0);

    # if <elm> is the identity return the null vector
    if elm = id  then
        return exp;
    fi;

    pfa := pcgs!.sortingPcgs;
    relords:=RelativeOrders(pfa);
    pcs := pcgs!.sortedPcSequence;
    pcsl:= pcgs!.sortedPcSequenceLeadCoeff;
    pcspow := pcgs!.sortedPcSeqPowers;
    new := pcgs!.newDepths;
    codepths:=pcgs!.minimumCodepths;

    # sift element through the sorted system
    step:=0; # the index in pcgs up to which we have already computed exponents
    while elm <> id  do
	#compute the next depth `dep' at which we have an exponent in pcgs.
        g   := elm;
        dep := Length(pcgs)+1;
        while g <> id  do
	    # do this by stepping down in pag
            dg := DepthOfPcElement( pfa, g );
	    if codepths[dg]>dep then
	      # once we have reached pfa-depth dg, we cannot acchieve `dep'
	      # any longer. So we may stop the descent through pfa here
	      g:=id;
            elif IsBound(pcs[dg])  then
                ll  := LeadingExponentOfPcElement( pfa, g );
                #lr  := LeadingExponentOfPcElement( pfa, pcs[dg]);
                lr  := pcsl[dg]; # precomputed value
                #ord := RelativeOrderOfPcElement( pfa, g );
		# the relative order is of course the rel. ord. in pfa
		# at depth dg.
		ord:=relords[dg];
                ll  := (ll/lr mod ord);
                #g   := LeftQuotient( pcs[dg]^ll, g ); 
                g   := LeftQuotient( pcspow[dg][ll], g ); #precomputed
                if new[dg] < dep  then
                    dep := new[dg];
                    led := ll;
		    if dep<=step+1 then
		      # this is the minimum possible pcgs-depth at this
		      # point
		      g:=id;
		    fi;
                fi;
            else
                Error( "<elm> must lie in group defined by <pcgs>" );
            fi;
        od;
        exp[dep] := led;
	step:=dep;
        elm := LeftQuotient( pcgs[dep]^led, elm );
    od;
    return exp;
end );

#############################################################################
##
#M  ExponentsOfPcElement( <unsorted-pcgs>, <elm>, <range> )
##

InstallOtherMethod( ExponentsOfPcElement,
    "unsorted pcgs/range",
    IsCollsElmsX,
    [ IsPcgs and IsUnsortedPcgsRep,
      IsObject,IsList ],
    0,
function( pcgs, elm,range )
    local   pfa,  pcs,  new,  dep,  id,  exp,  g,  dg,  ll,  lr,  ord,  
            led,pcsl,max,step,codepths,pcspow,relords;

    id  := OneOfPcgs(pcgs);
    exp := ListWithIdenticalEntries(Length(pcgs),0);

    # if <elm> is the identity return the null vector
    if elm = id or Length(range)=0  then
        return exp{range};
    fi;

    max:=Maximum(range);
    pfa := pcgs!.sortingPcgs;
    relords:=RelativeOrders(pfa);
    pcs := pcgs!.sortedPcSequence;
    pcsl:= pcgs!.sortedPcSequenceLeadCoeff;
    pcspow := pcgs!.sortedPcSeqPowers;
    new := pcgs!.newDepths;
    codepths:=pcgs!.minimumCodepths;
        
    # sift element through the sorted system
    step:=0; # the index in pcgs up to which we have already computed exponents
    while elm <> id  do
	#compute the next depth `dep' at which we have an exponent in pcgs.
        g   := elm;
        dep := Length(pcgs)+1;
        while g <> id  do
	    # do this by stepping down in pag
            dg := DepthOfPcElement( pfa, g );

	    if codepths[dg]>dep then
	      # once we have reached pfa-depth dg, we cannot acchieve `dep'
	      # any longer. So we may stop the descent through pfa here
	      g:=id;
            elif IsBound(pcs[dg])  then
                ll  := LeadingExponentOfPcElement( pfa, g );
                #lr  := LeadingExponentOfPcElement( pfa, pcs[dg]);
                lr  := pcsl[dg]; # precomputed value
                #ord := RelativeOrderOfPcElement( pfa, g );
		# the relative order is of course the rel. ord. in pfa
		# at depth dg.
		ord:=relords[dg];
                ll  := (ll/lr mod ord);
                #g   := LeftQuotient( pcs[dg]^ll, g ); 
                g   := LeftQuotient( pcspow[dg][ll], g ); #precomputed
                if new[dg] < dep  then
                    dep := new[dg];
                    led := ll;
		    if dep<=step+1 then
		      # this is the minimum possible pcgs-depth at this
		      # point
		      g:=id;
		    fi;
                fi;
            else
                Error( "<elm> must lie in group defined by <pcgs>" );
            fi;
        od;

        exp[dep] := led;
	step:=dep;
	if dep>=max then
	  # we have found all exponents, may stop
	  break;
	fi;
        elm := LeftQuotient( pcgs[dep]^led, elm );
    od;
    return exp{range};
end);


#############################################################################
##
#M  LeadingExponentOfPcElement( <unsorted-pcgs>, <elm> )
##
InstallMethod( LeadingExponentOfPcElement,
    "unsorted pcgs",
    IsCollsElms,
    [ IsPcgs and IsUnsortedPcgsRep,
      IsObject ],
    0,

function( pcgs, elm )
    local   pfa,  pcs,  new,  dep,  id,  dg,  ll,  lr,  ord, led,pcsl,
            relords,pcspow,codepths,step;

    id  := OneOfPcgs(pcgs);
    # if <elm> is the identity return fail
    if elm = id  then
        return fail;
    fi;

    pfa := pcgs!.sortingPcgs;
    relords:=RelativeOrders(pfa);
    pcs := pcgs!.sortedPcSequence;
    pcsl:= pcgs!.sortedPcSequenceLeadCoeff;
    pcspow := pcgs!.sortedPcSeqPowers;
    new := pcgs!.newDepths;
    codepths:=pcgs!.minimumCodepths;
    dep := Length(pcgs)+1;

    # sift element through the sorted system
    while elm <> id  do
	# do this by stepping down in pag
        dg := DepthOfPcElement( pfa, elm );

	if codepths[dg]>dep then
	  # once we have reached pfa-depth dg, we cannot acchieve `dep'
	  # any longer. So we may stop the descent through pfa here
	  elm:=id;
	elif IsBound(pcs[dg])  then
            ll  := LeadingExponentOfPcElement( pfa, elm );
	    #lr  := LeadingExponentOfPcElement( pfa, pcs[dg]);
	    lr  := pcsl[dg]; # precomputed value
	    #ord := RelativeOrderOfPcElement( pfa, elm );
	    # the relative order is of course the rel. ord. in pfa
	    # at depth dg.
	    ord:=relords[dg];
	    ll  := (ll/lr mod ord);
	    #elm := LeftQuotient( pcs[dg]^ll, elm); 
	    elm := LeftQuotient( pcspow[dg][ll], elm ); #precomputed

            if new[dg] < dep  then
                dep := new[dg];
                led := ll;
            fi;
        else
            Error( "<elm> must lie in group defined by <pcgs>" );
        fi;
    od;
    return led;
end );

#############################################################################
##

#M  Order( <obj> )  . . . . . . . . . . . . . . . . . . order of a pc-element
##

#############################################################################
InstallMethod( Order,
        "method for a pc-element",
        HasDefiningPcgs,
        [ IsMultiplicativeElementWithOne ], 3,
        function( g )
    local   pcgs,  rorders,  one,  ord,  d,  rord;

    pcgs := DefiningPcgs( FamilyObj( g ) );
    rorders := RelativeOrders( pcgs );
    
    one := g^0;
    ord := 1;

    if IsPrimeOrdersPcgs( pcgs ) then
        while g <> one do
            d    := DepthOfPcElement( pcgs, g );
            rord := rorders[ d ];
            ord  := ord * rord;
            g    := g^rord;
        od;
    else
        while g <> one do
            d    := DepthOfPcElement( pcgs, g );
            if not IsBound( rorders[d] ) or rorders[ d ] = 0 then
                return infinity;
            fi;
            rord := rorders[ d ];
            rord := rord / Gcd( ExponentOfPcElement( pcgs, g, d ), rord );
            ord  := ord * rord;
            g    := g^rord;
        od;
    fi;
    return ord;
end );



#############################################################################
##

#E  pcgspcg.gi	. . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##
