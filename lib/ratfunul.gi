#############################################################################
##
#W  ratfunul.gi                 GAP Library                      Frank Celler
#W                                                             Andrew Solomon
#W                                                           Alexander Hulpke
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1999 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the methods for rational functions that know that they
##  are univariate laurent polynomials.
##
Revision.ratfunul_gi :=
    "@(#)$Id$";

#############################################################################
##
#M  LaurentPolynomialByCoefficients( <fam>, <cofs>, <val>, <ind> )
##
InstallMethod( LaurentPolynomialByCoefficients, "with indeterminate", true,
    [ IsUFDFamily, IsList, IsInt, IsInt ], 0,
function( fam, cofs, val, ind )
  # construct a laurent polynomial

  fam:=RationalFunctionsFamily(fam);
  if Length(cofs)>0 and (IsZero(cofs[1]) or IsZero(cofs[Length(cofs)])) then
    if not IsMutable(cofs) then
      cofs:=ShallowCopy(cofs);
    fi;
    val:=val+RemoveOuterCoeffs(cofs,fam!.zeroCoefficient);
  fi;


  # make sure that the valuation is correct
  if 0 = Length(cofs)  then
    # if its the zero polynomial, send [[],0] to LaurentPolynomialByCoefficientList
    return LaurentPolynomialByExtRep(fam,[[],0],ind);
  else
    return LaurentPolynomialByExtRep(fam,[cofs,val],ind);
  fi;

end );

#############################################################################
InstallOtherMethod( LaurentPolynomialByCoefficients, "fam, cof,val",true,
    [ IsFamily, IsList, IsInt ], 0,
function( fam, cofs, val )
    return LaurentPolynomialByCoefficients( fam, cofs, val, 1 );
end );

#############################################################################
##
#M  UnivariatePolynomialByCoefficients( <fam>, <cofs>, <ind> )
##


#############################################################################
InstallMethod( UnivariatePolynomialByCoefficients, "fam, cof,ind",true,
    [ IsFamily, IsList, IsPosInt ], 0,
function( fam, cofs, ind )
    return LaurentPolynomialByCoefficients( fam, cofs, 0, ind );
end );

#############################################################################
InstallOtherMethod( UnivariatePolynomialByCoefficients, "fam,cof",true,
    [ IsFamily, IsList ], 0,
function( fam, cofs )
    return LaurentPolynomialByCoefficients( fam, cofs, 0, 1 );
end );

#############################################################################
InstallMethod( UnivariatePolynomial, "ring,cof,indn",true,
    [ IsRing, IsRingElementCollection,IsPosInt ], 0,
function( ring, cofs,indn )
    return LaurentPolynomialByCoefficients( ElementsFamily(FamilyObj(ring)),
                                            cofs, 0, indn );
end );

#############################################################################
InstallOtherMethod( UnivariatePolynomial, "ring,cof",true,
    [ IsRing, IsRingElementCollection ], 0,
function( ring, cofs )
    return LaurentPolynomialByCoefficients( ElementsFamily(FamilyObj(ring)),
                                            cofs, 0, 1 );
end );

#############################################################################
InstallMethod( CoefficientsOfUnivariatePolynomial, "use laurent coeffs",true,
    [ IsUnivariatePolynomial ], 0,
function(f);
  f:=CoefficientsOfLaurentPolynomial(f);
  return ShiftedCoeffs(f[1],f[2]);
end );

RedispatchOnCondition( CoefficientsOfUnivariatePolynomial, true, 
    [ IsRationalFunction ], [ IsUnivariatePolynomial ], 0);

#############################################################################
##
#M  DegreeOfLaurentPolynomial( <laurent> )
##
InstallMethod( DegreeOfLaurentPolynomial,
    true,
    [ IsRationalFunction and IsLaurentPolynomial ],
    0,

function( obj )
    local   cofs;

    cofs := CoefficientsOfLaurentPolynomial(obj);
    if IsEmpty(cofs[1])  then
        return infinity;
    else
        return cofs[2] + Length(cofs[1]) - 1;
    fi;
end );

#############################################################################
##
#M  DegreeIndeterminate( pol, ind )
##
InstallOtherMethod(DegreeIndeterminate,"laurent,indetnr",true,
  [IsLaurentPolynomial,IsPosInt],0,
function(pol,ind)
local d;
  d:=DegreeOfLaurentPolynomial(pol);
  # unless constant: return 0 as we are in the wrong game
  if d>0 and IndeterminateNumberOfUnivariateRationalFunction(pol)<>ind then
    return 0;
  fi;
  return d;
end);

#############################################################################
##
#M  IsPolynomial(<laurpol>)
##
InstallMethod(IsPolynomial,"rational function rep.",true,
  [IsLaurentPolynomialDefaultRep],0,
function(f)
  return CoefficientsOfLaurentPolynomial(f)[2]>=0; # test valuation
end);

#############################################################################
##
#F  BRCIUnivPols( <upol>, <upol> ) test for common base ring and for
##                           common indeterminate of UnivariatePolynomials
InstallGlobalFunction( BRCIUnivPols, function(f,g)
local dom,d,x;
  if IsLaurentPolynomial(f) and IsLaurentPolynomial(g) then
    dom:=FamilyObj(f);
    if dom<>FamilyObj(g) then
      return fail; # different coefficient families
    fi;
    dom:=CoefficientsFamily(dom);

    # is either polynomial constant? if yes we must permit different
    # indeterminate numbers
    d:=DegreeOfLaurentPolynomial(f);
    if d=0 or d=infinity then
      return [dom,IndeterminateNumberOfLaurentPolynomial(g)];
    fi;
    x:=IndeterminateNumberOfLaurentPolynomial(f);
    d:=DegreeOfLaurentPolynomial(g);
    if d<>0 and d<>infinity and 
       x<>IndeterminateNumberOfLaurentPolynomial(g) then
      return fail;
    fi;
    # all OK
    return [dom,x];
  fi;
  return fail;
end );

#############################################################################
##
#M  ExtRepNumeratorRatFun(<ulaurent>)
##
##
##  Modification of ExtRepOfObj() AS
InstallMethod(ExtRepNumeratorRatFun,"laurent polynomial rep.",true,
  [IsLaurentPolynomialDefaultRep],0,
function( obj )
    local   zero,  cofs,  val,  ind,  quo,  ext,  i,  j;

    zero := FamilyObj(obj)!.zeroCoefficient;
    cofs := CoefficientsOfLaurentPolynomial(obj);
    if Length(cofs) = 0 then
      return [];
    fi;
    val  := Maximum(0,cofs[2]); # negagive will go into denominator
    cofs := cofs[1];

    ind  := IndeterminateNumberOfUnivariateRationalFunction(obj);

    ext := [];
    for i  in [ 0 .. Length(cofs)-1 ]  do
        if cofs[i+1] <> zero  then
            j := val + i;
            if j <> 0  then
                Add( ext, [ ind, j ] );
                Add( ext, cofs[i+1] );
            else
                Add( ext, [] );
                Add( ext, cofs[i+1] );
            fi; 
        fi; 
    od; 
    
    return ext;
    
end );



#############################################################################
##
#M  ExtRepDenominatorRatFun(<ulaurent>)
##
InstallMethod(ExtRepDenominatorRatFun,"laurent polynomial rep.",true,
  [IsLaurentPolynomialDefaultRep],0,
function(obj)
    local   cofs,  val,  ind,  quo,  ext,  i,  j;

    cofs := CoefficientsOfLaurentPolynomial(obj);
		if Length(cofs) = 0 then
			return [[], FamilyObj(obj)!.oneCoefficient];
		fi;
    val  := cofs[2];
    cofs := cofs[1];
    ind  := IndeterminateNumberOfUnivariateRationalFunction(obj);
		
    # This is to compute the denominator
			
    if val < 0  then
        quo := [ [ ind, -val ], FamilyObj(obj)!.oneCoefficient ];
		else
		  quo := [ [],  FamilyObj(obj)!.oneCoefficient ];
    fi; 
    
    return quo;
    
end);

#############################################################################
##
#M  One(<laurent>)
##
InstallMethod(OneOp,"univariate",true,
  [ IsRationalFunction and IsUnivariateRationalFunction ], 0,
function(p)
local indn,fam;
  fam:=FamilyObj(p);
  indn := IndeterminateNumberOfUnivariateRationalFunction(p);
  if not IsBound(fam!.univariateOnePolynomials[indn]) then
    fam!.univariateOnePolynomials[indn]:=
      LaurentPolynomialByExtRep(fam,[[fam!.oneCoefficient],0],indn);
  fi;
  return fam!.univariateOnePolynomials[indn];
end);

# avoid the one of the family (which is not univariate!)
InstallMethod(One,"univariate",true,
  [ IsRationalFunction and IsUnivariateRationalFunction ], 0, OneOp);

#############################################################################
##
#M  Zero(<laurent>)
##
InstallMethod(ZeroOp,"univariate",true,
  [ IsRationalFunction and IsUnivariateRationalFunction ], 0,
function(p)
local indn,fam;
  fam:=FamilyObj(p);
  indn := IndeterminateNumberOfUnivariateRationalFunction(p);
  if not IsBound(fam!.univariateZeroPolynomials[indn]) then
    fam!.univariateZeroPolynomials[indn]:=
      LaurentPolynomialByExtRep(fam,[[],0],indn);
  fi;
  return fam!.univariateZeroPolynomials[indn];

end);

# avoid the one of the family (which is not univariate!)
InstallMethod(Zero,"univariate",true,
  [ IsRationalFunction and IsUnivariateRationalFunction ], 0, ZeroOp);

#############################################################################
##
#M  IndeterminateOfUnivariateRationalFunction( <laurent> )
##
InstallMethod( IndeterminateOfUnivariateRationalFunction,
  "use `IndeterminateNumber'",true,
  [ IsRationalFunction and IsUnivariateRationalFunction ], 0,
function( obj )
    local   fam;

    fam := FamilyObj(obj);
    return LaurentPolynomialByExtRep(fam,
        [[ FamilyObj(obj)!.oneCoefficient ],1],
        IndeterminateNumberOfUnivariateRationalFunction(obj) );
end );


# Arithmetic

#############################################################################
##
#M  AdditiveInverseOp( <laurent> )
##
InstallMethod( AdditiveInverseOp,"laurent polynomial",
    true, [ IsRationalFunction and IsLaurentPolynomial ], 0,
function( obj )
local   cofs,  indn;

  cofs := CoefficientsOfLaurentPolynomial(obj);
  indn := IndeterminateNumberOfUnivariateRationalFunction(obj);

  return LaurentPolynomialByExtRep(FamilyObj(obj),
      [List(cofs[1],AdditiveInverse),cofs[2]],indn);

end );

#############################################################################
##
#M  InverseOp( <laurent> )
##
InstallMethod( InverseOp,"try to express as laurent polynomial", true,
    [ IsRationalFunctionsFamilyElement and IsLaurentPolynomial ], 0,
function( obj )
local   cofs,  indn;

  indn := IndeterminateNumberOfUnivariateRationalFunction(obj);

  # this only works if we have only one coefficient
  cofs := CoefficientsOfLaurentPolynomial(obj);
  if 1 <> Length(cofs[1])  then
    TryNextMethod();
  fi;

  # invert the valuation
  return LaurentPolynomialByExtRep(FamilyObj(obj),
      [[Inverse(cofs[1][1])], -cofs[2]], indn );
end );

#############################################################################
##
#M  <laurent> * <laurent>
##
InstallMethod( \*, "laurent * laurent", IsIdenticalObj,
    [ IsRationalFunction and IsLaurentPolynomial,
      IsRationalFunction and IsLaurentPolynomial], 0,
function( left, right )
local   indn,  fam,  prd,  l,  r,  m,  n,  i,  z,  j,  val;

  # this method only works for the same indeterminate
  indn:=BRCIUnivPols(left,right);
  if indn=fail then 
    TryNextMethod();
  fi;

  # fold the coefficients
  fam := FamilyObj(left);
  prd := [];

  # special treatment of zero
  l   := CoefficientsOfLaurentPolynomial(left);
  if Length(l[1])=0 then
    return left;
  fi;

  r   := CoefficientsOfLaurentPolynomial(right);
  if Length(r[1])=0 then
    return right;
  fi;

  m   := Length(l[1]);
  n   := Length(r[1]);
#T Use `ProductCoeffs' ?
  for i  in [ 1 .. m+n-1 ]  do
      z := fam!.zeroCoefficient;
      for j  in [ Maximum(i+1-n,1) .. Minimum(m,i) ]  do
	  z := z + l[1][j] * r[1][i+1-j];
      od;
      prd[i] := z;
  od;
  val := l[2] + r[2];
  val:=val+RemoveOuterCoeffs(prd,fam!.zeroCoefficient);

  # return the polynomial
  return LaurentPolynomialByExtRep(fam,[prd, val], indn[2] );
end );

#############################################################################
##
#M  <laurent> + <laurent>
##
InstallMethod( \+, "laurent + laurent", IsIdenticalObj,
    [ IsRationalFunction and IsLaurentPolynomial,
      IsRationalFunction and IsLaurentPolynomial ], 0,
function( left, right )
local   indn,  fam,  zero,  l,  r,  val,  sum,  vdf,  i;

  # this method only works for the same indeterminate
  indn:=BRCIUnivPols(left,right);
  if indn=fail then 
    TryNextMethod();
  fi;

  # get the coefficients
  fam  := FamilyObj(left);
  zero := fam!.zeroCoefficient;
  l    := CoefficientsOfLaurentPolynomial(left);
  r    := CoefficientsOfLaurentPolynomial(right);

  # add both coefficients lists
  if l[2]=r[2] then
    sum:=ShallowCopy(l[1]);
    AddCoeffs(sum,r[1]);
    val:=l[2];
  elif l[2] < r[2]  then
      val := l[2];
      sum := ShallowCopy(l[1]);
      vdf := r[2] - l[2];
      for i  in [ Length(sum)+1 .. Length(r[1])+vdf ] do
	  sum[i] := zero;
      od;
      for i  in [ 1 .. Length(r[1]) ]  do
	  sum[i+vdf] := sum[i+vdf] + r[1][i];
      od;
  else
      val := r[2];
      sum := ShallowCopy(r[1]);
      vdf := l[2] - r[2];
      for i  in [ Length(sum)+1 .. Length(l[1])+vdf ] do
	  sum[i] := zero;
      od;
      for i  in [ 1 .. Length(l[1]) ]  do
	  sum[i+vdf] := l[1][i] + sum[i+vdf];
      od;
  fi;

  val:=val+RemoveOuterCoeffs(sum,fam!.zeroCoefficient);
  if Length(sum)=0 then
    val:=0; # special case: result is 0.
  fi;
  # and return the polynomial (we might get a new valuation!)
  return LaurentPolynomialByExtRep(fam, [sum, val], indn[2] );

end);

#############################################################################
##
#M  <coeff>       * <laurent>
##
##
BindGlobal("ProdCoeffLaurpol",function( coef, laur )
local   fam, zero,  indn,  tmp,  prd,  val;

  if IsZero(coef) then return Zero(laur);
  elif IsOne(coef) then return laur;fi;

  fam:=FamilyObj(laur);
  indn := IndeterminateNumberOfUnivariateRationalFunction(laur);

  # multiply by zero gives the zero polynomial
  zero := fam!.zeroCoefficient;

  # construct the product and check the valuation in case zero divisors
  tmp := CoefficientsOfLaurentPolynomial(laur);
  prd := coef * tmp[1];
  val := 0;
  while val < Length(prd) and prd[val+1] = zero  do
    val := val + 1;
  od;
  if Length(prd) = val  then
    return LaurentPolynomialByExtRep(fam,[[], 0], indn );
  elif 0 = val  then
    return LaurentPolynomialByExtRep(fam,[prd, tmp[2]], indn );
  else
    return LaurentPolynomialByExtRep(fam,
	[prd{[val+1..Length(prd)]}, tmp[2]+val], indn );
  fi;

end );

InstallMethod( \*, "coeff * laurent", IsCoeffsElms,
  [ IsRingElement, IsRationalFunction and IsLaurentPolynomial ], 0,
  ProdCoeffLaurpol);

InstallMethod( \*, "laurent * coeff", IsElmsCoeffs,
  [ IsRationalFunction and IsLaurentPolynomial,IsRingElement ], 0,
  function(l,c) return ProdCoeffLaurpol(c,l);end);


#############################################################################
##
#M  <coeff>       + <laurent>
##
##  This method is  installed for all  rational functions because it does not
##  matter if one is  in a 'RationalFunctionsFamily',  a 'LaurentPolynomials-
##  Family', or a 'UnivariatePolynomialsFamily'.   The sum is defined  in all
##  three cases.
##
BindGlobal("SumCoeffLaurpol", function( coef, laur )
local   fam,zero,  tmp,  indn,  val,  sum,  i;

  if IsZero(coef) then return laur;fi;

  indn := IndeterminateNumberOfUnivariateRationalFunction(laur);

  fam:=FamilyObj(laur);
  zero := fam!.zeroCoefficient;
  tmp  := CoefficientsOfLaurentPolynomial(laur);
  val  := tmp[2];

  # if coef is trivial return laur
  if coef = zero  then
      return laur;

  # the polynomial is trivial
  elif 0 = Length(tmp[1])  then
      # we create, no problem occurs
      return LaurentPolynomialByExtRep(fam, [[coef], 0], indn );

  # the constant is present
  elif val <= 0 and 0 < val + Length(tmp[1])  then
      sum := ShallowCopy(tmp[1]);
      i:=1-val;
      if (i=1 or i=Length(sum)) and sum[i]+coef=fam!.zeroCoefficient then
	# be careful if cancellation happens at an end
        sum[i]:=fam!.zeroCoefficient;
	val:=val+RemoveOuterCoeffs(sum,fam!.zeroCoefficient);
      else
	# no cancellation in first place
	sum[i] := coef + sum[i];
      fi;
      return LaurentPolynomialByExtRep(fam, [sum, val], indn );

  # every coefficients has a negative exponent
  elif val + Length(tmp[1]) <= 0  then
      sum := ShallowCopy(tmp[1]);
      for i  in [ Length(sum)+1 .. -val ]  do
	  sum[i] := zero;
      od;
      sum[1-val] := coef;
      # we add at the end, no problem occurs
      return LaurentPolynomialByExtRep(fam, [sum, val], indn );

  # every coefficients has a positive exponent
  else
      sum := [coef];
      for i  in [ 2 .. val ]  do
	  sum[i] := zero;
      od;
      Append( sum, tmp[1] );
      # we add in the first position, no problem occurs
      return LaurentPolynomialByExtRep(fam, [sum, 0], indn );

  fi;
end );

InstallMethod( \+, "coeff + laurent", IsCoeffsElms,
    [ IsRingElement, IsRationalFunction and IsLaurentPolynomial ], 0,
    SumCoeffLaurpol);

InstallMethod( \+, "laurent + coeff", IsElmsCoeffs,
    [ IsRationalFunction and IsLaurentPolynomial, IsRingElement ], 0,
    function(l,c) return SumCoeffLaurpol(c,l); end);

# special convenience: permit to add rationals
InstallMethod( \+, "coeff + laurent", true,
    [ IsRat, IsRationalFunction and IsLaurentPolynomial ], 0,
  function(c,r) return SumCoeffLaurpol(c*FamilyObj(r)!.oneCoefficient,r); end);

InstallMethod( \+, "laurent + coeff", true,
    [ IsRationalFunction and IsLaurentPolynomial, IsRat ], 0,
  function(l,c) return SumCoeffLaurpol(c*FamilyObj(l)!.oneCoefficient,l); end);


#############################################################################
##
#F  QuotRemLaurpols(left,right,mode)
##
InstallGlobalFunction(QuotRemLaurpols,function(f,g,mode)
local fam,indn,val,q,m,n,i,k,c;
  fam:=FamilyObj(f);
  indn := BRCIUnivPols(f,g); # use to get the indeterminate
  if indn=fail then
    return fail; # can't do anything
  fi;
  f:=CoefficientsOfLaurentPolynomial(f);
  g:=CoefficientsOfLaurentPolynomial(g);
  if Length(g[1])=0 then
    return fail; # cannot divide by 0
  fi;
  if f[2]>0 then
    f:=ShiftedCoeffs(f[1],f[2]);
  else
    f:=ShallowCopy(f[1]);
  fi;
  if g[2]>0 then
    g:=ShiftedCoeffs(g[1],g[2]);
  else
    g:=g[1];
  fi;

  #T might use: ReduceCoeffs?
  # try to divide
  q:=[];
  n:=Length(g);
  m:=Length(f)-n;
  for i in [0..m] do
    c:=f[m-i+n]/g[n];
    for k in [1..n] do
      f[m-i+k]:=f[m-i+k]-c*g[k];
    od;
    q[m-i+1]:=c;
  od;

  if mode=1 or mode=4 then
    if mode=4 and ForAny(f,i->not IsZero(i)) then
      return fail;
    fi;
    val:=RemoveOuterCoeffs(q,fam!.zeroCoefficient);
    q:=LaurentPolynomialByExtRep(fam,[q,val],indn[2]);
    return q;
  elif mode=2 then
    val:=RemoveOuterCoeffs(f,fam!.zeroCoefficient);
    f:=LaurentPolynomialByExtRep(fam,[f,val],indn[2]);
    return f;
  elif mode=3 then
    val:=RemoveOuterCoeffs(q,fam!.zeroCoefficient);
    q:=LaurentPolynomialByExtRep(fam,[q,val],indn[2]);
    val:=RemoveOuterCoeffs(f,fam!.zeroCoefficient);
    f:=LaurentPolynomialByExtRep(fam,[f,val],indn[2]);
    return [q,f];
  fi;

end);

#############################################################################
##
#M  <unilau> / <unilau> (if possible)
##
##  While w rely for ordinary rat. fun. on a*Inverse(b) we do not want this
##  for laurent polynomials, as the inverse would have to be represented as
##  a rational function, not a laurent polynomial.
InstallMethod(\/,"upol/upol",true,[IsLaurentPolynomial and IsPolynomial,
  IsLaurentPolynomial and IsPolynomial],2,
function(a,b)
local q;
  q:=QuotRemLaurpols(a,b,4);
  if q=fail then
    TryNextMethod();
  fi;
  return q;
end);

#############################################################################
##
#M  QuotientRemainder( [<pring>,] <upol>, <upol> )
##
InstallMethod(QuotientRemainder,"laurent, ring",IsCollsElmsElms,
  [IsPolynomialRing,IsLaurentPolynomial,IsLaurentPolynomial],0,
function (R,f,g)
local q;
  q:=QuotRemLaurpols(f,g,3);
  if q=fail then
    TryNextMethod();
  fi;
  return q;
end);

RedispatchOnCondition(QuotientRemainder,IsCollsElmsElms,
  [IsPolynomialRing,IsRationalFunction,IsRationalFunction],
                [,IsLaurentPolynomial,IsLaurentPolynomial],0);

InstallOtherMethod(QuotientRemainder,"laurent",IsIdenticalObj,
                [IsLaurentPolynomial,IsLaurentPolynomial],0,
function (f,g)
local q;
  q:=QuotRemLaurpols(f,g,3);
  if q=fail then
    TryNextMethod();
  fi;
  return q;
end);

RedispatchOnCondition(QuotientRemainder,IsIdenticalObj,
  [IsRationalFunction,IsRationalFunction],
  [IsLaurentPolynomial,IsLaurentPolynomial],0);

#############################################################################
##
#M  Quotient( [<pring>], <upol>, <upol> )
##
InstallMethod(Quotient,"laurent, ring",IsCollsElmsElms,[IsPolynomialRing,
                IsLaurentPolynomial,IsLaurentPolynomial],0,
function (R,f,g)
  return Quotient(f,g);
end);

InstallOtherMethod(Quotient,"laurent",IsIdenticalObj,
  [IsLaurentPolynomial,IsLaurentPolynomial],0,
function (f,g)
local q;
  return QuotRemLaurpols(f,g,4);
end);

#############################################################################
##
#M  QuotientMod( <pring>, <upol>, <upol>, <upol> )
##
InstallMethod(QuotientMod,"laurent",IsCollsElmsElmsElms,
  [IsRing,IsRingElement,IsRingElement,IsRingElement],0,
function (R,r,s,m)
local f,g,h,fs,gs,hs,q,t;
    f := s;  fs := 1;
    g := m;  gs := 0;
    while g <> Zero(g) do
        t := QuotientRemainder(f,g);
        h := g;          hs := gs;
        g := t[2];       gs := fs - t[1]*gs;
        f := h;          fs := hs;
    od;
    q:=QuotRemLaurpols(r,f,1);
    if q = fail  then
        return fail;
    else
        return (fs*q) mod m;
    fi;
end);

#############################################################################
##
#M  PowerMod( <pring>, <upol>, <exp>, <upol> )	. . . . power modulo
##
InstallMethod(PowerMod,"laurent",IsCollsElmsXElms,
   [IsPolynomialRing,IsLaurentPolynomial,IsInt,IsLaurentPolynomial],0,
function(R,g,e,m)
local val,brci,fam;

  brci:=BRCIUnivPols(g,m);
  if brci=fail then TryNextMethod();fi;

  fam:=FamilyObj(g);
  # if <m> is of degree zero return the zero polynomial
  if DegreeOfLaurentPolynomial(m) = 0  then
    return Zero(g);

  # if <e> is zero return one
  elif e = 0  then
    return One(g);
  fi;

  # reduce polynomial
  g:=EuclideanRemainder(R,g,m);

  # and invert if necessary
  if e < 0  then
    g := QuotientMod(R,One(R),g,m);
    if g = fail  then
      Error("<g> must be invertable module <m>");
    fi;
    e := -e;
  fi;

  g:=CoefficientsOfLaurentPolynomial(g);
  m:=CoefficientsOfLaurentPolynomial(m);

  # use 'PowerModCoeffs' to power polynomial
  if g[2]=m[2] then
    val:=g[2];
    g:=g[1];
    m:=m[1];
  else
    val:=0;
    g:=ShiftedCoeffs(g[1],g[2]);
    m:=ShiftedCoeffs(m[1],m[2]);
  fi;
  g:=PowerModCoeffs(g,e,m);
  val:=val+RemoveOuterCoeffs(g,fam!.zeroCoefficient);
  g:=LaurentPolynomialByExtRep(fam,[g,val],brci[2]);
  return g;
end);

#############################################################################
##
#M  \=( <upol>, <upol> )  comparison
##
InstallMethod(\=,"laurent",IsIdenticalObj,
  [IsLaurentPolynomial,IsLaurentPolynomial],0,
function(a,b)
local ac,bc;
  ac:=CoefficientsOfLaurentPolynomial(a);
  bc:=CoefficientsOfLaurentPolynomial(b);
  if ac<>bc then 
    return false;
  fi;
  # is the indeterminate important?
  if Length(ac[1])+ac[2]>1 and IndeterminateNumberOfLaurentPolynomial(a)<>
     IndeterminateNumberOfLaurentPolynomial(b) then
    return false;
  fi;
  return true;
end);

#############################################################################
##
#M  \<( <upol>, <upol> )  comparison
##
InstallMethod(\<,"Univariate Polynomials",IsIdenticalObj,
              [IsLaurentPolynomial,IsLaurentPolynomial],0,
function(a,b)
local ac,bc,l,m,z,da,db;
  ac:=CoefficientsOfLaurentPolynomial(a);
  bc:=CoefficientsOfLaurentPolynomial(b);

  # we have problems if they have (truly) different indeterminate numbers
  # (i.e.: both are not constant and the indnums differ
  if (ac[2]<>0 or Length(ac[1])>1) and (bc[2]<>0 or Length(bc[1])>1) and 
    IndeterminateNumberOfLaurentPolynomial(a)<>
     IndeterminateNumberOfLaurentPolynomial(b) then
    TryNextMethod();
  fi;

  da:=Length(ac[1])+ac[2];
  db:=Length(bc[1])+bc[2];

  if da=db then
    # the total length is the same. We do not need to care about shift
    # factors!
    a:=ac[1];b:=bc[1];
    l:=Length(a);
    m:=Length(b);
    while l>0 and m>0 do
      if a[l]<b[m] then
        return true;
      elif a[l]>b[m] then
        return false;
      fi;
      l:=l-1;m:=m-1;
    od;
    # all the coefficients were the same. So we have to compare with a zero
    # that would have been shifted in
    if l>0 then
      z:=Zero(a[l]);
      # we don't need a `l>0' condition, because ending zeroes were shifted
      # out initially
      while a[l]=z do
        l:=l-1;
      od;
      return a[l]<z;
    elif m>0 then
      z:=Zero(b[m]);
      # we don't need a `m>0' condition, because ending zeroes were shifted
      # out initially
      while b[m]=z do
        m:=m-1;
      od;
      return b[m]>z;
    else
      # they are the same
      return false;
    fi;
  else
    # compare the degrees
    return da<db;
  fi;
end);

#############################################################################
##
#F  RandomPol( <fam>, <deg> )
##
InstallGlobalFunction(RandomPol,function(dom,deg)
local i,c;
  c:=[];
  for i in [0..deg] do
    Add(c,Random(dom));
  od;
  while c[deg+1]=Zero(dom) do
    c[deg+1]:=Random(dom);
  od;
  return LaurentPolynomialByCoefficients(FamilyObj(c[1]),c,0,1);
end);

#############################################################################
##
#M  LeadingCoefficient( <upol> )
##
InstallMethod(LeadingCoefficient,"laurent",true,[IsLaurentPolynomial],0,
function(f)
local fam;
  fam:=FamilyObj(f);
  f:=CoefficientsOfLaurentPolynomial(f);
  if Length(f[1])=0 then
    return fam!.zeroCoefficient;
  else
    return f[1][Length(f[1])];
  fi;
end);

#############################################################################
##
#F  LeadingMonomial . . . . . . . . . . . for a univariate laurent polynomial
##
InstallMethod( LeadingMonomial,"for a univariate laurent polynomial", true,
        [ IsLaurentPolynomial ], 0,
  p -> [ IndeterminateNumberOfLaurentPolynomial( p),
         DegreeOfLaurentPolynomial( p ) ]);

#############################################################################
##
#M  EuclideanRemainder( <pring>, <upol>, <upol> )
##
InstallOtherMethod(EuclideanRemainder,"laurent",IsCollsElmsElms,
	      [IsPolynomialRing,IsLaurentPolynomial,IsLaurentPolynomial],0,
function(R,a,b)
local q;
  q:=QuotRemLaurpols(a,b,2);
  if q=fail then
    TryNextMethod();
  fi;
  return q;
end);

#############################################################################
##
#M  \mod( <upol>, <upol> )
##
InstallMethod(\mod,"laurent",IsIdenticalObj,
	      [IsLaurentPolynomial,IsLaurentPolynomial],0,
function(a,b)
local q;
  q:=QuotRemLaurpols(a,b,2);
  if q=fail then
    TryNextMethod();
  fi;
  return q;
end);

#############################################################################
##
#M  GcdOp( <pring>, <upol>, <upol> )  . . . . . .  for univariate polynomials
##
InstallMethod( GcdOp,"univariate polynomial",IsCollsElmsElms,[IsEuclideanRing,
                IsPolynomial,IsPolynomial],0,
function(R,f,g)
local gcd,u,v,w,val,brci;

  brci:=BRCIUnivPols(f,g);
  if brci=fail then TryNextMethod();fi;
  f:=CoefficientsOfLaurentPolynomial(f);
  g:=CoefficientsOfLaurentPolynomial(g);

  # remove common x^i term
  val:=Minimum(f[2],g[2]);
  # the gcd cannot contain any further x^i parts, we removed them all!
  f:=ShallowCopy(f[1]);
  g:=ShallowCopy(g[1]);

  # perform a Euclidean algorithm
  u:=f;
  v:=g;
  while 0<Length(v) do
    w:=v;
    ReduceCoeffs(u,v);
    ShrinkCoeffs(u);
    v:=u;
    u:=w;
  od;
  gcd:=u*u[Length(u)]^-1;

  # return the gcd
  return LaurentPolynomialByCoefficients(brci[1],gcd,val,brci[2]);
end);

RedispatchOnCondition( GcdOp,IsCollsElmsElms,
  [IsEuclideanRing, IsRationalFunction,IsRationalFunction],
  [, IsUnivariatePolynomial,IsUnivariatePolynomial],0);

#############################################################################
##
#M  StandardAssociate( <pring>, <lpol> )
##
InstallMethod(StandardAssociate,"laurent",
  IsCollsElms,[IsPolynomialRing, IsLaurentPolynomial],0,
function(R,f)
local l,a;

  l:=LeadingCoefficient(f);
  if not IsZero(l) then
    # get standard associate of leading term
    f:=f*Quotient(CoefficientsRing(R),
                  StandardAssociate(CoefficientsRing(R),l),l);
  fi;
  return f;
end);

#############################################################################
##
#M  Derivative( <upol> )
##
InstallOtherMethod(Derivative,"Laurent Polynomials",true,
                [IsLaurentPolynomial],0,
function(f)
local d,i,ind;

  ind := [CoefficientsFamily(FamilyObj(f)),
           IndeterminateNumberOfUnivariateRationalFunction(f)];
  d:=CoefficientsOfLaurentPolynomial(f);
  if Length(d[1])=0 then
    # special case: Derivative of 0-Polynomial
    return f;
  fi;
  f:=d;
  d:=[];
  for i in [1..Length(f[1])]  do
      d[i] := (i+f[2]-1)*f[1][i];
  od;
  return LaurentPolynomialByCoefficients(ind[1],d,f[2]-1,ind[2]);
end);

RedispatchOnCondition(Derivative,true,
  [IsPolynomial],[IsLaurentPolynomial],0);

#############################################################################
##
#F  Discriminant( <f> ) . . . . . . . . . . . . discriminant of polynomial f
##
InstallOtherMethod(Discriminant,"laurent",true,[IsLaurentPolynomial],0,
function(f)
local d;
  # the discriminant is \prod_i\prod_{j\not= i}(\alpha_i-\alpha_j), but
  # to avoid chaos with symmetric polynomials, we better compute it as
  # the resultant of f and f'
  d:=DegreeOfLaurentPolynomial(f);
  return (-1)^(d*(d-1)/2)*Resultant(f,Derivative(f),
    IndeterminateNumberOfLaurentPolynomial(f))/LeadingCoefficient(f);
end);

RedispatchOnCondition(Discriminant,true,
  [IsPolynomial],[IsLaurentPolynomial],0);

#############################################################################
##
#M  Value( <upol>, <elm>, <one> )
##
InstallOtherMethod( Value,"Laurent, ring element, and mult. neutral element",
    true, [ IsLaurentPolynomial, IsRingElement, IsRingElement ], 0,
function( f, x, one )
local val, i;
  val:= Zero( one );
  f:= CoefficientsOfLaurentPolynomial( f );
  i:= Length( f[1] );
  while 0 < i do
    val:= val * x + one * f[1][i];
    i:= i-1;
  od;
  if 0 <> f[2] then
    val:= val * x^f[2];
  fi;
  return val;
end );

#############################################################################
##
#M  Value( <upol>, <elm> )
##
InstallOtherMethod(Value,"LaurentPolynomial",true,
  [IsLaurentPolynomial,IsRingElement],0,
function(f,x)
  return Value(f,x,FamilyObj(f)!.oneCoefficient);
end);

# Because Mat+1 <>Mat+Mat^0 we want a different default for this important
# case.
InstallOtherMethod(Value,"LaurentPolynomial on Matrix",true,
  [IsLaurentPolynomial,IsMatrix],0,
function(f,x)
  return Value(f,x,One(x));
end);

RedispatchOnCondition(Value,true,[IsRationalFunction,IsRingElement],
  [IsLaurentPolynomial,IsRingElement],0);

#############################################################################
##
#E
##
