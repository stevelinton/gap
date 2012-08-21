#############################################################################
##
#W  ratfun.gi                   GAP Library                      Frank Celler
#W                                                             Andrew Solomon
#W                                                           Alexander Hulpke
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1999 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file  contains    the  methods  for    rational  functions,  laurent
##  polynomials and polynomials and their families.
##
Revision.ratfun_gi :=
    "@(#)$Id$";

#############################################################################
##
#M  IndeterminateName(<fam>,<nr>)
#M  HasIndeterminateName(<fam>,<nr>)
#M  SetIndeterminateName(<fam>,<nr>,<name>)
##
InstallMethod(IndeterminateName,"for rational function families",true,
  [IsRationalFunctionsFamily,IsPosInt],0,
function(fam,nr)
  if IsBound(fam!.namesIndets[nr]) then
    return fam!.namesIndets[nr];
  else
    return fail;
  fi;
end);

InstallMethod(HasIndeterminateName,"for rational function families",true,
  [IsRationalFunctionsFamily,IsPosInt],0,
function(fam,nr)
  return IsBound(fam!.namesIndets[nr]);
end);

InstallMethod(SetIndeterminateName,"for rational function families",true,
  [IsRationalFunctionsFamily,IsPosInt,IsString],0,
function(fam,nr,str)
  if IsBound(fam!.namesIndets[nr]) and fam!.namesIndets[nr]<>str then
    Error("indeterminate number ",nr,
          " has been baptized already differently");
  else
    fam!.namesIndets[nr]:=Immutable(str);
  fi;
end);

InstallMethod(SetName,"set name of indeterminate",
  true,[IsLaurentPolynomial,IsString],
  SUM_FLAGS+1, # we want to be better than the setter
function(indet,name)
local c;
  c:=CoefficientsOfLaurentPolynomial(indet);
  if not Length(c[1])=1 and One(c[1][1])=c[1][1] and c[2]=1 then
    TryNextMethod();
  fi;
  SetIndeterminateName(FamilyObj(indet),
      IndeterminateNumberOfLaurentPolynomial(indet),name);
end);

# Functions to create objects in the three representations

#############################################################################
##
#F  LaurentPolynomialByExtRep(<rfam>,<coeffs>,<inum>)
##
InstallGlobalFunction(LaurentPolynomialByExtRep,
function(rfam,coeffs,inum)
local f,typ;
  #coeffs[1] = list, coeffs[2] = valuation

# trap code for unreduced coeffs.
# if Length(coeffs[1])>0 
#    and (IsZero(coeffs[1][1]) or IsZero(coeffs[1][Length(coeffs[1])])) then
#   Error("zero coeff!");
# fi;

  # check for constants and zero
	if 0 = Length(coeffs) then
		# it is the zero polynomial
		typ := rfam!.threeLaurentPolynomialTypes[2];
  elif 0 = coeffs[2] and 1 = Length(coeffs[1])  then
			# unshifted and one coefficient - constant
      typ := rfam!.threeLaurentPolynomialTypes[2];
  elif 0 <= coeffs[2]  then
			# possibly shifted left - polynomial
      typ := rfam!.threeLaurentPolynomialTypes[3];
  else
      typ := rfam!.threeLaurentPolynomialTypes[1];
  fi;
  # objectify
  f := rec();
  ObjectifyWithAttributes(f,typ,
    IndeterminateNumberOfLaurentPolynomial, inum,
    CoefficientsOfLaurentPolynomial, coeffs);

  # and return the polynomial
  return f;
end );

#############################################################################
##
#F  PolynomialByExtRep(<rfam>,<ext>)
##
InstallGlobalFunction(PolynomialByExtRep,
function(rfam,ext)
local f;
  # objectify
  f := rec();
  ObjectifyWithAttributes(f,rfam!.defaultPolynomialType,
    ExtRepPolynomialRatFun, ext);

  # and return the polynomial
  return f;
end );

#############################################################################
##
#F  RationalFunctionByExtRep(<rfam>,<num>,<den>)
##
##
InstallGlobalFunction(RationalFunctionByExtRep,
function(rfam,num,den)
local f;
  # objectify
  f := rec();
  ObjectifyWithAttributes(f,rfam!.defaultRatFunType,
    ExtRepNumeratorRatFun, num,
    ExtRepDenominatorRatFun, den);

  # and return the polynomial
  return f;
end );

# basic operations to compute attribute values for the properties
# This is the only place where methods should be installed based on the
# representation.


#############################################################################
##
#M  IsLaurentPolynomial( <rat-fun> )
##
InstallMethod( IsLaurentPolynomial,
    true,
    [ IsUnivariateRationalFunction ],
    0,

function( obj )
    local   den;
   
#T: GGT
    den := ExtRepDenominatorRatFun( obj );

    # there has to be only one monomial
    return 2 = Length(den);
end );


#############################################################################
##
#M  IsConstantRationalFunction(<ulaurent>)
##
InstallMethod(IsConstantRationalFunction,"polynomial",true,
  [IsRationalFunction and IsPolynomial],0,
function(f)
local extf;

  extf := ExtRepPolynomialRatFun(f);
  return  Length(extf) = 0 or (Length(extf)=2 and extf[1]=[]);
end);

#############################################################################
##
#M  ExtRepPolynomialRatFun(<ulaurent>)
##
InstallMethod(ExtRepPolynomialRatFun,"laurent polynomial rep.",true,
  [IsLaurentPolynomialDefaultRep and IsPolynomial],0,
function(f)
local coefs, ind, extrep, i, shift,fam;
  fam:=FamilyObj(f);
  coefs := CoefficientsOfLaurentPolynomial(f);
  ind := IndeterminateNumberOfLaurentPolynomial(f);
  extrep := [];
  shift := coefs[2];
  for i in [1 .. Length(coefs[1])] do
    if coefs[1][i]<>fam!.zeroCoefficient then
      Append(extrep,[[ind, i + shift -1], coefs[1][i]]);
    fi;
  od;
  return extrep;
  
end);

#############################################################################
##
#M  IsPolynomial(<ratfun>)
##
InstallMethod(IsPolynomial,"rational function rep.",true,
  [IsRationalFunctionDefaultRep],0,
function(f)
local q;
  q:=QuotientPolynomialsExtRep(FamilyObj(f),
	  ExtRepNumeratorRatFun(f),ExtRepDenominatorRatFun(f));
  if q=fail then
    return false;
  else
    SetExtRepPolynomialRatFun(f,q);
    return true;
  fi;
end);

#############################################################################
##
#M  ExtRepPolynomialRatFun(<ratfun>)
##
InstallMethod(ExtRepPolynomialRatFun,"rational function rep.",true,
  [IsRationalFunctionDefaultRep and IsPolynomial],0,
function(f)
  return QuotientPolynomialsExtRep(FamilyObj(f),
	  ExtRepNumeratorRatFun(f),ExtRepDenominatorRatFun(f));
end);

#############################################################################
##
#M  ExtRepNumeratorRatFun(<poly>)
##
InstallMethod(ExtRepNumeratorRatFun,"polynomial rep -> ExtRepPolynomialRatFun",
  true, [IsPolynomialDefaultRep],0,ExtRepPolynomialRatFun);

#############################################################################
##
#M  ExtRepDenominatorRatFun(<poly>)
##
InstallMethod(ExtRepDenominatorRatFun,"polynomial, return constant",true,
  [IsPolynomialDefaultRep],0,
function(f)
local fam;
  fam:=FamilyObj(f);
  # store the constant ext rep. for one in the family
  if not IsBound(fam!.constantDenominatorExtRep) then
    fam!.constantDenominatorExtRep:=
      Immutable([[],One(CoefficientsFamily(fam))]);
  fi;
  return fam!.constantDenominatorExtRep;
end);


#############################################################################
##
#F  IsUnivariateRationalFunctionByNumerAndDenom( <num>, <den> )
##
##  <num> and <den> are the second entries in the 'ExtRep' value of
##  polynomials, 
##
IsUnivariateRationalFunctionByNumerAndDenom := function( num, den )
    local   ind,  i;

#T: GGT
    # now check the monomials
    ind := false;
    for i  in [ 1, 3 .. Length(den)-1 ]  do
        if 2 < Length(den[i])  then
            return false;
        elif 2 = Length(den[i])  then
            if ind = false  then
                ind := den[i][1];
            elif ind <> den[i][1]  then
                return false;
            fi;
        fi;
    od;
    for i  in [ 1, 3 .. Length(num)-1 ]  do
        if 2 < Length(num[i])  then
            return false;
        elif 2 = Length(num[i])  then
            if ind = false  then
                ind := num[i][1];
            elif ind <> num[i][1]  then
                return false;
            fi;
        fi;
    od;
    return true;
end;


#############################################################################
##
#F  UnivariatenessTestRationalFunction(<f>)
##
InstallGlobalFunction(UnivariatenessTestRationalFunction,function(f)
local fam,notuniv,cannot,num,den,hasden,indn,col,val,i,j,nud,pos;
  fam:=FamilyObj(f);

  notuniv:=[false,fail,false,fail];  # answer if know to be not univariate
  cannot:=[fail,fail,fail,fail];     # answer if the test fails because
                                     # there is no multivariate GCD.

  # try to become a polynomial if possible. In particular we know the
  # denominator to be cancelled out if possible.
  if IsPolynomial(f) then
    num := ExtRepPolynomialRatFun(f);
    den:=[[],fam!.oneCoefficient];
  else
    num := ExtRepNumeratorRatFun(f);
    den := ExtRepDenominatorRatFun(f);
  fi;

  if Length(den[1])> 0 then
    # try a GCD cancellation
    i:=TryGcdCancelExtRepPolynomials(fam,num,den);
    if i<>fail then
      num:=i[1];
      den:=i[2];
    fi;

    #T: must do multivariate GCD (otherwise a `false' answer is not guaranteed)
  fi;
  hasden:=true;

  indn:=false; # the indeterminate number we want to get
  if Length(den)=2 and Length(den[1])=0 then
    if not IsOne(den[2]) then
      # take care of denominator so that we can throw it away afterwards.
      den:=den[2];
      num:=ShallowCopy(num);
      for i in [2,4..Length(num)] do
        num[i]:=num[i]/den;
      od;
    fi;
    hasden:=false;
    val:=0;

  elif Length(den)=2 then
    # this is the only case in which we can spot a laurent polynomial

    # We assume that the cancellation test will have dealt properly with
    # denominators which are monomials. So what we need here is only one
    # indeterminate, otherwise we must fail
    if Length(den[1])>2 then
      return notuniv;
    fi;

    indn:=den[1][1]; # this is the indeterminate number we need to have
    val:=-den[1][2];
    if not IsOne(den[2]) then
      # take care of denominator so that we can throw it away afterwards.
      den:=den[2];
      num:=ShallowCopy(num);
      for i in [2,4..Length(num)] do
        num[i]:=num[i]/den;
      od;
    fi;
    hasden:=false;
  fi;

  col:=[];
  nud:=1; # last position isto which we can assign without holes
  # now process the numerator
  for i in [2,4..Length(num)] do

    if Length(num[i-1])>0 then
      if indn=false then
	#set the indeterminate
	indn:=num[i-1][1];
      elif indn<>num[i-1][1] then
	# inconsistency:
	if hasden then
	  return cannot;
	else
	  return notuniv;
	fi;
      fi;
    fi;

    if Length(num[i-1])>2 then
      if hasden then
        return cannot;
      else
        return notuniv;
      fi;
    fi;

    # now we know the monomial to be [indn,exp]

    # set the coefficient
    if Length(num[i-1])=0 then
      # exp=0
      pos:=1;
    else
      pos:=num[i-1][2]+1;
    fi;

    # fill zeroes in the coefficient list
    for j in [nud..pos-1] do
      col[j]:=fam!.zeroCoefficient;
    od;

    col[pos]:=num[i];
    nud:=pos+1;
    

  od;

  if hasden then
    # because we have a special hook above for laurent polynomials, we
    # cannot be a laurent polynomial any longer.

    # now process the denominator
    for i in [2,4..Length(den)] do

      if Length(den[i-1])>0 then
	if indn=false then
	  #set the indeterminate
	  indn:=den[i-1][1];
	elif indn<>den[i-1][1] then
	  # inconsistency:
	  return cannot;
	fi;
      fi;

      if Length(den[i-1])>2 then
	return cannot;
      fi;

    od;

    # the indeterminate number must be set, we have a nonvanishing
    # denominator
    return [true,indn,false,fail];

  else
    # no denominator to deal with: We are univariate laurent

    # shift properly
    val:=val+RemoveOuterCoeffs(col,fam!.zeroCoefficient);

    if indn=false then
      indn:=1; #default value
    fi;

    return [true,indn,true,[col,val]];
  fi;

end );

#############################################################################
##
#M  IsUnivariateRationalFunction
##
##
InstallMethod( IsUnivariateRationalFunction,"ratfun", true,
  [ IsRationalFunction ], 0,
function(f)
local l;
  l:=UnivariatenessTestRationalFunction(f);
  if l[1]=fail then
    Error("cannot test univariateness without a proper multivariate GCD");
  fi;

  # note Laurent information
  if not HasIsLaurentPolynomial(f) then
    SetIsLaurentPolynomial(f,l[3]);
  fi;

  if l[1]=false then
    return false;
  fi;

  # note indeterminate number
  if not HasIndeterminateNumberOfUnivariateRationalFunction(f) then
    SetIndeterminateNumberOfUnivariateRationalFunction(f,l[2]);
  fi;

  # note Coefficients information
  if l[3]=true and not HasCoefficientsOfLaurentPolynomial(f) then
    SetCoefficientsOfLaurentPolynomial(f,l[4]);
  fi;

  return true;
end);

#############################################################################
##
#M  IsLaurentPolynomial
##
##
InstallMethod( IsLaurentPolynomial,"ratfun", true,
  [ IsRationalFunction ], 0,
function(f)
local l;
  l:=UnivariatenessTestRationalFunction(f);
  if l[1]=fail then
    Error("cannot test laurentness without a proper multivariate GCD");
  fi;

  # note Univariateness information
  if not HasIsUnivariateRationalFunction(f) then
    SetIsUnivariateRationalFunction(f,l[1]);
  fi;

  if l[3]=false then
    return false;
  fi;

  # note indeterminate number
  if not HasIndeterminateNumberOfUnivariateRationalFunction(f) then
    SetIndeterminateNumberOfUnivariateRationalFunction(f,l[2]);
  fi;

  # note Coefficients information
  if not HasCoefficientsOfLaurentPolynomial(f) then
    SetCoefficientsOfLaurentPolynomial(f,l[4]);
  fi;

  return true;
end);

#############################################################################
##
#M  IndeterminateNumberOfUnivariateRationalFunction
##
##
InstallMethod( IndeterminateNumberOfUnivariateRationalFunction,"ratfun", true,
  [ IsUnivariateRationalFunction ], 0,
function(f)
local l;
  l:=UnivariatenessTestRationalFunction(f);
  if l[1]=fail then
    Error(
      "cannot determine indeterminate # without a proper multivariate GCD");
  elif l[1]=false then
    Error("inconsistency!");
  fi;

  # note univariateness number
  if not HasIsUnivariateRationalFunction(f) then
    SetIsUnivariateRationalFunction(f,true);
  fi;

  # note Laurent information
  if not HasIsLaurentPolynomial(f) then
    SetIsLaurentPolynomial(f,l[3]);
  fi;

  # note Coefficients information
  if l[3]=true and not HasCoefficientsOfLaurentPolynomial(f) then
    SetCoefficientsOfLaurentPolynomial(f,l[4]);
  fi;

  return l[2];
end);


#############################################################################
##
#M  CoefficientsOfLaurentPolynomial( <rat-fun> )
##
InstallMethod( CoefficientsOfLaurentPolynomial,"ratfun",true,
    [ IsRationalFunction and IsLaurentPolynomial ], 0,
function(f)
local l;
  l:=UnivariatenessTestRationalFunction(f);
  if l[1]=fail then
    Error(
      "cannot determine coefficients without a proper multivariate GCD");
  elif l[3]=false then
    Error("inconsistency!");
  fi;

  # note univariateness number
  if not HasIsUnivariateRationalFunction(f) then
    SetIsUnivariateRationalFunction(f,true);
  fi;

  # note Laurent information
  if not HasIsLaurentPolynomial(f) then
    SetIsLaurentPolynomial(f,true);
  fi;

  return l[4];
end);

## now everything else will be installed based on properties and will use
# these basic functions as an interface.

#############################################################################
##
#M  NumeratorOfRationalFunction( <ratfun> )
##
InstallMethod( NumeratorOfRationalFunction,"call ExtRepNumerator",true,
  [ IsRationalFunction ],0,
function( f )
  return PolynomialByExtRep(FamilyObj(f),ExtRepNumeratorRatFun(f));
end );

#############################################################################
##
#M  DenominatorOfRationalFunction( <ratfun> )
##
InstallMethod( DenominatorOfRationalFunction,"call ExtRepDenominator",true,
  [ IsRationalFunction ],0,
function( f )
  return PolynomialByExtRep(FamilyObj(f),ExtRepDenominatorRatFun(f));
end );

#############################################################################
##
#M  AsPolynomial( <ratfun> )
##
InstallMethod( AsPolynomial,"call ExtRepPolynomial",true,
  [ IsRationalFunction and IsPolynomial],0,
function( f )
  return PolynomialByExtRep(FamilyObj(f),ExtRepPolynomialRatFun(f));
end );


#############################################################################
# 
# Functions for dealing with monomials 
# The monomials are represented as Zipped Lists. 
# i.e. sorted lists [i1,e1,i2, e2,...] where i1<i2<...are the indeterminates
# from smallest to largest
# AS 4/11/98
#
#############################################################################


#############################################################################
##
#F  MonomialTotalDegreeLess  . . . . . . total degree ordering for monomials
##
InstallGlobalFunction( MonomialTotalDegreeLess,
    function( u, v )
    local   lu, lv,      # length of u/v as a list
            len,         # difference in length of u/v as words
            i,           # loop variable
            lexico;      # flag for the lexicoghraphic ordering of u and v

    lu := Length(u); lv := Length(v);

    ##  Discard a common prefix in u and v and decide if u is
    ##  lexicographically smaller than v.
    i := 1; while i <= lu and i <= lv and u[i] = v[i] do
        i := i+1;
    od;

    if i > lu then  ## u is a prefix of v.
        return lu < lv;
    fi;
    if i > lv then  ## v is a prefix of u, but not equal to u.
        return false;
    fi;

    ##  Decide if u is lexicographically smaller than v.
    if i mod 2 = 1 then         ##  the indeterminates in u and v differ
        lexico := u[i] < v[i]; i := i+1;
    else                        ##  the exponents in u and v differ
        lexico := u[i] > v[i];
    fi;

    ##  Now compute the difference of the lengths
    len := 0; while i <= lu and i <= lv do
        len := len + u[i];
        len := len - v[i];
        i := i+2;
    od;
    ##  Only one of the following while loops will be executed.
    while i <= lu do len := len + u[i]; i := i+2; od;
    while i <= lv do len := len - v[i]; i := i+2; od;

    if len = 0 then return lexico; fi;

    return len < 0;
end );

#############################################################################
##
#F  MonomialRevLexicoLess(mon1,mon2) . . . .  reverse lexicographic ordering
##
InstallGlobalFunction( MonomialRevLexicoLess, function(m,n)
local x,y;
  # assume m and n are lexicographically sorted (otherwise we have to do
  # further work)
  x:=Length(m)-1;
  y:=Length(n)-1;

  while x>0 and y>0 do
    if m[x]>n[y] then
      return false;
    elif m[x]<n[y] then
      return true;
    # now m[x]=n[y]
    elif m[x+1]>n[y+1] then
      return false;
    elif m[x+1]<n[y+1] then
      return true;
    fi;
    # thus same coeffs, step down
    x:=x-2;
    y:=y-2;
  od;
  if x<=0 and y>0 then
    return true;
  else
    return false;
  fi;
end );

#############################################################################
##
##  Low level workhorse for operations with monomials in Zipped form
#M  ZippedSum( <z1>, <z2>, <czero>, <funcs> )
##
##  czero is the 0 of the coefficients ring
##  <funcs>[1] is the comparison function (usually \<)
##  <funcs>[2] is the addition operation (usu. \+ or \-)
##
InstallMethod( ZippedSum,
    true,
    [ IsList,
      IsList,
      IsObject,
      IsList ],
    0,
function( z1, z2, zero, f )
    local   sum,  i1,  i2,  i;

    sum := [];
    i1  := 1;
    i2  := 1;
    while i1 <= Length(z1) and i2 <= Length(z2)  do
        ##  are the two monomials equal ?
        if z1[i1] = z2[i2]  then
            ##  compute the sum of the coefficients
            i := f[2]( z1[i1+1], z2[i2+1] );
            if i <> zero  then
                ##  Add the term to the sum if the coefficient is not zero
                Add( sum, z1[i1] );
                Add( sum, i );
            fi;
            i1 := i1+2;
            i2 := i2+2;
        elif f[1]( z1[i1], z2[i2] )  then  ##  z1[i1] < z2[i2] ?
            ##  z1[i1] is the smaller of the two monomials and gets added to
            ##  the sum.  We have to apply the sum function to the
            ##  coefficient and zero.
            if z1[i1+1] <> zero  then
                Add( sum, z1[i1] );
                Add( sum, f[2]( z1[i1+1], zero ) );
            fi;
            i1 := i1+2;
        else
            ##  z1[i1] is the smaller of the two monomials
            if z2[i2+1] <> zero  then
                Add( sum, z2[i2] );
                Add( sum, f[2]( zero, z2[i2+1] ) );
            fi;
            i2 := i2+2;
        fi;
    od;
    ##  Now append the rest of the longer polynomial to the sum.  Note that
    ##  only one of the following loops is executed.
    for i  in [ i1, i1+2 .. Length(z1)-1 ]  do
        if z1[i+1] <> zero  then
            Add( sum, z1[i] );
            Add( sum, f[2]( z1[i+1], zero ) );
        fi;
    od;
    for i  in [ i2, i2+2 .. Length(z2)-1 ]  do
        if z2[i+1] <> zero  then
            Add( sum, z2[i] );
            Add( sum, f[2]( zero, z2[i+1] ) );
        fi;
    od;
    return sum;
end );

#############################################################################
##
#F  ZippedListProduct . . . . . . . . . . . . . . . .  multiply two monomials
##
ZippedListProduct := function( l, r )
    return ZippedSum( l, r, 0, [ \<, \+ ] );
end;

#############################################################################
##
#F  ZippedListQuotient  . . . . . . . . . . . .  divide a monomial by another
##
ZippedListQuotient := function( l, r )
  return ZippedSum( l, r, 0, [ \<, \- ] );
end;



#############################################################################
##
#M  ZippedProduct( <z1>, <z2>, <czero>, <funcs> )
##
##  Finds the product of the two polynomials in extrep form. 
##  Eg.  ZippedProduct([[1,2,2,3],2,[2,4],3],[[1,3,2,1],5],0,f);
##  gives [ [ 1, 3, 2, 5 ], 15, [ 1, 5, 2, 4 ], 10 ]
##  where
##  f :=[ ZippedListProduct,  MonomialTotalDegreeLess, \+, \* ]; 
##
InstallMethod( ZippedProduct,
    true,
    [ IsList,
      IsList,
      IsObject,
      IsList ],
    0,

function( z1, z2, zero, f )
    local   mons,  cofs,  i,  j,  c,  prd;

    # fold the product
    mons := [];
    cofs := [];
    for i  in [ 1, 3 .. Length(z1)-1 ]  do
        for j  in [ 1, 3 .. Length(z2)-1 ]  do
            ## product of the coefficients.
            c := f[4]( z1[i+1], z2[j+1] );
            if c <> zero  then
                ##  add the product of the monomials
                Add( mons, f[1]( z1[i], z2[j] ) );
                ##  and the coefficient
                Add( cofs, c );
            fi;
        od;
    od;

    # sort monomials
    SortParallel( mons, cofs, f[2] );

    # sum coeffs
    prd := [];
    i   := 1;
    while i <= Length(mons)  do
        c := cofs[i];
        while i < Length(mons) and mons[i] = mons[i+1]  do
            i := i+1;
            c := f[3]( c, cofs[i] );    ##  add coefficients
        od;
        if c <> zero  then
            ## add the term to the product
            Add( prd, mons[i] );
            Add( prd, c );
        fi;
        i := i+1;
    od;

    # and return the product
    return prd;

end );


# Function to create the rational functions family and store the 
# default types

#############################################################################
##
#M  RationalFunctionsFamily( <fam> )
##
InstallMethod( RationalFunctionsFamily,
    true,
    [ IsUFDFamily ],
    1,

function( efam )
    local   fam;

    # create a new family in the category <IsRationalFunctionsFamily>
    fam := NewFamily(
      "RationalFunctionsFamily(...)",
      IsRationalFunction and IsRationalFunctionsFamilyElement,
      IsObject,
      IsUFDFamily and IsRationalFunctionsFamily );

		
    # default type for rational functions
      fam!.defaultRatFunType := NewType( fam,
	      IsRationalFunctionDefaultRep and
	      HasExtRepNumeratorRatFun and HasExtRepDenominatorRatFun);


    # default type for polynomials
      fam!.defaultPolynomialType := NewType( fam,
	      IsPolynomial and IsPolynomialDefaultRep and
	      HasExtRepPolynomialRatFun);


    # default type for univariate laurent polynomials
    fam!.threeLaurentPolynomialTypes := 
      [ NewType( fam,
	    IsLaurentPolynomial
	    and IsLaurentPolynomialDefaultRep and
	    HasIndeterminateNumberOfLaurentPolynomial and
	    HasCoefficientsOfLaurentPolynomial), 

	    NewType( fam,
	      IsLaurentPolynomial
	      and IsLaurentPolynomialDefaultRep and
	      HasIndeterminateNumberOfLaurentPolynomial and
	      HasCoefficientsOfLaurentPolynomial and
	      IsConstantRationalFunction and IsUnivariatePolynomial),

	    NewType( fam,
	      IsLaurentPolynomial and IsLaurentPolynomialDefaultRep and
	      HasIndeterminateNumberOfLaurentPolynomial and
	      HasCoefficientsOfLaurentPolynomial and
	      IsUnivariatePolynomial)];

    # functions to add zipped lists
    fam!.zippedSum := [ MonomialTotalDegreeLess, \+ ];

    # functions to multiply zipped lists
    fam!.zippedProduct := [ ZippedListProduct,
                            MonomialTotalDegreeLess, \+, \* ];

    # set the one and zero coefficient
    fam!.zeroCoefficient := Zero(efam);
    fam!.oneCoefficient  := One(efam);

    # set the coefficients
    SetCoefficientsFamily( fam, efam );

    # Set the characteristic.
    if HasCharacteristic( efam ) then
      SetCharacteristic( fam, Characteristic( efam ) );
    fi;


    # and set one and zero
    SetZero( fam, PolynomialByExtRep(fam,[]));
    SetOne( fam, PolynomialByExtRep(fam,[[],fam!.oneCoefficient]));

    # we will store separate `one's for univariate polynomials. This will
    # allow to keep univariate calculations in this one indeterminate.
    fam!.univariateOnePolynomials:=[];
    fam!.univariateZeroPolynomials:=[];

    # assign a names list
    fam!.namesIndets := [];

    # and return
    return fam;

end );

# this method is only to get a resonable error message in case the ring does
# not know to be a UFD.
InstallOtherMethod( RationalFunctionsFamily,"not UFD ring", true,
    [ IsObject ],
    0,
function(obj)
  Error("You can only create rational functions over a UFD");
end);


#############################################################################
##
#F  ExtRepOfPolynomial_PrintObj( <fam>, <ext> )
##
ExtRepOfPolynomial_PrintObj := function(fam, ext )
local   zero,  one,   i,  d,  c,  j,ind;

    # zero := ext[1];
    zero :=  fam!.zeroCoefficient;
    one  := fam!.oneCoefficient;
    # ext  := ext[2];
    if Length(ext)=0 then
      Print(zero);
    fi; 
    for i  in [ 1, 3 .. Length(ext)-1 ]  do
      if not IsZero(ext[i+1]) then
        if 1 < i  then
          Print("+");
        fi;
        c := "*";
        if ext[i+1] = one and 0 < Length(ext[i])  then
            c := "";
	else
	  Print(ext[i+1]);
        fi;
        if 0 < Length(ext[i])  then
            Print(c); 
            for j  in [ 1, 3 .. Length(ext[i])-1 ]  do
                if 1 < j  then
		  Print( "*" );
                fi;
		ind:=ext[i][j];
		if HasIndeterminateName(fam,ind) then
                    Print(IndeterminateName(fam,ind));
                else
                    Print("x_",ind);
		fi;
                if 1 <> ext[i][j+1]  then
		  Print("^", ext[i][j+1] );
                fi;
            od;
        fi;
      fi;
    od;

end;



#############################################################################
##
#M  PrintObj( <rat-fun> )
##
##  This method is installed for all  rational function.
##
InstallMethod( PrintObj,"rational function", true, [ IsRationalFunction ], 0,
function( obj ) local   fam;
  fam := FamilyObj(obj);
  Print( "(" );
    ExtRepOfPolynomial_PrintObj(fam, ExtRepNumeratorRatFun(obj));
  Print( ")" );
  Print( "/" );
  Print( "(" );
  ExtRepOfPolynomial_PrintObj(fam, ExtRepDenominatorRatFun(obj));
  Print( ")" );
end );

InstallMethod( PrintObj,"polynomial", true, [ IsPolynomial ], 0,
function( obj ) local   fam;
  ExtRepOfPolynomial_PrintObj(FamilyObj(obj),ExtRepPolynomialRatFun(obj));
end );


#############################################################################
##
#M  OneOp( <rat-fun> )
##
InstallMethod( OneOp, "defer to family", true,
    [ IsRationalFunction ], 0,
function(obj)
  return One(FamilyObj(obj));
end);

#############################################################################
##
#M  ZeroOp( <rat-fun> )
##
InstallMethod( ZeroOp, "defer to family", true,
    [ IsRationalFunction ], 0,
function(obj)
  return Zero(FamilyObj(obj));
end);

# Arithmetic (only for rational functions and polynomials, everything
# particularly unvariate will be in ratfunul.gi)

#############################################################################
##
#M  AdditiveInverse( <rat-fun> )
##
##
InstallMethod( AdditiveInverseOp,"rational function", true,
    [ IsRationalFunction ], 0,
function( obj )
    local   fam,  i, newnum;

    fam := FamilyObj(obj);
    newnum := ShallowCopy(ExtRepNumeratorRatFun(obj));
    for i  in [ 2, 4 .. Length(newnum) ]  do
        newnum[i] := -newnum[i];
    od;
    return RationalFunctionByExtRep(fam,newnum,ExtRepDenominatorRatFun(obj));
end );

InstallMethod( AdditiveInverseOp,"polynomial", true,
    [ IsPolynomial ], 0,
function( obj )
    local   fam,  i, newnum;

    fam := FamilyObj(obj);
    newnum := ShallowCopy(ExtRepNumeratorRatFun(obj));
    for i  in [ 2, 4 .. Length(newnum) ]  do
        newnum[i] := -newnum[i];
    od;
    return PolynomialByExtRep(fam,newnum);
end );

#############################################################################
##
#M  Inverse( <rat-fun> )
##
##  This exhibits the use of RationalFunctionByPolynomials to do cancellation
##  and special cases which give rise to more specific types of rational fns.
##  RationalFunctionByExtRep does no checking whatever. 
##
InstallMethod( InverseOp, "rational function", true,
    [ IsRationalFunctionsFamilyElement ], 0,
function( obj )
local   num;

    # get the family and check the zeros
    num := ExtRepNumeratorRatFun(obj);
    if Length(num)=0 then
      Error("division by zero");
    fi;

    return RationalFunctionByExtRep(FamilyObj(obj),
      ExtRepDenominatorRatFun(obj) , num);
end );

#############################################################################
##
#M  <polynomial> + <polynomial>
##
##
InstallMethod( \+, "polynomial + polynomial", IsIdenticalObj,
    [ IsPolynomial, IsPolynomial ], 0,
function( left, right )
local   fam,  i, extleft, extright;

  if IsZero(right) then
    return left;
  elif IsZero(left) then
    return right;
  fi;

  fam   := FamilyObj(left);

  return PolynomialByExtRep(fam, 
	  ZippedSum(ExtRepPolynomialRatFun(left),
                    ExtRepPolynomialRatFun(right),
	            fam!.zeroCoefficient, fam!.zippedSum));
end );

#############################################################################
##
#M  <polynomial> * <polynomial>
##
##  We assume that if we have a polynomial
##  then ExtRepPolynomialRatFun will work. 
##
InstallMethod( \*, "polynomial * polynomial", IsIdenticalObj,
    [ IsPolynomial, IsPolynomial ], 0,
function( left, right )
local   fam;

  if IsZero(left) then
    return left;
  elif IsZero(right) then
    return right;
  elif HasIsOne(left) and IsOne(left) then
    return right;
  elif HasIsOne(right) and IsOne(right) then
    return left;
  fi;

  # get the family and check the zeros
  fam   := FamilyObj(left);

  return PolynomialByExtRep(fam, ZippedProduct(
	    ExtRepPolynomialRatFun(left),
	    ExtRepPolynomialRatFun(right),
	    fam!.zeroCoefficient, fam!.zippedProduct));

end);

#############################################################################
##
#M  <rat-fun>     = <rat-fun>
##
##  This method is  installed for all  rational functions.
##
##  Relies on Zipped multiplication ... a/b = c/d <=> ac = bd.
##  This way we do not need any GCD
##
InstallMethod( \=,"rational functions", IsIdenticalObj,
    [ IsRationalFunction, IsRationalFunction ], 0,
function( left, right )
local   fam,  leftnum, leftden, rightnum, rightden, p1, p2, czero;

  # get the family and check the zeros
  fam   := FamilyObj(left);
  leftden  := ExtRepDenominatorRatFun(left);
  rightnum := ExtRepNumeratorRatFun(right);

  p1 := ZippedProduct(ExtRepNumeratorRatFun(left),
		      ExtRepDenominatorRatFun(right),
		      fam!.zeroCoefficient,fam!.zippedProduct);

  p2 := ZippedProduct(ExtRepNumeratorRatFun(right),
		      ExtRepDenominatorRatFun(left),
		      fam!.zeroCoefficient,fam!.zippedProduct);

  return p1 = p2;
end);

InstallMethod( \=,"polynomial", IsIdenticalObj,
    [ IsPolynomial, IsPolynomial ], 0,
function( left, right )
  return ExtRepPolynomialRatFun(left)=ExtRepPolynomialRatFun(right);
end);

#############################################################################
##
#M  <ratfun> < <ratfun>
##
InstallMethod(\<,"rational functions",IsIdenticalObj,
  [IsRationalFunction,IsRationalFunction],0,
function(left,right)
local a,b,fam,i, j;
  if HasIsPolynomial(left) and IsPolynomial(left)
     and HasIsPolynomial(right) and IsPolynomial(right) then
    a:=ExtRepPolynomialRatFun(left);
    b:=ExtRepPolynomialRatFun(right);
  else
    fam:=FamilyObj(a);
    a := ZippedProduct(ExtRepNumeratorRatFun(left),
			ExtRepDenominatorRatFun(right),
			fam!.zeroCoefficient,fam!.zippedProduct);

    b := ZippedProduct(ExtRepNumeratorRatFun(right),
			ExtRepDenominatorRatFun(left),
			fam!.zeroCoefficient,fam!.zippedProduct);
  fi;

  i:=Length(a)-1;
  j:=Length(b)-1;
  while i>0 and j>0 do
    # compare the last monomials
    if a[i]=b[j] then
      # the monomials are the same, compare the coefficients
      if a[i+1]=b[j+1] then
        # the coefficients are also the same. Must continue
        i:=i-2;
        j:=j-2;
      else
        # let the coefficients decide
        return a[i+1]<b[j+1];
      fi;
    elif MonomialTotalDegreeLess(a[i],b[j]) then
      # a is strictly smaller
      return true;
    else
      # a is strictly larger
      return false;
    fi;
  od;
  # is there an a-remainder (then a is larger)
  # or are both polynomials equal?
  if i>0 or i=j then
    return false;
  else
    return true;
  fi;
end);

#############################################################################
##
#M  <coeff>  * <rat-fun>
##
##
InstallGlobalFunction(ProdCoefRatfun,
function( coef, ratfun)
local   fam,  i, extnum,pol;

  if IsZero(coef) then
    return Zero(ratfun);
  fi;

  if IsOne(coef) then
    return ratfun;
  fi;

  fam   := FamilyObj(ratfun);

  pol:=HasIsPolynomial(ratfun) and IsPolynomial(ratfun);

  if pol then
    extnum := ShallowCopy(ExtRepPolynomialRatFun(ratfun));
  else
    extnum := ShallowCopy(ExtRepNumeratorRatFun(ratfun));
  fi;

  for i  in [ 2, 4 .. Length(extnum) ]  do
    extnum[i] := coef * extnum[i];
  od;

  # We can do this because a/b is cancelled <=> c*a/b is cancelled
  # where c is a constant.
  if pol then
    return PolynomialByExtRep( fam, extnum);
  else
    return RationalFunctionByExtRep( fam, extnum, 
	  ExtRepDenominatorRatFun(ratfun));
  fi;

end);



#############################################################################
##
#M  <coeff>       * <rat-fun>
##
##
InstallMethod( \*, "coeff * rat-fun", IsCoeffsElms,
    [ IsRingElement, IsRationalFunction ],
    3, # so we dont call  positive integer * additive element
function(c, r)
  return ProdCoefRatfun(c,r);
end);
		
#############################################################################
##
#M  <rat-fun>     * <coeff>
##
##
InstallMethod( \*, "rat-fun * coeff", IsElmsCoeffs,
    [ IsRationalFunction, IsRingElement ],
    3, # so we dont call  positive integer * additive element
function(r, c)
  return ProdCoefRatfun(c,r);
end);

#############################################################################
##
#M  <polynomial>     + <coeff>
##
##
InstallGlobalFunction(SumCoefPolynomial,
function( cf, rf )
local   fam,  i, extrf;

  if IsZero(cf) then
    return rf;
  fi;

  fam   := FamilyObj(rf);
  extrf  := ExtRepPolynomialRatFun(rf);
  # assume the constant term is in the first position
  if Length(extrf)>0 and Length(extrf[1])=0 then
    if extrf[2]=-cf then
      extrf:=extrf{[3..Length(extrf)]};
    else
      extrf:=ShallowCopy(extrf);
      extrf[2]:=extrf[2]+cf;
    fi;
  else
    extrf:=Concatenation([[],cf],extrf);
  fi;

  return PolynomialByExtRep(fam,extrf);

end );

InstallMethod( \+, "polynomial + coeff", IsElmsCoeffs,
    [ IsPolynomial, IsRingElement ], 0,
function( left, right )
  return SumCoefPolynomial(right, left);
end );

InstallMethod( \+, "coeff + polynomial ", IsCoeffsElms,
    [ IsRingElement, IsPolynomial], 0,
function( left, right )
  return SumCoefPolynomial(left, right);
end);

InstallGlobalFunction( QuotientPolynomialsExtRep,
function(fam, p, q )
local   zero,  quot, lcq,  lmq,  mon,  i, coeff;

  if Length(q)=0 then
    return fail; #safeguard
  fi;

  quot := [];

  lcq := q[Length(q)];
  lmq := q[Length(q)-1];

  p:=ShallowCopy(p);
  while Length(p)>0 do
    ##  divide the leading monomial of q by the leading monomial of p
    mon  := ZippedListQuotient( p[Length(p)-1], lmq );

      ##  check if mon has negative exponents
      for i in [2,4..Length(mon)] do
	  if mon[i] < 0 then return fail; fi;
      od;

      ##  now add the quotient of the coefficients
      coeff := p[Length(p)] / lcq;

      ##  Add coeff, mon to quot, the result is sorted in reversed order.
      Add( quot,  coeff );
      Add( quot,  mon );

      ## p := p - mon * q;
      #  compute -q*mon;
      mon  := ZippedProduct(q,[mon,-coeff],
        fam!.zeroCoefficient,fam!.zippedProduct);
  
      # add it to p
      p:=ZippedSum(p,mon,fam!.zeroCoefficient,fam!.zippedSum);
  od;

  quot := Reversed(quot);
  return quot;
end );

#############################################################################
##
#F  SpecializedExtRepPol(<fam>,<ext>,<ind>,<val>)
##
InstallGlobalFunction(SpecializedExtRepPol,function(fam,ext,ind,val)
local e,i,p,m,c;
  e:=[];
  for i in [1,3..Length(ext)-1] do
    # is the indeterminate used in the monomial
    p:=PositionProperty([1,3..Length(ext[i])-1],j->ext[i][j]=ind);
    if p=fail then
      m:=ext[i];
      c:=ext[i+1];
    else
      # yes, compute changed monomial and coefficient
      p:=2*p-1; #actual position 1,3..
      m:=ext[i]{Concatenation([1..p-1],[p+2..Length(ext[i])])};
      c:=ext[i+1]*val^ext[i][p+1];
    fi;
    e:=ZippedSum(e,[m,c],fam!.zeroCoefficient,fam!.zippedSum);
  od;
  return e;
end);

InstallMethod(HeuristicCancelPolynomialsExtRep,"ignore",true,
  [IsRationalFunctionsFamily,IsList,IsList],
  # fallback: lower than default for the weakest conditions
  -1,
function(f,a,b)
  return fail; # can't do anything
end);

InstallGlobalFunction(TryGcdCancelExtRepPolynomials,function(fam,num,den)
local q,p,e,i,j,cnt;
  q:=QuotientPolynomialsExtRep(fam,num,den);
  if q<>fail then
    # true quotient
    return [q,[[],fam!.oneCoefficient]];
  fi;
  
  q:=HeuristicCancelPolynomialsExtRep(fam,num,den);
  if IsList(q) then
    # we got something
    num:=q[1];
    den:=q[2];
  fi;

  # special treatment if the denominator is a monomial
  if Length(den)=2 then
    # is the denominator a constant?
    if Length(den[1])>0 then
      q:=den[1];
      e:=q{[2,4..Length(q)]}; # the indeterminants exponents
      q:=q{[1,3..Length(q)-1]}; # the indeterminant occuring
      IsSSortedList(q);
      i:=1;
      while i<Length(num) and ForAny(e,j->j>0) do
	cnt:=0; # how many indeterminants did we find
	for j in [1,3..Length(num[i])-1] do
	  p:=Position(q,num[i][j]); # uses PositionSorted
	  if p<>fail then
	    cnt:=cnt+1; # found one
	    e[p]:=Minimum(e[p],num[i][j+1]); # gcd via exponents
	  fi;
	od;
	if cnt<Length(e) then
	  e:=[0,0]; # not all indets found: cannot cancel!
	fi;
        i:=i+2;
      od;
      if ForAny(e,j->j>0) then
	Info(InfoPoly,3,"common monomial ",e);
        # found a common monomial
	num:=ShallowCopy(num);
	for i in [1,3..Length(num)-1] do
	  num[i]:=ShallowCopy(num[i]);
	  for j in [1,3..Length(num[i])-1] do
	    p:=Position(q,num[i][j]); # uses PositionSorted
	    num[i][j+1]:=num[i][j+1]-e[p]; #reduce
	  od;
	od;

	p:=ShallowCopy(den[1]);
	i:=[2,4..Length(p)];
	p{i}:=p{i}-e; # reduce exponents
	den:=[p,den[2]]; #new denominator
      fi;
    fi;
    # remove the denominator coefficient
    if not IsOne(den[2]) then
      num:=ShallowCopy(num);
      for i in [2,4..Length(num)] do
	num[i]:=num[i]/den[2];
      od;
      den:=[den[1],fam!.oneCoefficient];
    fi;
  fi;

  return [num,den];
end);

InstallGlobalFunction(RationalFunctionByExtRepWithCancellation,
function(fam,num,den)
local t;
  t:=TryGcdCancelExtRepPolynomials(fam,num,den);
  if Length(t[2])=2 and Length(t[2][1])=0 and IsOne(t[2][2]) then
    return PolynomialByExtRep(fam,t[1]);
  else
    return RationalFunctionByExtRep(fam,t[1],t[2]);
  fi;
end);

#############################################################################
##
#M  <rat-fun>     * <rat-fun>
##
InstallMethod( \*, "rat-fun * rat-fun", IsIdenticalObj,
    [ IsRationalFunction, IsRationalFunction ], 0,
function( left, right )
local fam,num,den;

  fam:=FamilyObj(left);
  if HasIsPolynomial(left) and IsPolynomial(left) then
    num:=ZippedProduct(ExtRepPolynomialRatFun(left),
		      ExtRepNumeratorRatFun(right),
		      fam!.zeroCoefficient,fam!.zippedProduct);
    den:=ExtRepDenominatorRatFun(right);
  elif HasIsPolynomial(right) and IsPolynomial(right) then
    num:=ZippedProduct(ExtRepPolynomialRatFun(right),
		      ExtRepNumeratorRatFun(left),
		      fam!.zeroCoefficient,fam!.zippedProduct);
    den:=ExtRepDenominatorRatFun(left);
  else
    num:=ZippedProduct(ExtRepNumeratorRatFun(left),
		      ExtRepNumeratorRatFun(right),
		      fam!.zeroCoefficient,fam!.zippedProduct);
    den:=ZippedProduct(ExtRepDenominatorRatFun(left),
		      ExtRepDenominatorRatFun(right),
		      fam!.zeroCoefficient,fam!.zippedProduct);
  fi;

  return RationalFunctionByExtRepWithCancellation(fam,num,den);
end);

#############################################################################
##
#M  Quotient  . . . . . . . . . . . . . . . . .  for multivariate polynomials
##
InstallMethod( Quotient,"multivar with ring",IsCollsElmsElms,
        [ IsPolynomialRing, IsPolynomial, IsPolynomial ], 0,
function( ring, p, q )
    return Quotient( p, q );
end );

InstallOtherMethod( Quotient,"multivar",IsIdenticalObj,
        [ IsPolynomial, IsPolynomial ], 0,
function( p, q )
  q:=QuotientPolynomialsExtRep(FamilyObj(p),ExtRepPolynomialRatFun(p),
                                            ExtRepPolynomialRatFun(q));
  if q<>fail then
    q:=PolynomialByExtRep(FamilyObj(p),q);
  fi;
  return q;
end );

#############################################################################
##
#M  <rat-fun> + <rat-fun>
##
InstallMethod( \+, "rat-fun + rat-fun", IsIdenticalObj,
    [ IsRationalFunction, IsRationalFunction ], 0,
function( left, right )
local fam,num,den,lnum,rnum,lden,rden,q;

  fam:=FamilyObj(left);
  if HasIsPolynomial(left) and IsPolynomial(left) then
    den:=ExtRepDenominatorRatFun(right);
    num:=ZippedProduct(ExtRepPolynomialRatFun(left),den,
		      fam!.zeroCoefficient,fam!.zippedProduct);
    num:=ZippedSum(num,ExtRepNumeratorRatFun(right),
		      fam!.zeroCoefficient,fam!.zippedSum);
  elif HasIsPolynomial(right) and IsPolynomial(right) then
    den:=ExtRepDenominatorRatFun(left);
    num:=ZippedProduct(ExtRepPolynomialRatFun(right),den,
		      fam!.zeroCoefficient,fam!.zippedProduct);
    num:=ZippedSum(num,ExtRepNumeratorRatFun(left),
		      fam!.zeroCoefficient,fam!.zippedSum);

  else
    lnum:=ExtRepNumeratorRatFun(left);
    rnum:=ExtRepNumeratorRatFun(right);
    lden:=ExtRepDenominatorRatFun(left);
    rden:=ExtRepDenominatorRatFun(right);

    if lden=rden then
      # same denominator: add numerators
      den:=lden;
      num:=ZippedSum(lnum,rnum,fam!.zeroCoefficient,fam!.zippedSum);
    else
      q:=QuotientPolynomialsExtRep(fam,lden,rden);
      if q<>fail then
	# left den. is a multiple of right den.
	den:=lden;
	num:=ZippedProduct(rnum,q,fam!.zeroCoefficient,fam!.zippedProduct);
	num:=ZippedSum(num,lnum,fam!.zeroCoefficient,fam!.zippedSum);
	else
	q:=QuotientPolynomialsExtRep(fam,rden,lden);
	if q<>fail then
	  # left den. is a multiple of right den.
	  den:=rden;
	  num:=ZippedProduct(lnum,q,fam!.zeroCoefficient,fam!.zippedProduct);
	  num:=ZippedSum(num,rnum,fam!.zeroCoefficient,fam!.zippedSum);
	else
	  #TODO: GCD of denominators

	  #worst case
	  num:=ZippedSum(ZippedProduct(lnum,rden,
			    fam!.zeroCoefficient,fam!.zippedProduct),
			  ZippedProduct(lnum,rden,
			    fam!.zeroCoefficient,fam!.zippedProduct),
			  fam!.zeroCoefficient,fam!.zippedSum);

	  den:=ZippedProduct(ExtRepDenominatorRatFun(left),
			      ExtRepDenominatorRatFun(right),
			      fam!.zeroCoefficient,fam!.zippedProduct);

        fi;
      fi;
    fi;
  fi;

  return RationalFunctionByExtRepWithCancellation(fam,num,den);

end);

#############################################################################
##
#M  <ratfun>  + <coeff>
##
##
InstallGlobalFunction(SumCoefRatfun,
function( cf, rf )
local   fam,  i, num,den;

  if IsZero(cf) then
    return rf;
  fi;

  fam   := FamilyObj(rf);
  den:=ExtRepDenominatorRatFun(rf);

  # multiply coefficient with denominator to let numerator summand
  num:=ShallowCopy(den);
  for i in [2,4..Length(num)] do
    num[i]:=num[i]*cf;
  od;

  num:=ZippedSum(num,ExtRepNumeratorRatFun(rf),
                 fam!.zeroCoefficient,fam!.zippedSum);

  return RationalFunctionByExtRepWithCancellation(fam,num,den);

end );

InstallMethod( \+, "ratfun + coeff", IsElmsCoeffs,
    [ IsRationalFunction, IsRingElement ], 0,
function( left, right )
  return SumCoefRatfun(right, left);
end );

InstallMethod( \+, "coeff + ratfun ", IsCoeffsElms,
    [ IsRingElement, IsRationalFunction], 0,
function( left, right )
  return SumCoefRatfun(left, right);
end);

#############################################################################
##
#M  DegreeIndeterminate( pol, ind )  degree in indeterminate number ind
##   #W!  fctn. will err if we take polynomial rings over polynomial rings
##
InstallMethod(DegreeIndeterminate,"pol,indetnr",true,
  [IsPolynomial,IsPosInt],0,
function(pol,ind)
local e,d,i,j;
  e:=ExtRepPolynomialRatFun(pol);
  e:=Filtered(e,IsList);
  d:=0; #the maximum degree so far
  for i in e do
    j:=1;
    while j<Length(i) do # searching the monomial
      if i[j]=ind then
        if i[j+1]>d then
          d:=i[j+1];
        fi;
        j:=Length(i);
      fi;
      j:=j+2;
    od;
  od;
  return d;
end);

InstallOtherMethod(DegreeIndeterminate,"pol,indet",IsIdenticalObj,
  [IsPolynomial,IsLaurentPolynomial],0,
function(pol,ind)
  return DegreeIndeterminate(pol,
           IndeterminateNumberOfLaurentPolynomial(ind));
end);

#############################################################################
##
#M  GcdOp( <pring>, <upol>, <upol> )  
##  for general rational functions in the hope that we can find them to be
##  polynomials or even univariate polynomials. We install further calls as 
##  the methods are implemented.
##  
##
InstallMethod( GcdOp,"Gcd(Polyring, Pol,Pol)",
    IsCollsElmsElms,[IsEuclideanRing,
                IsRationalFunction,IsRationalFunction],0,
function(R,f,g)
local gcd,u,v,w,val,brci;

	if IsUnivariatePolynomial(f) and IsUnivariatePolynomial(g) 
		and IndeterminateNumberOfUnivariateRationalFunction(f) = 
		IndeterminateNumberOfUnivariateRationalFunction(g) then
		return GcdOp(R,f,g);
	fi;

	return fail;
end);

#############################################################################
##
#M  Value
##                               
InstallOtherMethod(Value,"multivariate polynomial, with one",
  true,[IsPolynomial,IsList,IsList,IsRingElement],0,
function(pol,inds,vals,one)
local f,i,j,v,c,m,p,fam,ivals;

  if Length(inds)<>Length(vals) then
    Error("wrong number of values");
  fi;

  # convert indeterminates to numbers
  for i in [1..Length(inds)] do
    if not IsPosInt(inds[i]) then
      inds[i]:=IndeterminateNumberOfUnivariateRationalFunction(inds[i]);
    fi;
  od;

  inds:=ShallowCopy(inds);
  ivals:=[]; # values according to index

  f:=ExtRepPolynomialRatFun(pol);
  fam:=CoefficientsFamily(FamilyObj(pol));
  i:=1;
  v:=Zero(fam)*one;
  while i<=Length(f) do
    c:=f[i];
    m:=one;
    j:=1;
    while j<=Length(c) do
      if not IsBound(ivals[c[j]]) then
        p:=Position(inds,c[j]);
	if p<>fail then
	  ivals[c[j]]:=vals[p];
	else
	  ivals[c[j]]:=UnivariatePolynomialByCoefficients(
	             fam,[Zero(fam),One(fam)],c[j]);
	fi;
      fi;
      m:=m*(ivals[c[j]]*one)^c[j+1];
      j:=j+2;
    od;
    v:=v+f[i+1]*m;
    i:=i+2;
  od;
  return v;
end );

RedispatchOnCondition(Value,true,[IsRationalFunction,IsList,IsList],
  [IsPolynomial,IsList,IsList],0);

InstallMethod(Value,"multivariate polynomial",
  true,[IsPolynomial,IsList,IsList],0,
function(pol,inds,vals)
  return Value(pol,inds,vals,One(CoefficientsFamily(FamilyObj(pol))));
end);

#############################################################################
##
#F  LeadingMonomial . . . . . . . . . . . . . .  for multivariate polynomials
##
InstallMethod( LeadingMonomial, "multivariate polynomials wrt total degree",
        true, [ IsPolynomial  ], 0,
function( pol )

  pol:=ExtRepPolynomialRatFun(pol);
  if Length( pol) = 0 then
      return [];
  fi;
  return pol[ Length(pol) - 1 ];

end );

#############################################################################
##
#F  LeadingCoefficient  . . . . . . . . . . . .  for multivariate polynomials
##
InstallMethod( LeadingCoefficient,"multivariate polynomials wrt total degree",
        true, [ IsPolynomial and IsPolynomialDefaultRep ], 0,
function( pol )
local e;
  e:=ExtRepPolynomialRatFun(pol);
  if Length(e)=0 then
    return FamilyObj(pol)!.zeroCoefficient;
  fi;
  return e[Length(e)];
end );

#############################################################################
##
#F  LeadingCoefficient( pol, ind )  of (multivariate) pol considered as
##         univariate pol in indeterminate # ind with polynomial coeffs.
##
InstallOtherMethod(LeadingCoefficient,"multivariate",true,
  [IsPolynomial,IsPosInt],0,
function(pol,ind)
local c,e,d,i,p;
  e:=ExtRepPolynomialRatFun(pol);

  d:=0;
  c:=[];
  for i in [1,3..Length(e)-1] do
    # test whether the indeterminate does occur
    p:=PositionProperty([1,3..Length(e[i])-1],j->e[i][j]=ind);
    if p<>fail then
      p:=p*2-1; # from indext in [1,3..] to number
      if e[i][p+1]>d then
	d:=e[i][p+1]; # new, higher degree
	c:=[]; # start anew
      fi;
      if e[i][p+1]=d then
	# remaining monomial with coefficient
	Append(c,[e[i]{Difference([1..Length(e[i])],[p,p+1])},e[i+1]]);
      fi;
    fi;
  od;
  return PolynomialByExtRep(FamilyObj(pol),c);
end);


#############################################################################
##
#M  PolynomialCoefficientsOfPolynomial(<pol>,<ind>)
##
InstallMethod(PolynomialCoefficientsOfPolynomial,"polynomial,integer",true,
  [IsRationalFunction and IsPolynomial,IsPosInt],0,
function(pol,ind)
local e,c,i,j,m,ex;
  e:=ExtRepPolynomialRatFun(pol);
  c:=[];
  for i in [1,3..Length(e)-1] do
    m:=e[i];
    j:=1;
    while j<=Length(m) and m[j]<>ind do
      j:=j+2;
    od;
    if j<Length(m) then
      ex:=m[j+1]+1;
      m:=m{Concatenation([1..j-1],[j+2..Length(m)])};
    else
      ex:=1;
    fi;
    if not IsBound(c[ex]) then
      c[ex]:=[];
    fi;
    Add(c[ex],m);
    Add(c[ex],e[i+1]);
  od;
  pol:=FamilyObj(pol);
  for i in [1..Length(c)] do
    if not IsBound(c[i]) then
      c[i]:=Zero(pol);
    else
      c[i]:=PolynomialByExtRep(pol,c[i]);
    fi;
  od;
  return c;
end);

InstallOtherMethod(PolynomialCoefficientsOfPolynomial,"polynomial,indet",
  IsIdenticalObj,
  [IsRationalFunction and IsPolynomial,IsRationalFunction and IsPolynomial],0,
function(pol,ind)
  return PolynomialCoefficientsOfPolynomial(pol,
           IndeterminateNumberOfLaurentPolynomial(ind));
end);



#############################################################################
##
#M  Discriminant(<pol>,<ind>)
##
InstallOtherMethod(Discriminant,"poly,inum",true,
  [IsRationalFunction and IsPolynomial,IsPosInt],0,
function(f,ind)
local d;
  d:=DegreeIndeterminate(f,ind);
  return (-1)^(d*(d-1)/2)*Resultant(f,Derivative(f,ind),ind)/
                           LeadingCoefficient(f,ind);
end);

InstallOtherMethod(Discriminant,"poly,ind",true,
  [IsRationalFunction and IsPolynomial,IsRationalFunction and IsPolynomial],0,
function(pol,ind)
  return Discriminant(pol,IndeterminateNumberOfLaurentPolynomial(ind));
end);

#############################################################################
##
#M  Derivative(<pol>,<ind>)
##
# (this way around because we need the indeterminate
InstallOtherMethod(Derivative,"poly,inum",true,
  [IsRationalFunction and IsPolynomial,IsPosInt],0,
function(pol,ind)
local fam;
  fam:=CoefficientsFamily(FamilyObj(pol));
  return Derivative(pol,UnivariatePolynomialByCoefficients(fam,
		          [Zero(fam),One(fam)],ind));
end);

InstallOtherMethod(Derivative,"poly,ind",true,
  [IsRationalFunction and IsPolynomial,IsRationalFunction and IsPolynomial],0,
function(pol,ind)
local d,c,i;
  d:=Zero(pol);
  c:=PolynomialCoefficientsOfPolynomial(pol,ind);
  for i in [2..Length(c)] do
    d := d + (i-1) * c[i] * ind^(i-2);
  od;
  return d;
end);

InstallGlobalFunction(OnIndeterminates,function(p,g)
local e,f,i,j,l,ll;
  if IsPolynomial(p) then
    e:=[ExtRepPolynomialRatFun(p)];
  else
    e:=[ExtRepNumeratorRatFun(p),ExtRepDenominatorRatFun(p)];
  fi;

  f:=[];
  for i in [1..Length(e)] do
    l:=[];
    for j in [1,3..Length(e[i])-1] do
      ll:=List([1,3..Length(e[i][j])-1],k->[e[i][j][k]^g,e[i][j][k+1]]);
      Sort(ll);
      Add(l,[Concatenation(ll),e[i][j+1]]);
    od;
    Sort(l);
    f[i]:=Concatenation(l);
  od;
  if Length(f)=1 then
    return PolynomialByExtRep(FamilyObj(p),f[1]);
  else
    return RationalFunctionByExtRep(FamilyObj(p),f[1],f[2]);
  fi;
end);

#############################################################################
##
#F  ConstantInBaseRingPol(pol,ind)   remove indeterminate ind from polynomial
##
BindGlobal("ConstantInBaseRingPol",function(pol,ind)
  if IsConstantRationalFunction(pol) and
    HasIndeterminateNumberOfUnivariateRationalFunction(pol) and
    IndeterminateNumberOfUnivariateRationalFunction(pol)=ind then
    # constant polynomial represented as univariate: take coefficient
    pol:=ExtRepPolynomialRatFun(pol)[2];
  fi;
  return pol;
end);

#############################################################################
##
#M  Resultant( <f>, <g>, <ind> )
##
InstallMethod(Resultant,"pol,pol,inum",IsFamFamX,
  [IsRationalFunction and IsPolynomial,IsRationalFunction and IsPolynomial,
  IsPosInt],0,
function(f,g,ind)
local fam,tw,res,m,n,valf,valg,con,mn,r,e,s,d,dr,px,x,y,onepol,stop;

  fam:=FamilyObj(f);
  onepol:=One(f);
  res:=onepol;
  onepol:=-onepol;

  # fix some special cases: for baseRing elements,  Degree
  #  may not work
  m:=DegreeIndeterminate(f,ind);
  n:=DegreeIndeterminate(g,ind);

  if n>m then
    # force f to be of larger degee
    res:=(onepol)^(n*m);
    tw:=f; f:=g; g:=tw;
    tw:=m; m:=n; n:=tw;
  fi;

  # trivial cases
  if m=0 then
    return ConstantInBaseRingPol(res*f^n,ind);
  elif n=0 then
    return ConstantInBaseRingPol(res*g^m,ind);
  fi;

  # and now we may start really, subresultant algorithm: S_j+1=g, S_j+2=f

  x:=fam!.oneCoefficient;
  y:=x;
  while 0<n do
    mn:=m-n;
    res:=res*(onepol^m)^n;

    # r:=PseudoDivision(f,g,ind)[2];
    # inline pseudo division: We only need the remainder!

    d:=LeadingCoefficient(g,ind);

    px:=LaurentPolynomialByExtRep(fam,[[fam!.oneCoefficient],1],ind);

    r:=f;
    e:=m-n+1;
    stop:=false;
    repeat
      dr:=DegreeIndeterminate(r,ind);
      if dr<n then
	r:=d^e*r;
        stop:=true;
      fi;
      if stop=false then
	s:=LeadingCoefficient(r,ind)*px^(dr-n);
	r:=d*r-s*g;
	e:=e-1;
      fi;
    until stop;

    m:=n;
    n:=dr;

    f:=g;
#    was: g:=r/(x*y^mn) However the double division seems more gently;
    g:=r/x/y^mn;
    x:=LeadingCoefficient(f,ind);
    y:=x^mn/y^(mn-1);
  od;

  res:=res*g;
  if m>1 then
    res:=res*(g/y)^(m-1);
  fi;

  return ConstantInBaseRingPol(res,ind);
end);


InstallOtherMethod(Resultant,"pol,pol,indet",IsFamFamFam,
  [IsRationalFunction and IsPolynomial,IsRationalFunction and IsPolynomial,
  IsRationalFunction and IsPolynomial],0,
function(a,b,ind)
  return Resultant(a,b,
           IndeterminateNumberOfLaurentPolynomial(ind));
end);

#############################################################################
##
#E  ratfun.gi . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##
