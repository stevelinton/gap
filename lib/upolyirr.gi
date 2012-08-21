#############################################################################
##
#W  upolyirr.gi                     GAP Library                 frank Luebeck
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file  contains methods to compute irreducible univariate polynomials
##
Revision.upolyirr_gi:=
  "@(#)$Id$";

#############################################################################
##
#F  AllMonicPolynomialCoeffsOfDegree( <n>, <q> )  . . . . . all coefficient 
#F  lists of monic polynomials over GF(<q>) of degree <n> 
##  
AllMonicPolynomialCoeffsOfDegree := function(n, q)
  local   x,  fq,  one,  res,  a,  fam;
  
  fq := AsSortedList(GF(q));
  one := One(GF(q));
  
  res := Tuples(fq, n);
  for a in res do 
    Add(a, one); 
  od;
  
  return res;
end;

#############################################################################
##
#F  AllIrreducibleMonicPolynomialCoeffsOfDegree( <n>, <q> )  . all coefficient
#F  lists of irreducible monic polynomials over GF(<q>) of degree <n> 
##  
#V  IRR_POLS_OVER_GF_CACHE:  a cache for the following function
##  
IRR_POLS_OVER_GF_CACHE := [];
##  RedCoeffDirectFun := ApplicableMethod(ReduceCoeffs,[[Z(3)],1,[Z(3)],1]);
AllIrreducibleMonicPolynomialCoeffsOfDegree := function(n, q)
  local   l,  zero,  i,  r,  p, new, neverdiv, rc;
  if not IsBound(IRR_POLS_OVER_GF_CACHE[q]) then
    IRR_POLS_OVER_GF_CACHE[q] := [];
  fi;
  if IsBound(IRR_POLS_OVER_GF_CACHE[q][n]) then
    return IRR_POLS_OVER_GF_CACHE[q][n];
  fi;
  
  # this is for going around converting coefficients to polynomials 
  # and using the \mod operator for divisibility tests
  # (I found a speedup factor of about 6 in the example n=9, q=3) 
  neverdiv := function(r, p)
    local   lr,  lp,  rr,  pp;
    lr := Length(r[1]);
    lp := Length(p);
    for rr in r do
      pp := ShallowCopy(p);
      # here we go around method selection which gives a 10% speedup
      ReduceCoeffs(pp, lp, rr, lr);
##        RedCoeffDirectFun(pp, lp, rr, lr);
      ShrinkCoeffs(pp);
      if Length(pp)=0 then
        return false;
      fi;
    od;
    return true;
  end;
  
  l := AllMonicPolynomialCoeffsOfDegree(n, q);
  zero := 0*Indeterminate(GF(q));
  for i in [1..Int(n/2)] do
    r := AllIrreducibleMonicPolynomialCoeffsOfDegree(i, q);
    new:= [];
    for p in l do
      if neverdiv(r, p) then
        Add(new, p);
      fi;
    od;
    l := new;
  od;
  IRR_POLS_OVER_GF_CACHE[q][n] := Immutable(l);
  return IRR_POLS_OVER_GF_CACHE[q][n];  
end;

#############################################################################
##
#F CompanionMat( <poly>
##
InstallGlobalFunction( CompanionMat, function ( arg )

    local c, l, res, i;

    # for the moment allow coefficients as well
    if not IsList( arg ) then
        c := CoefficientsOfLaurentPolynomial( arg[1] );
    else
        c := arg[1];
    fi;
    
    l := Length( c ) - 1;
    res := NullMat( l, l );
    res[1][l] := -c[1];
    for i in [2..l] do
        res[i][i-1] := 1;
        res[i][l] := -c[i];
    od;
    return res;
end );
 
#############################################################################
##
#F AllIrreducibleMonicPolynomials( <degree>, <field> )
##
InstallGlobalFunction( AllIrreducibleMonicPolynomials, 
function( degree, field )
    local q, coeffs, fam, nr;
    if not IsFinite( field ) then
        Error("field must be finite");
    fi;
    q := Size(field);
    nr := IndeterminateNumberOfLaurentPolynomial( 
          Indeterminate(field,"x"));
    coeffs := AllIrreducibleMonicPolynomialCoeffsOfDegree(degree,q);
    fam := FamilyObj( Zero(field) );
    return List( coeffs, 
           x -> LaurentPolynomialByCoefficients(fam,x,nr ) );
end );

