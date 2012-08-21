#############################################################################
##
#W  upoly.gi                     GAP Library                 Alexander Hulpke
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1999 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains methods for univariate polynomials
##
Revision.upoly_gi:=
  "@(#)$Id$";

#############################################################################
##
#M  IrrFacsPol(<f>) . . . lists of irreducible factors of polynomial over
##                        ring, initialize default
##
InstallMethod(IrrFacsPol,true,[IsPolynomial],0,f -> []);

#############################################################################
##
#F  StoreFactorsPol( <pring>, <upol>, <factlist> ) . . . . store factors list
##
InstallGlobalFunction(StoreFactorsPol,function(R,f,fact)
local i,irf;
  irf:=IrrFacsPol(f);
  if not ForAny(irf,i->i[1]=R) then
    Add(irf,[R,fact]);
  fi;
end);

#############################################################################
##
#M  IsIrreducibleRingElement(<pol>) . . . Irreducibility test for polynomials
##
InstallMethod(IsIrreducibleRingElement,"polynomial",IsCollsElms,
  [IsPolynomialRing,IsPolynomial],0,
function(R,f)
  return Length(Factors(R,f))<=1;
end);

#############################################################################
##
#F  RootsOfUPol(<upol>) . . . . . . . . . . . . . . . . roots of a polynomial
##
InstallGlobalFunction( RootsOfUPol, function(f)
  local roots,factor;
  roots:=[];
  for factor in Factors(f) do
    if DegreeOfLaurentPolynomial(factor)=1 then
      factor:=CoefficientsOfLaurentPolynomial(factor);
      if factor[2]=0 then
	Add(roots,-factor[1][1]/factor[1][2]);
      else
	Add(roots,0*factor[1][1]);
      fi;
    fi;
  od;
  return roots;
end );

#M  for factorization redisplatch if found out the polynomial is univariate
RedispatchOnCondition(Factors,true,[IsPolynomial],[IsUnivariatePolynomial],0);
RedispatchOnCondition(Factors,true,[IsRing,IsPolynomial],
  [,IsUnivariatePolynomial],0);
RedispatchOnCondition(Factors,true,[IsRing,IsPolynomial,IsRecord],
  [,IsUnivariatePolynomial,],0);
RedispatchOnCondition(IsIrreducibleRingElement,true,[IsRing,IsPolynomial],
  [,IsUnivariatePolynomial],0);

#############################################################################
##
#F  CyclotomicPol( <n> )  . . .  coefficients of <n>-th cyclotomic polynomial
##
InstallGlobalFunction( CyclotomicPol, function( n )

    local f,   # result (after stripping off other cyclotomic polynomials)
          div, # divisors of 'n'
          d,   # one divisor of 'n'
          q,   # coefficiens of a quotient that arises in division
          g,   # coefficients of 'd'-th cyclotomic polynomial
          l,   # degree of 'd'-th cycl. pol.
          m,
          i,
          c,
          k;

    if not IsBound( CYCLOTOMICPOLYNOMIALS[ n ] ) then

      # We have to compute the polynomial. Start with 'X^n - 1' ...
      f := List( [ 1 .. n ], x -> 0 );
      f[1]     := -1;
      f[ n+1 ] :=  1;

      div:= ShallowCopy( DivisorsInt( n ) );
      RemoveSet( div, n );

      # ... and divide by all 'd'-th cyclotomic polynomials
      # for proper divisors 'd' of 'n'.
      for d in div do
        q := [];
        g := CyclotomicPol( d );
        l := Length( g );
        m := Length( f ) - l;
        for i  in [ 0 .. m ]  do
          c := f[ m - i + l ] / g[ l ];
          for k  in [ 1 .. l ]  do
            f[ m - i + k ] := f[ m - i + k ] - c * g[k];
          od;
          q[ m - i + 1 ] := c;
        od;
        f:= q;
      od;

      # store the coefficients list
      CYCLOTOMICPOLYNOMIALS[n]:= Immutable( f );
    else

      # just fetch the coefficients list
      f := CYCLOTOMICPOLYNOMIALS[n];
    fi;

    # return the coefficients list
    return f;
end );


############################################################################
##
#F  CyclotomicPolynomial( <F>, <n> ) . . . . . .  <n>-th cycl. pol. over <F>
##
##  returns the <n>-th cyclotomic polynomial over the ring <F>.
##
InstallGlobalFunction( CyclotomicPolynomial, function( F, n )

    local char;   # characteristic of 'F'

    if not IsInt( n ) or n <= 0 or not IsRing( F ) then
      Error( "<n> must be a positive integer, <F> a ring" );
    fi;

    char:= Characteristic( F );
    if char <> 0 then

      # replace 'n' by its $p^{\prime}$ part
      while n mod char = 0  do
        n := n / char;
      od;
    fi;
    return UnivariatePolynomial( F, One( F ) * CyclotomicPol(n) );
end );

#############################################################################
##
#E  upoly.gi  . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##

