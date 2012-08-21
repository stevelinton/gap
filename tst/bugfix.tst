#############################################################################
##
#W  bugfix.tst                
##
#H  $Id$
##
gap> START_TEST("bugfixes test");

##  Check to see if the strongly connected component (Error 3) fix has been 
##     installed  
##
gap> M := Monoid([Transformation( [ 2, 3, 4, 5, 5 ] ),
> Transformation( [ 3, 1, 4, 5, 5 ] ),
> Transformation( [ 2, 1, 4, 3, 5 ] ) ]);;
gap> Size(GreensLClasses(M)[2])=2;
true

##  Check the fix in OrbitStabilizerAlgorithm (Error 4) for infinite groups. 
##
gap> N:=GroupByGenerators(
>   [ [ [ 0, -1, 0, 0 ], [ 1, 0, 0, 0 ], [ 0, 0, 0, -1 ], [ 0, 0, 1, 0 ] ], 
>     [ [ 0, 0, 1, 0 ], [ 0, 0, 0, 1 ], [ -1, 0, 0, 0 ], [ 0, -1, 0, 0 ] ], 
>     [ [ 0, 0, 1, 0 ], [ 0, 0, 0, 1 ], [ -1, 0, 1, 0 ], [ 0, -1, 0, 1 ] ], 
>     [ [ 0, 0, 1, 0 ], [ 0, 0, 0, 1 ], [ -1, 0, 0, -1 ], [ 0, -1, 1, 0 ] ], 
>     [ [ 1, 0, 0, 0 ], [ 0, 1, 0, 0 ], [ 0, 0, 0, -1 ], [ 0, 0, 1, 0 ] ], 
>     [ [ 0, 1, 0, 0 ], [ 1, 0, 0, 0 ], [ 0, 0, 0, 1 ], [ 0, 0, 1, 0 ] ] ] );
<matrix group with 6 generators>
gap> IsFinite(N);
false
gap> G:=GroupByGenerators( [ [ [ 0, -1, 0, 0 ], [ 1, 0, 0, 0 ], 
>   [ 0, 0, 0, -1 ], [ 0, 0, 1, 0 ] ] ] );
Group([ [ [ 0, -1, 0, 0 ], [ 1, 0, 0, 0 ], [ 0, 0, 0, -1 ], [ 0, 0, 1, 0 ] ] 
 ])
gap> Centralizer(N,G);
<matrix group of size infinity with 6 generators>

## iterated autgp (5)
gap> g:=Group((1,2,3),(4,5,6),(2,3)(5,6));;
gap> aut:=AutomorphismGroup(g);;
gap> ccu:=ConjugacyClasses(aut);;
gap> aut2:=AutomorphismGroup(aut);;


## field conversion (6)
gap> v := [];;
gap> ConvertToVectorRep(v,3);;
gap> ConvertToVectorRep(v,9);;


## EulerianFunction (10)
gap> EulerianFunction( DihedralGroup(8), 2);
24
gap> EulerianFunction( CyclicGroup(6), 1 );
2
gap> EulerianFunction( CyclicGroup(5), 1 );
4


gap> STOP_TEST( "bugfix.tst", 396400 );
#############################################################################
##
#E  bugfix.tst . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##

