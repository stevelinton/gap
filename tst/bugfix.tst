gap> START_TEST("bugfixes test");

gap> VERSION;
"4.1 fix 6"

# fix #1
gap> g:=Image(IsomorphismFpGroupByPcgs(FamilyPcgs(SmallGroup(72,41)),"g"));;
gap> IdGroup(g);
[ 72, 41 ]


gap> a:=2^31+1;; b:=2^30+1;;
gap> RemInt(a,b) = a mod b;
true
gap> a:=2^66+1;; b:=2^65+1;;
gap> RemInt(a,b) = a mod b;
true

gap> ProductCoeffs([],0,[],0);
[  ]
gap> A := [[0,0],[0,0]];
[ [ 0, 0 ], [ 0, 0 ] ]
gap> LLLReducedBasis( A, "linearcomb");
rec( basis := [  ], relations := [ [ 1, 0 ], [ 0, 1 ] ], 
  transformation := [  ], mue := [  ], B := [  ] )
gap> dom := Domain([1..2]);
<object>
gap> el := Elements(dom);
[ 1, 2 ]
gap> tl := List([1,2],x->List(el,y->Tuple([y,el[x]])));
[ [ Tuple( [ 1, 1 ] ), Tuple( [ 2, 1 ] ) ], 
  [ Tuple( [ 1, 2 ] ), Tuple( [ 2, 2 ] ) ] ]
gap> gens := List(tl,x->GeneralMappingByElements(dom,dom,x));
[ <general mapping: <object> -> <object> >, 
  <general mapping: <object> -> <object> > ]
gap> MagmaWithOne(gens);
<monoid with 2 generators>

# The following command requires the tables of marks to be installed. If
# they are not installed it will issue a - then harmless - error.
gap> tom:=TableOfMarks("A5");
TableOfMarks( "A5" )


#fix #2

gap> F := GF(3);;
gap> fam := ElementsFamily(FamilyObj(F));;
gap> p := LaurentPolynomialByCoefficients( fam, [One(F)], 0 );;
gap> Derivative(p);;
gap> Gcd( p, Derivative(p) );
Z(3)^0

gap> AllPrimitiveGroups(DegreeOperation,64);
[ <permutation group of size 576 with 2 generators>, 
  <permutation group of size 896 with 3 generators>, 
  <permutation group of size 1152 with 3 generators>, 
  <permutation group of size 1344 with 3 generators>, 
  <permutation group of size 1728 with 3 generators>, 
  <permutation group of size 1728 with 4 generators>, 
  <permutation group of size 2688 with 4 generators>, 
  <permutation group of size 2688 with 4 generators>, 
  <permutation group of size 3456 with 5 generators>, 
  <permutation group of size 3456 with 5 generators>, 
  <permutation group of size 3456 with 4 generators>, 
  <permutation group of size 4032 with 3 generators>, 
  <permutation group of size 4032 with 4 generators>, 
  <permutation group of size 4032 with 3 generators>, 
  <permutation group of size 5184 with 4 generators>, 
  <permutation group of size 6272 with 4 generators>, 
  <permutation group of size 6912 with 6 generators>, 
  <permutation group of size 6912 with 3 generators>, 
  <permutation group of size 8064 with 5 generators>, 
  <permutation group of size 8064 with 4 generators>, 
  <permutation group of size 10368 with 5 generators>, 
  <permutation group of size 10368 with 5 generators>, 
  <permutation group of size 10368 with 4 generators>, 
  <permutation group of size 12096 with 4 generators>, 
  <permutation group of size 13824 with 4 generators>, 
  <permutation group of size 13824 with 3 generators>, 
  <permutation group of size 13824 with 4 generators>, 
  <permutation group of size 18816 with 5 generators>, 
  <permutation group of size 18816 with 5 generators>, 
  <permutation group of size 20736 with 6 generators>, 
  <permutation group of size 20736 with 3 generators>, 
  <permutation group of size 24192 with 3 generators>, 
  <permutation group of size 27648 with 4 generators>, 
  <permutation group of size 41472 with 4 generators>, 
  <permutation group of size 41472 with 4 generators>, 
  <permutation group of size 41472 with 4 generators>, 
  <permutation group of size 41472 with 3 generators>, 
  <permutation group of size 56448 with 6 generators>, 
  <permutation group of size 82944 with 9 generators>, 
  <permutation group of size 82944 with 8 generators>, 2^6:SL(6,2), 
  <permutation group of size 3612672 with 6 generators>, 
  2^6:GL(3,4):2 < GL(6,2), 2^6:SL(3,4):2 < GL(6,2), 2^6:GL(3,4) < GL(6,2), 
  2^6:SL(3,4) < GL(6,2), 3.A_6.2 max GL(3,4).2, 3.A_6 max GL(3,4), 
  2^6:GL(2,8):3 < GL(6,2), 2^6:SL(2,8):3 < GL(6,2), 2^6:GL(2,8) < GL(6,2), 
  2^6:SL(2,8) < GL(6,2), 2^6:SL(3,2) o SL(2,2), 
  <permutation group of size 32256 with 4 generators>, 2^6:Sp(6,2), 
  2^6:O(-1,6,2), <permutation group of size 1658880 with 4 generators>, 
  2^6:O(+1,6,2), <permutation group of size 1290240 with 5 generators>, 
  S_7 max S_8 = O+(6,2) max Sp(6,2), (S_7 max S_8 = O+(6,2) max Sp(6,2))', 
  U_3(3):2 max Sp(6,2), (U_3(3):2 max Sp(6,2))', 
  L_2(7):2 max U_3(3):2 max Sp(6,2), A8 on 1-sets^2.1, A8 on 1-sets^2.2, 
  A8 on 1-sets^2.3, A8 on 1-sets^2.4, L2,7 on projective points^2.1, 
  L2,7 on projective points^2.2, L2,7 on projective points^2.3, 
  L2,7 on projective points^2.4, Alt( [ 1 .. 64 ] ), Sym( [ 1 .. 64 ] ) ]

gap> gens:= [(3,10)(6,18)(11,26)(12,27)(13,28)(19,40)(20,41)(24,32)(29,53)
> (30,54)
> (31,55)(33,57)(42,69)(43,70)(45,71)(49,61)(51,63)(58,83)(59,84)(60,85)
> (62,86)(64,87)(68,82)(72,91)(73,92)(75,93)(78,94)(80,89)(81,90)(88,99),
> (1,2)(3,6)(4,7)(9,17)(10,18)(11,19)(13,32)(14,21)(23,37)(24,28)
> (25,38)(26,40)(29,42)(31,61)(33,63)(34,46)(39,65)(48,66)(49,55)(50,67)
> (51,57)(53,69)(58,72)(60,89)(62,90)(68,78)(80,85)(81,86)(82,94)(83,91),
> (1,3)(2,6)(4,11)(7,19)(9,24)(14,29)(17,28)(20,44)
> (21,42)(23,49)(25,51)(27,56)(34,58)(37,55)(38,57)(39,68)
> (43,74)(45,76)(46,72)(48,80)(50,81)(54,77)(65,78)(66,85)
> (67,86)(73,95)(75,96)(84,98)(87,97)(99,100),
> (1,4)(2,7)(3,11)(6,19)(8,22)(10,26)(12,30)(18,40)(27,54)(35,36)
> (48,50)(56,77)(60,62)(66,67)(73,75)(80,81)(85,86)(89,90)(92,93)(95,96),
> (4,14)(7,21)(11,29)(15,36)(19,42)(22,47)(23,50)(26,53)(30,59)(31,62)
> (37,67)(40,69)(43,75)(49,81)(54,84)(55,86)(61,90)(70,93)(74,96)(77,98),
> (5,15)(9,23)(13,31)(14,34)(17,37)(20,43)(21,46)(24,49)
> (28,55)(29,58)(32,61)(41,70)(42,72)(44,74)(47,79)(53,83)
> (59,88)(69,91)(84,99)(98,100),(5,16)(9,25)(13,33)(17,38)
> (20,45)(24,51)(28,57)(32,63)(34,65)(39,46)(41,71)(44,76)
> (52,79)(58,78)(64,88)(68,72)(82,91)(83,94)(87,99)(97,100),
> (2,8)(3,12)(5,17)(7,22)(10,27)(11,30)(15,37)(16,38)(20,32)(21,47)
> (24,41)(26,54)(29,59)(35,66)(36,67)(39,52)(43,61)(45,63)(46,79)(49,70)
> (51,71)(53,84)(58,88)(64,78)(73,89)(75,90)(80,92)(81,93)(83,99)(87,94)];;
gap> g:=Group(gens); 
<permutation group with 8 generators>
gap> Length( ConjugacyClasses(g) );
49

gap> a:=[[1,2,-1,3,3/4,3],[2,1,3/4,3,-1,3],[-1,3,1,2,3,3/4],
> [3/4,3,2,1,3,-1],[3,-1,3,3/4,1,2],[3,3/4,3,-1,2,1]];;
gap> mp:=MinimalPolynomial(Rationals, a, 1);
-14175/256+5865/64*x_1-37/2*x_1^2-31/4*x_1^3+x_1^4
gap> CompanionMat(mp);
[ [ 0, 0, 0, 14175/256 ], [ 1, 0, 0, -5865/64 ], [ 0, 1, 0, 37/2 ], 
  [ 0, 0, 1, 31/4 ] ]

gap> g := GroupRing(GF(7), SymmetricGroup(4));
<algebra-with-one over GF(7), with 2 generators>
gap> g := GroupRing(GF(7), SymmetricGroup(4));;
gap> I:= Ideal( g, [ Basis(g)[1] ] );;
gap> J:= Ideal( g, [ Basis(I)[1] ] ); 
<two-sided ideal in <algebra-with-one over GF(7), with 2 generators>, 
  (1 generators)>

gap> m:= IdentityMat( 2, GF(3) );;
gap> DirectSumMat( m,m);
[ [ Z(3)^0, 0*Z(3), 0*Z(3), 0*Z(3) ], [ 0*Z(3), Z(3)^0, 0*Z(3), 0*Z(3) ], 
  [ 0*Z(3), 0*Z(3), Z(3)^0, 0*Z(3) ], [ 0*Z(3), 0*Z(3), 0*Z(3), Z(3)^0 ] ]

gap> b := BinaryRelationByListOfImagesNC([[1],[2],[3]]);;
gap> IsDomain(Source(b));
true

# The following command requires the tables of marks to be installed. If
# they are not installed it will issue a - then harmless - error.
gap> G:=DihedralGroup(6);
<pc group of size 6 with 2 generators>
gap> tm:=TableOfMarks(G);
TableOfMarks( Group( [ f1, f2 ] ) )
gap> H:=RepresentativeTom(tm,2);
Group([ f1 ])
gap> th:=CharacterTable(H);
CharacterTable( Group([ f1 ]) )
gap> Size(H);
2
gap> SizesConjugacyClasses(th);
[ 1, 1 ]

# fix#4

gap> v := [1,0]*Z(4)^0;
[ Z(2)^0, 0*Z(2) ]
gap> MakeImmutable(v);
gap> ConvertToVectorRep(v,4);
4
gap> NumberFFVector(v,4);
4

gap> code := 42000196945440135986257788391020509453777404676419;;
gap> H := PcGroupCode( code, 1008 );
<pc group of size 1008 with 7 generators>
gap> list := Pcgs(H);;
gap> g := Comm( list[2], list[1] );;
gap> p:=PrimePowerComponents( g );
[ f3*f4*f5*f6^3*f7^2, f5*f6^2*f7, f6*f7 ]
gap> li:= List( p, Order );
[ 4, 9, 7 ]

gap> F:= GF(3^10);
GF(3^10)
gap> r:= PrimitiveRoot( F );
Z(3^10)
gap> qq:= Size( F ) - 1;
59048
gap> (r^36369)^qq;
Z(3)^0

gap> f := FreeGroup(1);
<free group on the generators [ f1 ]>
gap> g := f / [f.1^4];
<fp group on the generators [ f1 ]>
gap> EpimorphismNilpotentQuotient(g);
[ f1 ] -> [ f1 ]

gap> CyclicGroup( NextPrimeInt(1000000000) );
<pc group of size 1000000007 with 1 generators>

# fix #5
gap> Zero(GF(2))^1;
0*Z(2)

# fix #6

gap> AllPrimitiveGroups(DegreeOperation,64);;

gap> s:=Semigroup([Transformation([1,1,1]),
> Transformation([2,2,2]),Transformation([3,3,3])]);;
gap> pairs:=[[Transformation([1,1,1]),Transformation([3,3,3])],
> [Transformation([2,2,2]),Transformation([3,3,3])]];;
gap> Length(EquivalenceClasses(
> SemigroupCongruenceByGeneratingPairs(s, pairs)));
1

gap> DicyclicGroup := function(n)
>      local F2,P;
>      F2 := FreeGroup( "a", "b" );
>      P:= F2 / [ F2.1^(2*n), F2.2^2*F2.1^(-n), F2.1*F2.2*F2.1*F2.2^(-1)];
>      return P;
> end;
function( n ) ... end
gap> G:=DicyclicGroup(15);
<fp group on the generators [ a, b ]>
gap>  SylowSubgroup(G,2);
Group(<fp, no generators known>)


gap> x5:= Indeterminate( Rationals, 5 );;
gap> x6:= Indeterminate( Rationals, 6 );;
gap> x7:= Indeterminate( Rationals, 7 );;
gap>  a:=x5^2+x5*x6+x5*x7+x6^2+x6*x7+x7^2;;
gap> b := OnIndeterminates(a,());;
gap> a=b;
true

gap> IsObject(Domain(FamilyObj(1),[1,2]));
true


gap> f := FreeSemigroup(1);
<free semigroup on the generators [ s1 ]>
gap> a := f.1;
s1
gap> (ApplicableMethod(\^, [a,-1]) <> fail) or
>       (ApplicableMethod(\^, [a,0]) <> fail);
false

gap> g:=SmallGroup(2^8, 6892);
<pc group of size 256 with 8 generators>
gap> gens:=GeneratorsOfGroup(g);
[ f1, f2, f3, f4, f5, f6, f7, f8 ]
gap> a1:=gens[1];; a2:=gens[2];; a3:=gens[3];; a4:=gens[4];; 
gap> a5:=gens[5];; a6:=gens[6];; a7:=gens[7];; a8:=gens[8];;
gap> h:=Subgroup(g, [a1,a2*a6,a4]);
Group([ f1, f2*f6, f4 ])
gap> h3:=h^a3;
Group([ f1*f6, f2*f6*f7, f4, f5, f7, f8 ])
gap> int:=Intersection(h,h3);
Group([ f2*f6*f7, f4, f5, f7, f8 ])

gap> f:=FreeSemigroup("a","b");;
gap> a:=f.1;;b:=f.2;;
gap> g:=f/[[b^3,a^2],[a^2,a]];;
gap> kbrws:=KnuthBendixRewritingSystem(g);
Knuth Bendix Rewriting System for Semigroup( [ a, b ] ) with rules
[ [ b^3, a^2 ], [ a^2, a ] ]
gap> ReduceRules(kbrws);
gap> kbrws;
Knuth Bendix Rewriting System for Semigroup( [ a, b ] ) with rules 
[ [ b^3, a ], [ a^2, a ] ]

gap> v := [Z(3)];
[ Z(3) ]
gap> ConvertToVectorRep (v);
3
gap> v{[]}+v{[]};
[  ]

gap> STOP_TEST( "bugfixes test", 31560000 );
