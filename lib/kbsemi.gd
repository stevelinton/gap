#############################################################################
##
#W  kbsemi.gd           GAP library        Andrew Solomon and Isabel Araujo
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the declarations for Knuth Bendix Rewriting Systems
##

Revision.kbsemi_gd :=
    "@(#)$Id$";


############################################################################
##
#C  IsKnuthBendixRewritingSystem(<obj>)
## 
##	returns true if <obj> is a Knuth Bendix Rewriting System.
##
DeclareCategory("IsKnuthBendixRewritingSystem", IsRewritingSystem);

#############################################################################
##
#A  KnuthBendixRewritingSystem(<S>)
##
##	returns the Knuth Bendix rewriting system of the FpSemigroup <S>
##	with respect to the shortlex ordering on words. 
##
DeclareAttribute("KnuthBendixRewritingSystem", IsFpSemigroup, "mutable");

#############################################################################
##
#A  FreeSemigroupOfKnuthBendixRewritingSystem(<rws>)
##
##  returns the free semigroup over which <rws> is
##  a rewriting system
##
DeclareAttribute("FreeSemigroupOfKnuthBendixRewritingSystem",
  IsKnuthBendixRewritingSystem);

#############################################################################
##
#A  SemigroupOfKnuthBendixRewritingSystem(<rws>)
##
##	returns the finitely presented semigroup of which <rws> is 
##	a rewriting system
## 
DeclareAttribute("SemigroupOfKnuthBendixRewritingSystem", 
	IsKnuthBendixRewritingSystem);


############################################################################
##
#F  CreateKnuthBendixRewritingSystemOfFpSemigroup(<S>,<lt>)
##  
##
DeclareGlobalFunction("CreateKnuthBendixRewritingSystemOfFpSemigroup");

############################################################################
##
#F  MakeKnuthBendixRewritingSystemConfluent(<RWS>)
##  
##
DeclareGlobalFunction("MakeKnuthBendixRewritingSystemConfluent");

############################################################################
##
#F  ReduceWordUsingRewritingSystem(<RWS>,<w>)
##  
##
DeclareGlobalFunction("ReduceWordUsingRewritingSystem");
