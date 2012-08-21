#############################################################################
##
#W  vec8bit.gi                   GAP Library                     Steve Linton
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file mainly installs the kernel methods for 8 bit vectors
##
Revision.vec8bit_gi :=
    "@(#)$Id$";

#############################################################################
##
#V  `TYPES_VEC8BIT . . . . . . . . prepared types for compressed GF(q) vectors
##
##  A length 2 list of length 257 lists. TYPES_VEC8BIT[0][q] will be the type
##  of mutable vectors over GF(q), TYPES_VEC8BIT[1][q] is the type of 
##  immutable vectors. The 257th position is bound to 1 to stop the lists
##  shrinking.
##
##  It is accessed directly by the kernel, so the format cannot be changed
##  without changing the kernel.
##

InstallValue(TYPES_VEC8BIT , [[],[]]);
TYPES_VEC8BIT[1][257] := 1;
TYPES_VEC8BIT[2][257] := 1;


#############################################################################
##
#F  TYPE_VEC8BIT( <q>, <mut> ) . .  computes type of compressed GF(q) vectors
##
##  Normally called by the kernel, caches results in TYPES_VEC8BIT
##

InstallGlobalFunction(TYPE_VEC8BIT,
  function( q, mut)
    local col,filts;
    if mut then col := 1; else col := 2; fi;
    if not IsBound(TYPES_VEC8BIT[col][q]) then
        filts := IsHomogeneousList and IsListDefault and IsCopyable and
                 Is8BitVectorRep and IsSmallList and
                 IsRingElementList;
        if mut then filts := filts and IsMutable; fi;
        TYPES_VEC8BIT[col][q] := NewType(FamilyObj(GF(q)),filts);
    fi;
    return TYPES_VEC8BIT[col][q];
end);

#############################################################################
##
#V  TYPE_FIELDINFO_8BIT type of the fieldinfo bags
##
##  These bags are created by the kernel and accessed by the kernel. The type
##  doesn't really say anything, because there are no applicable operations.
##

InstallValue( TYPE_FIELDINFO_8BIT,
  NewType(NewFamily("FieldInfo8BitFamily", IsObject),
          IsObject and IsDataObjectRep));

#############################################################################
##
#M  Length( <vec> )
##

InstallMethod( Length, "For a compressed VecFFE", 
        true, [IsList and Is8BitVectorRep], 0, LEN_VEC8BIT);

#############################################################################
##
#M  <vec> [ <pos> ]
##

InstallMethod( \[\],  "For a compressed VecFFE", 
        true, [IsList and Is8BitVectorRep, IsPosInt], 0, ELM_VEC8BIT);

#############################################################################
##
#M  <vec> [ <pos> ] := <val>
##
##  This may involve turning <vec> into a plain list, if <val> does
##  not lie in the appropriate field.
##
##  <vec> may also be converted back into vector rep over a bigger field.
##
               
InstallMethod( \[\]\:\=,  "For a compressed VecFFE", 
        true, [IsMutable and IsList and Is8BitVectorRep, IsPosInt, IsObject], 
        0, ASS_VEC8BIT);

#############################################################################
##
#M  Unbind( <vec> [ <pos> ] )
##
##  Unless the last position is being unbound, this will result in <vec>
##  turning into a plain list
##

InstallMethod( Unbind\[\], "For a compressed VecFFE",
        true, [IsMutable and IsList and Is8BitVectorRep, IsPosInt],
        0, UNB_VEC8BIT);

#############################################################################
##
#M  ViewObj( <vec> )
##
##  Up to length 10, GF(q) vectors are viewed in full, over that a 
##  description is printed
##

InstallMethod( ViewObj, "For a compressed VecFFE",
        true, [Is8BitVectorRep and IsSmallList], 0,
        function( vec )
    if (LEN_VEC8BIT(vec) > 10) then
        Print("< ");
        if not IsMutable(vec) then
            Print("im");
        fi;
        Print("mutable compressed vector length ",
              LEN_VEC8BIT(vec)," over GF(",Q_VEC8BIT(vec),") >");
    else
        PrintObj(vec);
    fi;
end);

#############################################################################
##
#M  PrintObj( <vec> )
##
##  Same method as for lists in internal rep. 
##

InstallMethod( PrintObj, "For a compressed VecFFE",
        true, [Is8BitVectorRep and IsSmallList], 0,
        function( vec )
    local i,l;
    Print("\>\>[ \>\>");
    l := Length(vec);
    if l <> 0 then
        PrintObj(vec[1]);
        for i in [2..l] do
            Print("\<,\<\>\> ");
            PrintObj(vec[i]);
        od;
    fi;
    Print(" \<\<\<\<]");
end);

#############################################################################
##
#M  ShallowCopy(<vec>)
##
##  kernel method produces a copy in the same representation
##

InstallMethod(ShallowCopy, "For a compressed VecFFE",
        true, [Is8BitVectorRep and IsSmallList], 0,
        SHALLOWCOPY_VEC8BIT);

#############################################################################
##
#M  <gf2vec>[<pos>] := <ffe>
##        
##  If we assign an element of a larger characteristic two field into
##  a GF(2) vector, then we want to convert to GF(q) representatiom
##  This method does it via plain lists, which is slow, but this event
##  should be rare
##
#InstallMethod(\[\]\:\=, "For a GF2 vector and an FFE in char 2",
#        IsCollsXElms, [IsMutable and IsList and IsGF2VectorRep,
#                IsPosInt,
#                IsFFE and IsInternalRep], 0,
#        function(l,pos,e)
#    if DegreeFFE(e) > 8 or pos > Length(l)+1 then
#        TryNextMethod();
#    else
#        ASS_GF2VEC(l,pos,e);
#        ConvertToVectorRep(l);
#    fi;
#end);

#############################################################################
##
#M  <vec1> + <vec2>
##
##  The method installation enforced same
##  characteristic. Compatability of fields and vector lengths is
##  handled in the method

InstallMethod( \+, "For two 8 bit vectors in same characteristic",
        IsIdenticalObj, [IsRowVector and Is8BitVectorRep,
                IsRowVector and Is8BitVectorRep], 0,
        SUM_VEC8BIT_VEC8BIT);

#############################################################################
##
#M  `PlainListCopyOp( <vec> ) 
##
##  Make the vector into a plain list (in place)
##

InstallMethod( PlainListCopyOp, "For an 8 bit vector",
        true, [IsSmallList and Is8BitVectorRep], 0,
        function (v)
    PLAIN_VEC8BIT(v);
    return v;
end);

#############################################################################
##
#M  ELM0_LIST( <vec> ) 
##
##  alternatibe element access interface, returns fail when unbound
##

InstallMethod(ELM0_LIST, "For an 8 bit vector",
        true, [IsList and Is8BitVectorRep, IsPosInt], 0,
        ELM0_VEC8BIT);

#############################################################################
##
#M  <vec>{<poss>}
##
##  multi-element access
##
InstallMethod(ELMS_LIST, "For an 8 bit vector and a plain list",
        true, [IsList and Is8BitVectorRep, 
               IsPlistRep and IsDenseList ], 0,
        ELMS_VEC8BIT);

InstallMethod(ELMS_LIST, "For an 8 bit vector and a range",
        true, [IsList and Is8BitVectorRep, 
               IsRange and IsInternalRep ], 0,
        ELMS_VEC8BIT_RANGE);

#############################################################################
##
#M  <vec>*<ffe>
##

InstallMethod(\*, "For an 8 bit vector and an FFE",
        IsCollsElms, [IsRowVector and Is8BitVectorRep,
                IsFFE and IsInternalRep], 0,
        PROD_VEC8BIT_FFE);

#############################################################################
##
#M <ffe>*<vec>
##

InstallMethod(\*, "For an FFE and an 8 bit vector ",
        IsElmsColls, [IsFFE and IsInternalRep, 
                IsRowVector and Is8BitVectorRep], 
        0,
        PROD_FFE_VEC8BIT);
#############################################################################
##
#M  <vecl> - <vecr>
##
InstallMethod(\-, "For two 8bit vectors",
        IsIdenticalObj, [IsRowVector and Is8BitVectorRep,
                IsRowVector and Is8BitVectorRep], 
        0,
        DIFF_VEC8BIT_VEC8BIT );

#############################################################################
##
#M  -<vec>
##

InstallMethod( AdditiveInverseOp, "For an 8 bit vector",
        true, [IsRowVector and Is8BitVectorRep],
        0,
        AINV_VEC8BIT);

#############################################################################
##
#M  ZeroOp( <vec> )
##
##  A mutable zero vector of the same field and length
##

InstallMethod( ZeroOp, "For an 8 bit vector",
        true, [IsRowVector and Is8BitVectorRep],
        0,
        ZERO_VEC8BIT);

#############################################################################
##
#M  <vec1> = <vec2>
##

InstallMethod( \=, "For 2 8 bit vectors",
        IsIdenticalObj, [IsRowVector and Is8BitVectorRep,
                IsRowVector and Is8BitVectorRep],
        0,
        EQ_VEC8BIT_VEC8BIT);

#############################################################################
##
#M  <vec1> < <vec2>
##
##  Usual lexicographic ordering
##

InstallMethod( \<, "For 2 8 bit vectors",
        IsIdenticalObj, [IsRowVector and Is8BitVectorRep,
                IsRowVector and Is8BitVectorRep],
        0,
        LT_VEC8BIT_VEC8BIT);

#############################################################################
##
#M  <vec1>*<vec2>
##
##  scalar product
#'
InstallMethod( \*, "For 2 8 bit vectors",
        IsIdenticalObj, [IsRingElementList and Is8BitVectorRep,
                IsRingElementList and Is8BitVectorRep],
        0,
        PROD_VEC8BIT_VEC8BIT);

#############################################################################
##
#M  AddRowVector( <vec1>, <vec2>, <mult>, <from>, <to> )
##
##  add <mult>*<vec2> to <vec1> in place
##

InstallOtherMethod( AddRowVector, "For 2 8 bit vectors and a field element and from and to",
        IsCollsCollsElmsXX, [ IsRowVector and Is8BitVectorRep,
                IsRowVector and Is8BitVectorRep,
                IsFFE and IsInternalRep, IsPosInt, IsPosInt ], 0,
        ADD_ROWVECTOR_VEC8BITS_5);

#############################################################################
##
#M  AddRowVector( <vec1>, <vec2>, <mult> )
##
##  add <mult>*<vec2> to <vec1> in place
##

InstallOtherMethod( AddRowVector, "For 2 8 bit vectors and a field element",
        IsCollsCollsElms, [ IsRowVector and Is8BitVectorRep,
                IsRowVector and Is8BitVectorRep,
                IsFFE and IsInternalRep ], 0,
        ADD_ROWVECTOR_VEC8BITS_3);

#############################################################################
##
#M  AddRowVector( <vec1>, <vec2> )
##
##  add <vec2> to <vec1> in place
##

InstallOtherMethod( AddRowVector, "For 2 8 bit vectors",
        IsIdenticalObj, [ IsRowVector and Is8BitVectorRep,
                IsRowVector and Is8BitVectorRep], 0,
        ADD_ROWVECTOR_VEC8BITS_2);

#############################################################################
##
#M  MultRowVector( <vec>, <ffe> )
##
##  multiply <vec> by <ffe> in place
##

InstallOtherMethod( MultRowVector, "For an 8 bit vector and an ffe",
        IsCollsElms, [ IsRowVector and Is8BitVectorRep,
                IsFFE and IsInternalRep], 0,
        MULT_ROWVECTOR_VEC8BITS);

#############################################################################
##
#M  PositionNot( <vec>, <zero )
#M  PositionNot( <vec>, <zero>, 0)
##
##
InstallOtherMethod( PositionNot, "for GF(2) vector and 0*Z(2)",
        IsCollsElms, [Is8BitVectorRep and IsRowVector , IsFFE and
                IsZero], 0,
        POSITION_NONZERO_VEC8BIT);

InstallMethod( PositionNot, "for GF(2) vector and 0*Z(2) and 0",
        IsCollsElmsX, [Is8BitVectorRep and IsRowVector , IsFFE and
                IsZero, IsZero and IsInt], 0,
        function(v,z,z1) 
    return POSITION_NONZERO_VEC8BIT(v,z); 
end);

#############################################################################
##
#M  Append( <vecl>, <vecr> )
##

InstallMethod( Append, "for GF2 vectors",
        IsIdenticalObj, [Is8BitVectorRep and IsMutable and IsList,
                Is8BitVectorRep and IsList], 0,
        APPEND_VEC8BIT);
        

