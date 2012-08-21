#include        "system.h"              /* system dependent part           */

const char * Revision_vecgf2_c =
   "@(#)$Id$";

#include        "gasman.h"              /* garbage collector               */
#include        "objects.h"             /* objects                         */
#include        "scanner.h"             /* scanner                         */

#include        "gap.h"                 /* error handling, initialisation  */

#include        "gvars.h"               /* global variables                */
#include        "calls.h"               /* generic call mechanism          */
#include        "opers.h"               /* generic operations              */

#include        "ariths.h"              /* basic arithmetic                */
#include        "finfield.h"            /* finite fields and ff elements   */

#include        "bool.h"                /* booleans                        */

#include        "records.h"             /* generic records                 */
#include        "precord.h"             /* plain records                   */

#include        "lists.h"               /* generic lists                   */
#include        "plist.h"               /* plain lists                     */
#include        "range.h"               /* ranges                          */
#include        "blister.h"             /* boolean lists                   */
#include        "string.h"              /* strings                         */

#define INCLUDE_DECLARATION_PART
#include        "vecgf2.h"              /* GF2 vectors                     */
#undef  INCLUDE_DECLARATION_PART

#include        "saveload.h"            /* saving and loading              */
#include        "integer.h"             /* (long) integers                 */


/****************************************************************************
**
*F * * * * * * * * * * * imported library variables * * * * * * * * * * * * *
*/


/****************************************************************************
**
*V  TYPE_LIST_GF2VEC  . . . . . . . . . . . . . . type of a GF2 vector object
*/
Obj TYPE_LIST_GF2VEC;


/****************************************************************************
**
*V  TYPE_LIST_GF2VEC_IMM  . . . . . .  type of an immutable GF2 vector object
*/
Obj TYPE_LIST_GF2VEC_IMM;


/****************************************************************************
**
*V  TYPE_LIST_GF2MAT  . . . . . . . . . . . . . . type of a GF2 matrix object
*/
Obj TYPE_LIST_GF2MAT;


/****************************************************************************
**
*V  TYPE_LIST_GF2MAT_IMM  . . . . . .  type of an immutable GF2 matrix object
*/
Obj TYPE_LIST_GF2MAT_IMM;


/****************************************************************************
**
*V  IsGF2VectorRep  . . . . . . . . . . . . . . . . . . . . . . . . .  filter
*/
Obj IsGF2VectorRep;


/****************************************************************************
**
*V  GF2One  . . . . . . . . . . . . . . . . . . . . . . . . . . .  one of GF2
*/
Obj GF2One;


/****************************************************************************
**
*V  GF2Zero . . . . . . . . . . . . . . . . . . . . . . . . . . . zero of GF2
*/
Obj GF2Zero;


/****************************************************************************
**
*F * * * * * * * * * * * * arithmetic operations  * * * * * * * * * * * * * *
*/


/****************************************************************************
**
*F  AddCoeffsGF2VecGF2Vec( <sum>, <vec> ) . . . . . . . .  add <vec> to <sum>
**
**  `AddCoeffsGF2VecGF2Vec' adds  the   entries of <vec>  to <sum>.    If the
**  length  are not equal the  missing entries are  assumed  to be zero.  The
**  position of the rightmost Z(2) is returned.
*/

UInt RightMostOneGF2Vec (
    Obj                 vec )
{
    UInt                len;

    len = LEN_GF2VEC(vec);
    while ( 0 < len ) {
        if ( BLOCK_ELM_GF2VEC(vec,len) == 0 )
	    len = BIPEB*((len-1)/BIPEB);
        else if ( BLOCK_ELM_GF2VEC(vec,len) & MASK_POS_GF2VEC(len) )
            break;
	else
	  len--;
    }
    return len;
}


Obj AddCoeffsGF2VecGF2Vec (
    Obj                 sum,
    Obj                 vec )
{
    UInt *              ptS;
    UInt *              ptV;
    UInt *              end;
    UInt                len;

    /* get the length                                                      */
    len = LEN_GF2VEC(vec);

    /* grow <sum> is necessary                                             */
    if ( LEN_GF2VEC(sum) < len ) {
        ResizeBag( sum, SIZE_PLEN_GF2VEC(len) );
        SET_LEN_GF2VEC( sum, len );
    }

    /* add <vec> to <sum>                                                  */
    ptS = BLOCKS_GF2VEC(sum);
    ptV = BLOCKS_GF2VEC(vec);
    end = ptS + ((len+BIPEB-1)/BIPEB);
    while ( ptS < end ) {
        *ptS++ ^= *ptV++;
    }
    return INTOBJ_INT(RightMostOneGF2Vec(sum));
}


/****************************************************************************
**
*F  AddPartialGF2VecGF2Vec( <sum>, <vl>, <vr>, <n> )  . . . . . . partial sum
**
**  'AddPartialGF2VecGF2Vec' adds the entries  of <vl> and <vr> starting from
**  that block which is corresponding to the entry with number <n> and stores
**  the result in <sum>.
**
**  Note: The other entries are set to be zero. So use a higher value for <n>
**        only for vectors, which both have leading zero-entries. 
**
**  You  can use  the parameter  <n> for  example for  an  gauss-algorithm on 
**  gf2-matrices  can be  improved,  because when  using the gauss-algorithm,
**  you  know that  the leading entries of two vectors to be  added are equal
**  zero. If <n> = 1 all entries are added. 
**
**  Note that the caller has to ensure, that <sum> is a gf2-vector with the 
**  correct size.
*/
Obj AddPartialGF2VecGF2Vec (
    Obj                 sum,
    Obj                 vl,
    Obj                 vr,
    UInt                n )
{
    UInt *              ptL;            /* bit field of <vl>               */
    UInt *              ptR;            /* bit field of <vr>               */
    UInt *              ptS;            /* bit field of <sum>              */
    UInt *              end;            /* end marker                      */
    UInt                len;            /* length of the list              */
    UInt                offset;         /* number of block to start adding */
    

    /* both operands lie in the same field                                 */
    len = LEN_GF2VEC(vl);
    if ( len != LEN_GF2VEC(vr) ) {
        ErrorQuit( "Vector +: vectors must have the same length",
                   0L, 0L );
        return 0;
    }


    /* calculate the offset for adding                                     */
    if ( n == 1 ) {  
        ptL = BLOCKS_GF2VEC(vl);
        ptR = BLOCKS_GF2VEC(vr);
        ptS = BLOCKS_GF2VEC(sum);
        end = ptS + ((len+BIPEB-1)/BIPEB);
    } else {
        offset = ( n - 1 ) / BIPEB;
        ptL = BLOCKS_GF2VEC(vl) + offset ;
        ptR = BLOCKS_GF2VEC(vr) + offset ;
        ptS = BLOCKS_GF2VEC(sum) + offset ;
        end = ptS + ((len+BIPEB-1)/BIPEB) - offset;
    }
    
    /* loop over the entries and add                                       */
    while ( ptS < end )
        *ptS++ = *ptL++ ^ *ptR++;

    /* return the result                                                   */
    return sum;
}


/****************************************************************************
**
*F  ProdGF2VecGF2Vec( <vl>, <vr> )  . . . . . . .  product of two GF2 vectors
**
**  'ProdVecGF2VecGF2' returns  the product of  the two GF2 vectors <vl> and
**  <vr>.   The product is  the folded sum of   the corresponding entries of
**  <vl> and <vr>.
**
**  'ProdVecGF2VecGF2' is an improved  version of the general multiplication,
**  which  does not  call 'PROD'  but uses bit  operations instead.   It will
**  always return either 'GF2One' or 'GF2Zero'.
*/
#ifdef SYS_IS_64_BIT

#define PARITY_BLOCK(m) \
  do { m = m ^ (m>>32); \
       m = m ^ (m>>16); \
       m = m ^ (m>>8);  \
       m = m ^ (m>>4);  \
       m = m ^ (m>>2);  \
       m = m ^ (m>>1);  \
  } while(0)

#else

#define PARITY_BLOCK(m) \
  do { m = m ^ (m>>16); \
       m = m ^ (m>>8);  \
       m = m ^ (m>>4);  \
       m = m ^ (m>>2);  \
       m = m ^ (m>>1);  \
  } while(0)

#endif

Obj ProdGF2VecGF2Vec ( vl, vr )
    Obj                 vl;
    Obj                 vr;
{
    UInt *              ptL;            /* bit field of <vl>               */
    UInt *              ptR;            /* bit field of <vr>               */
    UInt                len;            /* length of the list              */
    UInt                nrb;            /* number of blocks in blist       */
    UInt                m;              /* number of bits in a block       */
    UInt                n;              /* number of bits in blist         */
    UInt                i;              /* loop variable                   */

    /* both operands lie in the same field                                 */
    len = LEN_GF2VEC(vl);
    if ( len != LEN_GF2VEC(vr) ) {
      ErrorQuit(
        "Vector *: <right> must have the same length as <left> (%d not %d)",
        len, (Int)LEN_GF2VEC(vr) );
      return 0;
    }

    /* loop over the entries and multiply                                  */
    ptL = BLOCKS_GF2VEC(vl);
    ptR = BLOCKS_GF2VEC(vr);
    nrb = NUMBER_BLOCKS_GF2VEC(vl);
    n   = 0;
    for ( i = 1;  i <= nrb;  i++ ) {
        m = (*ptL++) & (*ptR++);
        PARITY_BLOCK(m);
        n ^= m;
    }

    /* return the result                                                   */
    return (n & 1) ? GF2One : GF2Zero;
}


/****************************************************************************
**
*F  ProdGF2VecGF2Mat( <vl>, <vr> )  . .  product of GF2 vector and GF2 matrix
**
**  'ProdGF2VecGF2Mat'  returns the product  of the  GF2 vector <vl>  and the
**  GF2 matrix  <vr>.   The product is   the sum of  the  rows of <vr>,  each
**  multiplied by the corresponding entry of <vl>.  Note that the  caller has
**  to ensure, that <vl> is a gf2-vector and <vr> is a gf2-matrix.
*/
Obj ProdGF2VecGF2Mat ( vl, vr )
    Obj                 vl;
    Obj                 vr;
{
    UInt                len;            /* length of the list              */
    UInt                stop;
    UInt                col;            /* length of the rows              */
    UInt                i;              /* loop variables                  */
    Obj                 prod;           /* product, result                 */
    UInt *              start;
    UInt *              end;
    UInt *              ptL;
    UInt                mask;
    
    /* both operands lie in the same field                                 */
    len = LEN_GF2VEC(vl);
    if ( len != LEN_GF2MAT(vr) ) {
      ErrorQuit(
        "Vector *: <right> must have the same length as <left> (%d not %d)",
        len, (Int)LEN_GF2MAT(vr) );
      return 0;
    }

    /* make the result vector                                              */
    col = LEN_GF2VEC( ELM_GF2MAT( vr, 1 ) );
    NEW_GF2VEC( prod, (IS_MUTABLE_OBJ(vl) || IS_MUTABLE_OBJ(vr)) ? 
		TYPE_LIST_GF2VEC : TYPE_LIST_GF2VEC_IMM, col );
    SET_LEN_GF2VEC( prod, col );
    
    /* get the start and end block                                         */
    start = BLOCKS_GF2VEC(prod);
    ptL   = BLOCKS_GF2VEC(vl);
    end   = start + (col+BIPEB-1)/BIPEB;

    /* loop over the vector                                                */
    for ( i = 1;  i <= len;  ptL++ )  {

        /* if the whole block is zero, get the next entry                  */
        if (*ptL == 0) {
            i += BIPEB;
            continue;
        }
        
        /* run through the block                                           */
        stop = i + BIPEB - 1;
        if ( len < stop )
            stop = len;
        for ( mask = 1;  i <= stop;  i++, mask <<= 1 ) {

            /* if there is entry add the row to the result                 */
            if ( (*ptL & mask) != 0 ) {
                UInt * ptPP = start;
                UInt * ptRR = BLOCKS_GF2VEC(ELM_GF2MAT(vr,i));
                while ( ptPP < end ) 
                    *ptPP++ ^= *ptRR++;
            }
        }
    }

    /* return the result                                                   */
    return prod;
}


/****************************************************************************
**
*F  ProdGF2MatGF2Vec( <ml>, <vr> )  . .  product of GF2 matrix and GF2 vector
**
**  'ProdGF2MatGF2Vec'  returns the product  of the  GF2 matrix <ml>  and the
**  GF2 vector  <vr>.   The ith entry of the
**  product is the inner product of  the  ith row of <ml> with <vr>.
**  Note that the  caller has
**  to ensure, that <ml> is a GF2 matrix and <vr> is a GF2 vector.
*/
Obj ProdGF2MatGF2Vec ( ml, vr )
    Obj                 ml;
    Obj                 vr;
{
    UInt                len;            /* length of the vector            */
    UInt                ln2;            /* length of the matrix            */
    UInt *              ptL;            /* bit field of <ml>[j]            */
    UInt *              ptR;            /* bit field of <vr>               */
    UInt                nrb;            /* number of blocks in blist       */
    UInt                m;              /* number of bits in a block       */
    UInt                n;              /* number of bits in blist         */
    UInt                i;              /* loop variable                   */
    UInt                j;              /* loop variable                   */
    Obj                 prod;           /* result                          */
    
    /* both operands lie in the same field                                 */
    len = LEN_GF2VEC(vr);
    ln2 = LEN_GF2MAT(ml);
    if ( 0 == ln2 ) {
        return CopyObj(ml,0);
    }
    if ( len != LEN_GF2VEC(ELM_GF2MAT(ml,1)) ) {
     ErrorQuit(
      "Vector *: <left>[1] must have the same length as <right> (%d not %d)",
      len, (Int)LEN_GF2VEC(ELM_GF2MAT(vr,1)) );
     return 0;
    }

    /* make the result vector                                              */
    NEW_GF2VEC( prod, (IS_MUTABLE_OBJ(ELM_GF2MAT(ml,1)) || IS_MUTABLE_OBJ(vr)) ? 
		TYPE_LIST_GF2VEC :TYPE_LIST_GF2VEC_IMM, ln2 );
    SET_LEN_GF2VEC( prod, ln2 );

    /* loop over the entries and multiply                                  */
    nrb = NUMBER_BLOCKS_GF2VEC(vr);
    for ( j = 1;  j <= ln2;  j++ ) {
        ptL = BLOCKS_GF2VEC(ELM_GF2MAT(ml,j));
        ptR = BLOCKS_GF2VEC(vr);
        n   = 0;
        for ( i = 1;  i <= nrb;  i++ ) {
            m = (*ptL++) & (*ptR++);
            PARITY_BLOCK(m);
            n ^= m;
        }
        if ( n & 1 )
            BLOCK_ELM_GF2VEC(prod,j) |= MASK_POS_GF2VEC(j);
    }

    /* return the result                                                   */
    return prod;
}

/****************************************************************************
**
*F  ProdGF2MatGF2Mat( <ml>, <mr> )  . .  product of GF2 matrix and GF2 matrix
**
**  'ProdGF2MatGF2Mat'  returns the product  of the  GF2 matrix <vl>  and the
**  GF2 vector  <vr>.  This simply calls ProdGF2VecGF2Mat once on each row.
*/

Obj ProdGF2MatGF2Mat( Obj ml, Obj mr )
{
  Obj prod;
  UInt i;
  UInt len;
  Obj row;
  len = LEN_GF2MAT(ml);
  prod = NewBag(T_POSOBJ, SIZE_PLEN_GF2MAT(len));
  SET_LEN_GF2MAT(prod,len);
  TYPE_POSOBJ(prod) = TYPE_LIST_GF2MAT_IMM;
  for (i = 1; i <= len; i++)
    {
      row = ProdGF2VecGF2Mat(ELM_GF2MAT(ml,i),mr);
      SET_ELM_GF2MAT(prod,i,row);
    }
  return prod;
}


/****************************************************************************
**
*F  InverseGF2Mat( <mat> )  . . . . . . . . . . . . . . inverse of GF2 matrix
*/
Obj InverseGF2Mat (
    Obj                 mat )
{
    UInt                len;            /* dimension                       */
    Obj                 inv;            /* result                          */
    Obj                 row;            /* row vector                      */
    Obj                 old;            /* row from <mat>                  */
    Obj                 tmp;            /* temporary                       */
    UInt *              ptQ;            /* data block of <row>             */
    UInt *              ptP;            /* data block of source row        */
    UInt *              end;            /* end marker                      */
    UInt *              end2;           /* end marker                      */
    UInt                i;              /* loop variable                   */
    UInt                k;              /* loop variable                   */

    /* make a structural copy of <mat> as list of GF2 vectors              */
    len = LEN_GF2MAT(mat);
    if ( len == 0 ) {
        return CopyObj(mat,0);
    }
    
    tmp = NEW_PLIST( T_PLIST, len );
    for ( i = len;  0 < i;  i-- ) {
        old = ELM_GF2MAT( mat, i );
        NEW_GF2VEC( row, TYPE_LIST_GF2VEC_IMM, len );
        SET_LEN_GF2VEC( row, len );
        ptQ = BLOCKS_GF2VEC(old);
        ptP = BLOCKS_GF2VEC(row);
        end = ptP + ((len+BIPEB-1)/BIPEB);
        while ( ptP < end )
            *ptP++ = *ptQ++;
        SET_ELM_PLIST( tmp, i, row );
        CHANGED_BAG(tmp);
    }
    mat = tmp;
    

    /* create the identity matrix                                          */
    tmp = NEW_PLIST( T_PLIST, len );
    for ( i = len;  0 < i;  i-- ) {
        NEW_GF2VEC( row, IS_MUTABLE_OBJ(ELM_GF2MAT(mat,1)) ?
		    TYPE_LIST_GF2VEC : TYPE_LIST_GF2VEC_IMM, len );
        SET_LEN_GF2VEC( row, len );
        BLOCK_ELM_GF2VEC(row,i) |= MASK_POS_GF2VEC(i);
        SET_ELM_PLIST( tmp, i, row );
        CHANGED_BAG(tmp);
    }
    inv = tmp;

    /* now start with ( id | mat ) towards ( inv | id )                    */
    for ( k = 1;  k <= len;  k++ ) {

        /* find a nonzero entry in column <k>                              */
        for ( i = k;  i <= len;  i++ ) {
            row = ELM_PLIST( mat, i );
            if ( BLOCK_ELM_GF2VEC(row,k) & MASK_POS_GF2VEC(k) )
                break;
        }
        if ( i > len )  {
            return Fail;
        }
        if ( i != k )  {
            row = ELM_PLIST( mat, i );
            SET_ELM_PLIST( mat, i, ELM_PLIST( mat, k ) );
            SET_ELM_PLIST( mat, k, row );
            row = ELM_PLIST( inv, i );
            SET_ELM_PLIST( inv, i, ELM_PLIST( inv, k ) );
            SET_ELM_PLIST( inv, k, row );
        }
        
        /* clear entries                                                   */
        old = ELM_PLIST( mat, k );
        end = BLOCKS_GF2VEC(old) + ((len+BIPEB-1)/BIPEB);
        for ( i = 1;  i <= len;  i++ ) {
            if ( i == k )
                continue;
            row = ELM_PLIST( mat, i );
            if ( BLOCK_ELM_GF2VEC(row,k) & MASK_POS_GF2VEC(k) ) {

                /* clear <mat>                                             */
                ptQ = &(BLOCK_ELM_GF2VEC(row,k));
                ptP = &(BLOCK_ELM_GF2VEC(old,k));
                while ( ptP < end ) {
                    *ptQ++ ^= *ptP++;
                }

                /* modify <inv>                                            */
                row  = ELM_PLIST( inv, i );
                ptQ  = BLOCKS_GF2VEC(row);
                row  = ELM_PLIST( inv, k );
                ptP  = BLOCKS_GF2VEC(row);
                end2 = ptP + ((len+BIPEB-1)/BIPEB);
                while ( ptP < end2 ) {
                    *ptQ++ ^= *ptP++;
                }
            }
        }
    }

    /* convert list <inv> into a matrix                                    */
    ResizeBag( inv, SIZE_PLEN_GF2MAT(len) );
    for ( i = len;  0 < i;  i-- ) {
        SET_ELM_GF2MAT( inv, i, ELM_PLIST(inv,i) );
    }
    SET_LEN_GF2MAT( inv, len );
    RetypeBag( inv, T_POSOBJ );
    TYPE_POSOBJ( inv ) = IS_MUTABLE_OBJ(mat) ? TYPE_LIST_GF2MAT : TYPE_LIST_GF2MAT_IMM;
    return inv;
}


/****************************************************************************
**

*F * * * * * * * * * * * *  conversion functions  * * * * * * * * * * * * * *
*/


/****************************************************************************
**

*F  PlainGF2Vec( <list> ) . . .  . convert a GF2 vector into an ordinary list
**
**  'PlainGF2Vec' converts the GF2 vector <list> to a plain list.
*/
void PlainGF2Vec (
    Obj                 list )
{
    Int                 len;            /* length of <list>                */
    UInt                i;              /* loop variable                   */
    Obj                 first;          /* first entry                     */

    /* resize the list and retype it, in this order                        */
    len = LEN_GF2VEC(list);
    RetypeBag( list, IS_MUTABLE_OBJ(list) ? T_PLIST : T_PLIST+IMMUTABLE );
    GROW_PLIST( list, (UInt)len );
    SET_LEN_PLIST( list, len );

    /* keep the first entry because setting the second destroys the first  */
    first = ELM_GF2VEC(list,1);

    /* wipe out the first entry of the GF2 vector (which becomes the       */
    /* entry of the plain list, in case the list has length 1.             */
    if (len == 1)
      SET_ELM_PLIST( list, 2, 0 );
    
    /* replace the bits by 'GF2One' or 'GF2Zero' as the case may be        */
    /* this must of course be done from the end of the list backwards      */
    for ( i = len;  1 < i;  i-- )
        SET_ELM_PLIST( list, i, ELM_GF2VEC( list, i ) );
    SET_ELM_PLIST( list, 1, first );

    CHANGED_BAG(list);
}


/****************************************************************************
**
*F  PlainGF2Mat( <list> ) . . .  . convert a GF2 matrix into an ordinary list
**
**  'PlainGF2Mat' converts the GF2 matrix <list> to a plain list.
*/
void PlainGF2Mat (
    Obj                 list )
{
    Int                 len;            /* length of <list>                */
    UInt                i;              /* loop variable                   */

    /* resize the list and retype it, in this order                        */
    len = LEN_GF2MAT(list);
    RetypeBag( list, IS_MUTABLE_OBJ(list) ? T_PLIST : T_PLIST+IMMUTABLE );
    SET_LEN_PLIST( list, len );

    /* shift the entries to the left                                       */
    for ( i = 1;  i <= len;  i++ ) {
        SET_ELM_PLIST( list, i, ELM_GF2MAT( list, i ) );
    }
    SHRINK_PLIST( list, len );
    CHANGED_BAG(list);
}


/****************************************************************************
**
*F  ConvGF2Vec( <list> )  . . . . .  convert a list into a GF2 vector objects
*/
void ConvGF2Vec (
    Obj                 list )
{
    Int                 len;            /* logical length of the vector    */
    Int                 i;              /* loop variable                   */
    UInt                block;          /* one block of the boolean list   */
    UInt                bit;            /* one bit of a block              */
        
    /* already in the correct representation                               */
    if ( IS_GF2VEC_REP(list) ) {
        return;
    }

    /* change its representation                                           */
    len   = LEN_LIST(list);

    /* We may have to resize the bag now because a length 1
       plain list is shorter than a length 1 VECGF2 */
    if (SIZE_PLEN_GF2VEC(len) > SIZE_OBJ(list))
      ResizeBag( list, SIZE_PLEN_GF2VEC(len) );

    /* now do the work */
    block = 0;
    bit   = 1;
    for ( i = 1;  i <= len;  i++ ) {
        if ( VAL_FFE( ELM_LIST( list, i ) ) )
            block |= bit;
        bit = bit << 1;
        if ( bit == 0 || i == len ) {
            BLOCK_ELM_GF2VEC(list,i) = block;
            block = 0;
            bit   = 1;
        }
    }

    /* retype and resize bag                                               */
    ResizeBag( list, SIZE_PLEN_GF2VEC(len) );
    SET_LEN_GF2VEC( list, len );
    if ( HAS_FILT_LIST( list, FN_IS_MUTABLE ) )
        TYPE_DATOBJ( list ) = TYPE_LIST_GF2VEC;
    else
        TYPE_DATOBJ( list ) = TYPE_LIST_GF2VEC_IMM;
    RetypeBag( list, T_DATOBJ );
}


/****************************************************************************
**
*F  FuncCONV_GF2VEC( <self>, <list> ) . . . . . convert into a GF2 vector rep
*/
Obj FuncCONV_GF2VEC (
    Obj                 self,
    Obj                 list )
{
    /* check whether <blist> is a GF2 vector                               */
#if 0
    while ( ! Is(blist) ) {
        blist = ErrorReturnObj(
            "CONV_GF2VEC: <blist> must be a boolean list (not a %s)",
            (Int)TNAM_OBJ(blist), 0L,
            "you can return a blist for <blist>" );
    }
#endif
    ConvGF2Vec(list);

    /* return nothing                                                      */
    return 0;
}


/****************************************************************************
**
*F  FuncPLAIN_GF2VEC( <self>, <list> ) . . .  convert back into ordinary list
*/
Obj FuncPLAIN_GF2VEC (
    Obj                 self,
    Obj                 list )
{
    /* check whether <list> is a GF2 vector                                */
    while ( ! IS_GF2VEC_REP(list) ) {
        list = ErrorReturnObj(
            "PLAIN_GF2VEC: <list> must be a GF2 vector (not a %s)",
            (Int)TNAM_OBJ(list), 0L,
            "you can return a GF2 vector for <list>" );
    }
    PlainGF2Vec(list);

    /* return nothing                                                      */
    return 0;
}


/****************************************************************************
**

*F * * * * * * * * * * * * list access functions  * * * * * * * * * * * * * *
*/


/****************************************************************************
**

*F  FuncEQ_GF2VEC_GF2VEC( <self>, <vl>, <vr> )   test equality of GF2 vectors
*/
Obj FuncEQ_GF2VEC_GF2VEC (
    Obj                 self,
    Obj                 vl,
    Obj                 vr )
{
    UInt                i;              /* loop variable                   */
    UInt *              bl;             /* block of <vl>                   */
    UInt *              br;             /* block of <vr>                   */
    UInt                len;            /* length of the list              */

    /* get and check the length                                            */
    len = LEN_GF2VEC(vl);
    if ( len != LEN_GF2VEC(vr) ) {
        return False;
    }

    /* check all blocks                                                    */
    bl = BLOCKS_GF2VEC(vl);
    br = BLOCKS_GF2VEC(vr);
    for ( i = NUMBER_BLOCKS_GF2VEC(vl);  1 < i;  i--, bl++, br++ ) {
        if ( *bl != *br )
            return False;
    }

    /* The last block remains */

    /* Maybe it's a full block */
    if (len % BIPEB == 0 && *bl != *br)
      return False;

    /* Otherwise shift away the rubbish high bits */
    if (((*bl) << (BIPEB - len %BIPEB)) != 
	((*br) << (BIPEB - len %BIPEB)))
      return False;

    /* Finally */
    return True;
}


/****************************************************************************
**
*F  FuncLEN_GF2VEC( <self>, <list> )  . . . . . . . .  length of a GF2 vector
*/
Obj FuncLEN_GF2VEC (
    Obj                 self,
    Obj                 list )
{
    return INTOBJ_INT(LEN_GF2VEC(list));
}


/****************************************************************************
**

*F  FuncELM0_GF2VEC( <self>, <list>, <pos> )  . select an elm of a GF2 vector
**
**  'ELM0_GF2VEC'  returns the element at the  position  <pos> of the boolean
**  list <list>, or `Fail' if <list> has no assigned  object at <pos>.  It is
**  the  responsibility of  the caller to   ensure  that <pos> is  a positive
**  integer.
*/
Obj FuncELM0_GF2VEC (
    Obj                 self,
    Obj                 list,
    Obj                 pos )
{
    UInt                p;

    p = INT_INTOBJ(pos);
    if ( LEN_GF2VEC(list) < p ) {
        return Fail;
    }
    else {
        return ELM_GF2VEC( list, p );
    }
}


/****************************************************************************
**
*F  FuncELM_GF2VEC( <self>, <list>, <pos> ) . . select an elm of a GF2 vector
**
**  'ELM_GF2VEC' returns the element at the position <pos>  of the GF2 vector
**  <list>.   An  error  is signalled  if  <pos>  is  not bound.    It is the
**  responsibility of the caller to ensure that <pos> is a positive integer.
*/
Obj FuncELM_GF2VEC (
    Obj                 self,
    Obj                 list,
    Obj                 pos )
{
    UInt                p;

    p = INT_INTOBJ(pos);
    if ( LEN_GF2VEC(list) < p ) {
        ErrorReturnVoid(
            "List Element: <list>[%d] must have an assigned value",
            p, 0L, "you can return after assigning a value" );
        return ELM_LIST( list, p );
    }
    else {
        return ELM_GF2VEC( list, p );
    }
}


/****************************************************************************
**
*F  FuncELMS_GF2VEC( <self>, <list>, <poss> ) . . . sublist from a GF2 vector
**
**  'ELMS_GF2VEC' returns a new list containing  the elements at the position
**  given in    the   list  <poss> from  the   vector   <list>.   It  is  the
**  responsibility of the caller to ensure that <poss>  is dense and contains
**  only positive integers.  An error is signalled if an element of <poss> is
**  larger than the length of <list>.
*/
Obj FuncELMS_GF2VEC (
    Obj                 self,
    Obj                 list,
    Obj                 poss )
{
    Obj                 elms;           /* selected sublist, result        */
    Int                 lenList;        /* length of <list>                */
    UInt *              ptrD;           /* pointer destination             */
    UInt *              ptrS;           /* pointer source                  */
    Int                 lenPoss;        /* length of positions             */
    Int                 pos;            /* position as integer             */
    Int                 cut;            /* cut point in a <BIPEB> block    */
    Int                 inc;            /* increment in a range            */
    Int                 i;              /* loop variable                   */

    /* get the length of <list>                                            */
    lenList = LEN_GF2VEC(list);

    /* general code for arbritrary lists, which are ranges                 */
    if ( ! IS_RANGE(poss) ) {

        /* get the length of <positions>                                   */
        lenPoss = LEN_LIST(poss);

        /* make the result vector                                          */
        NEW_GF2VEC( elms, TYPE_LIST_GF2VEC, lenPoss );
        SET_LEN_GF2VEC( elms, lenPoss );

        /* loop over the entries of <positions> and select                 */
        for ( i = 1;  i <= lenPoss;  i++ ) {

            /* get next position                                           */
            pos = INT_INTOBJ( ELMW_LIST( poss, i ) );
            if ( lenList < pos ) {
                ErrorQuit( "List Elements: <list>[%d] must have a value",
                           pos, 0L );
                return 0;
            }

            /* assign the element into <elms>                              */
            if ( ELM_GF2VEC( list, pos ) == GF2One ) {
                BLOCK_ELM_GF2VEC(elms,i) |= MASK_POS_GF2VEC(i);
            }
        }

    }

    /* special code for ranges                                             */
    else {

        /* get the length of <positions>, the first elements, and the inc. */
        lenPoss = GET_LEN_RANGE(poss);
        pos = GET_LOW_RANGE(poss);
        inc = GET_INC_RANGE(poss);

        /* check that no <position> is larger than <lenList>               */
        if ( lenList < pos ) {
            ErrorQuit( "List Elements: <list>[%d] must have a value",
                       pos, 0L );
            return 0;
        }
        if ( lenList < pos + (lenPoss-1) * inc ) {
            ErrorQuit( "List Elements: <list>[%d] must have a value",
                       pos + (lenPoss-1) * inc, 0L );
            return 0;
        }

        /* make the result vector                                          */
        NEW_GF2VEC( elms, TYPE_LIST_GF2VEC, lenPoss );
        SET_LEN_GF2VEC( elms, lenPoss );

        /* special code for ranges with increment of one and perfect fit   */
        cut = (pos-1) % BIPEB;
        if ( inc == 1 && cut == 0 ) {
            ptrS = BLOCKS_GF2VEC(list) + ((pos-1)/BIPEB);
            ptrD = BLOCKS_GF2VEC(elms);
            for ( i = (lenPoss+BIPEB-1)/BIPEB;  0 < i;  i-- )
                *ptrD++ = *ptrS++;
        }

        /* special code for ranges with increment of one                   */
        else if ( inc == 1 ) {
            ptrS = BLOCKS_GF2VEC(list) + ((pos-1)/BIPEB);
            ptrD = BLOCKS_GF2VEC(elms);
            for ( i = lenPoss;  BIPEB <= i;  ptrD++, ptrS++, i -= BIPEB ) {
                *ptrD = (ptrS[0] >> cut) | (ptrS[1] << (BIPEB-cut));
            }
            if ( 0 < i )
                *ptrD = *ptrS >> cut;
	    if (BIPEB - cut < i)
	      *ptrD |= ptrS[1] << (BIPEB-cut);
        }

        /* loop over the entries of <positions> and select                 */
        else {
            for ( i = 1;  i <= lenPoss;  i++, pos += inc ) {
                if ( ELM_GF2VEC(list,pos) == GF2One ) {
                    BLOCK_ELM_GF2VEC(elms,i) |= MASK_POS_GF2VEC(i);
                }
            }
        }
    }

    /* return the result                                                   */
    return elms;
}


/****************************************************************************
**

*F  FuncASS_GF2VEC( <self>, <list>, <pos>, <elm> ) set an elm of a GF2 vector
**
**  'ASS_GF2VEC' assigns the element  <elm> at the position  <pos> to the GF2
**  vector <list>.
**
**  It is the responsibility of the caller  to ensure that <pos> is positive,
**  and that <elm> is not 0.
*/

static Obj ConvertToVectorRep;	/* BH: changed to static */

Obj FuncASS_GF2VEC (
    Obj                 self,
    Obj                 list,
    Obj                 pos,
    Obj                 elm )
{
    UInt                p;

    /* check that <list> is mutable                                        */
    if ( ! IS_MUTABLE_OBJ(list) ) {
        ErrorReturnVoid(
            "Lists Assignment: <list> must be a mutable list",
            0L, 0L,
            "you can return and ignore the assignment" );
        return 0;
    }

    /* get the position                                                    */
    p = INT_INTOBJ(pos);

    /* if <elm> is Z(2) or 0*Z(2) and the position is OK, keep rep         */
    if ( p <= LEN_GF2VEC(list)+1 ) {
        if ( LEN_GF2VEC(list)+1 == p ) {
            ResizeBag( list, SIZE_PLEN_GF2VEC(p) );
            SET_LEN_GF2VEC( list, p );
        }
        if ( EQ(GF2One,elm) ) {
            BLOCK_ELM_GF2VEC(list,p) |= MASK_POS_GF2VEC(p);
        }
        else if ( EQ(GF2Zero,elm) ) {
            BLOCK_ELM_GF2VEC(list,p) &= ~MASK_POS_GF2VEC(p);
        }
        else {
            PlainGF2Vec(list);
            SET_ELM_PLIST( list, p, elm );

	    /* might be GF(2^k) element, in which case we can do something */
	    CALL_1ARGS(ConvertToVectorRep, list);
        }
        
    }
    else {
        PlainGF2Vec(list);
        ASS_LIST( list, p, elm );
    }
    return 0;
}

/****************************************************************************
**
*F  FuncPLAIN_GF2MAT( <self>, <list> ) . . .  convert back into ordinary list
*/
Obj FuncPLAIN_GF2MAT (
    Obj                 self,
    Obj                 list )
{
    PlainGF2Mat(list);

    /* return nothing                                                      */
    return 0;
}


/****************************************************************************
**
*F  FuncASS_GF2MAT( <self>, <list>, <pos>, <elm> ) set an elm of a GF2 matrix
**
**  'ASS_GF2MAT' assigns the element  <elm> at the position  <pos> to the GF2
**  matrix <list>.
**
**  It is the responsibility of the caller  to ensure that <pos> is positive,
**  and that <elm> is not 0.
*/
Obj FuncASS_GF2MAT (
    Obj                 self,
    Obj                 list,
    Obj                 pos,
    Obj                 elm )
{
    UInt                p;

    /* check that <list> is mutable                                        */
    if ( ! IS_MUTABLE_OBJ(list) ) {
        ErrorReturnVoid(
            "Lists Assignment: <list> must be a mutable list",
            0L, 0L,
            "you can return and ignore the assignment" );
        return 0;
    }

    /* get the position                                                    */
    p = INT_INTOBJ(pos);

    /* if <elm> is a GF2 vector and the length is OK, keep the rep         */
    if ( ! IS_GF2VEC_REP(elm) || IS_MUTABLE_OBJ(elm) ) {
        PlainGF2Mat(list);
        ASS_LIST( list, p, elm );
    }
    else if ( p == 1 && 0 == LEN_GF2MAT(list) ) {
        ResizeBag( list, SIZE_PLEN_GF2MAT(p) );
        SET_ELM_GF2MAT( list, p, elm );
    }
    else if ( p > LEN_GF2MAT(list)+1 ) {
        PlainGF2Mat(list);
        ASS_LIST( list, p, elm );
    }
    else if ( LEN_GF2VEC(elm) == LEN_GF2VEC(ELM_GF2MAT(list,1)) ) {
        if ( LEN_GF2MAT(list)+1 == p ) {
            ResizeBag( list, SIZE_PLEN_GF2MAT(p) );
            SET_LEN_GF2MAT( list, p );
        }
        SET_ELM_GF2MAT( list, p, elm );
        CHANGED_BAG(list);
    }
    else {
        PlainGF2Mat(list);
        ASS_LIST( list, p, elm );
    }
    return 0;
}


/****************************************************************************
**

*F  FuncUNB_GF2VEC( <self>, <list>, <pos> ) . unbind position of a GF2 vector
**
**  'UNB_GF2VEC' unbind  the element at  the position  <pos> in  a GF2 vector
**  <list>.
**
**  It is the responsibility of the caller  to ensure that <pos> is positive.
*/
Obj FuncUNB_GF2VEC (
    Obj                 self,
    Obj                 list,
    Obj                 pos )
{
    UInt                p;

    /* check that <list> is mutable                                        */
    if ( ! IS_MUTABLE_OBJ(list) ) {
        ErrorReturnVoid(
            "Lists Assignment: <list> must be a mutable list",
            0L, 0L,
            "you can return and ignore the assignment" );
        return 0;
    }

    /* get the position                                                    */
    p = INT_INTOBJ(pos);

    /* if we unbind the last position keep the representation              */
    if ( LEN_GF2VEC(list) < p ) {
        ;
    }
    else if ( LEN_GF2VEC(list) == p ) {
        ResizeBag( list, SIZE_PLEN_GF2VEC(p-1) );
        SET_LEN_GF2VEC( list, p-1 );
    }
    else {
        PlainGF2Vec(list);
        UNB_LIST( list, p );
    }
    return 0;
}


/****************************************************************************
**
*F  FuncUNB_GF2MAT( <self>, <list>, <pos> ) . unbind position of a GF2 matrix
**
**  'UNB_GF2VEC' unbind  the element at  the position  <pos> in  a GF2 matrix
**  <list>.
**
**  It is the responsibility of the caller  to ensure that <pos> is positive.
*/
Obj FuncUNB_GF2MAT (
    Obj                 self,
    Obj                 list,
    Obj                 pos )
{
    UInt                p;

    /* check that <list> is mutable                                        */
    if ( ! IS_MUTABLE_OBJ(list) ) {
        ErrorReturnVoid(
            "Lists Assignment: <list> must be a mutable list",
            0L, 0L,
            "you can return and ignore the assignment" );
        return 0;
    }

    /* get the position                                                    */
    p = INT_INTOBJ(pos);

    /* if we unbind the last position keep the representation              */
    if ( LEN_GF2MAT(list) < p ) {
        ;
    }
    else if ( LEN_GF2VEC(list) == p ) {
        ResizeBag( list, SIZE_PLEN_GF2MAT(p-1) );
        SET_LEN_GF2MAT( list, p-1 );
    }
    else {
        PlainGF2Vec(list);
        UNB_LIST( list, p );
    }
    return 0;
}


/****************************************************************************
**

*F * * * * * * * * * * * * arithmetic operations  * * * * * * * * * * * * * *
*/


/****************************************************************************
**

*F  FuncZERO_GF2VEC( <self>, <mat> )  . . . . . . . . . . . . zero GF2 vector
**
**  return the zero vector over GF2 of the same length as <mat>.
*/
Obj FuncZERO_GF2VEC (
    Obj                 self,
    Obj                 mat )
{
    Obj                 zero;
    UInt                len;

    /* create a new GF2 vector                                             */
    len = LEN_GF2VEC(mat);
    NEW_GF2VEC( zero, IS_MUTABLE_OBJ(mat) ? TYPE_LIST_GF2VEC : TYPE_LIST_GF2VEC_IMM, len );
    SET_LEN_GF2VEC( zero, len );
    return zero;
}


/****************************************************************************
**
*F  FuncINV_GF2MAT( <self>, <mat> ) . . . . . . . . . . .  inverse GF2 matrix
*/
Obj FuncINV_GF2MAT (
    Obj                 self,
    Obj                 mat )
{
    UInt                len;

    len = LEN_GF2MAT(mat);
    if ( len != 0 ) {
        if ( len != LEN_GF2VEC(ELM_GF2MAT(mat,1)) ) {
            mat = ErrorReturnObj( "<matrix> must be square", 0, 0,
                                  "you can return a square matrix" );
            return FuncINV_GF2MAT(self,mat);
        }
    }
    return InverseGF2Mat(mat);
}


/****************************************************************************
**
*F  FuncSUM_GF2VEC_GF2VEC( <self>, <vl>, <vr> ) . . . . .  sum of GF2 vectors
**
**  'FuncSUM_GF2VEC_GF2VEC' returns the sum  of the two gf2-vectors <vl>  and
**  <vr>.  The sum is a new gf2-vector, where each element is  the sum of the
**  corresponding entries of <vl>  and <vr>.  The  major work is done  in the
**  routine   'AddPartialGF2VecGF2Vec'     which     is         called   from
**  'FuncSUM_GF2VEC_GF2VEC'.
**
**  'FuncSUM_GF2VEC_GF2VEC'  is  an improved  version of 'SumListList', which
**  does not call 'SUM' but uses bit operations instead.
*/
Obj FuncSUM_GF2VEC_GF2VEC (
    Obj                 self,
    Obj                 vl,
    Obj                 vr )
{
    Obj                 sum;            /* sum, result                     */
    UInt                len;            /* length of the list              */

    /* get and check the length                                            */
    len = LEN_GF2VEC(vl);
    if ( len != LEN_GF2VEC(vr) ) {
      vr = ErrorReturnObj(
        "Vector +: <right> must have the same length as <left> (%d not %d)",
        len, (Int)LEN_GF2VEC(vr),
        "you can return a new list for <right>" );
      return SUM( vl, vr );
    }

    /* construct the result vector                                         */
    NEW_GF2VEC( sum, (IS_MUTABLE_OBJ(vl) || IS_MUTABLE_OBJ(vr)) ? 
		TYPE_LIST_GF2VEC :TYPE_LIST_GF2VEC_IMM, len );
    SET_LEN_GF2VEC( sum, len );

    /* and add the two argument vectors                                    */
    AddPartialGF2VecGF2Vec ( sum, vl, vr, 1 );
    return sum;
}

/****************************************************************************
**
*F  FuncMULT_ROW_VECTOR_GF2VECS_2( <self>, <vl>, <mul> )
**                                      . . . . .  sum of GF2 vectors
**
*/
Obj FuncMULT_ROW_VECTOR_GF2VECS_2 (
    Obj                 self,
    Obj                 vl,
    Obj                 mul )
{
    UInt                len;            /* length of the list              */
    if (EQ(mul,GF2One))
      return (Obj) 0;
    else if (EQ(mul,GF2Zero))
      {
	AddCoeffsGF2VecGF2Vec(vl,vl);
	return (Obj) 0;
      }
    else
      return TRY_NEXT_METHOD;
}


/****************************************************************************
**
*F  FuncPROD_GF2VEC_GF2VEC( <self>, <vl>, <vr> )  . .  product of GF2 vectors
**
**  'FuncPROD_GF2VEC_GF2VEC' returns the product of  the two GF2 vectors <vl>
**  and <vr>.  The product is either `GF2One' or `GF2Zero'.
*/
Obj FuncPROD_GF2VEC_GF2VEC (
    Obj                 self,
    Obj                 vl,
    Obj                 vr )
{
    return ProdGF2VecGF2Vec( vl, vr );
}


/****************************************************************************
**
*F  FuncPROD_GF2VEC_GF2MAT( <self>, <vl>, <vr> ) product of GF2 vector/matrix
**
**  'FuncPROD_GF2VEC_GF2MAT' returns  the product of the GF2 vectors <vl> and
**  the GF2 matrix <vr>.
**
**  The  product is  again a  GF2 vector.  It  is  the  responsibility of the
**  caller to ensure that <vl> is a  GF2 vector, <vr>  a GF2 matrix.
*/
Obj FuncPROD_GF2VEC_GF2MAT (
    Obj                 self,
    Obj                 vl,
    Obj                 vr )
{
    return ProdGF2VecGF2Mat( vl, vr );
}

/****************************************************************************
**
*F  FuncPROD_GF2MAT_GF2MAT( <self>, <ml>, <mr> ) product of GF2 vector/matrix
**
**  'FuncPROD_GF2MAT_GF2MAT' returns  the product of the GF2 matricess <ml> and
**  <mr>.
**
**  The  product is  again a  GF2 matrix.  It  is  the  responsibility of the
**  caller to ensure that <ml> and <mr> are  GF2 matrices
*/
Obj FuncPROD_GF2MAT_GF2MAT (
    Obj                 self,
    Obj                 ml,
    Obj                 mr )
{
    return ProdGF2MatGF2Mat( ml, mr );
}


/****************************************************************************
**
*F  FuncPROD_GF2MAT_GF2VEC( <self>, <vl>, <vr> ) product of GF2 matrix/vector
**
**  'FuncPROD_GF2VEC_GF2MAT' returns  the product of the GF2 matrix  <vl> and
**  the GF2 vector <vr>.
**
**  The  product is  again a  GF2 vector.  It  is  the  responsibility of the
**  caller to ensure that <vr> is a  GF2 vector, <vl>  a GF2 matrix.
*/
Obj FuncPROD_GF2MAT_GF2VEC (
    Obj                 self,
    Obj                 vl,
    Obj                 vr )
{
    return ProdGF2MatGF2Vec( vl, vr );
}


/****************************************************************************
**
*F  FuncADDCOEFFS_GF2VEC_GF2VEC_MULT( <self>, <vl>, <vr>, <mul> ) GF2 vectors
*/
Obj FuncADDCOEFFS_GF2VEC_GF2VEC_MULT (
    Obj                 self,
    Obj                 vl,
    Obj                 vr,
    Obj                 mul )
{
    /* do nothing if <mul> is zero                                         */
    if ( EQ(mul,GF2Zero) ) {
        return INTOBJ_INT( RightMostOneGF2Vec(vl) );
    }

    /* add if <mul> is one                                                 */
    if ( EQ(mul,GF2One) ) {
        return AddCoeffsGF2VecGF2Vec( vl, vr );
    }

    /* try next method                                                     */
    return TRY_NEXT_METHOD;
}

/****************************************************************************
**
*F  FuncADDCOEFFS_GF2VEC_GF2VEC_MULT( <self>, <vl>, <vr>, <mul>, <from>, <to> )
**  GF2 vectors
*/
Obj FuncADDCOEFFS_GF2VEC_GF2VEC_MULT_LIMS (
    Obj                 self,
    Obj                 vl,
    Obj                 vr,
    Obj                 mul )
{
    /* do nothing if <mul> is zero                                         */
    if ( EQ(mul,GF2Zero) ) {
        return INTOBJ_INT( RightMostOneGF2Vec(vl) );
    }

    /* add if <mul> is one                                                 */
    if ( EQ(mul,GF2One) ) {
        return AddCoeffsGF2VecGF2Vec( vl, vr );
    }

    /* try next method                                                     */
    return TRY_NEXT_METHOD;
}


/****************************************************************************
**
*F  FuncADDCOEFFS_GF2VEC_GF2VEC( <self>, <vl>, <vr> ) . . . . . . GF2 vectors
*/
Obj FuncADDCOEFFS_GF2VEC_GF2VEC (
    Obj                 self,
    Obj                 vl,
    Obj                 vr )
{
    return AddCoeffsGF2VecGF2Vec( vl, vr );
}


/****************************************************************************
**
*F  FuncSHRINKCOEFFS_GF2VEC( <self>, <vec> )  . . . . . remove trailing zeros
*/
Obj FuncSHRINKCOEFFS_GF2VEC (
    Obj                 self,
    Obj                 vec )
{
    UInt                len;
    UInt                nbb;
    UInt                onbb;
    UInt *              ptr;
    UInt		off;

    /* get length and number of blocks                                     */
    len = LEN_GF2VEC(vec);
    if ( len == 0 ) {
        return INTOBJ_INT(0);
    }

    nbb = ( len + BIPEB - 1 ) / BIPEB;
    onbb = nbb; 
    ptr = BLOCKS_GF2VEC(vec) + (nbb-1);
    off = BIPEB - (len%BIPEB);
    /* mask out the last bits */
#ifdef SYS_IS_64_BIT
    *ptr &= 0xffffffffffffffff >> off;
#else
    *ptr &= 0xffffffff >> off;
#endif

    /* find last non-trivial block */
    while ( 0 < nbb && ! *ptr ) {
        nbb--;
        ptr--;
    }
    /* did the block number change? */
    if (nbb < onbb) {
      len = nbb * BIPEB;
    }

    /* find position inside this block                   */
    /* we are guaranteed not to cross a block boundary ! */
    while ( 0 < len && ! ( *ptr & MASK_POS_GF2VEC(len) ) ) {
        len--;
    }
    ResizeBag( vec, SIZE_PLEN_GF2VEC(len) );
    SET_LEN_GF2VEC( vec, len );
    return INTOBJ_INT(len);
}

/****************************************************************************
**
*F  FuncPOSITION_NONZERO_GF2VEC( <self>, <vec>, <zero>) ..find first non-zero
**
**  The pointless zero argument is because this is a method for PositionNot
*/
Obj FuncPOSITION_NONZERO_GF2VEC(
    Obj                 self,
    Obj                 vec,
    Obj                 zero)
{
    UInt                len;
    UInt                nbb;
    UInt                nb;
    UInt *              ptr;
    UInt                pos;

    /* get length and number of blocks                                     */
    len = LEN_GF2VEC(vec);
    if ( len == 0 ) {
      return INTOBJ_INT(len+1);
    }

    /* find first non-trivial block                                         */
    nbb = 0;
    ptr = BLOCKS_GF2VEC(vec);
    nb = NUMBER_BLOCKS_GF2VEC(vec);
    while ( nbb < nb && ! *ptr ) {
        nbb++;
        ptr++;
    }

    /* find position inside this block                                     */
    pos = nbb * BIPEB + 1;
    while ( pos <= len && ! ( *ptr & MASK_POS_GF2VEC(pos) ) ) {
        pos++;
    }
    /* as the code is intended to run over, trailing 1's are innocent */
    if (pos <= len)
      return INTOBJ_INT(pos);
    else
      return INTOBJ_INT(len+1);
}


/****************************************************************************
**
*F  FuncAPPEND_VECGF2( <self>, <vecl>, <vecr> )
**
*/

Obj FuncAPPEND_VECGF2( Obj self, Obj vecl, Obj vecr )
{
  UInt lenl, lenr;
  UInt *ptrl;
  UInt *ptrr;
  UInt offl, nextr,off2;		/* 0 based */
  lenl = LEN_GF2VEC(vecl);
  lenr = LEN_GF2VEC(vecr);
  ResizeBag(vecl, SIZE_PLEN_GF2VEC(lenl+lenr));
  ptrl = BLOCKS_GF2VEC(vecl) + (lenl-1)/BIPEB;
  ptrr = BLOCKS_GF2VEC(vecr);
  offl = lenl % BIPEB;
  off2 = BIPEB - offl;
  nextr = 0;

  /* mask out the last bits */
#ifdef SYS_IS_64_BIT
  *ptrl &= 0xffffffffffffffff >> off2;
#else
  *ptrl &= 0xffffffff >> off2;
#endif

  while (nextr < lenr)
    {
      *ptrl |= (*ptrr) << offl;
      ptrl++;
      nextr += off2;
      if (nextr >= lenr -1)
	break;
      *ptrl = (*ptrr) >> off2;
      ptrr++;
      nextr += offl;
    }
  SET_LEN_GF2VEC(vecl,lenl+lenr);
  return (Obj) 0;
}

/****************************************************************************
**
*F  FuncSHALLOWCOPY_VECGF2( <self>, <vec> )
**
*/

Obj FuncSHALLOWCOPY_VECGF2( Obj self, Obj vec)
{
  Obj copy;
  UInt len;
  UInt *ptrS;
  UInt *ptrD;
  UInt *endS;
  len = LEN_GF2VEC(vec);
  NEW_GF2VEC( copy, TYPE_LIST_GF2VEC, len);
  SET_LEN_GF2VEC(copy,len);
  ptrS = BLOCKS_GF2VEC(vec);
  ptrD = BLOCKS_GF2VEC(copy);
  endS = ptrS + NUMBER_BLOCKS_GF2VEC(vec);
  while (ptrS < endS)
    *ptrD++ = *ptrS++;
  return copy;
}

/****************************************************************************
**
*F  FuncNUMBER_VECGF2( <self>, <vect> )
**
*/

/* A list of flip values for bytes (i.e. ..xyz -> zyx..) */
static const UInt1 revertlist [] ={
 0, 128, 64, 192, 32, 160, 96, 224, 16, 144, 80, 208, 48, 176, 112, 240, 8, 
  136, 72, 200, 40, 168, 104, 232, 24, 152, 88, 216, 56, 184, 120, 248, 4, 
  132, 68, 196, 36, 164, 100, 228, 20, 148, 84, 212, 52, 180, 116, 244, 12, 
  140, 76, 204, 44, 172, 108, 236, 28, 156, 92, 220, 60, 188, 124, 252, 2, 
  130, 66, 194, 34, 162, 98, 226, 18, 146, 82, 210, 50, 178, 114, 242, 10, 
  138, 74, 202, 42, 170, 106, 234, 26, 154, 90, 218, 58, 186, 122, 250, 6, 
  134, 70, 198, 38, 166, 102, 230, 22, 150, 86, 214, 54, 182, 118, 246, 14, 
  142, 78, 206, 46, 174, 110, 238, 30, 158, 94, 222, 62, 190, 126, 254, 1, 
  129, 65, 193, 33, 161, 97, 225, 17, 145, 81, 209, 49, 177, 113, 241, 9, 
  137, 73, 201, 41, 169, 105, 233, 25, 153, 89, 217, 57, 185, 121, 249, 5, 
  133, 69, 197, 37, 165, 101, 229, 21, 149, 85, 213, 53, 181, 117, 245, 13, 
  141, 77, 205, 45, 173, 109, 237, 29, 157, 93, 221, 61, 189, 125, 253, 3, 
  131, 67, 195, 35, 163, 99, 227, 19, 147, 83, 211, 51, 179, 115, 243, 11, 
  139, 75, 203, 43, 171, 107, 235, 27, 155, 91, 219, 59, 187, 123, 251, 7, 
  135, 71, 199, 39, 167, 103, 231, 23, 151, 87, 215, 55, 183, 119, 247, 15, 
  143, 79, 207, 47, 175, 111, 239, 31, 159, 95, 223, 63, 191, 127, 255
};

/* Takes an UInt a on n bits and returns the Uint obtained by reverting the
 * bits */
UInt revertbits(UInt a, Int n)
{
  UInt b,c;
  Int i;
  b=0;
  while (n>8) {
    c=a&0xff; /* last byte */
    a = a>>8;
    b = b<<8;
    b += (UInt) revertlist[(UInt1)c]; /* add flipped */
    n -=8;
  }
  /* cope with the last n bits */
  a &= 0xff;
  b= b<<n;
  c=(UInt) revertlist[(UInt1)a];
  c = c>> (8-n);
  b+=c;
  return b;
}

Obj FuncNUMBER_VECGF2( Obj self, Obj vec )
{
  UInt len,nd,i,nonz,head,a;
  UInt off,off2;		/* 0 based */
  Obj zahl;  /* the long number */
  UInt *num,*vp;
  len = LEN_GF2VEC(vec);
  num = BLOCKS_GF2VEC(vec) + (len-1)/BIPEB;
  off = len % BIPEB;
  off2 = BIPEB - off;

  /* mask out the last bits */
#ifdef SYS_IS_64_BIT
  *num &= 0xffffffffffffffff >> off2;
#else
  *num &= 0xffffffff >> off2;
#endif

  if (len <=NR_SMALL_INT_BITS) 
    /* it still fits into a small integer */
    return INTOBJ_INT(revertbits(*num,len));
  else {
    /* we might have to build a long integer */

    /* the number of words we need. A word is two digits */
    nd = ((len-1)/NR_DIGIT_BITS/2)+1;

    zahl = NewBag( T_INTPOS, (((nd+1)>>1)<<1)*sizeof(UInt) );
    /* +1)>>1)<<1: round up to next even number*/

    vp = (UInt*)ADDR_OBJ(zahl); /* the place we write to
    nonz=0; /* last non-zero position */
    i=1;

    if (off!=0) {
      head = revertbits(*num,off); /* the last 'off' bits, reverted */
      while (i<nd) {
	/* next word */
	num--;
	*vp = head; /* the bits left from last word */
	a = revertbits(*num,BIPEB); /* the full word reverted */
	head = a>>off2; /* next head: trailing `off' bits */
	a =a << off; /* the rest of the word */
	*vp |=a;
	if (*vp != 0) {nonz=i;} 
	vp++;
	i++;
      }
      *vp++ = head; /* last head bits */
      if (head !=0) {
	nonz=i; 
      }
    }
    else {
      while (i<=nd) {
        *vp=revertbits(*num--,BIPEB);
	if (*vp != 0) {nonz=i;} 
	vp++;
	i++;
      }
    }


    i=nd%2; 
    if (i==1) { 
      *vp=0; /* erase the trailing two digits if existing */
      nd++; /* point to the last position */
    }

    if ((nonz<=1)) {
      /* there were only entries in the first word. Can we make it a small
       * int? */
      num = (UInt*)ADDR_OBJ(zahl);
      if (0==(*num & (15<<NR_SMALL_INT_BITS))) {
	return INTOBJ_INT(*num);
      }
    }

    /* if there are mult. of 2 words of zero entries we have to remove them */
    if ((nd>2) && ((nd-1)>nonz)) {
      /* get the length */
      while ((nd>2) && ((nd-1)>nonz)) {
	nd -= 2;
      } 
      ResizeBag(zahl,nd*sizeof(UInt)); 

    }

    return zahl;
  }

}


/****************************************************************************
**
*F * * * * * * * * * * * * * initialize package * * * * * * * * * * * * * * *
*/


/****************************************************************************
**

*V  GVarFuncs . . . . . . . . . . . . . . . . . . list of functions to export
*/
static StructGVarFunc GVarFuncs [] = {

    { "CONV_GF2VEC", 1, "list",
      FuncCONV_GF2VEC, "src/vecgf2.c:CONV_GF2VEC" },

    { "PLAIN_GF2VEC", 1, "gf2vec",
      FuncPLAIN_GF2VEC, "src/vecgf2.c:PLAIN_GF2VEC" },

    { "PLAIN_GF2MAT", 1, "gf2mat",
      FuncPLAIN_GF2MAT, "src/vecgf2.c:PLAIN_GF2MAT" },

    { "EQ_GF2VEC_GF2VEC", 2, "gf2vec, gf2vec",
      FuncEQ_GF2VEC_GF2VEC, "src/vecgf2.c:EQ_GF2VEC_GF2VEC" },

    { "LEN_GF2VEC", 1, "gf2vec",
      FuncLEN_GF2VEC, "src/vecgf2.c:LEN_GF2VEC" },

    { "ELM0_GF2VEC", 2, "gf2vec, pos",
      FuncELM0_GF2VEC, "src/vecgf2.c:ELM0_GF2VEC" },

    { "ELM_GF2VEC", 2, "gf2vec, pos",
      FuncELM_GF2VEC, "src/vecgf2.c:ELM_GF2VEC" },

    { "ELMS_GF2VEC", 2, "gf2vec, poss",
      FuncELMS_GF2VEC, "src/vecgf2.c:ELMS_GF2VEC" },

    { "ASS_GF2VEC", 3, "gf2vec, pos, elm",
      FuncASS_GF2VEC, "src/vecgf2.c:ASS_GF2VEC" },

    { "ASS_GF2MAT", 3, "gf2mat, pos, elm",
      FuncASS_GF2MAT, "src/vecgf2.c:ASS_GF2MAT" },

    { "UNB_GF2VEC", 2, "gf2vec, pos",
      FuncUNB_GF2VEC, "src/vecgf2.c:UNB_GF2VEC" },

    { "UNB_GF2MAT", 2, "gf2mat, pos",
      FuncUNB_GF2MAT, "src/vecgf2.c:UNB_GF2MAT" },

    { "ZERO_GF2VEC", 1, "gf2vec",
      FuncZERO_GF2VEC, "src/vecgf2.c:ZERO_GF2VEC" },

    { "INV_GF2MAT", 1, "gf2mat",
      FuncINV_GF2MAT, "src/vecgf2.c:INV_GF2MAT" },

    { "SUM_GF2VEC_GF2VEC", 2, "gf2vec, gf2vec",
      FuncSUM_GF2VEC_GF2VEC, "src/vecgf2.c:SUM_GF2VEC_GF2VEC" },

    { "PROD_GF2VEC_GF2VEC", 2, "gf2vec, gf2vec",
      FuncPROD_GF2VEC_GF2VEC, "src/vecgf2.c:PROD_GF2VEC_GF2VEC" },

    { "PROD_GF2VEC_GF2MAT", 2, "gf2vec, gf2mat",
      FuncPROD_GF2VEC_GF2MAT, "src/vecgf2.c:PROD_GF2VEC_GF2MAT" },

    { "PROD_GF2MAT_GF2VEC", 2, "gf2mat, gf2vec",
      FuncPROD_GF2MAT_GF2VEC, "src/vecgf2.c:PROD_GF2MAT_GF2VEC" },

    { "PROD_GF2MAT_GF2MAT", 2, "gf2matl, gf2matr",
      FuncPROD_GF2MAT_GF2MAT, "src/vecgf2.c:PROD_GF2MAT_GF2MAT" },

    { "ADDCOEFFS_GF2VEC_GF2VEC_MULT", 3, "gf2vec, gf2vec, mul",
      FuncADDCOEFFS_GF2VEC_GF2VEC_MULT, "src/vecgf2.c:ADDCOEFFS_GF2VEC_GF2VEC_MULT" },

    { "ADDCOEFFS_GF2VEC_GF2VEC", 2, "gf2vec, gf2vec",
      FuncADDCOEFFS_GF2VEC_GF2VEC, "src/vecgf2.c:ADDCOEFFS_GF2VEC_GF2VEC" },

    { "SHRINKCOEFFS_GF2VEC", 1, "gf2vec",
      FuncSHRINKCOEFFS_GF2VEC, "src/vecgf2.c:SHRINKCOEFFS_GF2VEC" },

    { "POSITION_NONZERO_GF2VEC", 2, "gf2vec, zero",
      FuncPOSITION_NONZERO_GF2VEC, "src/vecgf2.c:POSITION_NONZERO_GF2VEC" },

    { "MULT_ROW_VECTOR_GF2VECS_2", 2, "gf2vecl, mul",
      FuncMULT_ROW_VECTOR_GF2VECS_2, "src/vecgf2.c:MULT_ROW_VECTOR_GF2VECS_2" },

    { "APPEND_GF2VEC", 2, "gf2vecl, gf2vecr",
      FuncAPPEND_VECGF2, "src/vecgf2.c:APPEND_GF2VEC" },

    { "SHALLOWCOPY_GF2VEC", 1, "gf2vec",
      FuncSHALLOWCOPY_VECGF2, "src/vecgf2.c:SHALLOWCOPY_GF2VEC" },

    { "NUMBER_GF2VEC", 1, "gf2vec",
      FuncNUMBER_VECGF2, "src/vecgf2.c:NUMBER_GF2VEC" },



    { 0 }

};


/****************************************************************************
**

*F  InitKernel( <module> )  . . . . . . . . initialise kernel data structures
*/
static Int InitKernel (
    StructInitInfo *    module )
{
    /* import kind functions                                               */
    ImportGVarFromLibrary( "TYPE_LIST_GF2VEC",     &TYPE_LIST_GF2VEC     );
    ImportGVarFromLibrary( "TYPE_LIST_GF2VEC_IMM", &TYPE_LIST_GF2VEC_IMM );
    ImportFuncFromLibrary( "IsGF2VectorRep",       &IsGF2VectorRep       );
    ImportGVarFromLibrary( "TYPE_LIST_GF2MAT",     &TYPE_LIST_GF2MAT     );
    ImportGVarFromLibrary( "TYPE_LIST_GF2MAT_IMM", &TYPE_LIST_GF2MAT_IMM );

    /* initialize one and zero of GF2                                      */
    ImportGVarFromLibrary( "GF2One",  &GF2One  );
    ImportGVarFromLibrary( "GF2Zero", &GF2Zero );

    /* init filters and functions                                          */
    InitHdlrFuncsFromTable( GVarFuncs );

    InitFopyGVar("ConvertToVectorRep", &ConvertToVectorRep);

    /* return success                                                      */
    return 0;
}


/****************************************************************************
**
*F  InitLibrary( <module> ) . . . . . . .  initialise library data structures
*/
static Int InitLibrary (
    StructInitInfo *    module )
{
    /* init filters and functions                                          */
    InitGVarFuncsFromTable( GVarFuncs );

    /* return success                                                      */
    return 0;
}


/****************************************************************************
**
*F  InitInfoGF2Vec()  . . . . . . . . . . . . . . . . table of init functions
*/
static StructInitInfo module = {
    MODULE_BUILTIN,                     /* type                           */
    "vecgf2",                           /* name                           */
    0,                                  /* revision entry of c file       */
    0,                                  /* revision entry of h file       */
    0,                                  /* version                        */
    0,                                  /* crc                            */
    InitKernel,                         /* initKernel                     */
    InitLibrary,                        /* initLibrary                    */
    0,                                  /* checkInit                      */
    0,                                  /* preSave                        */
    0,                                  /* postSave                       */
    0                                   /* postRestore                    */
};

StructInitInfo * InitInfoGF2Vec ( void )
{
    module.revision_c = Revision_vecgf2_c;
    module.revision_h = Revision_vecgf2_h;
    FillInVersion( &module );
    return &module;
}


/****************************************************************************
**

*E  vecgf2.c  . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
*/
