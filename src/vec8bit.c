#include        "system.h"              /* system dependent part           */

const char * Revision_vec8bit_c =
   "@(#)$Id$";

#include        <assert.h>
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

#include        "vector.h"              /* vectors */
#include        "listoper.h"              /* default list ops */

#define INCLUDE_DECLARATION_PART
#include        "vec8bit.h"              /* GFQ vectors                     */
#undef  INCLUDE_DECLARATION_PART

#include        "saveload.h"            /* saving and loading              */
#include        "opers.h"
#include        "integer.h"             /* integer functions needed for NUMBER_ */

/****************************************************************************
**
**
*H  There are two representations of GFQ vectors with entries packed into
**  bytes. The super-rep is IsVec8BitRep, which inherits from IsDataObjectRep
**  The 1st 4 bytes  stores the actual vector length (in field elements)
**  as a C integer. The 2nd component stores the field size as a C integer
**  The data bytes begin at the 3rd component
**  
**  The subrepresentation is for those fields of characteristic 2 where
**  vector addition over matching fields can be done by xor
**
**  In addition, this file defines format and access for the fieldinfo
**  objects which contain the meat-axe tables for the arithmetics
**
*/



/****************************************************************************
**
*F  IS_VEC8BIT_REP( <obj> )  . . . . . . check that <obj> is in 8bit GFQ vector rep
*/
static Obj IsVec8bitRep;

#define IS_VEC8BIT_REP(obj) \
  (TNUM_OBJ(obj)==T_DATOBJ && DoFilter(IsVec8bitRep,obj))



/****************************************************************************
**
*F  LEN_VEC8BIT( <vec> ) . . . . .. . . . . . . .length of an 8 bit GF vector
**
**  'LEN_VEC8BIT' returns the logical length of the 8bit GFQ vector <list>,
**  as a C integer.
**
**  Note that 'LEN_VEC8BIT' is a macro, so do not call it with  arguments that
**  have sideeffects.
*/
#define LEN_VEC8BIT(list)         ((Int)(ADDR_OBJ(list)[1]))

/****************************************************************************
**
*F  SET_LEN_VEC8BIT( <vec>, <len> )  . . . . set length of an 8 bit GF vector
**
**  'SET_LEN_VEC8BIT' sets the logical length of the 8bit GFQ vector <vec>,
**  to the C integer <len>.
**
*/
#define SET_LEN_VEC8BIT(list,len)         ((ADDR_OBJ(list)[1] = (Obj)(len)))

/****************************************************************************
**
*F  FIELD_VEC8BIT( <vec> ) . . . .. . . . . .field size of an 8 bit GF vector
**
**  'FIELD_VEC8BIT' returns the field size Q of the 8bit GFQ vector <list>,
**  as a C integer.
**
**  Note that 'FIELD_VEC8BIT' is a macro, so do not call it with  arguments
**  that have sideeffects.
*/

#define FIELD_VEC8BIT(list)         ((Int)(ADDR_OBJ(list)[2]))

/****************************************************************************
**
*F  SET_FIELD_VEC8BIT( <vec>, <q> )  . . set field size of an 8 bit GF vector
**
**  'SET_FIELD_VEC8BIT' sets the field size of the 8bit GFQ vector <vec>,
**  to the C integer <q>.
**
*/
#define SET_FIELD_VEC8BIT(list,q)         ((ADDR_OBJ(list)[2] = (Obj)(q)))


/****************************************************************************
**
*F  BYTES_VEC8BIT( <list> ) . . . . . . . . . first byte of a 8bit GFQ vector
**
**  returns a pointer to the start of the data of the 8bit GFQ vector
*/
#define BYTES_VEC8BIT(list)             ((UInt1*)(ADDR_OBJ(list)+3))


/****************************************************************************
**
*V  FieldInfo8Bit . .  . . . . . . . . .plain list (length 256) of field info
**
**  This list caches the field info used for the fast arithmetic
*/

static Obj FieldInfo8Bit;


/****************************************************************************
**
*F  Q_FIELDINFO_8BIT( <obj> )       . . . access to fields in structure
*F  P_FIELDINFO_8BIT( <obj> )
*F  ELS_BYTE_FIELDINFO_8BIT( <obj> )
*F  SETELT_FIELDINFO_8BIT( <obj> )
*F  GETELT_FIELDINFO_8BIT( <obj> )
*F  SCALMUL_FIELDINFO_8BIT( <obj> )
*F  ADD_FIELDINFO_8BIT( <obj> )
*F  SET_XXX_FIELDINFO_8BIOT( <obj>, <xxx> ) . . .setters needed by ANSI
**                                         needed for scalar but not pointers
**
**  For machines with alignment restrictions. it's important to put all
**  the word-sized data BEFORE all the byte-sized data (especially FFE_FELT...
**  which may have odd length
*/

#define Q_FIELDINFO_8BIT( info ) ((UInt)(ADDR_OBJ(info)[1]))
#define SET_Q_FIELDINFO_8BIT( info, q ) (ADDR_OBJ(info)[1] = (Obj)(q))
#define P_FIELDINFO_8BIT( info ) ((UInt)(ADDR_OBJ(info)[2]))
#define SET_P_FIELDINFO_8BIT( info, p ) (ADDR_OBJ(info)[2] = (Obj)(p))
#define D_FIELDINFO_8BIT( info ) ((UInt)(ADDR_OBJ(info)[3]))
#define SET_D_FIELDINFO_8BIT( info, d ) (ADDR_OBJ(info)[3] = (Obj)(d))
#define ELS_BYTE_FIELDINFO_8BIT( info ) ((UInt)(ADDR_OBJ(info)[4]))
#define SET_ELS_BYTE_FIELDINFO_8BIT( info, e ) (ADDR_OBJ(info)[4] = (Obj)(e))
#define FFE_FELT_FIELDINFO_8BIT( info ) (ADDR_OBJ(info)+5)
#define FELT_FFE_FIELDINFO_8BIT( info ) ((UInt1*)(FFE_FELT_FIELDINFO_8BIT(info)+Q_FIELDINFO_8BIT(info)))
#define SETELT_FIELDINFO_8BIT( info ) (FELT_FFE_FIELDINFO_8BIT( info ) + Q_FIELDINFO_8BIT(info))
#define GETELT_FIELDINFO_8BIT( info ) \
     (SETELT_FIELDINFO_8BIT(info) + \
      256*Q_FIELDINFO_8BIT(info)*ELS_BYTE_FIELDINFO_8BIT(info))
#define SCALAR_FIELDINFO_8BIT( info ) \
     (GETELT_FIELDINFO_8BIT(info)+256*ELS_BYTE_FIELDINFO_8BIT(info))
#define INNER_FIELDINFO_8BIT( info ) \
     (SCALAR_FIELDINFO_8BIT( info ) + 256*Q_FIELDINFO_8BIT(info))
#define ADD_FIELDINFO_8BIT( info ) \
     (INNER_FIELDINFO_8BIT( info ) + 256*256)




/****************************************************************************
**
*F SET_LEN_VEC8BIT( <list>, <len> ) .  set the logical length of a
*  8bit GFQ vector
**
**  'SET_LEN_VEC8BIT' sets the length of the boolean list  <list> to the value
**  <len>, which must be a positive C integer.
**
**  Note that 'SET_LEN_VEC8BIT' is a macro, so do  not  call it with arguments
** that have sideeffects.

#define SET_LEN_VEC8BIT(list,len)        (ADDR_OBJ(list)[1] = (Obj)(len)) 
*/

/****************************************************************************
**

*F * * * * * * * * * * * imported library variables * * * * * * * * * * * * *
*/


/****************************************************************************
**
*F  TypeVec8Bit( <q>, <mut> ) . . .  . . .type of a  vector object
**
*/
Obj TYPES_VEC8BIT;
Obj TYPE_VEC8BIT;

Obj TypeVec8Bit( UInt q, UInt mut)
{
  UInt col = mut ? 1 : 2;
  Obj type;
  type = ELM_PLIST(ELM_PLIST(TYPES_VEC8BIT, col),q);
  if (type == 0)
    return CALL_2ARGS(TYPE_VEC8BIT, INTOBJ_INT(q), mut ? True: False);
  else
    return type;
}



/****************************************************************************
**
*V  TYPE_FIELDINFO_8BIT
**
**  A type of data object with essentially no GAP visible semantics at all
**  
*/

Obj TYPE_FIELDINFO_8BIT;


#define SIZE_VEC8BIT(len,elts) (3*sizeof(UInt)+((len)+(elts)-1)/(elts))

/****************************************************************************
**									  
*V  GetFieldInfo( <q> ) . .make or recover the meataxe table for a field
**                         always call this, as the tables are lost by
**                         save/restore. It's very cheap if the table already
**                         exists
**
*/


static const UInt1 GF4Lookup[] =  {0,2,1,3};
static const UInt1 GF8Lookup[] =  {0, 4, 2, 1, 6, 3, 7, 5};

static const UInt1 GF16Lookup[] = {0, 8, 4, 2, 1, 12, 6, 3, 13, 10, 5,
14, 7, 15, 11, 9};

static const UInt1 GF32Lookup[] = {0, 16, 8, 4, 2, 1, 20, 10, 5, 22,
11, 17, 28, 14, 7, 23, 31, 27, 25, 24, 12, 6, 3, 21, 30, 15, 19, 29,
26, 13, 18, 9};

static const UInt1 GF64Lookup[] = { 0, 32, 16, 8, 4, 2, 1, 54, 27, 59,
43, 35, 39, 37, 36, 18, 9, 50, 25, 58, 29, 56, 28, 14, 7, 53, 44, 22,
11, 51, 47, 33, 38, 19, 63, 41, 34, 17, 62, 31, 57, 42, 21, 60, 30,
15, 49, 46, 23, 61, 40, 20, 10, 5, 52, 26, 13, 48, 24, 12, 6, 3, 55,
45 };

static const UInt1 GF128Lookup[] = { 0, 64, 32, 16, 8, 4, 2, 1, 96,
48, 24, 12, 6, 3, 97, 80, 40, 20, 10, 5, 98, 49, 120, 60, 30, 15, 103,
83, 73, 68, 34, 17, 104, 52, 26, 13, 102, 51, 121, 92, 46, 23, 107,
85, 74, 37, 114, 57, 124, 62, 31, 111, 87, 75, 69, 66, 33, 112, 56,
28, 14, 7, 99, 81, 72, 36, 18, 9, 100, 50, 25, 108, 54, 27, 109, 86,
43, 117, 90, 45, 118, 59, 125, 94, 47, 119, 91, 77, 70, 35, 113, 88,
44, 22, 11, 101, 82, 41, 116, 58, 29, 110, 55, 123, 93, 78, 39, 115,
89, 76, 38, 19, 105, 84, 42, 21, 106, 53, 122, 61, 126, 63, 127, 95,
79, 71, 67, 65 };

static const UInt1 GF256Lookup[] = { 0, 128, 64, 32, 16, 8, 4, 2, 1,
184, 92, 46, 23, 179, 225, 200, 100, 50, 25, 180, 90, 45, 174, 87,
147, 241, 192, 96, 48, 24, 12, 6, 3, 185, 228, 114, 57, 164, 82, 41,
172, 86, 43, 173, 238, 119, 131, 249, 196, 98, 49, 160, 80, 40, 20,
10, 5, 186, 93, 150, 75, 157, 246, 123, 133, 250, 125, 134, 67, 153,
244, 122, 61, 166, 83, 145, 240, 120, 60, 30, 15, 191, 231, 203, 221,
214, 107, 141, 254, 127, 135, 251, 197, 218, 109, 142, 71, 155, 245,
194, 97, 136, 68, 34, 17, 176, 88, 44, 22, 11, 189, 230, 115, 129,
248, 124, 62, 31, 183, 227, 201, 220, 110, 55, 163, 233, 204, 102, 51,
161, 232, 116, 58, 29, 182, 91, 149, 242, 121, 132, 66, 33, 168, 84,
42, 21, 178, 89, 148, 74, 37, 170, 85, 146, 73, 156, 78, 39, 171, 237,
206, 103, 139, 253, 198, 99, 137, 252, 126, 63, 167, 235, 205, 222,
111, 143, 255, 199, 219, 213, 210, 105, 140, 70, 35, 169, 236, 118,
59, 165, 234, 117, 130, 65, 152, 76, 38, 19, 177, 224, 112, 56, 28,
14, 7, 187, 229, 202, 101, 138, 69, 154, 77, 158, 79, 159, 247, 195,
217, 212, 106, 53, 162, 81, 144, 72, 36, 18, 9, 188, 94, 47, 175, 239,
207, 223, 215, 211, 209, 208, 104, 52, 26, 13, 190, 95, 151, 243, 193,
216, 108, 54, 27, 181, 226, 113};

static const UInt1 PbyQ[] = { 0, 1, 2, 3, 2, 5, 0, 7, 2, 3, 0, 11, 0,
13, 0, 0, 2, 17, 0, 19, 0, 0, 0, 23, 0, 5, 0, 3, 0, 29, 0, 31, 2, 0,
0, 0, 0, 37, 0, 0, 0, 41, 0, 43, 0, 0, 0, 47, 0, 7, 0, 0, 0, 53, 0, 0,
0, 0, 0, 59, 0, 61, 0, 0, 2, 0, 0, 67, 0, 0, 0, 71, 0, 73, 0, 0, 0, 0,
0, 79, 0, 3, 0, 83, 0, 0, 0, 0, 0, 89, 0, 0, 0, 0, 0, 0, 0, 97, 0, 0,
0, 101, 0, 103, 0, 0, 0, 107, 0, 109, 0, 0, 0, 113, 0, 0, 0, 0, 0, 0,
0, 11, 0, 0, 0, 5, 0, 127, 2, 0, 0, 131, 0, 0, 0, 0, 0, 137, 0, 139,
0, 0, 0, 0, 0, 0, 0, 0, 0, 149, 0, 151, 0, 0, 0, 0, 0, 157, 0, 0, 0,
0, 0, 163, 0, 0, 0, 167, 0, 13, 0, 0, 0, 173, 0, 0, 0, 0, 0, 179, 0,
181, 0, 0, 0, 0, 0, 0, 0, 0, 0, 191, 0, 193, 0, 0, 0, 197, 0, 199, 0,
0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 211, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
223, 0, 0, 0, 227, 0, 229, 0, 0, 0, 233, 0, 0, 0, 0, 0, 239, 0, 241,
0, 3, 0, 0, 0, 0, 0, 0, 0, 251, 0, 0, 0, 0, 2 };

static const UInt1 DbyQ[] = { 0, 1, 1, 1, 2, 1, 0, 1, 3, 2, 0, 1, 0,
1, 0, 0, 4, 1, 0, 1, 0, 0, 0, 1, 0, 2, 0, 3, 0, 1, 0, 1, 5, 0, 0, 0,
0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0,
1, 0, 1, 0, 0, 6, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 4,
0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0,
0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 1,
7, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1,
0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0,
1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0,
5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8};



static const UInt1 * Char2Lookup[9] = {
  0L, 0L,
  GF4Lookup,
  GF8Lookup,
  GF16Lookup,
  GF32Lookup,
  GF64Lookup,
  GF128Lookup,
  GF256Lookup};

Obj GetFieldInfo8Bit( UInt q)
{
  FF   gfq;			/* the field */
  UInt p;			/* characteristic */
  UInt d;			/* degree */
  UInt i,j,k;			/* loop variables */
  UInt e;			/* number of elements per byte */
  UInt size;			/* data structure size */
  UInt pows[7];  		/* table of powers of q for packing
				   and unpacking bytes */
  Obj info;			/* The table being constructed */
  FFV mult;			/* multiplier for scalar product */
  FFV prod;			/* used in scalar product */
  UInt val;                     /* used to build up some answers */
  UInt elt,el1,el2;             /* used to build up some answers */
  FFV *succ;
  
  assert(2< q && q <= 256);
  
  /*  if the answer not stored, we have to compute it */
  if (ELM_PLIST(FieldInfo8Bit, q ) == 0)
    {
      p = (UInt)PbyQ[q];
      d = (UInt)DbyQ[q];
      gfq = FiniteField(p,d);
      e = 0;
      for (i = 1; i <= 256; i *= q)
	pows[e++] = i;
      pows[e] = i;		/* simplifies things to have one more */
      e--;
      
      size = sizeof(Obj) +	/* type */
	sizeof(Obj) +		/* q */
	sizeof(Obj) +		/* p */
	sizeof(Obj) +           /* d */
	sizeof(Obj) +		/* els per byte */
	q +			/* numbering from FFV */
	q*sizeof(Obj) +		/* immediate FFE by number */
	256*q*e +		/* set element lookup */
	256*e +			/* get element lookup */
	256*q +                 /* scalar multiply */
	256*256 +               /* inner product */
	((p == 2) ? 0 : (256*256));	/* add byte */
      info = NewBag(T_DATOBJ, size);
      TYPE_DATOBJ(info) = TYPE_FIELDINFO_8BIT;

      /* from here to the end, no garbage collections should happen */
      succ = SUCC_FF(gfq);
      SET_Q_FIELDINFO_8BIT(info,q);
      SET_P_FIELDINFO_8BIT(info, p);
      SET_D_FIELDINFO_8BIT(info, d);
      SET_ELS_BYTE_FIELDINFO_8BIT(info, e);

      /* conversion tables FFV to/from our numbering
	 we assume that 0 and 1 are always the zero and one
	 of the field. In char 2, we assume that xor corresponds
	 to addition, otherwise, the order doesn't matter */
      
      if (p != 2)		
	for (i = 0; i < q; i++)
	  FELT_FFE_FIELDINFO_8BIT(info)[i] = (UInt1)i;
      else			
	for (i = 0; i < q; i++)
	  FELT_FFE_FIELDINFO_8BIT(info)[i] = Char2Lookup[d][i];

      /* simply invert the permutation to get the other one */
      for (i = 0; i < q; i++)
	FFE_FELT_FIELDINFO_8BIT(info)[FELT_FFE_FIELDINFO_8BIT(info)[i]] =
	  NEW_FFE(gfq,i);

      /* entry setting table SETELT...[(i*e+j)*256 +k] is the result
	 of overwriting the jth element with i in the byte k */
      for (i = 0; i < q; i++)
	for (j = 0; j < e; j++)
	  for (k = 0; k < 256; k++)
	    SETELT_FIELDINFO_8BIT(info)[(i*e + j)*256 + k] = (UInt1)
	      ((k/pows[j+1])*pows[j+1] + i*pows[j] + (k % pows[j]));

      /* entry access GETELT...[i*256+j] recovers the ith entry from the
	 byte j */
      for (i = 0; i < e; i++)
	for(j = 0; j < 256; j++)
	  GETELT_FIELDINFO_8BIT(info)[i*256 + j] = (UInt1)(j/pows[i])%q;

      /* scalar * vector multiply SCALAR...[i*256+j] is the scalar
	 product of the byte j with the felt i */
      for (i = 0; i < q; i++)
	{
	  mult = VAL_FFE(FFE_FELT_FIELDINFO_8BIT(info)[i]);
	  for(j = 0; j < 256; j++)
	    {
	      val = 0;
	      for (k  = 0; k < e; k++)
		{
		  elt = VAL_FFE(FFE_FELT_FIELDINFO_8BIT(info)
				[GETELT_FIELDINFO_8BIT(info)[k*256+j]]);
		  prod = PROD_FFV(elt,mult,succ);
		  val += pows[k]*FELT_FFE_FIELDINFO_8BIT(info)[prod];
		}
	      SCALAR_FIELDINFO_8BIT(info)[i*256+j] = val;
	    }
	}

      /* inner product INNER...[i+256*j] is the felt which is the contribution
	 to the inner product of bytes i and j */

      for ( i = 0; i < 256; i++)
	for (j = i; j < 256; j++)
	  {
	    val = 0;
	    for (k = 0; k < e; k++)
	      {
		el1 = VAL_FFE(FFE_FELT_FIELDINFO_8BIT(info)
			      [GETELT_FIELDINFO_8BIT(info)[k*256+i]]);
		el2 = VAL_FFE(FFE_FELT_FIELDINFO_8BIT(info)
			      [GETELT_FIELDINFO_8BIT(info)[k*256+j]]);
		elt = PROD_FFV( el1, el2, succ);
		val = SUM_FFV(val, elt, succ);
	      }
	    val = FELT_FFE_FIELDINFO_8BIT(info)[val];
	    INNER_FIELDINFO_8BIT(info)[i+256*j] = val;
	    INNER_FIELDINFO_8BIT(info)[j+256*i] = val;
	  }
	    
      /* In odd characteristic, we need the addition table
	 ADD...[i*256+j] is the vector sum of bytes i and j */
      if (p != 2)
	{
	  for (i = 0; i < 256; i++)
	    for (j = i; j < 256; j++)
	      {
		val = 0;
		for (k = 0; k < e; k++)
		  {
		    el1 = VAL_FFE(FFE_FELT_FIELDINFO_8BIT(info)
				  [GETELT_FIELDINFO_8BIT(info)[k*256+i]]);
		    el2 = VAL_FFE(FFE_FELT_FIELDINFO_8BIT(info)
				  [GETELT_FIELDINFO_8BIT(info)[k*256+j]]);
		    val += pows[k]*
		      FELT_FFE_FIELDINFO_8BIT(info)[SUM_FFV(el1,el2, succ)];
		  }
		ADD_FIELDINFO_8BIT(info)[i+256*j] = val;
		ADD_FIELDINFO_8BIT(info)[j+256*i] = val;
	      }
	}
      

      /* remember the result */
      SET_ELM_PLIST(FieldInfo8Bit,q,info);
      CHANGED_BAG(FieldInfo8Bit);
    }
  info = ELM_PLIST(FieldInfo8Bit,q);
  /*  assert(SCALAR_FIELDINFO_8BIT(info)[512+q-1] != 0); */
  return info;
}
     



/****************************************************************************
**
*F  ConvVec8Bit( <list> )  . .  . . .  convert a list into 8bit vector object
*/

void ConvVec8Bit (
    Obj                 list,
    UInt                q)
{
    Int                 len;            /* logical length of the vector    */
    Int                 i;              /* loop variable                   */
    UInt                p;	/* char */
    UInt                d;	/* degree */
    FF                  f;	/* field */
    Obj                 x;	/* an element */
    Obj                 info;	/* field info object */
    UInt                elts;	/* elements per byte */
    UInt1 *             settab;	/* element setting table */
    UInt1 *             convtab; /* FFE -> FELT conversion table */
    Obj                 firstthree[3]; /* the first three entries
					may get clobbered my the early bytes */
    UInt                e;	/* loop varibale */
    UInt1               byte;	/* byte under construction */
    UInt1*              ptr;	/* place to put byte */
    Obj                elt;
    UInt               val;
    UInt               nsize;
        
    /* already in the correct representation                               */
    if ( IS_VEC8BIT_REP(list) ) {
        return;
    }
    len   = LEN_LIST(list);

    /* we used to be able to  be called on any dense homogenous list of FFEs
       we need to check that they all lie in a small enough field
       this check passes to the caller now*/
    
    if (q > 256)
      ErrorQuit("Field size %d is too much for 8 bits\n",
		q, 0L);
    if (q == 2)
      ErrorQuit("GF2 has its own representation\n",0L,0L);

    
    /* OK, so now we know which field we want, set up data */
    info = GetFieldInfo8Bit(q);
    p = P_FIELDINFO_8BIT(info);
    d = D_FIELDINFO_8BIT(info);
    f = FiniteField(p,d);
    
    elts = ELS_BYTE_FIELDINFO_8BIT(info);
    settab = SETELT_FIELDINFO_8BIT(info);
    convtab = FELT_FFE_FIELDINFO_8BIT(info);

    /* We may need to resize first, as small lists get BIGGER
       in this process */
    nsize = SIZE_VEC8BIT(len,elts);
    if (nsize > SIZE_OBJ(list))
      ResizeBag(list,nsize);
    
    /* writing the first byte may clobber the third list entry
       before we have read it, so we take a copy */
    firstthree[0] = ELM0_LIST(list,1);
    firstthree[1] = ELM0_LIST(list,2);
    firstthree[2] = ELM0_LIST(list,3);
    
    /* main loop -- e is the element within byte */
    e = 0;
    byte = 0;
    ptr = BYTES_VEC8BIT(list);
    for ( i = 1;  i <= len;  i++ ) {
      elt = (i <= 3) ? firstthree[i-1] : ELM_LIST(list,i);
      assert(CHAR_FF(FLD_FFE(elt)) == p);
      assert( d % DegreeFFE(elt) == 0);
      val = VAL_FFE(elt);
      if (val != 0 && FLD_FFE(elt) != f)
	{
	  val = 1+(val-1)*(q-1)/(SIZE_FF(FLD_FFE(elt))-1);
	}
      byte = settab[(e + elts*convtab[val])*256 + byte];
      if (++e == elts || i == len)
	{
	  *ptr++ = byte;
	  byte = 0;
	  e = 0;
	}
    }

    /* retype and resize bag */
    if (nsize != SIZE_OBJ(list))
      ResizeBag( list, nsize );
    SET_LEN_VEC8BIT( list, len );
    SET_FIELD_VEC8BIT(list, q );
    TYPE_DATOBJ( list ) =
      TypeVec8Bit( q, HAS_FILT_LIST( list, FN_IS_MUTABLE));
    RetypeBag( list, T_DATOBJ );
}


/****************************************************************************
**
*F  FuncCONV_VEC8BIT( <self>, <list> ) . . . . . convert into 8bit vector rep
*/
Obj FuncCONV_VEC8BIT (
    Obj                 self,
    Obj                 list,
    Obj                 q)
{
  ConvVec8Bit(list, INT_INTOBJ(q));
  
  /* return nothing                                                      */
  return 0;
}


/****************************************************************************
**
*F  PlainVec8Bit( <list> ) . . . convert an 8bit vector into an ordinary list
**
**  'PlainVec8Bit' converts the  vector <list> to a plain list.
*/
    
void PlainVec8Bit (
    Obj                 list )
{
    Int                 len;            /* length of <list>                */
    UInt                i;              /* loop variable                   */
    Obj                 first;          /* first entry                     */
    Obj                 second;
    UInt                q;
    UInt                p;
    UInt                d;
    UInt                elts;
    FF                  field;
    Obj                 info;
    UInt1              *gettab;

    /* resize the list and retype it, in this order                        */
    len = LEN_VEC8BIT(list);
    q = FIELD_VEC8BIT(list);
    info = GetFieldInfo8Bit(q);
    elts = ELS_BYTE_FIELDINFO_8BIT(info);
    p = P_FIELDINFO_8BIT(info);
    d = D_FIELDINFO_8BIT(info);
    field = FiniteField(p,d);
    
    RetypeBag( list, IS_MUTABLE_OBJ(list) ? T_PLIST_FFE :
	       T_PLIST_FFE+IMMUTABLE );
    GROW_PLIST( list, (UInt)len );
    SET_LEN_PLIST( list, len );

    gettab = GETELT_FIELDINFO_8BIT(info);
    /* keep the first two entries
       because setting the third destroys them  */
    first = FFE_FELT_FIELDINFO_8BIT(info)[gettab[BYTES_VEC8BIT(list)[0]]];
    if (len > 1)
      second =
	FFE_FELT_FIELDINFO_8BIT(info)
	 [gettab[256*(1 % elts)+BYTES_VEC8BIT(list)[1/elts]]];

    /* replace the bits by FF elts as the case may be        */
    /* this must of course be done from the end of the list backwards      */
    for ( i = len;  2 < i;  i-- )
        SET_ELM_PLIST( list, i,
		       FFE_FELT_FIELDINFO_8BIT(info)
		       [gettab[256*((i-1)%elts)+
			      BYTES_VEC8BIT( list )[ (i-1) /elts]]] );
    if (len > 1)
      SET_ELM_PLIST( list, 2, second );
    SET_ELM_PLIST( list, 1, first );

    /* Null out any entries after the end of valid data */
    for (i = len+1; i < (SIZE_BAG(list)+sizeof(Obj) -1 ) /sizeof(Obj); i++)
      SET_ELM_PLIST(list, i, (Obj) 0);
    
    CHANGED_BAG(list);
}

/****************************************************************************
**
*F  FuncPLAIN_VEC8BIT( <self>, <list> ) . . .  convert back into ordinary list
*/
Obj FuncPLAIN_VEC8BIT (
    Obj                 self,
    Obj                 list )
{
    /* check whether <list> is an 8bit vector                                */
    while ( ! IS_VEC8BIT_REP(list) ) {
        list = ErrorReturnObj(
            "CONV_BLIST: <list> must be an 8bit vector (not a %s)",
            (Int)TNAM_OBJ(list), 0L,
            "you can return an 8bit vector for <list>" );
    }
    PlainVec8Bit(list);

    /* return nothing                                                      */
    return 0;
}


/****************************************************************************
**
*F * * * * * * * * * * * * arithmetic operations  * * * * * * * * * * * * * *
*/

#define NUMBLOCKS_VEC8BIT(len,elts) \
        (((len) + sizeof(UInt)*(elts)-1)/(sizeof(UInt)*(elts)))

#define BLOCKS_VEC8BIT(vec) ((UInt *)BYTES_VEC8BIT(vec))     


/****************************************************************************
**
*F  AddVec8BitVec8BitInner( <sum>, <vl>, <vr>, <start>, <stop> )
**
**  This is the real vector add routine. Others are all calls to this
**  one.
**  Addition is done from THE BLOCK containing <start> to the one
**  containing <stop> INCLUSIVE. The remainder of <sum> is unchanged.
**  <sum> may be the same vector as <vl> or
**  <vr>. <vl> and <vr> must be over the same field and <sum> must be
**  initialized as a vector over this field of length at least <stop>.
**
*/

void  AddVec8BitVec8BitInner( Obj sum,
			      Obj vl,
			      Obj vr,
			      UInt start,
			      UInt stop )
{
  Obj info;
  UInt p;
  UInt elts;
  
  info = GetFieldInfo8Bit(FIELD_VEC8BIT(sum));
  assert(Q_FIELDINFO_8BIT(info) == FIELD_VEC8BIT(vl));
  assert(Q_FIELDINFO_8BIT(info) == FIELD_VEC8BIT(vr));
  assert(LEN_VEC8BIT(sum) >= stop);
  assert(LEN_VEC8BIT(vl) >= stop);
  assert(LEN_VEC8BIT(vr) >= stop);
  p = P_FIELDINFO_8BIT(info);
  elts = ELS_BYTE_FIELDINFO_8BIT(info);
  /* Convert from 1 based to zero based addressing */
  start --;
  stop --;
  if (p == 2)
    {
      UInt *ptrL2;
      UInt *ptrR2;
      UInt *ptrS2;
      UInt *endS2;
      ptrL2 = BLOCKS_VEC8BIT(vl) + start/(sizeof(UInt)*elts);
      ptrR2 = BLOCKS_VEC8BIT(vr) + start/(sizeof(UInt)*elts);
      ptrS2 = BLOCKS_VEC8BIT(sum) + start/(sizeof(UInt)*elts);
      endS2 = BLOCKS_VEC8BIT(sum) + stop/(sizeof(UInt)*elts)+1;
      while (ptrS2 < endS2)
	*ptrS2++ = *ptrL2++ ^ *ptrR2++;
    }
  else
    {
      UInt1 *ptrL;
      UInt1 *ptrR;
      UInt1 *ptrS;
      UInt1 *endS;
      UInt1 *addtab;
      addtab = ADD_FIELDINFO_8BIT(info);
      ptrL = BYTES_VEC8BIT(vl) + start/elts;
      ptrR = BYTES_VEC8BIT(vr) + start/elts;
      ptrS = BYTES_VEC8BIT(sum) + start/elts;
      endS = BYTES_VEC8BIT(sum) + stop/elts + 1;
      while (ptrS < endS)
	*ptrS++ = addtab[256* (*ptrL++) + *ptrR++];
    }
  return;
}

/****************************************************************************
**
*F  SumVec8BitVec8Bit( <vl>, <vr> )
**
**  This is perhaps the simplest wrapper for the Add..Inner function
**  it allocates a new vector for the result, and adds the whole vectors into
**  it. No checking is done. The result follows the new mutability convention
**  (mutable if either argument is).
*/

Obj SumVec8BitVec8Bit( Obj vl, Obj vr )
{
  Obj sum;
  Obj info;
  UInt elts;
  UInt q;
  UInt len;
  q = FIELD_VEC8BIT(vl);
  len = LEN_VEC8BIT(vl);
  info = GetFieldInfo8Bit(q);
  elts = ELS_BYTE_FIELDINFO_8BIT(info);
  sum = NewBag(T_DATOBJ, SIZE_VEC8BIT(len,elts));
  SET_LEN_VEC8BIT(sum, len);
  TYPE_DATOBJ(sum) =
    TypeVec8Bit(q, IS_MUTABLE_OBJ(vl) || IS_MUTABLE_OBJ(vr));
  SET_FIELD_VEC8BIT(sum, q);
  CHANGED_BAG(sum);
  AddVec8BitVec8BitInner( sum, vl, vr, 1, len);
  return sum;
}

/****************************************************************************
**
*F  FuncSUM_VEC8BIT_VEC8BIT( <self>, <vl>, <vr> )
**
** This is the GAP callable method for +. The method installation should
** ensure that we have matching characteristics, but we may not have a common
** field or the same lengths
**
*/

static Obj ConvertToVectorRep;  /* BH: changed to static */


Obj FuncSUM_VEC8BIT_VEC8BIT( Obj self, Obj vl, Obj vr)
{
  Obj sum;
  if (LEN_VEC8BIT(vl) != LEN_VEC8BIT(vr))
    {
      vr = ErrorReturnObj( "SUM: <left> and <right> must be the same length",
			 0L,0L,"You can return a new vector for <right>");

      /* Now redispatch, because vr could be anything */
      return SUM(vl,vr);
    }

  /* we should really handle this case "in house" this will be
     horribly slow */
  if (FIELD_VEC8BIT(vl) != FIELD_VEC8BIT(vr))
    {
      sum = SumListList(vl,vr);
      CALL_1ARGS(ConvertToVectorRep, sum);
      return sum;
    }
  
  /* Finally the main line */
  return SumVec8BitVec8Bit(vl, vr);
}


/****************************************************************************
**
*F  MultVec8BitFFEInner( <prod>, <vec>, <scal>, <start>, <stop> )
**
**  This is the real vector * scalar routine. Others are all calls to this
**  one.
**  Multiplication is done from THE BLOCK containing <start> to the one
**  containing <stop> INCLUSIVE. The remainder of <prod> is unchanged.
**  <prod> may be the same vector as <vec> 
**  <scal> must be written over the field of <vec> and
**  <prod> must be
**  initialized as a vector over this field of length at least <stop>.
**
*/

void MultVec8BitFFEInner( Obj prod,
			  Obj vec,
			  Obj scal,
			  UInt start,
			  UInt stop )
{
  Obj info;
  UInt p;
  UInt q;
  UInt elts;
  UInt1 *ptrV;
  UInt1 *ptrS;
  UInt1 *endS;
  UInt1 *tab;
  
  info = GetFieldInfo8Bit(FIELD_VEC8BIT(prod));
  q = Q_FIELDINFO_8BIT(info);
  p = P_FIELDINFO_8BIT(info);
  elts = ELS_BYTE_FIELDINFO_8BIT(info);
  
  assert(q == FIELD_VEC8BIT(vec));
  assert(LEN_VEC8BIT(prod) >= stop);
  assert(LEN_VEC8BIT(vec) >= stop);
  assert(q == SIZE_FF(FLD_FFE(scal)));


  /* convert to 0 based addressing */
  start--;
  stop--;
  tab = SCALAR_FIELDINFO_8BIT(info) +
    256*FELT_FFE_FIELDINFO_8BIT(info)[VAL_FFE(scal)];
  ptrV = BYTES_VEC8BIT(vec) + start/elts;
  ptrS = BYTES_VEC8BIT(prod) + start/elts;
  endS = BYTES_VEC8BIT(prod) + stop/elts + 1;
  while (ptrS < endS)
    *ptrS++ = tab[*ptrV++];
  return;
}

/****************************************************************************
**
*F  MultVec8BitFFE( <vec>, <scal> ) . . . simple scalar multiply
**
**  This is a basic wrapper for Mult...Inner. It allocates space for
**  the result, promotes the scalar to the proper field if necessary and
**  runs over the whole vector
**
*/

Obj MultVec8BitFFE( Obj vec, Obj scal )
{
  Obj prod;
  Obj info;
  UInt elts;
  UInt q;
  UInt len;
  UInt v;
  q = FIELD_VEC8BIT(vec);
  len = LEN_VEC8BIT(vec);
  info = GetFieldInfo8Bit(q);
  elts = ELS_BYTE_FIELDINFO_8BIT(info);
  prod = NewBag(T_DATOBJ, SIZE_VEC8BIT(len,elts));
  SET_LEN_VEC8BIT(prod, len);
  TYPE_DATOBJ(prod) =
    TypeVec8Bit(q, IS_MUTABLE_OBJ(vec));
  SET_FIELD_VEC8BIT(prod, q);
  CHANGED_BAG(prod);
  if (SIZE_FF(FLD_FFE(scal)) != q)
    {
      v = VAL_FFE(scal);
      if (v != 0)
	v = 1+ (v-1)*(q-1)/(SIZE_FF(FLD_FFE(scal))-1);
      scal = NEW_FFE( FiniteField(P_FIELDINFO_8BIT(info),
				  D_FIELDINFO_8BIT(info)),v);
    }
  MultVec8BitFFEInner( prod, vec, scal, 1, len);
  return prod;
}

/****************************************************************************
**
*F  CopyVec8Bit( <list>, <mut> ) .copying function
**
*/


Obj CopyVec8Bit( Obj list, UInt mut )
{
  Obj copy;
  UInt1 *ptrS, *ptrD;
  UInt n,size;
  UInt q;
  size = SIZE_BAG(list);
  copy = NewBag( T_DATOBJ, size);
  q = FIELD_VEC8BIT(list);
  TYPE_DATOBJ(copy) = TypeVec8Bit(q,mut);
  CHANGED_BAG(copy);
  SET_LEN_VEC8BIT(copy, LEN_VEC8BIT(list));
  SET_FIELD_VEC8BIT(copy,q);
  ptrS = BYTES_VEC8BIT(list);
  ptrD = BYTES_VEC8BIT(copy);
  for (n = 3*sizeof(UInt); n < size; n++)
    *ptrD++ = *ptrS++;
  return copy;
}



/****************************************************************************
**
*F  ZeroVec8Bit( <q>, <len>, <mut> ). . . . . . . . . . .return a zero vector
**
*/

Obj ZeroVec8Bit ( UInt q, UInt len, UInt mut )
{
  Obj zerov;
  UInt1 *ptr;
  UInt n,size;
  Obj info;
  info = GetFieldInfo8Bit(q);
  size = SIZE_VEC8BIT( len, ELS_BYTE_FIELDINFO_8BIT(info));
  zerov = NewBag( T_DATOBJ, size);
  TYPE_DATOBJ(zerov) = TypeVec8Bit(q,mut);
  CHANGED_BAG(zerov);
  SET_LEN_VEC8BIT(zerov, len);
  SET_FIELD_VEC8BIT(zerov, q);
  ptr = BYTES_VEC8BIT(zerov);
  for (n = 3*sizeof(UInt); n < size; n++)
    *ptr++ = (UInt1)0;
  return zerov;
}


/****************************************************************************
**
*F  FuncPROD_VEC8BIT_FFE( <self>, <vec>, <ffe> )
**
** This is the GAP callable method for *. The method installation should
** ensure that we have matching characteristics, but we may not have a common
** field
**
*/


Obj FuncPROD_VEC8BIT_FFE( Obj self, Obj vec, Obj ffe)
{
  Obj prod;
  Obj info;
  UInt d;

  if (VAL_FFE(ffe) == 1) /* ffe is the one */
    {
      prod = CopyVec8Bit( vec, IS_MUTABLE_OBJ(vec));
    }
  else if (VAL_FFE(ffe) == 0)
    return ZeroVec8Bit(FIELD_VEC8BIT(vec),
		       LEN_VEC8BIT(vec),
		       IS_MUTABLE_OBJ(vec));
  
  info = GetFieldInfo8Bit(FIELD_VEC8BIT(vec));
  d = D_FIELDINFO_8BIT(info);

  /* family predicate should have handled this */
  assert(CHAR_FF(FLD_FFE(ffe)) == P_FIELDINFO_8BIT(info));

  /* check for field compatibility */
  if (d % DEGR_FF(FLD_FFE(ffe)))
    {
      prod = ProdListScl(vec,ffe);
      CALL_1ARGS(ConvertToVectorRep, prod);
      return prod;
    }
  
  /* Finally the main line */
  return MultVec8BitFFE(vec, ffe);
}

/****************************************************************************
**
*F  FuncZERO_VEC8BIT( <self>, <vec> )
**
*/

Obj FuncZERO_VEC8BIT( Obj self, Obj vec )
{
  return ZeroVec8Bit( FIELD_VEC8BIT(vec),
		      LEN_VEC8BIT(vec),
		      IS_MUTABLE_OBJ(vec));
}

/****************************************************************************
**
*F  FuncPROD_FFE_VEC8BIT( <self>, <ffe>, <vec> )
**
** This is the GAP callable method for *. The method installation should
** ensure that we have matching characteristics, but we may not have a common
** field
**
** Here we can fall back on the method above.
*/

Obj FuncPROD_FFE_VEC8BIT( Obj self, Obj ffe, Obj vec)
{
  return FuncPROD_VEC8BIT_FFE(self, vec, ffe);
}

/****************************************************************************
**
*F  FuncAINV_VEC8BIT( <self>, <vec> )
**
** This is the GAP callable method for unary -.
*/

Obj FuncAINV_VEC8BIT( Obj self, Obj vec )
{
  Obj info;
  UInt p;
  UInt d;
  UInt minusOne;
  FF f;
  info = GetFieldInfo8Bit(FIELD_VEC8BIT(vec));
  p = P_FIELDINFO_8BIT(info);
  
  /* characteristic 2 case */
  if (2 == p)
    {
      if (!IS_MUTABLE_OBJ(vec))
	return vec;
      return CopyVec8Bit( vec, 1);
    }

  /* Otherwise */
  f = FiniteField( p, D_FIELDINFO_8BIT(info));
  minusOne = NEG_FFV( 1,SUCC_FF(f) );
  return MultVec8BitFFE(vec, NEW_FFE( f, minusOne));
}

/****************************************************************************
**
*F  AddVec8BitVec8BitMultInner( <sum>, <vl>, <vr>, <mult> <start>, <stop> )
**
**  This is the real vector add multiple routine. Others are all calls to this
**  one. It adds <mult>*<vr> to <vl> leaving the result in <sum>
** 
**  Addition is done from THE BLOCK containing <start> to the one
**  containing <stop> INCLUSIVE. The remainder of <sum> is unchanged.
**  <sum> may be the same vector as <vl> or
**  <vr>. <vl> and <vr> must be over the same field and <sum> must be
**  initialized as a vector over this field of length at least <stop>.
**
**  <mult> is assumed to be over the correct field 
**
*/

void  AddVec8BitVec8BitMultInner( Obj sum,
				  Obj vl,
				  Obj vr,
				  Obj mult,
				  UInt start,
				  UInt stop )
{
  Obj info;
  UInt p;
  UInt elts;
  UInt1 *ptrL;
  UInt1 *ptrR;
  UInt1 *ptrS;
  UInt1 *endS;
  UInt1 *addtab;
  UInt1 *multab;

  /* Handle special cases of <mult> */
  if (VAL_FFE(mult) == 0)
    return;

  if (VAL_FFE(mult) == 1)
    {
      AddVec8BitVec8BitInner( sum, vl, vr, start, stop );
      return;
    }
  
  /*  so we have some work. get the tables */
  info = GetFieldInfo8Bit(FIELD_VEC8BIT(sum));

  /* check everything */
  assert(Q_FIELDINFO_8BIT(info) == FIELD_VEC8BIT(vl));
  assert(Q_FIELDINFO_8BIT(info) == FIELD_VEC8BIT(vr));
  assert(LEN_VEC8BIT(sum) >= stop);
  assert(LEN_VEC8BIT(vl) >= stop);
  assert(LEN_VEC8BIT(vr) >= stop);
  assert(SIZE_FF(FLD_FFE(mult)) == FIELD_VEC8BIT(vl));
  
  p = P_FIELDINFO_8BIT(info);
  elts = ELS_BYTE_FIELDINFO_8BIT(info);
  
  /* Convert from 1 based to zero based addressing */
  start --;
  stop --;
  if (p != 2)
    addtab = ADD_FIELDINFO_8BIT(info);

  multab = SCALAR_FIELDINFO_8BIT(info) +
    256*FELT_FFE_FIELDINFO_8BIT(info)[VAL_FFE(mult)];
  
  ptrL = BYTES_VEC8BIT(vl) + start/elts;
  ptrR = BYTES_VEC8BIT(vr) + start/elts;
  ptrS = BYTES_VEC8BIT(sum) + start/elts;
  endS = BYTES_VEC8BIT(sum) + stop/elts + 1;
  if (p != 2)
    while (ptrS < endS)
      *ptrS++ = addtab[256* (*ptrL++) + multab[*ptrR++]];
  else
    while (ptrS < endS)
      *ptrS++ = *ptrL++ ^ multab[*ptrR++];

  return;
}

/****************************************************************************
**
*F  FuncMULT_ROW_VECTOR( <self>, <vec>, <mul> )
**
**  In-place scalar multiply
*/


Obj FuncMULT_ROWVECTOR_VEC8BITS( Obj self, Obj vec, Obj mul)
{
  UInt q;
  q = FIELD_VEC8BIT(vec);

  if (VAL_FFE(mul) == 1)
    return;
  
  /* Now check the field of <mul> */
  if (q != SIZE_FF(FLD_FFE(mul)))
    {
      Obj info;
      UInt d,d1;
      FFV val;
      info = GetFieldInfo8Bit(q);
      d = D_FIELDINFO_8BIT(info);
      d1 = DegreeFFE(mul);
      if (d % d1)
	return TRY_NEXT_METHOD;
      val = VAL_FFE(mul);
      if (val != 0)
	val = 1 + (val-1)*(q-1)/(SIZE_FF(FLD_FFE(mul))-1);
      mul = NEW_FFE(FiniteField(P_FIELDINFO_8BIT(info),d),val);
    }
  MultVec8BitFFEInner( vec, vec, mul, 1, LEN_VEC8BIT(vec));
  return (Obj)0;
}

/****************************************************************************
**
*F  FuncADD_ROWVECTOR_VEC8BITS_5( <self>, <vl>, <vr>, <mul>, <from>, <to> )
**
**  The three argument method for AddRowVector
**
*/

Obj AddRowVector;

Obj FuncADD_ROWVECTOR_VEC8BITS_5( Obj self, Obj vl, Obj vr, Obj mul, Obj from, Obj to)
{
  UInt q;
  UInt len;
  len = LEN_VEC8BIT(vl);
  /* There may be nothing to do */
  if (LT(to,from))
    return (Obj) 0;
  
  if (len != LEN_VEC8BIT(vr))
    {
      vr = ErrorReturnObj( "AddRowVector  : <left> and <right> must be the same length",
			   0L,0L,"You can return a new vector for <right>");
      
      /* Now redispatch, because vr could be anything */
      return CALL_3ARGS(AddRowVector, vl, vr, mul);
    }
  while (LT(INTOBJ_INT(len),to))
    {
      to = ErrorReturnObj( "AddRowVector : <to> (%d)is greater than the length of the vectors (%d)",
			   INT_INTOBJ(to), len,
			   "You can return a new value for <to>");
    }
  if (LT(to,from))
    return (Obj) 0;
  
  /* Now we know that the characteristics must match, but not the fields */
  q = FIELD_VEC8BIT(vl);
  if (q != FIELD_VEC8BIT(vr))
    {
      return TRY_NEXT_METHOD;
    }
  /* Now check the field of <mul> */
  if (q != SIZE_FF(FLD_FFE(mul)))
    {
      Obj info;
      UInt d,d1;
      FFV val;
      info = GetFieldInfo8Bit(q);
      d = D_FIELDINFO_8BIT(info);
      d1 = DegreeFFE(mul);
      if (d % d1)
	return TRY_NEXT_METHOD;
      val = VAL_FFE(mul);
      if (val != 0)
	val = 1 + (val-1)*(q-1)/(SIZE_FF(FLD_FFE(mul))-1);
      mul = NEW_FFE(FiniteField(P_FIELDINFO_8BIT(info),d),val);
    }
  AddVec8BitVec8BitMultInner( vl, vl, vr, mul, INT_INTOBJ(from), INT_INTOBJ(to));
  return (Obj)0;
}

/****************************************************************************
**
*F  FuncADD_ROWVECTOR_VEC8BITS_3( <self>, <vl>, <vr>, <mul> )
**
**  The three argument method for AddRowVector
**
*/


Obj FuncADD_ROWVECTOR_VEC8BITS_3( Obj self, Obj vl, Obj vr, Obj mul)
{
  UInt q;
  if (LEN_VEC8BIT(vl) != LEN_VEC8BIT(vr))
    {
      vr = ErrorReturnObj( "SUM: <left> and <right> must be the same length",
			   0L,0L,"You can return a new vector for <right>");
      
      /* Now redispatch, because vr could be anything */
      return CALL_3ARGS(AddRowVector, vl, vr, mul);
    }
  /* Now we know that the characteristics must match, but not the fields */
  q = FIELD_VEC8BIT(vl);
  if (q != FIELD_VEC8BIT(vr))
    {
      return TRY_NEXT_METHOD;
    }
  /* Now check the field of <mul> */
  if (q != SIZE_FF(FLD_FFE(mul)))
    {
      Obj info;
      UInt d,d1;
      FFV val;
      info = GetFieldInfo8Bit(q);
      d = D_FIELDINFO_8BIT(info);
      d1 = DegreeFFE(mul);
      if (d % d1)
	return TRY_NEXT_METHOD;
      val = VAL_FFE(mul);
      if (val != 0)
	val = 1 + (val-1)*(q-1)/(SIZE_FF(FLD_FFE(mul))-1);
      mul = NEW_FFE(FiniteField(P_FIELDINFO_8BIT(info),d),val);
    }
  AddVec8BitVec8BitMultInner( vl, vl, vr, mul, 1, LEN_VEC8BIT(vl));
  return (Obj)0;
}

/****************************************************************************
**
*F  FuncADD_ROWVECTOR_VEC8BITS_2( <self>, <vl>, <vr>)
**
**  The two argument method for AddRowVector
**
*/


Obj FuncADD_ROWVECTOR_VEC8BITS_2( Obj self, Obj vl, Obj vr)
{
  UInt q;
  if (LEN_VEC8BIT(vl) != LEN_VEC8BIT(vr))
    {
      vr = ErrorReturnObj( "SUM: <left> and <right> must be the same length",
			   0L,0L,"You can return a new vector for <right>");
      
      /* Now redispatch, because vr could be anything */
      return CALL_2ARGS(AddRowVector, vl, vr);
    }
  /* Now we know that the characteristics must match, but not the fields */
  q = FIELD_VEC8BIT(vl);
  if (q != FIELD_VEC8BIT(vr))
    {
      return TRY_NEXT_METHOD;
    }
  AddVec8BitVec8BitInner( vl, vl, vr, 1, LEN_VEC8BIT(vl));
  return (Obj)0;
}


/****************************************************************************
**
*F  SumVec8BitVec8BitMult( <vl>, <vr>, <mult> )
**
**  This is perhaps the simplest wrapper for the Add..MultInner function
**  it allocates a new vector for the result, and adds the whole vectors into
**  it. Mult is promoted to the proper field if necessary.
**  The result follows the new mutability convention
**  (mutable if either argument is).
*/

Obj SumVec8BitVec8BitMult( Obj vl, Obj vr, Obj mult )
{
  Obj sum;
  Obj info;
  UInt elts;
  UInt q;
  UInt len;
  FFV v;
  q = FIELD_VEC8BIT(vl);
  len = LEN_VEC8BIT(vl);
  info = GetFieldInfo8Bit(q);
  elts = ELS_BYTE_FIELDINFO_8BIT(info);
  sum = NewBag(T_DATOBJ, SIZE_VEC8BIT(len,elts));
  SET_LEN_VEC8BIT(sum, len);
  TYPE_DATOBJ(sum) =
    TypeVec8Bit(q, IS_MUTABLE_OBJ(vl) || IS_MUTABLE_OBJ(vr));
  SET_FIELD_VEC8BIT(sum,q );
  CHANGED_BAG(sum);
  if (SIZE_FF(FLD_FFE(mult)) != q)
    {
      v = VAL_FFE(mult);
      if (v != 0)
	v = 1+ (v-1)*(q-1)/(SIZE_FF(FLD_FFE(mult))-1);
      mult = NEW_FFE( FiniteField(P_FIELDINFO_8BIT(info),
				  D_FIELDINFO_8BIT(info)),v);
    }
  AddVec8BitVec8BitMultInner( sum, vl, vr, mult, 1, len);
  return sum;
}

/****************************************************************************
**
*F  FuncDIFF_VEC8BIT_VEC8BIT ( <self>, <vl>, <vr> )
**
**  GAP callable method for binary -
*/
Obj FuncDIFF_VEC8BIT_VEC8BIT( Obj self, Obj vl, Obj vr)
{
  Obj diff;
  Obj info;
  UInt p;
  FF f;
  FFV minusOne;
  
  if (LEN_VEC8BIT(vl) != LEN_VEC8BIT(vr))
    {
      vr = ErrorReturnObj( "SUM: <left> and <right> must be the same length",
			 0L,0L,"You can return a new vector for <right>");

      /* Now redispatch, because vr could be anything */
      return DIFF(vl,vr);
    }

  /* we should really handle this case "in house" this will be
     horribly slow */
  if (FIELD_VEC8BIT(vl) != FIELD_VEC8BIT(vr))
    {
      diff = DiffListList(vl,vr);
      CALL_1ARGS(ConvertToVectorRep, diff);
      return diff;
    }
  
  /* Finally the main line */
  info = GetFieldInfo8Bit(FIELD_VEC8BIT(vl));
  f = FiniteField( P_FIELDINFO_8BIT(info), D_FIELDINFO_8BIT(info));
  minusOne = NEG_FFV( 1,SUCC_FF(f) );

  return SumVec8BitVec8BitMult(vl, vr, NEW_FFE(f,minusOne) );
}

/****************************************************************************
**
*F  CmpVec8BitVec8Bit( <vl>, <vr> ) .. comparison, returns -1, 0 or 1
**
**  characteristic and field should have been checked outside, but we must
**  deal with length variations
*/

Int CmpVec8BitVec8Bit( Obj vl, Obj vr )
{
  Obj info;
  UInt q;
  UInt lenl;
  UInt lenr;
  UInt1 *ptrL;
  UInt1 *ptrR;
  UInt1 *endL;
  UInt1 *endR;
  UInt elts;
  UInt vall,valr;
  UInt e;
  UInt1 *gettab;
  Obj *ffe_elt;
  UInt len;
  FF f;
  assert(FIELD_VEC8BIT(vl) == FIELD_VEC8BIT(vr));
  q = FIELD_VEC8BIT(vl);
  info = GetFieldInfo8Bit(q);
  f = FiniteField(P_FIELDINFO_8BIT(info),
		  D_FIELDINFO_8BIT(info));
  lenl = LEN_VEC8BIT(vl);
  lenr = LEN_VEC8BIT(vr);
  elts = ELS_BYTE_FIELDINFO_8BIT(info);
  ptrL = BYTES_VEC8BIT(vl);
  ptrR = BYTES_VEC8BIT(vr);

  /* we stop a little short, so as to handle the final byte
     separately */
  endL = ptrL + lenl/elts;
  endR = ptrR + lenr/elts;
  gettab = GETELT_FIELDINFO_8BIT(info);
  ffe_elt = FFE_FELT_FIELDINFO_8BIT(info);
  while (ptrL < endL && ptrR < endR)
    {
      if (*ptrL == *ptrR)
	{
	  ptrL++;
	  ptrR++;
	}
      else
	{
	  for (e = 0; e < elts; e++)
	    {
	      vall = gettab[*ptrL + 256*e];
	      valr = gettab[*ptrR + 256*e];
	      if (vall != valr)
		{
		  if (LT( ffe_elt[vall], ffe_elt[valr]))
		    return -1;
		  else
		    return 1;
		}
	    }
	  ErrorQuit("panic: bytes differed but all entries the same",
		    0L, 0L);
	}
    }
  /* now the final byte */

  /* a quick and easy case */
  if (lenl == lenr && *ptrL == *ptrR) 
    return 0;

  /* the more general case */
  if (lenl < lenr)
    len = lenl;
  else
    len = lenr;

  /* look first at the shared part */
  for (e = 0; e < (len % elts); e++) 
    {
      vall = gettab[*ptrL + 256*e];
      valr = gettab[*ptrR + 256*e];
      if (vall != valr)  
	{
	  if (LT( ffe_elt[vall], ffe_elt[valr]))  
	    return -1;
	  else
	    return 1;
	}
    }
    /* if that didn't decide then the longer list is bigger */
  if (lenr > lenl)
    return -1;
  else if (lenr == lenl)
    return 0;
  else
    return 1;
}

/****************************************************************************
**
*F  ScalarProductVec8Bits( <vl>, <vr> ) scalar product of vectors
**
**  Assumes that length and field match
**
*/

Obj ScalarProductVec8Bits( Obj vl, Obj vr )
{
  Obj info;
  FFV acc;
  UInt1 *ptrL;
  UInt1 *ptrR;
  UInt1 *endL;
  UInt len;
  UInt q;
  UInt elts;
  FFV *succ;
  FF f;
  FFV contrib;
  len = LEN_VEC8BIT(vl);
  q = FIELD_VEC8BIT(vl);
  assert(q == FIELD_VEC8BIT(vr));
  assert(len == LEN_VEC8BIT(vr));
  info = GetFieldInfo8Bit(q);
  elts = ELS_BYTE_FIELDINFO_8BIT(info);
  
  ptrL = BYTES_VEC8BIT(vl);
  ptrR = BYTES_VEC8BIT(vr);
  endL = ptrL + (len+elts-1)/elts;

  acc = 0;
  f = FiniteField( P_FIELDINFO_8BIT(info),
		   D_FIELDINFO_8BIT(info));
  succ = SUCC_FF(f);
  while (ptrL < endL)
    {
      contrib = VAL_FFE(FFE_FELT_FIELDINFO_8BIT(info)
			[INNER_FIELDINFO_8BIT(info)
			[*ptrL++ + 256* *ptrR++]]);
      acc = SUM_FFV(acc, contrib, succ);
    }
  return NEW_FFE(f,acc);
  
}

/****************************************************************************
**
*F  FuncPROD_VEC8BIT_VEC8BIT( <self>, <vl>, <vr> )
*/

Obj FuncPROD_VEC8BIT_VEC8BIT( Obj self, Obj vl, Obj vr )
{
  if (FIELD_VEC8BIT(vl) != FIELD_VEC8BIT(vr) ||
      LEN_VEC8BIT(vl) != LEN_VEC8BIT(vr))
    return ProdListList(vl,vr);

  return ScalarProductVec8Bits(vl, vr);
}
    
  
/****************************************************************************
**
*F  FuncEQ_VEC8BIT_VEC8BIT( <self>, <vl>, <vr> )
**
*/

Obj FuncEQ_VEC8BIT_VEC8BIT( Obj self, Obj vl, Obj vr )
{
  if (FIELD_VEC8BIT(vl) != FIELD_VEC8BIT(vr))
    return EqListList(vl,vr) ? True : False;
  
  return (CmpVec8BitVec8Bit(vl,vr) == 0) ? True : False;
}

/****************************************************************************
**
*F  FuncLT_VEC8BIT_VEC8BIT( <self>, <vl>, <vr> )
**
*/

Obj FuncLT_VEC8BIT_VEC8BIT( Obj self, Obj vl, Obj vr )
{
  if (FIELD_VEC8BIT(vl) != FIELD_VEC8BIT(vr))
    return LtListList(vl,vr) ? True : False;
  
  return (CmpVec8BitVec8Bit(vl,vr) == -1) ? True : False;
}

/****************************************************************************
**
*F * * * * * * * * * * * * list access functions  * * * * * * * * * * * * * *
*/

/****************************************************************************
**
*F  FuncSHALLOWCOPY_VEC8BIT( <self>, <list> ) . shallowcopy method
**
*/


Obj FuncSHALLOWCOPY_VEC8BIT( Obj self, Obj list )
{
  return CopyVec8Bit(list, 1);
}


/****************************************************************************
**
*F  FuncLEN_VEC8BIT( <self>, <list> )  . . . . . . . .  length of a vector
*/
Obj FuncLEN_VEC8BIT (
    Obj                 self,
    Obj                 list )
{
    return INTOBJ_INT(LEN_VEC8BIT(list));
}

/****************************************************************************
**
*F  FuncQ_VEC8BIT( <self>, <list> )  . . . . . . . .  length of a vector
*/
Obj FuncQ_VEC8BIT (
    Obj                 self,
    Obj                 list )
{
    return INTOBJ_INT(FIELD_VEC8BIT(list));
}


/****************************************************************************
**
*F  FuncELM0_VEC8BIT( <self>, <list>, <pos> )  . select an elm of a GF2 vector
**
**  'ELM0_VEC8BIT'  returns the element at the  position  <pos> of the boolean
**  list <list>, or `Fail' if <list> has no assigned  object at <pos>.  It is
**  the  responsibility of  the caller to   ensure  that <pos> is  a positive
**  integer.
*/

Obj FuncELM0_VEC8BIT (
    Obj                 self,
    Obj                 list,
    Obj                 pos )
{
    UInt                p;
    Obj			info;
    UInt elts;

    p = INT_INTOBJ(pos);
    if ( LEN_VEC8BIT(list) < p ) {
        return Fail;
    }
    else {
      info = GetFieldInfo8Bit(FIELD_VEC8BIT(list));
      elts = ELS_BYTE_FIELDINFO_8BIT(info);
      return FFE_FELT_FIELDINFO_8BIT(info)[
		GETELT_FIELDINFO_8BIT(info)[BYTES_VEC8BIT(list)[(p-1)/elts] +
					   256*((p-1)%elts)]];
    }
}


/****************************************************************************
**
*F  FuncELM_VEC8BIT( <self>, <list>, <pos> ) . . select an elm of a GF2 vector
**
**  'ELM_VEC8BIT' returns the element at the position <pos>  of the GF2 vector
**  <list>.   An  error  is signalled  if  <pos>  is  not bound.    It is the
**  responsibility of the caller to ensure that <pos> is a positive integer.
*/
Obj FuncELM_VEC8BIT (
    Obj                 self,
    Obj                 list,
    Obj                 pos )
{
    UInt                p;
    Obj			info;
    UInt elts;

    p = INT_INTOBJ(pos);
    if ( LEN_VEC8BIT(list) < p ) {
        ErrorReturnVoid(
            "List Element: <list>[%d] must have an assigned value",
            p, 0L, "you can return after assigning a value" );
        return ELM_LIST( list, p );
    }
    else {
      info = GetFieldInfo8Bit(FIELD_VEC8BIT(list));
      elts = ELS_BYTE_FIELDINFO_8BIT(info);
      return FFE_FELT_FIELDINFO_8BIT(info)[
		GETELT_FIELDINFO_8BIT(info)[BYTES_VEC8BIT(list)[(p-1)/elts] +
					   256*((p-1)%elts)]];

    }
}


/****************************************************************************
**
*F  FuncELMS_VEC8BIT( <self>, <list>, <poss> ) . select elms of an 8 bit vector
**
**  The results are returned in the compressed format
*/
Obj FuncELMS_VEC8BIT (
    Obj                 self,
    Obj                 list,
    Obj                 poss )
{
    UInt                p;
    Obj			info;
    UInt                elts;
    UInt                len;
    Obj                 res;
    UInt                i;
    UInt                elt;
    UInt1               *gettab;
    UInt1               *settab;
    UInt1               *ptrS;
    UInt1               *ptrD;
    UInt                 e;
    UInt1                byte;
    
    info = ELM_PLIST(FieldInfo8Bit,FIELD_VEC8BIT(list));
    elts = ELS_BYTE_FIELDINFO_8BIT(info);
    len = LEN_PLIST(poss);
    res = NewBag(T_DATOBJ, SIZE_VEC8BIT( len, elts));
    TYPE_DATOBJ(res) = TYPE_DATOBJ(list);
    SET_FIELD_VEC8BIT(res, FIELD_VEC8BIT(list));
    SET_LEN_VEC8BIT(res, len);
    gettab = GETELT_FIELDINFO_8BIT(info);
    settab = SETELT_FIELDINFO_8BIT(info);
    ptrS = BYTES_VEC8BIT(list);
    ptrD = BYTES_VEC8BIT(res);
    e = 0;
    byte = 0;
    for (i = 1; i <= len; i++)
      {
	p = INT_INTOBJ(ELM_PLIST(poss,i));
	elt = gettab[ptrS[(p-1)/elts] + 256*((p-1)%elts)];
	byte = settab[ byte + 256*(e + elts*elt)];
	e++;
	if (e == elts)
	  {
	    *ptrD++ = byte;
	    e = 0;
	    byte = 0;
	  }
      }
    if (e)
      *ptrD = byte;
    
    return res;
}



/****************************************************************************
**
*F  FuncELMS_VEC8BIT_RANGE( <self>, <list>, <range> ) .
**                                         select elms of an 8 bit vector
**
**  With increment 1, one might do better, especially if it happens
**  to be aligned. Ignore this for now.
**  The results are returned in the compressed format
*/
Obj FuncELMS_VEC8BIT_RANGE (
    Obj                 self,
    Obj                 list,
    Obj                 range  )
{
    UInt                p;
    Obj			info;
    UInt                elts;
    UInt                len;
    UInt                low;
    UInt                inc;
    Obj                 res;
    UInt                i;
    UInt                elt;
    UInt1               *gettab;
    UInt1               *settab;
    UInt1               *ptrS;
    UInt1               *ptrD;
    UInt                 e;
    UInt1                byte;
    
    info = ELM_PLIST(FieldInfo8Bit,FIELD_VEC8BIT(list));
    elts = ELS_BYTE_FIELDINFO_8BIT(info);
    len = GET_LEN_RANGE(range);
    low = GET_LOW_RANGE(range);
    inc = GET_INC_RANGE(range);
    res = NewBag(T_DATOBJ, SIZE_VEC8BIT( len, elts));
    TYPE_DATOBJ(res) = TYPE_DATOBJ(list);
    SET_FIELD_VEC8BIT(res, FIELD_VEC8BIT(list));
    SET_LEN_VEC8BIT(res, len);
    gettab = GETELT_FIELDINFO_8BIT(info);
    settab = SETELT_FIELDINFO_8BIT(info);
    ptrS = BYTES_VEC8BIT(list);
    ptrD = BYTES_VEC8BIT(res);
    e = 0;
    byte = 0;
    p = low-1;			/* the -1 converts to 0 base */
    if (p % elts == 0 && inc == 1 && len >= elts)
      {
	while (p < low + len - elts)
	  {
	    *ptrD++ =ptrS[p/elts];
	    p += elts;
	  }
	byte = 0;
	e = 0;
	if ( p < low + len)
	  {
	    while (p < low + len)
	      {
		elt = gettab[ptrS[p/elts] + 256*(p%elts)];
		byte = settab[ byte + 256 *(e + elts *elt)];
		e++;
		p++;
	      }
	    *ptrD = byte;
	  }
      }
    else
      {
	for (i = 1; i <= len; i++)
	  {
	    elt = gettab[ptrS[p/elts] + 256*(p%elts)];
	    byte = settab[ byte + 256*(e + elts*elt)];
	    e++;
	    if (e == elts)
	      {
		*ptrD++ = byte;
		e = 0;
		byte = 0;
	      }
	    p += inc;
	  }
	if (e)
	  *ptrD = byte;
      }
    
    return res;
}




/****************************************************************************
**
*F  FuncASS_VEC8BIT( <self>, <list>, <pos>, <elm> ) set an elm of a GF2 vector
**
**  'ASS_VEC8BIT' assigns the element  <elm> at the position  <pos> to the GF2
**  vector <list>.
**
**  It is the responsibility of the caller  to ensure that <pos> is positive,
**  and that <elm> is not 0.
*/
Obj FuncASS_VEC8BIT (
    Obj                 self,
    Obj                 list,
    Obj                 pos,
    Obj                 elm )
{
    UInt                p;
    Obj                 info;
    UInt                elts;
    UInt                chr;
    UInt                d;
    UInt                q;
    FF                  f;
    UInt v;

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
    info = GetFieldInfo8Bit(FIELD_VEC8BIT(list));
    elts = ELS_BYTE_FIELDINFO_8BIT(info);
    chr = P_FIELDINFO_8BIT(info);
    d = D_FIELDINFO_8BIT(info);
    q = Q_FIELDINFO_8BIT(info);


    if ( p <= LEN_VEC8BIT(list)+1 ) {
      if ( LEN_VEC8BIT(list)+1 == p ) {
	ResizeBag( list, SIZE_VEC8BIT(p,elts));
	SET_LEN_VEC8BIT( list, p);
      }
      if (IS_FFE(elm) &&
	  chr == CharFFE(elm))
	{
	  if (d % DegreeFFE(elm) == 0)
	    {
	      v = VAL_FFE(elm);
	      if (v != 0 && q != SIZE_FF(FLD_FFE(elm)))
		v = 1+(v-1)*(q-1)/(SIZE_FF(FLD_FFE(elm))-1);
	      
	      BYTES_VEC8BIT(list)[(p-1) / elts] =
		SETELT_FIELDINFO_8BIT(info)
		[256*(elts*FELT_FFE_FIELDINFO_8BIT(info)[v]+(p-1)%elts) +
		BYTES_VEC8BIT(list)[(p-1)/elts]];
	      return 0;
	    }
	  else
	    {
	      /* proabbly we should handle many more cases like
	       this */
	      f = CommonFF(FiniteField(chr,d),d,
			   FLD_FFE(elm),DegreeFFE(elm));
	      if (f && SIZE_FF(f) <= 256)
		{
		  PlainVec8Bit(list);
		  SET_ELM_PLIST( list, p, elm );
		  ConvVec8Bit(list,SIZE_FF(f));
		  return 0;
		}
	    }
	}
    }

    /* We fall through here if the assignment position is so large
       as to leave a hole, or if the object to be assigned is
       not of the right characteristic, or would create too large a field */
    PlainVec8Bit(list);
    AssPlistFfe( list, p, elm );
    return 0;
}



/****************************************************************************
**
*F  FuncUNB_VEC8BIT( <self>, <list>, <pos> ) . unbind position of a GFQ vector
**
**  'UNB_VEC8BIT' unbind  the element at  the position  <pos> in  a GFQ vector
**  <list>.
**
**  It is the responsibility of the caller  to ensure that <pos> is positive.
*/
Obj FuncUNB_VEC8BIT (
    Obj                 self,
    Obj                 list,
    Obj                 pos )
{
    UInt                p;
    Obj                 info;
    UInt elts;

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
    if ( LEN_VEC8BIT(list) < p ) {
        ;
    }
    else if ( LEN_VEC8BIT(list) == p ) {
      /* zero out the last entry first, for safety */
      info = ELM_PLIST(FieldInfo8Bit,FIELD_VEC8BIT(list));
      elts = ELS_BYTE_FIELDINFO_8BIT(info);
      BYTES_VEC8BIT(list)[(p-1)/elts] =
	SETELT_FIELDINFO_8BIT(info)[((p-1) % elts)*256 +
				   BYTES_VEC8BIT(list)[(p-1)/elts]];
        ResizeBag( list, 3*sizeof(UInt)+(p+elts-2)/elts );
        SET_LEN_VEC8BIT( list, p-1);
    }
    else {
        PlainVec8Bit(list);
        UNB_LIST( list, p );
    }
    return 0;
}

/****************************************************************************
**
*F  FuncPOSITION_NONZERO_VEC8BIT( <self>, <list>, <zero> ) .
**                               
**
*/
Obj FuncPOSITION_NONZERO_VEC8BIT (
    Obj                 self,
    Obj                 list,
    Obj                 zero )
{
    Obj                 info;
    UInt len;
    UInt nb;
    UInt i,j;
    UInt elts;
    UInt1 *ptr;
    UInt1 byte;
    UInt1 *gettab;

    len = LEN_VEC8BIT(list);
    info = GetFieldInfo8Bit(FIELD_VEC8BIT(list));
    elts = ELS_BYTE_FIELDINFO_8BIT(info);
    nb = (len + elts -1)/elts;
    ptr = BYTES_VEC8BIT(list);
    i = 0;
    while (i < nb && !ptr[i])
      i++;
    if (i >= nb)
      return INTOBJ_INT(len+1);
    byte = ptr[i];
    gettab = GETELT_FIELDINFO_8BIT(info) + byte;
    j = 0;
    while (gettab[256*j] == 0)
      j++;
    return INTOBJ_INT(elts*i+j+1);
}

/****************************************************************************
**
*F  FuncAPPEND_VEC8BIT( <self>, <vecl>, <vecr> ) .
**                               
**
*/
Obj FuncAPPEND_VEC8BIT (
    Obj                 self,
    Obj                 vecl,
    Obj                 vecr )
{
    Obj                 info;
    UInt lenl,lenr;
    UInt nb;
    UInt i;
    UInt elts;
    UInt1 *ptrl,*ptrr;
    UInt1 bytel, byter, elt;
    UInt1 *gettab, *settab;
    UInt posl, posr;

    if (FIELD_VEC8BIT(vecl) != FIELD_VEC8BIT(vecr))
      return TRY_NEXT_METHOD;
    
    lenl = LEN_VEC8BIT(vecl);
    lenr = LEN_VEC8BIT(vecr);
    info = GetFieldInfo8Bit(FIELD_VEC8BIT(vecl));
    elts = ELS_BYTE_FIELDINFO_8BIT(info);
    ResizeBag( vecl, SIZE_VEC8BIT(lenl+lenr,elts));

    if (lenl % elts == 0)
      {
	ptrl = BYTES_VEC8BIT(vecl) + lenl/elts;
	ptrr = BYTES_VEC8BIT(vecr);
	nb = (lenr + elts - 1)/elts;
	for (i = 0; i < nb; i++)
	  *ptrl++ = *ptrr++;
      }
    else
      {
	ptrl = BYTES_VEC8BIT(vecl) + (lenl -1)/elts;
	bytel = *ptrl;
	posl = lenl;
	posr = 0;
	ptrr = BYTES_VEC8BIT(vecr);
	byter = *ptrr;
	gettab = GETELT_FIELDINFO_8BIT(info);
	settab = SETELT_FIELDINFO_8BIT(info);
	while (posr < lenr)
	  {
	    elt = gettab[ byter + 256 * (posr % elts) ];
	    bytel = settab[ bytel + 256 * ( posl % elts + elts * elt)];
	    if (++posl % elts == 0)
	      {
		*ptrl++ = bytel; 
		bytel = 0;
	      }
	    if ( ++posr % elts == 0)
	      {
		byter = *++ptrr;
	      }
	  }
	*ptrl = bytel;
      }
    SET_LEN_VEC8BIT(vecl, lenl + lenr);
    return (Obj) 0;
}

/****************************************************************************
**
*F  FuncNUMBER_VEC8BIT( <self>, <vec> )
**
*/

Obj FuncNUMBER_VEC8BIT (Obj self, Obj vec)

{
    Obj			info;
    UInt                elts;
    UInt                len;
    UInt                i;
    UInt                elt;
    UInt1               *gettab;
    UInt1               *ptrS;

    Obj                 res;
    Obj 		f;
    
    info = GetFieldInfo8Bit(FIELD_VEC8BIT(vec));
    elts = ELS_BYTE_FIELDINFO_8BIT(info);
    gettab = GETELT_FIELDINFO_8BIT(info);
    ptrS = BYTES_VEC8BIT(vec);
    len = LEN_VEC8BIT(vec);
    res = INTOBJ_INT(0);
    f = INTOBJ_INT(FIELD_VEC8BIT(vec)); /* Field size as GAP integer */

    for (i = 0; i < len; i++)
      {
	elt = gettab[ptrS[i/elts] + 256*(i%elts)];
	res=ProdInt(res,f); /* ``shift'' */
	res=SumInt(res,(Obj)(INTOBJ_INT(elt)));
      }
    
    return res;
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

    { "CONV_VEC8BIT", 2, "list,q",
      FuncCONV_VEC8BIT, "src/vec8bit.c:CONV_VEC8BIT" },

    { "PLAIN_VEC8BIT", 1, "gfqvec",
      FuncPLAIN_VEC8BIT, "src/vec8bit.c:PLAIN_VEC8BIT" },

    { "LEN_VEC8BIT", 1, "gfqvec",
      FuncLEN_VEC8BIT, "src/vec8bit.c:LEN_VEC8BIT" },

    { "ELM0_VEC8BIT", 2, "gfqvec, pos",
      FuncELM0_VEC8BIT, "src/vec8bit.c:ELM0_VEC8BIT" },

    { "ELM_VEC8BIT", 2, "gfqvec, pos",
      FuncELM_VEC8BIT, "src/vec8bit.c:ELM_VEC8BIT" },

    { "ELMS_VEC8BIT", 2, "gfqvec, poss",
      FuncELMS_VEC8BIT, "src/vec8bit.c:ELMS_VEC8BIT" },

    { "ELMS_VEC8BIT_RANGE", 2, "gfqvec, range",
      FuncELMS_VEC8BIT_RANGE, "src/vec8bit.c:ELMS_VEC8BIT_RANGE" },

    { "ASS_VEC8BIT", 3, "gfqvec, pos, elm",
      FuncASS_VEC8BIT, "src/vec8bit.c:ASS_VEC8BIT" },

    { "UNB_VEC8BIT", 2, "gfqvec, pos",
      FuncUNB_VEC8BIT, "src/vec8bit.c:UNB_VEC8BIT" },

    { "Q_VEC8BIT", 1, "gfqvec",
      FuncQ_VEC8BIT, "src/vec8bit.c:Q_VEC8BIT" },

    { "SHALLOWCOPY_VEC8BIT", 1, "gfqvec",
      FuncSHALLOWCOPY_VEC8BIT, "src/vec8bit.c:SHALLOWCOPY_VEC8BIT" },

    { "SUM_VEC8BIT_VEC8BIT", 2, "gfqvecl, gfqvecr",
      FuncSUM_VEC8BIT_VEC8BIT, "src/vec8bit.c:SUM_VEC8BIT_VEC8BIT" },

    { "DIFF_VEC8BIT_VEC8BIT", 2, "gfqvecl, gfqvecr",
      FuncDIFF_VEC8BIT_VEC8BIT, "src/vec8bit.c:DIFF_VEC8BIT_VEC8BIT" },

    { "PROD_VEC8BIT_FFE", 2, "gfqvec, gfqelt",
      FuncPROD_VEC8BIT_FFE, "src/vec8bit.c:PROD_VEC8BIT_FFE" },

    { "PROD_FFE_VEC8BIT", 2, "gfqelt, gfqvec",
      FuncPROD_FFE_VEC8BIT, "src/vec8bit.c:PROD_FFE_VEC8BIT" },
    
    { "AINV_VEC8BIT", 1, "gfqvec",
      FuncAINV_VEC8BIT, "src/vec8bit.c:AINV_VEC8BIT" },

    { "ZERO_VEC8BIT", 1, "gfqvec",
      FuncZERO_VEC8BIT, "src/vec8bit.c:ZERO_VEC8BIT" },

    { "EQ_VEC8BIT_VEC8BIT", 2, "gfqvecl, gfqvecr",
      FuncEQ_VEC8BIT_VEC8BIT, "src/vec8bit.c:EQ_VEC8BIT_VEC8BIT" },

    { "LT_VEC8BIT_VEC8BIT", 2, "gfqvecl, gfqvecr",
      FuncLT_VEC8BIT_VEC8BIT, "src/vec8bit.c:LT_VEC8BIT_VEC8BIT" },

    { "PROD_VEC8BIT_VEC8BIT", 2, "gfqvecl, gfqvecr",
      FuncPROD_VEC8BIT_VEC8BIT, "src/vec8bit.c:PROD_VEC8BIT_VEC8BIT" },

    {"ADD_ROWVECTOR_VEC8BITS_5", 5, "gfqvecl, gfqvecr, mul, from, to",
      FuncADD_ROWVECTOR_VEC8BITS_5, "src/vec8bit.c:ADD_ROWVECTOR_VEC8BITS_5" },

    {"ADD_ROWVECTOR_VEC8BITS_3", 3, "gfqvecl, gfqvecr, mul",
      FuncADD_ROWVECTOR_VEC8BITS_3, "src/vec8bit.c:ADD_ROWVECTOR_VEC8BITS_3" },

    {"ADD_ROWVECTOR_VEC8BITS_2", 2, "gfqvecl, gfqvecr",
      FuncADD_ROWVECTOR_VEC8BITS_2, "src/vec8bit.c:ADD_ROWVECTOR_VEC8BITS_2" },

    {"MULT_ROWVECTOR_VEC8BITS", 2, "gfqvec, ffe",
      FuncMULT_ROWVECTOR_VEC8BITS, "src/vec8bit.c:MULT_ROWVECTOR_VEC8BITS" },

    {"POSITION_NONZERO_VEC8BIT", 2, "vec8bit, zero",
       FuncPOSITION_NONZERO_VEC8BIT, "src/vec8bit.c:POSITION_NONZERO_VEC8BIT" },

    {"APPEND_VEC8BIT", 2, "vec8bitl, vec8bitr",
       FuncAPPEND_VEC8BIT, "src/vec8bit.c:APPEND_VEC8BIT" },

    {"NUMBER_VEC8BIT", 1, "gfqvec",
       FuncNUMBER_VEC8BIT, "src/vec8bit.c:NUMBER_VEC8BIT" },

    { 0 }

};


/****************************************************************************
**
*F  PreSave( <module ) . . . . . . discard big recoverable data before saving
**
**  It will get rebuilt automatically, both in the saving workspace and in
** the loaded one and is not endian-safe anyway
*/

static Int PreSave( StructInitInfo * module )
{
  UInt q;
  for (q = 3; q <= 256; q++)
    SET_ELM_PLIST(FieldInfo8Bit, q, (Obj) 0);

  /* return success */
  return 0;
}

/****************************************************************************
**
*F  InitKernel( <module> )  . . . . . . . . initialise kernel data structures
*/
static Int InitKernel (
    StructInitInfo *    module )
{
  /* import kind functions                                               */
  ImportFuncFromLibrary( "TYPE_VEC8BIT",       &TYPE_VEC8BIT     );
  ImportGVarFromLibrary( "TYPES_VEC8BIT",      &TYPES_VEC8BIT     );
  ImportFuncFromLibrary( "Is8BitVectorRep",    &IsVec8bitRep       );
  ImportGVarFromLibrary( "TYPE_FIELDINFO_8BIT",&TYPE_FIELDINFO_8BIT     );
  
  /* init filters and functions                                          */
  InitHdlrFuncsFromTable( GVarFuncs );
  
  InitGlobalBag( &FieldInfo8Bit, "src/vec8bit.c:FieldInfo8Bit" );

  InitFopyGVar("ConvertToVectorRep", &ConvertToVectorRep);
  InitFopyGVar("AddRowVector", &AddRowVector);

  
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

  FieldInfo8Bit = NEW_PLIST(T_PLIST_NDENSE,257);
  SET_ELM_PLIST(FieldInfo8Bit,257,INTOBJ_INT(1));
  SET_LEN_PLIST(FieldInfo8Bit,257);
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
    "vec8bit",                           /* name                           */
    0,                                  /* revision entry of c file       */
    0,                                  /* revision entry of h file       */
    0,                                  /* version                        */
    0,                                  /* crc                            */
    InitKernel,                         /* initKernel                     */
    InitLibrary,                        /* initLibrary                    */
    0,                                  /* checkInit                      */
    PreSave,                            /* preSave                        */
    0,                                  /* postSave                       */
    0                                   /* postRestore                    */
};

StructInitInfo * InitInfoVec8bit ( void )
{
    module.revision_c = Revision_vec8bit_c;
    module.revision_h = Revision_vec8bit_h;
    FillInVersion( &module );
    return &module;
}


/****************************************************************************
**

*E  vec8bit.c  . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
*/
