#############################################################################
##
#W  ctbl.gi                     GAP library                     Thomas Breuer
#W                                                           & Goetz Pfeiffer
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the implementations corresponding to the declarations
##  in `ctbl.gd'.
##
##  1. Some Remarks about Character Theory in GAP
##  2. Character Table Categories
##  3. The Interface between Character Tables and Groups
##  4. Operators for Character Tables
##  5. Attributes and Properties for Groups as well as for Character Tables
##  6. Attributes and Properties only for Character Tables
##  x. Operations Concerning Blocks
##  7. Other Operations for Character Tables
##  8. Creating Character Tables
##  9. Printing Character Tables
##  10. Constructing Character Tables from Others
##  11. Sorted Character Tables
##  12. Storing Normal Subgroup Information
##  13. Auxiliary Stuff
##
Revision.ctbl_gi :=
    "@(#)$Id$";


#############################################################################
##
##  1. Some Remarks about Character Theory in GAP
##


#############################################################################
##
##  2. Character Table Categories
##

#############################################################################
##
#V  NearlyCharacterTablesFamily
##
InstallValue( NearlyCharacterTablesFamily,
    NewFamily( "NearlyCharacterTablesFamily", IsNearlyCharacterTable ) );


#############################################################################
##
##  3. The Interface between Character Tables and Groups
##


#############################################################################
##
#F  ConnectGroupAndCharacterTable( <G>, <tbl>[, <arec>] )
#F  ConnectGroupAndCharacterTable( <G>, <tbl>, <bijection> )
##
InstallGlobalFunction( ConnectGroupAndCharacterTable, function( arg )

    local G, tbl, arec, ccl, compat;

    # Get and check the arguments.
    if   Length( arg ) = 2 and IsGroup( arg[1] )
                           and IsOrdinaryTable( arg[2] ) then
      arec:= rec();
    elif Length( arg ) = 3 and IsGroup( arg[1] )
                           and IsOrdinaryTable( arg[2] )
                           and ( IsRecord( arg[3] ) or IsList(arg[3]) ) then
      arec:= arg[3];
    else
      Error( "usage: ConnectGroupAndCharacterTable(<G>,<tbl>[,<arec>])" );
    fi;

    G   := arg[1];
    tbl := arg[2];

    if HasUnderlyingGroup( tbl ) then
      Error( "<tbl> has already underlying group" );
    elif HasOrdinaryCharacterTable( G ) then
      Error( "<G> has already a character table" );
    fi;

    ccl:= ConjugacyClasses( G );
#T How to exploit the known character table
#T if the conjugacy classes of <G> are not yet computed?

    if IsList( arec ) then
      compat:= arec;
    else
      compat:= CompatibleConjugacyClasses( G, ccl, tbl, arec );
    fi;

    if IsList( compat ) then

      # Permute the classes if necessary.
      if compat <> [ 1 .. Length( compat ) ] then
        ccl:= ccl{ compat };
      fi;

      # The identification is unique, store attribute values.
      SetUnderlyingGroup( tbl, G );
      SetOrdinaryCharacterTable( G, tbl );
      SetConjugacyClasses( tbl, ccl );
      SetIdentificationOfConjugacyClasses( tbl, compat );

      return true;

    else
      return false;
    fi;

    end );


#############################################################################
##
#M  CompatibleConjugacyClasses( <G>, <ccl>, <tbl>[, <arec>] )
##
InstallMethod( CompatibleConjugacyClasses,
    "three argument version, call `CompatibleConjugacyClassesDefault'",
    true,
    [ IsGroup, IsList, IsOrdinaryTable ], 0,
    function( G, ccl, tbl )
    return CompatibleConjugacyClassesDefault( G, ccl, tbl, rec() );
    end );

InstallMethod( CompatibleConjugacyClasses,
    "four argument version, call `CompatibleConjugacyClassesDefault'",
    true,
    [ IsGroup, IsList, IsOrdinaryTable, IsRecord ], 0,
    CompatibleConjugacyClassesDefault );


#############################################################################
##
#M  CompatibleConjugacyClasses( <tbl>[, <arec>] )
##
InstallMethod( CompatibleConjugacyClasses,
    "one argument version, call `CompatibleConjugacyClassesDefault'",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )
    return CompatibleConjugacyClassesDefault( false, false, tbl, rec() );
    end );

InstallMethod( CompatibleConjugacyClasses,
    "two argument version, call `CompatibleConjugacyClassesDefault'",
    true,
    [ IsOrdinaryTable, IsRecord ], 0,
    function( tbl, arec )
    return CompatibleConjugacyClassesDefault( false, false, tbl, arec );
    end );


#############################################################################
##
#F  CompatibleConjugacyClassesDefault( <G>, <ccl>, <tbl>, <arec> )
#F  CompatibleConjugacyClassesDefault( false, false, <tbl>, <arec> )
##
InstallGlobalFunction( CompatibleConjugacyClassesDefault,
    function( G, ccl, tbl, arec )

    local natchar,     # natural character (if known)
          nccl,        # no. of conjugacy classes of `G'
          identpos,    # identified positions of classes of `tbl'
          identccl,    # corresponding identified classes in `ccl'
          compat,      # bijection from table to group, result
          tbl_orders,  # element orders of classes in `tbl'
          orders,      # set of all element orders of `tbl'
          equpos,      # list of position tuples that are not yet identified
          equccl,      # corresponding list of class tuples
          update,      # local function to update after each invariant
          done,        # local function to update after each invariant
          result,      # return value
          tbl_classes, # class lengths in `tbl'
          usesymm,     # local function to use table automorphisms
          usepowers,   # local function to use power maps
          primes,      # primes for that the power maps are stored
          sums,        # list of lengths of entries in `equpos'
          i,
          values,
          strange,
          degree,      # degree of the permutation character
          j,
          tbl_powermap,
          symm,        # group of symmetries that is still available
          tuple,
          p,
          pos,
          ep,
          galoisfams, treatable, list, fam, id, k, rep, ords;

    if IsBound( arec.natchar ) then
      natchar:= arec.natchar;
    fi;

    nccl:= NrConjugacyClasses( tbl );

    if ccl <> false and Length( ccl ) <> nccl then
      return fail;
    fi;

    # We construct a bijection of equivalence classes
    # given by certain invariants.
    identpos:= [];
    identccl:= [];
    compat:= [];

    # The function `update' moves identified classes/positions from
    # `equccl' resp. `equpos' to `identccl' resp. `identpos'.
    # It returns `fail' if the lengths of tuples are different
    # (and hence table and group do not fit together),
    # `false' if ambiguities remained, and `true' otherwise.
    update := function()
      for i in [ 1 .. Length( equpos ) ] do
        if IsBound( equpos[i] ) then
          if Length( equpos[i] ) <> Length( equccl[i] ) then
            return fail;
          elif Length( equpos[i] ) = 0 then
            Unbind( equpos[i] );
            Unbind( equccl[i] );
          elif Length( equpos[i] ) = 1 then
            Append( identpos, equpos[i] );
            Append( identccl, equccl[i] );
            Unbind( equpos[i] );
            Unbind( equccl[i] );
          fi;
        fi;
      od;
      equpos:= Compacted( equpos );
      equccl:= Compacted( equccl );

      if IsEmpty( equpos ) then

        # unique identification
        SortParallel( identpos, identccl );
# hack for the moment ...
        if G <> false then
          compat:= List( identpos, i -> First( identpos,
                         j -> Representative( identccl[i] ) in ccl[j] ) );
        fi;
# end of hack ...
        return true;
      else

        # not yet done
        Info( InfoCharacterTable, 2, "not yet identified:\n",
              "#I  ", equpos );
        return false;
      fi;
    end;

    done:= function( bool )
      if bool = true then
        Info( InfoCharacterTable, 2, "unique identification" );
        if G = false then
          result:= [];
        else
          result:= compat;
        fi;
        return true;
      elif bool = fail then
        Assert( G <> false,
                "impossible incompatibility in class identification" );
        Info( InfoCharacterTable, 2, "<G> and <tbl> do not fit together" );
        result:= fail;
        return true;
      else
        return false;
      fi;
    end;

    # Use element orders.
    Info( InfoCharacterTable, 2,
          "using element orders to identify classes" );
    tbl_orders:= OrdersClassRepresentatives( tbl );
    orders:= Set( tbl_orders );
    equpos:= List( orders, x -> Filtered( [ 1 .. nccl ],
                                  i -> tbl_orders[i] = x ) );
    if G = false then
      equccl:= equpos;
    else
      equccl:= List( orders, x -> Filtered( ccl,
                              c -> Order( Representative( c ) ) = x ) );
    fi;

    # Are we done?
    if done( update() ) then
      return result;
    fi;

    # Use class lengths.
    Info( InfoCharacterTable, 2,
          "using class lengths to identify classes" );
    tbl_classes:= SizesConjugacyClasses( tbl );
    for i in [ 1 .. Length( equpos ) ] do
      values:= Set( tbl_classes{ equpos[i] } );
      if Length( values ) > 1 then
        for j in values do
          Add( equpos, Filtered( equpos[i], x -> tbl_classes[x] = j ) );
          if G = false then
            Add( equccl, Filtered( equpos[i], x -> tbl_classes[x] = j ) );
          else
            Add( equccl, Filtered( equccl[i], x -> Size( x ) = j ) );
          fi;
        od;
        Unbind( equpos[i] );
        Unbind( equccl[i] );
      fi;
    od;

    # Are we done?
    if done( update() ) then
      return result;
    fi;

    # Use the natural character if it is prescribed.
    if IsBound( natchar ) then
      Info( InfoCharacterTable, 2,
            "using natural character to identify classes" );

      strange:= false;
      degree:= natchar[1];
      for i in [ 1 .. Length( equpos ) ] do
        values:= Set( natchar{ equpos[i] } );
        if 1 < Length( values ) then
          for j in values do
            Add( equpos, Filtered( equpos[i], x -> natchar[x] = j ) );
            if G = false then
              Add( equccl, Filtered( equpos[i], x -> natchar[x] = j ) );
            elif IsPermGroup( G ) then
              Add( equccl, Filtered( equccl[i],
                             x -> degree - NrMovedPoints(
                                          Representative( x ) ) = j ) );
            elif IsMatrixGroup( G ) then
              Add( equccl, Filtered( equccl[i],
                             x -> TraceMat( Representative( x ) ) = j ) );
            else
              strange:= true;
            fi;
          od;
          if not strange then
            Unbind( equpos[i] );
            Unbind( equccl[i] );
          fi;
        fi;
      od;

      if strange = true then
        Info( InfoCharacterTable, 2,
              "<G> is no perm. or matrix group, ignore natural character" );
      fi;

      # Are we done?
      if done( update() ) then
        return result;
      fi;

    fi;

    # Use power maps.
#T use maps for all prime divisors of the group order!
    tbl_powermap:= ComputedPowerMaps( tbl );
    primes:= Filtered( [ 2 .. Length( tbl_powermap ) ],
                       i -> IsBound( tbl_powermap[i] ) );

    usepowers:= function( p )

      local i, powers, powersset, j, pos, ppos;

      Info( InfoCharacterTable, 2, " (p = ", p, ")" );

      # First consider each set of nonidentified classes
      # together with its `p'-th powers.
      for i in [ 1 .. Length( equpos ) ] do

        if IsBound( equpos[i] ) then

          powers:= tbl_powermap[p]{ equpos[i] };
          powersset:= Set( powers );
          if 1 < Length( powersset ) then

            while not IsEmpty( powersset ) do
              j:= powersset[1];
              pos:= Position( identpos, j );
              if pos <> fail then
                Add( equpos, Filtered( equpos[i],
                         x -> tbl_powermap[p][x] = j ) );
                if G = false then
                  Add( equccl, Filtered( equpos[i],
                           x -> tbl_powermap[p][x] = j ) );
                else
                  Add( equccl, Filtered( equccl[i],
                           x -> Representative( x )^p in identccl[ pos ] ) );
                fi;
                powersset:= Difference( powersset, [ j ] );
              else
                pos:= First( [ 1 .. Length( equpos ) ],
                             k -> IsBound( equpos[k] ) and j in equpos[k] );
                Add( equpos, Filtered( equpos[i],
                         x -> tbl_powermap[p][x] in equpos[ pos ] ) );
                if G = false then
                  Add( equccl, Filtered( equpos[i],
                           x -> tbl_powermap[p][x] in equpos[ pos ] ) );
                else
                  Add( equccl, Filtered( equccl[i],
                           x -> ForAny( equccl[ pos ],
                                   c -> Representative( x )^p in c ) ) );
                fi;
                powersset:= Difference( powersset, equpos[ pos ] );
              fi;

            od;
            Unbind( equpos[i] );
            Unbind( equccl[i] );

          fi;

        fi;

      od;

      # Now consider each set of nonidentified classes
      # together with its `p'-th roots.

      # First look at `p'-th roots that are already identified.
      for i in [ 1 .. Length( identpos ) ] do

        powers:= tbl_powermap[p][ identpos[i] ];
        if not powers in identpos then

          # The power of an identified class can be identified.
          pos:= First( [ 1 .. Length( equpos ) ],
                       k -> IsBound( equpos[k] ) and powers in equpos[k] );
          if G = false then
            ppos:= Position( equccl[ pos ], powers );
          else
            ppos:= First( [ 1 .. Length( equccl[ pos ] ) ],
                  k -> Representative( identccl[i] )^p in equccl[ pos ][k] );
          fi;

          Add( identpos, powers );
          Add( identccl, equccl[ pos ][ ppos ] );

          equpos[ pos ]:= Difference( equpos[ pos ], [ powers ] );
          equccl[ pos ]:= equccl[ pos ]{ Difference(
                  [ 1 .. Length( equccl[ pos ] ) ], [ ppos ] ) };

        fi;

      od;

      # Now look at `p'-th roots that are not yet identified.
#T compute the positions of not identified root classes;
#T if they are not a union of `equpos' lists then
#T refine the partition

    end;

    # Use symmetries of the table.
    symm:= AutomorphismsOfTable( tbl );

    if IsBound( natchar ) then

      # There may be asymmetries because of the prescribed character.
      # Compute the subgroup that stabilizes each tuple in `equpos' setwise.
      for i in equpos do
        symm:= Stabilizer( symm, i, OnSets );
      od;

    fi;

    # Sort `equpos' according to decreasing element order.
    # (catch automorphisms for long orbits, hope for powers
    # if ambiguities remain)
    ords:= List( equpos, x -> - tbl_orders[ x[1] ] );
    ords:= Sortex( ords );
    equpos:= Permuted( equpos, ords );
    equccl:= Permuted( equccl, ords );

    # If all points in a tuple of `equpos' are equivalent under table
    # automorphism, we may separate one point from the others.
    usesymm:= function()
      for i in [ 1 .. Length( equpos ) ] do
        if Size( symm ) <> 1 then
          tuple:= equpos[i];
          if     Length( tuple ) > 1
             and tuple = Set( Orbit( symm, tuple[1], OnPoints ) ) then
            symm:= Stabilizer( symm, tuple[1] );
            Add( identpos, equpos[i][1] );
            Add( identccl, equccl[i][1] );
            equpos[i]:= equpos[i]{ [ 2 .. Length( equpos[i] ) ] };
            equccl[i]:= equccl[i]{ [ 2 .. Length( equccl[i] ) ] };
            Info( InfoCharacterTable, 2,
                  "found useful table automorphism" );
          fi;
        fi;
      od;
    end;

    repeat

      sums:= List( equpos, Length );

      Info( InfoCharacterTable, 2, "using power maps to identify classes" );
      for p in primes do

        usepowers( p );

        # Are we done?
        if done( update() ) then
          return result;
        fi;

      od;

      Info( InfoCharacterTable, 2,
            "using table automorphisms to identify classes" );
      usesymm();

      # Are we done?
      if done( update() ) then
        return result;
      fi;

    until sums = List( equpos, Length );

    # Use Galois conjugacy of classes.
    galoisfams:= GaloisMat( TransposedMat( Irr( tbl ) ) ).galoisfams;
    galoisfams:= Filtered( galoisfams, IsList );
    galoisfams:= List( galoisfams, x -> x[1] );

    treatable:= Filtered( equpos,
                          list -> ForAny( galoisfams,
                                          x -> IsSubset( x, list ) ) );
    if not IsEmpty( treatable ) then
      Info( InfoCharacterTable, 2,
            "use Galois conjugacy (explicit computations)" );
    fi;
    for list in treatable do
      fam:= First( galoisfams, x -> IsSubset( x, list ) );
      if Set( fam ) <> Set( list ) then

        id:= Difference( fam, list )[1];
        for i in ShallowCopy( list ) do
#T suffices?

          k:= First( PrimeResidues( tbl_orders[i] ),
                  x -> ForAll( Irr( tbl ),
#T !
                           chi -> GaloisCyc( chi[ id ], x ) = chi[i] ) );
          ep:= Position( equpos, list );
          if G = false then
            Add( equpos, [ i ] );
            Add( equccl, [ i ] );
            RemoveSet( list, i );
            equccl[ ep ]:= Difference( equccl[ ep ], [ i ] );
          else
            rep:= Representative( identccl[ Position( identpos, id ) ] );
            pos:= Position( equccl[ ep ], ConjugacyClass( G, rep^k ) );
            Add( equpos, [ i ] );
            Add( equccl, [ equccl[ ep ][ pos ] ] );
            RemoveSet( list, i );
            equccl[ ep ]:= Concatenation( equccl[ ep ]{ [ 1 .. pos-1 ] },
                equccl[ ep ]{ [ pos+1 .. Length( equccl[ ep ] ) ] } );
          fi;

        od;

        pos:= Position( equpos, list );
        Unbind( equpos[ pos ] );
        Unbind( equccl[ pos ] );

      fi;
    od;

    # Are we done?
    if done( update() ) then
      return result;
    fi;

    treatable:= Filtered( equpos,
                          list -> ForAny( galoisfams,
                                          x -> IsSubset( x, list ) ) );
    if treatable <> [] then
      Info( InfoCharacterTable, 2,
            "use Galois powers (explicit computations)" );
    fi;
    for list in treatable do
      fam:= First( galoisfams, x -> IsSubset( x, list ) );
      primes:= Filtered( [ 2 .. Length( tbl_powermap ) ],
                         i ->     IsBound( tbl_powermap[i] )
                              and ForAny( identpos,
                                           j -> tbl_powermap[i][j] = fam[1] ) );
      if primes <> [] then

        p:= primes[1];
        for i in ShallowCopy( list ) do
#T reicht das?
          id:= First( identpos, x -> tbl_powermap[p][x] = i );
          ep:= Position( equpos, list );
          if G = false then
            Add( equpos, [ i ] );
            Add( equccl, [ i ] );
            RemoveSet( list, i );
            equccl[ ep ]:= Difference( equccl[ ep ], [ i ] );
          else
            rep:= Representative( identccl[ Position( identpos, id ) ] )^p;
            pos:= Position( equccl[ ep ], ConjugacyClass( G, rep ) );
            Add( equpos, [ i ] );
            Add( equccl, [ equccl[ ep ][ pos ] ] );
            RemoveSet( list, i );
            equccl[ep]:= Concatenation( equccl[ep]{ [ 1 .. pos-1 ] },
                equccl[ep]{ [ pos+1 .. Length( equccl[ep] ) ] } );
          fi;
        od;

        pos:= Position( equpos, list );
        Unbind( equpos[ pos ] );
        Unbind( equccl[ pos ] );

      fi;
    od;

    # Are we done?
    if done( update() ) then
      return result;
    fi;

    # (meanwhile destroyed)
    primes:= Filtered( [ 2 .. Length( tbl_powermap ) ],
                       i -> IsBound( tbl_powermap[i] ) );
    repeat

      sums:= List( equpos, Length );

      Info( InfoCharacterTable, 2, "using power maps to identify classes" );
      for p in primes do

        usepowers( p );

        # Are we done?
        if done( update() ) then
          return result;
        fi;

      od;

      Info( InfoCharacterTable, 2,
            "using table automorphisms to identify classes" );
      usesymm();

      # Are we done?
      if done( update() ) then
        return result;
      fi;

    until sums = List( equpos, Length );

    # no identification yet ...
    Info( InfoCharacterTable, 2, "not identified classes: ", equpos );
    if G = false then
      return equpos;
    else
      return fail;
    fi;
end );


#############################################################################
##
##  4. Operators for Character Tables
##


#############################################################################
##
#M  \mod( <ordtbl>, <p> ) . . . . . . . . . . . . . . . . . <p>-modular table
##
InstallMethod( \mod,
    "for ord. char. table, and pos. integer (call `BrauerTable')",
    true,
    [ IsOrdinaryTable, IsPosInt ], 0,
    BrauerTable );


#############################################################################
##
#M  \*( <tbl1>, <tbl2> )  . . . . . . . . . . . . .  direct product of tables
##
InstallOtherMethod( \*,
    "for two nearly character tables (call `CharacterTableDirectProduct')",
    true,
    [ IsNearlyCharacterTable, IsNearlyCharacterTable ], 0,
    CharacterTableDirectProduct );


#############################################################################
##
#M  \/( <tbl>, <list> )  . . . . . . . . .  character table of a factor group
##
InstallOtherMethod( \/,
    "for char. table, and positions list (call `CharacterTableFactorGroup')",
    true,
    [ IsNearlyCharacterTable, IsList and IsCyclotomicCollection ], 0,
    CharacterTableFactorGroup );


#############################################################################
##
##  5. Attributes and Properties for Groups as well as for Character Tables
##


#############################################################################
##
#M  CharacterDegrees( <G> ) . . . . . . . . . . . . . . . . . . . for a group
#M  CharacterDegrees( <G>, <zero> ) . . . . . . . . . .  for a group and zero
##
##  The attribute delegates to the two-argument version.
##  The two-argument version delegates to `Irr'.
##
InstallMethod( CharacterDegrees,
    "for a group (call the two-argument version)",
    true,
    [ IsGroup ], 0,
    G -> CharacterDegrees( G, 0 ) );

InstallMethod( CharacterDegrees,
    "for a group, and zero",
    true,
    [ IsGroup, IsZeroCyc ], 0,
    function( G, zero )
    return Collected( List( Irr( G ), DegreeOfCharacter ) );
    end );

InstallMethod( CharacterDegrees,
    "for a group, and positive integer",
    true,
    [ IsGroup, IsPosInt ], 0,
    function( G, p )
    if Size( G ) mod p = 0 then
      return CharacterDegrees( CharacterTable( G, p ) );
    else
      return CharacterDegrees( G, 0 );
    fi;
    end );


#############################################################################
##
#M  CharacterDegrees( <tbl> ) . . . . . . . . . . . . . for a character table
##
##  If the table knows its group and the irreducibles are not yet stored then
##  we try to avoid the computation of the irreducibles and therefore
##  delegate to the group.
##  Otherwise we use the irreducibles.
##
InstallMethod( CharacterDegrees,
    "for a character table",
    true,
    [ IsCharacterTable ], 0,
    function( tbl )
    if HasUnderlyingGroup( tbl ) and not HasIrr( tbl ) then
      return CharacterDegrees( UnderlyingGroup( tbl ) );
    else
      return Collected( List( Irr( tbl ), DegreeOfCharacter ) );
    fi;
    end );


#############################################################################
##
#M  CharacterDegrees( <G> ) . . . . . for group handled via nice monomorphism
##
AttributeMethodByNiceMonomorphism( CharacterDegrees, [ IsGroup ] );


#############################################################################
##
#M  Irr( <G> )  . . . . . . . . . . . . . . . . . . . . . . . . . for a group
##
##  Delegate to the two-argument version.
##
InstallMethod( Irr,
    "for a group (call the two-argument version)",
    true,
    [ IsGroup ], 0,
    G -> Irr( G, 0 ) );


#############################################################################
##
#M  Irr( <G>, <p> )   . . . . . . . . . . . . . . . . for a group and a prime
##
InstallMethod( Irr,
    "for a group, and a prime",
    true,
    [ IsGroup, IsPosInt ], 0,
    function( G, p )
    return Irr( BrauerTable( G, p ) );
    end );


#############################################################################
##
#M  Irr( <modtbl> ) . . . . . . . . . . . . . for a <p>-solvable Brauer table
##
##  Compute the modular irreducibles from the ordinary irreducibles
##  using the Fong-Swan Theorem.
##
InstallMethod( Irr,
    "for a <p>-solvable Brauer table (use the Fong-Swan Theorem)",
    true,
    [ IsBrauerTable ], 0,
    function( modtbl )

    local p,       # characteristic
          ordtbl,  # ordinary character table
          i,       # loop variable
          rest,    # restriction of characters to 'p'-regular classes
          irr,     # list of Brauer characters
          cd,      # list of ordinary character degrees
          deg,     # one character degree
          chars,   # characters of a given degree
          dec;     # decomposition of ordinary characters
                   # into known Brauer characters

    p:= UnderlyingCharacteristic( modtbl );
    ordtbl:= OrdinaryCharacterTable( modtbl );

    if not IsPSolvableCharacterTable( ordtbl, p ) then
      TryNextMethod();
    fi;

    rest:= RestrictedClassFunctions( Irr( ordtbl ), modtbl );

    if Size( ordtbl ) mod p <> 0 then

      # Catch a trivial case.
      irr:= rest;

    else

      # Start with the linear characters.
      # (Choose the same succession as in the ordinary table,
      # in particular leave the trivial character at first position
      # if this is the case for `ordtbl'.)
      irr:= [];
      for i in rest do
        if DegreeOfCharacter( i ) = 1 and not i in irr then
          Add( irr, i );
        fi;
      od;
      cd:= Set( List( rest, DegreeOfCharacter ) );
      RemoveSet( cd, 1 );

      for deg in cd do
        chars:= Set( Filtered( rest, x -> DegreeOfCharacter( x ) = deg ) );
#T improve this!!!
        dec:= Decomposition( irr, chars, "nonnegative" );
        for i in [ 1 .. Length( dec ) ] do
          if dec[i] = fail then
            Add( irr, chars[i] );
          fi;
        od;
      od;

    fi;

    # Return the irreducible Brauer characters.
    return irr;
    end );


#############################################################################
##
#M  Irr( <ordtbl> ) . . . . . . . .  for an ord. char. table with known group
##
##  We must delegate this to the underlying group.
##
InstallMethod( Irr,
    "for an ord. char. table with known group (delegate to the group)",
    true,
    [ IsOrdinaryTable and HasUnderlyingGroup ], 0,
    ordtbl -> Irr( UnderlyingGroup( ordtbl ) ) );


#############################################################################
##
#M  IBr( <modtbl> ) . . . . . . . . . . . . . .  for a Brauer character table
#M  IBr( <G>, <p> ) . . . . . . . . . . . .  for a group, and a prime integer
##
InstallMethod( IBr,
    "for a Brauer table",
    true,
    [ IsBrauerTable ], 0,
    Irr );

InstallMethod( IBr,
    "for a group, and a prime integer",
    true,
    [ IsGroup, IsPosInt ], 0,
    function( G, p ) return Irr( G, p ); end );


#############################################################################
##
#M  LinearCharacters( <G> )
##
##  Delegate to the two-argument version, as for `Irr'.
##
InstallMethod( LinearCharacters,
    "for a group (call the two-argument version)",
    true,
    [ IsGroup ], 0,
    G -> LinearCharacters( G, 0 ) );


#############################################################################
##
#M  LinearCharacters( <G>, 0 )
##
InstallMethod( LinearCharacters,
    "for a group, and zero",
    true,
    [ IsGroup, IsZeroCyc ], 0,
    function( G, zero )
    local pi, img, tbl, fus;

    if IsAbelian( G ) then
      return Irr( G, 0 );
    fi;

    pi:= NaturalHomomorphismByNormalSubgroup( G, DerivedSubgroup( G ) );
    img:= ImagesSource( pi );
    tbl:= CharacterTable( G );
    fus:= FusionConjugacyClasses( pi, tbl, CharacterTable( img ) );
    return RestrictedClassFunctions( Irr( img, 0 ), pi );
#T better utilize `DxLinearCharacters'?
    end );


#############################################################################
##
#M  LinearCharacters( <G>, 0 )
##
InstallMethod( LinearCharacters,
    "for a group with known ordinary table, and zero",
    true,
    [ IsGroup and HasOrdinaryCharacterTable, IsZeroCyc ], 0,
    function( G, zero )
    local tbl;
    tbl:= OrdinaryCharacterTable( G );
    if HasIrr( tbl ) then
      return LinearCharacters( tbl );
    else
      TryNextMethod();
    fi;
    end );


#############################################################################
##
#M  LinearCharacters( <G>, <p> )
##
InstallMethod( LinearCharacters,
    "for a group, and positive integer",
    true,
    [ IsGroup, IsPosInt ], 0,
    function( G, p )
    if not IsPrimeInt( p ) then
      Error( "<p> must be a prime" );
    fi;
    return Filtered( LinearCharacters( G, 0 ),
                     chi -> Conductor( chi ) mod p <> 0 );
    end );


#############################################################################
##
#M  LinearCharacters( <ordtbl> )  . . . . . . . . . . . for an ordinary table
##
InstallMethod( LinearCharacters,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable ], 0,
    function( ordtbl )
    if HasIrr( ordtbl ) then
      return Filtered( Irr( ordtbl ), chi -> chi[1] = 1 );
    elif HasUnderlyingGroup( ordtbl ) then
      return LinearCharacters( UnderlyingGroup( ordtbl ) );
    else
      TryNextMethod();
    fi;
    end );


#############################################################################
##
#M  LinearCharacters( <modtbl> )  . . . . . . . . . . . .  for a Brauer table
##
InstallMethod( LinearCharacters,
    "for a Brauer table",
    true,
    [ IsBrauerTable ], 0,
    modtbl -> DuplicateFreeList( RestrictedClassFunctions(
                  LinearCharacters( modtbl ), modtbl ) ) );


#############################################################################
##
#M  OrdinaryCharacterTable( <G> ) . . . . . . . . . . . . . . . . for a group
#M  OrdinaryCharacterTable( <modtbl> )  . . . .  for a Brauer character table
##
##  In the first case, we setup the table object.
##  In the second case, we delegate to `OrdinaryCharacterTable' for the
##  group.
##
InstallMethod( OrdinaryCharacterTable,
    "for a group",
    true,
    [ IsGroup ], 0,
    function( G )
    local tbl, ccl, idpos, bijection;

    # Make the object.
    tbl:= Objectify( NewType( NearlyCharacterTablesFamily,
                              IsOrdinaryTable and IsAttributeStoringRep ),
                     rec() );

    # Store the attribute values of the interface.
    SetUnderlyingGroup( tbl, G );
    SetUnderlyingCharacteristic( tbl, 0 );
    ccl:= ConjugacyClasses( G );
    idpos:= First( [ 1 .. Length( ccl ) ],
                   i -> Order( Representative( ccl[i] ) ) = 1 );
    if idpos = 1 then
      bijection:= [ 1 .. Length( ccl ) ];
    else
      ccl:= Concatenation( [ ccl[ idpos ] ], ccl{ [ 1 .. idpos-1 ] },
                           ccl{ [ idpos+1 .. Length( ccl ) ] } );
      bijection:= Concatenation( [ idpos ], [ 1 .. idpos-1 ],
                                 [ idpos+1 .. Length( ccl ) ] );
    fi;
    SetConjugacyClasses( tbl, ccl );
    SetIdentificationOfConjugacyClasses( tbl, bijection );

    # Return the table.
    return tbl;
    end );


##############################################################################
##
#M  AbelianInvariants( <tbl> )  . . . . . . . for an ordinary character table
##
##  For all Sylow $p$ subgroups of the factor of <tbl> by the normal subgroup
##  given by `ClassPositionsOfDerivedSubgroup( <tbl> )',
##  compute the abelian invariants by repeated factoring by a cyclic group
##  of maximal order.
##
InstallMethod( AbelianInvariants,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )

    local kernel,  # cyclic group to be factored out
          inv,     # list of invariants, result
          primes,  # list of prime divisors of actual size
          max,     # list of actual maximal orders, for 'primes'
          pos,     # list of positions of maximal orders
          orders,  # list of representative orders
          i,       # loop over classes
          j;       # loop over primes

    # Do all computations modulo the derived subgroup.
    kernel:= ClassPositionsOfDerivedSubgroup( tbl );
    if 1 < Length( kernel ) then
      tbl:= tbl / kernel;
    fi;
#T cheaper to use only orders and power maps,
#T and to avoid computing several tables!
#T (especially avoid to compute the irreducibles of the original
#T table if they are not known!)

    inv:= [];

    while 1 < Size( tbl ) do

      # For all prime divisors $p$ of the size,
      # compute the element of maximal $p$ power order.
      primes:= Set( FactorsInt( Size( tbl ) ) );
      max:= List( primes, x -> 1 );
      pos:= [];
      orders:= OrdersClassRepresentatives( tbl );
      for i in [ 2 .. Length( orders ) ] do
        if IsPrimePowerInt( orders[i] ) then
          j:= 1;
          while orders[i] mod primes[j] <> 0 do
            j:= j+1;
          od;
          if orders[i] > max[j] then
            max[j]:= orders[i];
            pos[j]:= i;
          fi;
        fi;
      od;

      # Update the list of invariants.
      Append( inv, max );

      # Factor out the cyclic subgroup.
      tbl:= tbl / ClassPositionsOfNormalClosure( tbl, pos );

    od;

    return AbelianInvariantsOfList( inv );
#T if we call this function anyhow, we can also take factors by the largest
#T cyclic subgroup of the commutator factor group!
    end );


#############################################################################
##
#M  Exponent( <tbl> ) . . . . . . . . . . . . for an ordinary character table
##
InstallMethod( Exponent,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    tbl -> Lcm( OrdersClassRepresentatives( tbl ) ) );


#############################################################################
##
#M  IsAbelian( <tbl> )  . . . . . . . . . . . for an ordinary character table
##
InstallMethod( IsAbelian,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    tbl -> Size( tbl ) = NrConjugacyClasses( tbl ) );


#############################################################################
##
#M  IsCyclic( <tbl> ) . . . . . . . . . . . . for an ordinary character table
##
InstallMethod( IsCyclic,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    tbl -> Size( tbl ) in OrdersClassRepresentatives( tbl ) );


#############################################################################
##
#M  IsFinite( <tbl> ) . . . . . . . . . . . . for an ordinary character table
##
InstallMethod( IsFinite,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    tbl -> IsInt( Size( tbl ) ) );


#############################################################################
##
#M  IsMonomialCharacterTable( <tbl> ) . . . . for an ordinary character table
##
InstallMethod( IsMonomialCharacterTable,
    "for an ordinary character table with underlying group",
    true,
    [ IsOrdinaryTable and HasUnderlyingGroup ], 0,
    tbl -> IsMonomialGroup( UnderlyingGroup( tbl ) ) );


#############################################################################
##
#F  CharacterTable_IsNilpotentFactor( <tbl>, <N> )
##
InstallGlobalFunction( CharacterTable_IsNilpotentFactor, function( tbl, N )
    local series;
    series:= CharacterTable_UpperCentralSeriesFactor( tbl, N );
    return Length( series[ Length( series ) ] ) = NrConjugacyClasses( tbl );
    end );


#############################################################################
##
#F  CharacterTable_IsNilpotentNormalSubgroup( <tbl>, <N> )
##
InstallGlobalFunction( CharacterTable_IsNilpotentNormalSubgroup,
    function( tbl, N )

    local classlengths,  # class lengths
          orders,        # orders of class representatives
          ppow,          # list of classes of prime power order
          part,          # one pair '[ prime, exponent ]'
          classes;       # classes of p power order for a prime p

    # Take the classes of prime power order.
    classlengths:= SizesConjugacyClasses( tbl );
    orders:= OrdersClassRepresentatives( tbl );
    ppow:= Filtered( N, i -> IsPrimePowerInt( orders[i] ) );

    for part in Collected( FactorsInt( Sum( classlengths{ N }, 0 ) ) ) do

      # Check whether the Sylow p subgroup of 'N' is normal in 'N',
      # i.e., whether the number of elements of p-power is equal to
      # the size of a Sylow p subgroup.
      classes:= Filtered( ppow, i -> orders[i] mod part[1] = 0 );
      if part[1] ^ part[2] <> Sum( classlengths{ classes }, 0 ) + 1 then
        return false;
      fi;

    od;
    return true;
    end );


#############################################################################
##
#M  IsNilpotentCharacterTable( <tbl> )
##
InstallMethod( IsNilpotentCharacterTable,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )
    local series;
    series:= ClassPositionsOfUpperCentralSeries( tbl );
    return Length( series[ Length( series ) ] ) = NrConjugacyClasses( tbl );
    end );


#############################################################################
##
#M  IsPerfectCharacterTable( <tbl> )  . . . . for an ordinary character table
##
InstallMethod( IsPerfectCharacterTable,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    tbl -> Number( Irr( tbl ), chi -> chi[1] = 1 ) = 1 );


#############################################################################
##
#M  IsSimpleCharacterTable( <tbl> ) . . . . . for an ordinary character table
##
InstallMethod( IsSimpleCharacterTable,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    tbl -> Length( ClassPositionsOfNormalSubgroups( tbl ) ) = 2 );


#############################################################################
##
#M  IsSolvableCharacterTable( <tbl> ) . . . . for an ordinary character table
##
InstallMethod( IsSolvableCharacterTable,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    tbl -> IsPSolvableCharacterTable( tbl, 0 ) );


#############################################################################
##
#M  IsSupersolvableCharacterTable( <tbl> )  . for an ordinary character table
##
InstallMethod( IsSupersolvableCharacterTable,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    tbl -> Size( ClassPositionsOfSupersolvableResiduum( tbl ) ) = 1 );


#############################################################################
##
#M  NrConjugacyClasses( <ordtbl> )  . . . . . for an ordinary character table
#M  NrConjugacyClasses( <modtbl> )  . . . . . .  for a Brauer character table
#M  NrConjugacyClasses( <G> )
##
##  We delegate from <tbl> to the underlying group in the general case.
##  If we know the centralizer orders or class lengths, however, we use them.
##
##  If the argument is a group, we can use the known class lengths of the
##  known ordinary character table.
##
InstallMethod( NrConjugacyClasses,
    "for an ordinary character table with underlying group",
    true,
    [ IsOrdinaryTable and HasUnderlyingGroup ], 0,
    ordtbl -> NrConjugacyClasses( UnderlyingGroup( ordtbl ) ) );

InstallMethod( NrConjugacyClasses,
    "for a Brauer character table",
    true,
    [ IsBrauerTable ], 0,
    modtbl -> Length( GetFusionMap( modtbl,
                                    OrdinaryCharacterTable( modtbl ) ) ) );

InstallMethod( NrConjugacyClasses,
    "for a character table with known centralizer orders",
    true,
    [ IsNearlyCharacterTable and HasSizesCentralizers ], 0,
    tbl -> Length( SizesCentralizers( tbl ) ) );

InstallMethod( NrConjugacyClasses,
    "for a character table with known class lengths",
    true,
    [ IsNearlyCharacterTable and HasSizesConjugacyClasses ], 0,
    tbl -> Length( SizesConjugacyClasses( tbl ) ) );

InstallMethod( NrConjugacyClasses,
    "for a group with known ordinary character table",
    true,
    [ IsGroup and HasOrdinaryCharacterTable ], 0,
    function( G )
    local tbl;
    tbl:= OrdinaryCharacterTable( G );
    if HasNrConjugacyClasses( tbl ) then
      return NrConjugacyClasses( tbl );
    else
      TryNextMethod();
    fi;
    end );


#############################################################################
##
#M  Size( <tbl> ) . . . . . . . . . . . . . . . . . . . for a character table
#M  Size( <G> )
##
##  We delegate from <tbl> to the underlying group in the general case.
##  If we know the centralizer orders, however, we use them.
##
##  If the argument is a group, we can use the known size of the
##  known ordinary character table.
##
InstallMethod( Size,
    "for a character table with underlying group",
    true,
    [ IsCharacterTable and HasUnderlyingGroup ], 0,
    tbl -> Size( UnderlyingGroup( tbl ) ) );

InstallMethod( Size,
    "for a character table with known centralizer orders",
    true,
    [ IsNearlyCharacterTable and HasSizesCentralizers ], 0,
    tbl -> SizesCentralizers( tbl )[1] );

InstallMethod( Size,
    "for a group with known ordinary character table",
    true,
    [ IsGroup and HasOrdinaryCharacterTable ], 0,
    function( G )
    local tbl;
    tbl:= OrdinaryCharacterTable( G );
    if HasSize( tbl ) then
      return Size( tbl );
    else
      TryNextMethod();
    fi;
    end );


#############################################################################
##
##  6. Attributes and Properties only for Character Tables
##

#############################################################################
##
#M  OrdersClassRepresentatives( <ordtbl> )  . for an ordinary character table
#M  OrdersClassRepresentatives( <modtbl> )  . .  for a Brauer character table
##
##  We delegate from <tbl> to the underlying group in the general case.
##  If we know the class lengths, however, we use them.
##
InstallMethod( OrdersClassRepresentatives,
    "for a Brauer character table (delegate to the ordinary table)",
    true,
    [ IsBrauerTable ], 0,
    function( modtbl )
    local ordtbl;
    ordtbl:= OrdinaryCharacterTable( modtbl );
    return OrdersClassRepresentatives( ordtbl ){ GetFusionMap( modtbl,
               ordtbl ) };
    end );

InstallMethod( OrdersClassRepresentatives,
    "for a character table with known group",
    true,
    [ IsNearlyCharacterTable and HasUnderlyingGroup ], 0,
    tbl -> List( ConjugacyClasses( tbl ),
                 c -> Order( Representative( c ) ) ) );

InstallMethod( OrdersClassRepresentatives,
    "for a character table, use known power maps",
    true,
    [ IsNearlyCharacterTable ], 0,
    function( tbl )

    local ord, p;

    # Compute the orders as determined by the known power maps.
    ord:= ElementOrdersPowerMap( ComputedPowerMaps( tbl ) );
    if ForAll( ord, IsInt ) then
      return ord;
    fi;

    # If these maps do not suffice, compute the missing power maps
    # and then try again.
    for p in Set( Factors( Size( tbl ) ) ) do
      PowerMap( tbl, p );
    od;
    ord:= ElementOrdersPowerMap( ComputedPowerMaps( tbl ) );
    Assert( 2, ForAll( ord, IsInt ),
            "computed power maps should determine element orders" );

    return ord;
    end );


#############################################################################
##
#M  SizesCentralizers( <ordtbl> ) . . . . . . for an ordinary character table
#M  SizesCentralizers( <modtbl> ) . . . . . . .  for a Brauer character table
##
##  If we know the class lengths, we use them.
##
InstallMethod( SizesCentralizers,
    "for a Brauer character table",
    true,
    [ IsBrauerTable ], 0,
    function( modtbl )
    local ordtbl;
    ordtbl:= OrdinaryCharacterTable( modtbl );
    return SizesCentralizers( ordtbl ){ GetFusionMap( modtbl, ordtbl ) };
    end );

InstallMethod( SizesCentralizers,
    "for a character table with known class lengths",
    true,
    [ IsNearlyCharacterTable and HasSizesConjugacyClasses ], 0,
    function( tbl )
    local classlengths, size;
    classlengths:= SizesConjugacyClasses( tbl );
    size:= Sum( classlengths, 0 );
    return List( classlengths, s -> size / s );
    end );

InstallMethod( SizesCentralizers,
    "for a character table with known group",
    true,
    [ IsNearlyCharacterTable and HasUnderlyingGroup ], 0,
    function( tbl )
    local size;
    size:= Size( tbl );
    return List( ConjugacyClasses( tbl ), c -> size / Size( c ) );
    end );


#############################################################################
##
#M  SizesConjugacyClasses( <ordtbl> ) . . . . for an ordinary character table
#M  SizesConjugacyClasses( <modtbl> ) . . . . .  for a Brauer character table
##
##  If we know the centralizer orders, we use them.
##
InstallMethod( SizesConjugacyClasses,
    "for a Brauer character table",
    true,
    [ IsBrauerTable ], 0,
    function( modtbl )
    local ordtbl;
    ordtbl:= OrdinaryCharacterTable( modtbl );
    return SizesConjugacyClasses( ordtbl ){ GetFusionMap( modtbl,
                                                          ordtbl ) };
    end );

InstallMethod( SizesConjugacyClasses,
    "for a character table with known centralizer sizes",
    true,
    [ IsNearlyCharacterTable and HasSizesCentralizers ], 0,
    function( tbl )
    local centsizes, size;
    centsizes:= SizesCentralizers( tbl );
    size:= centsizes[1];
    return List( centsizes, s -> size / s );
    end );

InstallMethod( SizesConjugacyClasses,
    "for a character table with known group",
    true,
    [ IsNearlyCharacterTable and HasUnderlyingGroup ], 0,
    tbl -> List( ConjugacyClasses( tbl ), Size ) );


#############################################################################
##
#M  AutomorphismsOfTable( <tbl> ) . . . . . . . . . . . for a character table
##
InstallMethod( AutomorphismsOfTable,
    "for a character table",
    true,
    [ IsCharacterTable ], 0,
    tbl -> TableAutomorphisms( tbl, Irr( tbl ) ) );


#############################################################################
##
#M  AutomorphismsOfTable( <modtbl> )  . . . for Brauer table & good reduction
##
##  The automorphisms may be stored already on the ordinary table.
##
InstallMethod( AutomorphismsOfTable,
    "for a Brauer table in the case of good reduction",
    true,
    [ IsBrauerTable ], 0,
    function( modtbl )
    if Size( modtbl ) mod UnderlyingCharacteristic( modtbl ) = 0 then
      TryNextMethod();
    else
      return AutomorphismsOfTable( OrdinaryCharacterTable( modtbl ) );
    fi;
    end );


#############################################################################
##
#M  ClassNames( <tbl> )  . . . . . . . . . . class names of a character table
##
InstallMethod( ClassNames,
    true,
    [ IsNearlyCharacterTable ], 0,
    function( tbl )

    local i,        # loop variable
          alpha,    # alphabet
          lalpha,   # length of the alphabet
          number,   # at position <i> the current number of
                    # classes of order <i>
          unknown,  # number of next unknown element order
          names,    # list of classnames, result
          name,     # local function returning right combination of letters
          orders;   # list of representative orders

    alpha:= [ "a","b","c","d","e","f","g","h","i","j","k","l","m",
              "n","o","p","q","r","s","t","u","v","w","x","y","z" ];
    lalpha:= Length( alpha );

    name:= function(n)
       local name;
       name:= "";
       while 0 < n do
          name:= Concatenation( alpha[ (n-1) mod lalpha + 1 ], name );
          n:= QuoInt( n-1, lalpha );
       od;
       return name;
    end;

    names:= [];

    if IsCharacterTable( tbl ) or HasOrdersClassRepresentatives( tbl ) then

      # A character table can be asked for representative orders,
      # also if they are not yet stored.
      orders:= OrdersClassRepresentatives( tbl );
      number:= [];
      unknown:= 1;
      for i in [ 1 .. NrConjugacyClasses( tbl ) ] do
        if IsInt( orders[i] ) then
          if not IsBound( number[ orders[i] ] ) then
            number[ orders[i] ]:= 1;
          fi;
          names[i]:= Concatenation( String( orders[i] ),
                                    name( number[ orders[i] ] ) );
          number[ orders[i] ]:= number[ orders[i] ] + 1;
        else
          names[i]:= Concatenation( "?", name( unknown ) );
          unknown:= unknown + 1;
        fi;
      od;

    else

      names[1]:= Concatenation( "1", alpha[1] );
      for i in [ 2 .. NrConjugacyClasses( tbl ) ] do
        names[i]:= Concatenation( "?", name( i-1 ) );
      od;

    fi;

    # Return the list of classnames.
    return names;
    end );


#############################################################################
##
#M  \.( <tbl>, <name> ) . . . . . . . . . position of a class with given name
##
##  If <name> is a class name of the character table <tbl> as computed by
##  `ClassNames', `<tbl>.<name>' is the position of the class with this name.
##
InstallMethod( \.,
    "for class names of a nearly character table",
    true,
    [ IsNearlyCharacterTable, IsInt ], 0,
    function( tbl, name )
    local pos;
    name:= NameRNam( name );
    pos:= Position( ClassNames( tbl ), name );
    if pos = fail then
      TryNextMethod();
    else
      return pos;
    fi;
    end );


#############################################################################
##
#M  ClassParameters( <tbl> )
##
InstallMethod( ClassParameters,
    "for a Brauer table (if the ordinary table knows class parameters)",
    true,
    [ IsBrauerTable ], 0,
    function( tbl )
    local ord;
    ord:= OrdinaryCharacterTable( tbl );
    if HasClassParameters( ord ) then
      return ClassParameters( ord ){ GetFusionMap( tbl, ord ) };
    else
      TryNextMethod();
    fi;
    end );


#############################################################################
##
#M  ClassPositionsOfNormalSubgroups( <tbl> )
##
InstallMethod( ClassPositionsOfNormalSubgroups,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )

    local kernels,  # list of kernels of irreducible characters
          ker1,     # loop variable
          ker2,     # loop variable
          normal,   # list of normal subgroups, result
          inter;    # intersection of two kernels

    # get the kernels of irreducible characters
    kernels:= Set( List( Irr( tbl ), ClassPositionsOfKernel ) );

    # form all possible intersections of the kernels
    normal:= ShallowCopy( kernels );
    for ker1 in normal do
      for ker2 in kernels do
        inter:= Intersection( ker1, ker2 );
        if not inter in normal then
          Add( normal, inter );
        fi;
      od;
    od;

    # return the list of normal subgroups
    normal:= SSortedList( normal );
    Sort( normal, function( x, y ) return Length(x) < Length(y); end );
    return normal;
    end );


#############################################################################
##
#M  ClassPositionsOfMaximalNormalSubgroups( <tbl> )
##
##  *Note* that the maximal normal subgroups of a group <G> can be computed
##  easily if the character table of <G> is known.  So if you need the table
##  anyhow, you should compute it before computing the maximal normal
##  subgroups of the group.
##
InstallMethod( ClassPositionsOfMaximalNormalSubgroups,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )

    local normal,    # list of all kernels
          maximal,   # list of maximal kernels
          k;         # one kernel

    # Every normal subgroup is an intersection of kernels of characters,
    # so maximal normal subgroups are kernels of irreducible characters.
    normal:= Set( List( Irr( tbl ), ClassPositionsOfKernel ) );

    # Remove non-maximal kernels
    RemoveSet( normal, [ 1 .. NrConjugacyClasses( tbl ) ] );
    Sort( normal, function(x,y) return Length(x) > Length(y); end );
    maximal:= [];
    for k in normal do
      if ForAll( maximal, x -> not IsSubsetSet( x, k ) ) then

        # new maximal element found
        Add( maximal, k );

      fi;
    od;

    return maximal;
    end );


#############################################################################
##
#M  ClassPositionsOfAgemo( <tbl>, <p> )
##
InstallMethod( ClassPositionsOfAgemo,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable, IsPosInt ], 0,
    function( tbl, p )
    return ClassPositionsOfNormalClosure( tbl, Set( PowerMap( tbl, p ) ) );
    end );


#############################################################################
##
#M  ClassPositionsOfCentre( <tbl> )
##
InstallMethod( ClassPositionsOfCentre,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )
    local classes;
    classes:= SizesConjugacyClasses( tbl );
    return Filtered( [ 1 .. NrConjugacyClasses( tbl ) ],
                     x -> classes[x] = 1 );
    end );


#############################################################################
##
#M  ClassPositionsOfDerivedSubgroup( <tbl> )
##
InstallMethod( ClassPositionsOfDerivedSubgroup,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )

    local der,   # derived subgroup, result
          chi;   # one irreducible character

    der:= [ 1 .. NrConjugacyClasses( tbl ) ];
    for chi in Irr( tbl ) do
#T support `Lin' ?
      if DegreeOfCharacter( chi ) = 1 then
        IntersectSet( der, ClassPositionsOfKernel( chi ) );
      fi;
    od;
    return der;
    end );


#############################################################################
##
#M  ClassPositionsOfElementaryAbelianSeries( <tbl> )
##
InstallMethod( ClassPositionsOfElementaryAbelianSeries,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )

    local elab,         # el. ab. series, result
          nsg,          # list of normal subgroups of 'tbl'
          actsize,      # size of actual normal subgroup
          classes,      # conjugacy class lengths
          next,         # next smaller normal subgroup
          nextsize;     # size of next smaller normal subgroup

    # Sort normal subgroups according to decreasing number of classes.
    nsg:= ShallowCopy( ClassPositionsOfNormalSubgroups( tbl ) );

    elab:= [ [ 1 .. NrConjugacyClasses( tbl ) ] ];
    Unbind( nsg[ Length( nsg ) ] );

    actsize:= Size( tbl );
    classes:= SizesConjugacyClasses( tbl );

    repeat

      next:= nsg[ Length( nsg ) ];
      nextsize:= Sum( classes{ next }, 0 );
      Add( elab, next );
      Unbind( nsg[ Length( nsg ) ] );
      nsg:= Filtered( nsg, x -> IsSubset( next, x ) );

      if not IsPrimePowerInt( actsize / nextsize ) then
        # `tbl' is not the table of a solvable group.
        return fail;
      fi;

      actsize:= nextsize;

    until Length( nsg ) = 0;

    return elab;
    end );


#############################################################################
##
#M  ClassPositionsOfFittingSubgroup( <tbl> )
##
##  The Fitting subgroup is the maximal nilpotent normal subgroup, that is,
##  the product of all normal subgroups of prime power order.
##
InstallMethod( ClassPositionsOfFittingSubgroup,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )

    local nsg,      # all normal subgroups of 'tbl'
          classes,  # class lengths
          ppord,    # classes in normal subgroups of prime power order
          n;        # one normal subgroup of 'tbl'

    # Compute all normal subgroups.
    nsg:= ClassPositionsOfNormalSubgroups( tbl );

    # Take the union of classes in all normal subgroups of prime power order.
    classes:= SizesConjugacyClasses( tbl );
    ppord:= [ 1 ];
    for n in nsg do
      if IsPrimePowerInt( Sum( classes{n}, 0 ) ) then
        UniteSet( ppord, n );
      fi;
    od;

    # Return the normal closure.
    return ClassPositionsOfNormalClosure( tbl, ppord );
    end );


#############################################################################
##
#M  ClassPositionsOfLowerCentralSeries( <tbl> )
##
##  Let <tbl> the character table of the group $G$.
##  The lower central series $[ K_1, K_2, \ldots, K_n ]$ of $G$ is defined
##  by $K_1 = G$, and $K_{i+1} = [ K_i, G ]$.
##  'LowerCentralSeries( <tbl> )' is a list
##  $[ C_1, C_2, \ldots, C_n ]$ where $C_i$ is the set of positions of
##  $G$-conjugacy classes contained in $K_i$.
##
##  Given an element $x$ of $G$, then $g\in G$ is conjugate to $[x,y]$ for
##  an element $y\in G$ if and only if
##  $\sum_{\chi\in Irr(G)} \frac{|\chi(x)|^2 \overline{\chi(g)}}{\chi(1)}
##  \not= 0$, or equivalently, if the structure constant
##  $a_{x,\overline{x},g}$ is nonzero.
##
##  Thus $K_{i+1}$ consists of all classes $Cl(g)$ in $K_i$ for that there
##  is an $x\in K_i$ such that $a_{x,\overline{x},g}$ is nonzero.
##
InstallMethod( ClassPositionsOfLowerCentralSeries,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )

    local series,     # list of normal subgroups, result
          K,          # actual last element of 'series'
          inv,        # list of inverses of classes of 'tbl'
          mat,        # matrix of structure constants
          i, j,       # loop over 'mat'
          running,    # loop not yet terminated
          new;        # next element in 'series'

    series:= [];
    series[1]:= [ 1 .. NrConjugacyClasses( tbl ) ];
    K:= ClassPositionsOfDerivedSubgroup( tbl );
    if K = series[1] then
      return series;
    fi;
    series[2]:= K;

    # Compute the structure constants $a_{x,\overline{x},g}$ with $g$ and $x$
    # in $K_2$.
    # Put them into a matrix, the rows indexed by $g$, the columns by $x$.
    inv:= PowerMap( tbl, -1 );
    mat:= List( K, x -> [] );
    for i in [ 2 .. Length( K ) ] do
      for j in K do
        mat[i][j]:= ClassMultiplicationCoefficient( tbl, K[i], j, inv[j] );
      od;
    od;

    running:= true;

    while running do

      new:= [ 1 ];
      for i in [ 2 .. Length( mat ) ] do
        if ForAny( K, x -> mat[i][x] <> 0 ) then
          Add( new, i );
        fi;
      od;

      if Length( new ) = Length( K ) then
        running:= false;
      else
        mat:= mat{ new };
        K:= K{ new };
        Add( series, new );
      fi;

    od;

    return series;
    end );


#############################################################################
##
#F  CharacterTable_UpperCentralSeriesFactor( <tbl>, <N> )
##
InstallGlobalFunction( CharacterTable_UpperCentralSeriesFactor,
    function( tbl, N )

    local Z,      # result list
          n,      # number of conjugacy classes
          M,      # actual list of pairs kernel/centre of characters
          nextM,  # list of pairs in next iteration
          kernel, # kernel of a character
          centre, # centre of a character
          i,      # loop variable
          chi;    # loop variable

    n:= NrConjugacyClasses( tbl );
    N:= Set( N );

    # instead of the irreducibles store pairs $[ \ker(\chi), Z(\chi) ]$.
    # `Z' will be the list of classes forming $Z_1 = Z(G/N)$.
    M:= [];
    Z:= [ 1 .. n ];
    for chi in Irr( tbl ) do
      kernel:= ClassPositionsOfKernel( chi );
      if IsSubsetSet( kernel, N ) then
        centre:= ClassPositionsOfCentre( chi );
        AddSet( M, [ kernel, centre ] );
        IntersectSet( Z, centre );
      fi;
    od;

    Z:= [ Z ];
    i:= 0;

    repeat
      i:= i+1;
      nextM:= [];
      Z[i+1]:= [ 1 .. n ];
      for chi in M do
        if IsSubsetSet( chi[1], Z[i] ) then
          Add( nextM, chi );
          IntersectSet( Z[i+1], chi[2] );
        fi;
      od;
      M:= nextM;
    until Z[i+1] = Z[i];
    Unbind( Z[i+1] );

    return Z;
end );


#############################################################################
##
#M  ClassPositionsOfUpperCentralSeries( <tbl> )
##
InstallMethod( ClassPositionsOfUpperCentralSeries,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable ], 0,
    tbl -> CharacterTable_UpperCentralSeriesFactor( tbl, [1] ) );


#############################################################################
##
#M  ClassPositionsOfSupersolvableResiduum( <tbl> )
##
InstallMethod( ClassPositionsOfSupersolvableResiduum,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )

    local nsg,       # list of all normal subgroups
          i,         # loop variable, position in `nsg'
          N,         # one normal subgroup
          posN,      # position of `N' in `nsg'
          size,      # size of `N'
          nextsize,  # size of largest normal subgroup contained in `N'
          classes;   # class lengths

    nsg:= ClassPositionsOfNormalSubgroups( tbl );

    # Go down a chief series, starting with the whole group,
    # until there is no step of prime order.
    i:= Length( nsg );
    nextsize:= Size( tbl );
    classes:= SizesConjugacyClasses( tbl );

    while 1 < i do

      posN:= i;
      N:= nsg[ posN ];
      size:= nextsize;

      # Get the largest normal subgroup contained in `N' \ldots
      i:= posN - 1;
      while not IsSubsetSet( N, nsg[ i ] ) do i:= i-1; od;

      # \ldots and its size.
      nextsize:= Sum( classes{ nsg[i] }, 0 );

      if not IsPrimeInt( size / nextsize ) then

        # The chief factor `N / nsg[i]' is not of prime order,
        # i.e., `N' is the supersolvable residuum.
        return N;

      fi;

    od;

    # The group is supersolvable.
    return [ 1 ];
    end );


#############################################################################
##
#M  ClassPositionsOfNormalClosure( <tbl>, <classes> )
##
InstallMethod( ClassPositionsOfNormalClosure,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable, IsHomogeneousList and IsCyclotomicCollection ], 0,
    function( tbl, classes )

    local closure,   # classes forming the normal closure, result
          chi,       # one irreducible character of 'tbl'
          ker;       # classes forming the kernel of 'chi'

    closure:= [ 1 .. NrConjugacyClasses( tbl ) ];
    for chi in Irr( tbl ) do
      ker:= ClassPositionsOfKernel( chi );
      if IsSubset( ker, classes ) then
        IntersectSet( closure, ker );
      fi;
    od;

    return closure;
    end );


#############################################################################
##
#M  Identifier( <tbl> ) . . . . . . . . . . . . . . . . for an ordinary table
##
InstallMethod( Identifier,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )

    # If the table knows its group and if this group has a name, take this.
    if HasUnderlyingGroup( tbl ) then
      tbl:= UnderlyingGroup( tbl );
      if HasName( tbl ) then
        return Name( tbl );
      fi;
    fi;

    # Otherwise construct an identifier that is unique.
    LARGEST_IDENTIFIER_NUMBER[1]:= LARGEST_IDENTIFIER_NUMBER[1] + 1;
    tbl:= Concatenation( "CT", String( LARGEST_IDENTIFIER_NUMBER[1] ) );
    ConvertToStringRep( tbl );
    return tbl;
    end );


#############################################################################
##
#M  Identifier( <tbl> ) . . . . . . . . . . . . . . . . .  for a Brauer table
##
InstallMethod( Identifier,
    "for a Brauer table",
    true,
    [ IsBrauerTable ], 0,
    tbl -> Concatenation( Identifier( OrdinaryCharacterTable( tbl ) ),
                          "mod",
                          String( UnderlyingCharacteristic( tbl ) ) ) );


#############################################################################
##
#M  InverseClasses( <tbl> ) . . .  method for an ord. table with irreducibles
##
InstallMethod( InverseClasses,
    "for a character table with known irreducibles",
    true,
    [ IsCharacterTable and HasIrr ], 0,
    function( tbl )

    local nccl,
          irreds,
          inv,
          isinverse,
          chi,
          remain,
          i, j;

    nccl:= NrConjugacyClasses( tbl );
    irreds:= Irr( tbl );
    inv:= [ 1 ];

    isinverse:= function( i, j )         # is `j' the inverse of `i' ?
    for chi in irreds do
      if not IsRat( chi[i] ) and chi[i] <> GaloisCyc( chi[j], -1 ) then
        return false;
      fi;
    od;
    return true;
    end;

    remain:= [ 2 .. nccl ];
    for i in [ 2 .. nccl ] do
      if i in remain then
        for j in remain do
          if isinverse( i, j ) then
            inv[i]:= j;
            inv[j]:= i;
            SubtractSet( remain, Set( [ i, j ] ) );
            break;
          fi;
        od;
      fi;
    od;

    return inv;
    end );


#############################################################################
##
#M  InverseClasses( <tbl> ) . . . . . . . . . .  method for a character table
##
InstallMethod( InverseClasses,
    "for a character table",
    true,
    [ IsCharacterTable ], 0,
    tbl -> PowerMap( tbl, -1 ) );


#############################################################################
##
#M  RealClasses( <tbl> )  . . . . . . . . . . . . . . the real-valued classes
##
InstallMethod( RealClasses,
    "for a character table",
    true,
    [ IsCharacterTable ], 0,
    function( tbl )
    local inv;
    inv:= PowerMap( tbl, -1 );
    return Filtered( [ 1 .. NrConjugacyClasses( tbl ) ], i -> inv[i] = i );
    end );


#############################################################################
##
#M  ClassOrbit( <tbl>, <cc> ) . . . . . . . . .  classes of a cyclic subgroup
##
InstallMethod( ClassOrbit,
    "for a character table, and a positive integer",
    true,
    [ IsCharacterTable, IsPosInt ], 0,
    function( tbl, cc )
    local i, oo, res;

    res:= [ cc ];
    oo:= OrdersClassRepresentatives( tbl )[cc];

    # find all generators of <cc>
    for i in [ 2 .. oo-1 ] do
       if GcdInt(i, oo) = 1 then
          AddSet( res, PowerMap( tbl, i, cc ) );
       fi;
    od;

    return res;
    end );


#############################################################################
##
#M  ClassRoots( <tbl> ) . . . . . . . . . . . .  nontrivial roots of elements
##
InstallMethod( ClassRoots,
    "for a character table",
    true,
    [ IsCharacterTable ], 0,
    function( tbl )

    local i, nccl, orders, p, pmap, root;

    nccl   := NrConjugacyClasses( tbl );
    orders := OrdersClassRepresentatives( tbl );
    root   := List([1..nccl], x->[]);

    for p in Set( Factors( Size( tbl ) ) ) do
       pmap:= PowerMap( tbl, p );
       for i in [1..nccl] do
          if i <> pmap[i] and orders[i] <> orders[pmap[i]] then
             AddSet(root[pmap[i]], i);
          fi;
       od;
    od;

    return root;
    end );


#############################################################################
##
##  x. Operations Concerning Blocks
##


#############################################################################
##
#M  PrimeBlocks( <tbl>, <p> )
##
InstallMethod( PrimeBlocks,
    "for an ordinary table, and a positive integer",
    true,
    [ IsOrdinaryTable, IsPosInt ], 0,
    function( tbl, p )

    local known, erg;

    if not IsPrimeInt( p ) then
      Error( "<p> a prime" );
    fi;

    known:= ComputedPrimeBlockss( tbl );

    # Start storing only after the result has been computed.
    # This avoids errors if a calculation had been interrupted.
    if not IsBound( known[p] ) then
      erg:= PrimeBlocksOp( tbl, p );
      known[p]:= erg;
    fi;

    return known[p];
    end );


#############################################################################
##
#M  PrimeBlocksOp( <tbl>, <p> )
##
##  Two ordinary irreducible characters $\chi, \psi$ of a group $G$ are said
##  to lie in the same $p$-block if the images of their central characters
##  $\omega_{\chi}, \omega_{\psi}$ under the homomorphism
##  $\ast \colon R \rightarrow R / M$ are equal.
##  The central character is the class function defined by
##  $\omega_{\chi}(g) = \chi(g) |Cl_G(g)| / \chi(1)$.
##  $R$ denotes the ring of algebraic integers in the complex numbers,
##  $M$ is a maximal ideal in $R$ with $pR \subseteq M$.
##  Thus $F = R/M$ is a field of characteristics $p$.
##
##  $\chi$ and $\psi$ lie in the same $p$-block if and only if there is an
##  integer $n$ such that $(\omega_{chi}(g) - \omega_{\psi}(g))^n \in pR$
##  (see~\cite{Isaacs}, p.~271).
##
##  Following the proof in~\cite{Isaacs},
##  a sufficient value for $n$ is $\varphi(\|g\|)$.
##  The test must be performed only for one class of each Galois family.
##
##  It is sufficient to test $p$-regular classes. % (see Feit, p.~150)
##
##  Any character $\chi$ where $p$ does not divide $\|G\| / \chi(1)$
##  (such a character is called defect zero character) forms a block of its
##  own.
##
##  For $|G| = p^a m$ where $p$ does not divide $m$, the defect of a block
##  is that $d$ where $p^{a-d}$ is the largest power of $p$ that divides all
##  degrees of the characters in the block.
##
##  The height of a $\chi$ is then the largest exponent $h$ where $p^h$
##  divides $\chi(1) / p^{a-d}$.
##
InstallMethod( PrimeBlocksOp,
    "for an ordinary table, and a positive integer",
    true,
    [ IsOrdinaryTable, IsPosInt ], 0,
    function( tbl, prime )

    local i, j,
          characters,
          nccl,
          classes,
          tbl_orders,
          primeblocks,
          blockreps,
          exponents,
          families,
          representatives,
          sameblock,
          central,
          found,
          ppart,
          tbl_irredinfo,
          inverse,
          d,
          filt,
          pos;

    characters:= List( Irr( tbl ), ValuesOfClassFunction );
    nccl:= Length( characters[1] );
    classes:= SizesConjugacyClasses( tbl );
    tbl_orders:= OrdersClassRepresentatives( tbl );

    primeblocks:= rec( block:= [], defect:= [] );
    blockreps:= [];

    # Compute a representative for each Galois family
    # of 'prime'-regular classes.
    families:= GaloisMat( TransposedMat( characters ) ).galoisfams;
#T better introduce attribute `RepCycSub' ?
    representatives:= Filtered( [ 2 .. nccl ],
                                x ->     families[x] <> 0
                                     and tbl_orders[x] mod prime <> 0 );

    exponents:= [];
    for i in representatives do
      exponents[i]:= Phi( tbl_orders[i] );
    od;

    # Compute the order of the 'prime' Sylow group of 'tbl'.
    ppart:= 1;
    d:= Size( tbl ) / prime;
    while IsInt( d ) do
      ppart:= ppart * prime;
      d:= d / prime;
    od;

    sameblock:= function( central1, central2 )
    local i, j, value, coeffs, n;
    for i in representatives do
      value:= central1[i] - central2[i];
      if IsInt( value ) then
        if value mod prime <> 0 then return false; fi;
      elif IsCyc( value ) then
        coeffs:= List( COEFFS_CYC( value ), x -> x mod prime );
        value:= 0;
        n:= Length( coeffs );
        for j in [ 1 .. Length( coeffs ) ] do
          value:= value + coeffs[j] * E( n ) ^ ( j - 1 );
        od;
#T `value mod prime' ?
        if not IsCycInt( ( value ^ exponents[i] ) / prime ) then
          return false;
        fi;
      else
        return false;
      fi;
    od;
    return true;
    end;

    for i in [ 1 .. Length( characters ) ] do
      if characters[i][1] mod ppart = 0 then

        # defect zero character
        pos:= Position( characters, characters[i] );
        if pos = i then
#T why useful ??
          Add( blockreps, characters[i] );
          primeblocks.block[i]:= Length( blockreps );
        else
          primeblocks.block[i]:= primeblocks.block[ pos ];
        fi;

      else
        central:= [];                       # the central character
        for j in [ 2 .. nccl ] do
          central[j]:= classes[j] * characters[i][j] / characters[i][1];
          if not IsCycInt( central[j] ) then
            Error( "central character ", i,
                   " is not an algebraic integer at class ", j );
          fi;
        od;
        j:= 1;
        found:= false;
        while j <= Length( blockreps ) and not found do
          if sameblock( central, blockreps[j] ) then
            primeblocks.block[i]:= j;
            found:= true;
          fi;
          j:= j + 1;
        od;
        if not found then
          Add( blockreps, central );
          primeblocks.block[i]:= Length( blockreps );
        fi;
      fi;
    od;

    # Compute the defects.
    inverse:= InverseMap( primeblocks.block );
    for i in inverse do
      if IsInt( i ) then
        Add( primeblocks.defect, 0 );    # defect zero character
        Info( InfoCharacterTable, 2,
              "defect 0: X[", i, "]" );
      else
        d:= ppart;
        for j in i do d:= GcdInt( d, characters[j][1] ); od;
        if d = ppart then
          d:= 0;
        else
          d:= Length( FactorsInt( ppart / d ) );              # the defect
        fi;
        Add( primeblocks.defect, d );

        if 2 <= InfoLevel( InfoCharacterTable ) then

          # print defect and heights
          Print( "#I defect ", d, ";\n" );

          for j in [ 0 .. d ] do
            filt:= Filtered( i, x -> GcdInt( ppart, characters[x][1] )
                                     = ppart / prime^(d-j) );
            if filt <> [] then
              Print( "#I     height ", j, ": X", filt, "\n" );
            fi;
          od;
        fi;

      fi;
    od;

    # Return the result.
    return primeblocks;
    end );


#############################################################################
##
#M  ComputedPrimeBlockss( <tbl> )
##
InstallMethod( ComputedPrimeBlockss,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable ], 0,
    tbl -> [] );


#############################################################################
##
#M  BlocksInfo( <modtbl> )
##
InstallMethod( BlocksInfo,
    "generic method for a Brauer character table",
    true,
    [ IsBrauerTable ], 0,
    function( modtbl )

    local ordtbl, prime, modblocks, decinv, k, ilist, ibr, rest, pblocks,
          ordchars, decmat, nccmod, modchars;

    ordtbl    := OrdinaryCharacterTable( modtbl );
    prime     := UnderlyingCharacteristic( modtbl );
    modblocks := [];

    if Size( ordtbl ) mod prime <> 0 then

      # If characteristic and group order are coprime then all blocks
      # are trivial.
      # (We do not need the Brauer characters.)
      decinv:= [ [ 1 ] ];
      MakeImmutable( decinv );
      for k in [ 1 .. NrConjugacyClasses( ordtbl ) ] do

        ilist:= [ k ];
        MakeImmutable( ilist );

        modblocks[k]:= rec( defect   := 0,
                            ordchars := ilist,
                            modchars := ilist,
                            basicset := ilist,
                            decinv   := decinv );

      od;

    else

      # We use the irreducible Brauer characters.
      ibr      := Irr( modtbl );
      rest     := RestrictedClassFunctions( Irr( ordtbl ), modtbl );
      pblocks  := PrimeBlocks( ordtbl, prime );
      ordchars := InverseMap( pblocks.block );
      decmat   := Decomposition( ibr, rest, "nonnegative" );
      nccmod   := Length( decmat[1] );
      for k in [ 1 .. Length( ordchars ) ] do
        if IsInt( ordchars[k] ) then
          ordchars[k]:= [ ordchars[k] ];
        fi;
      od;
      MakeImmutable( ordchars );

      for k in [ 1 .. Length( pblocks.defect ) ] do

        modchars:= Filtered( [ 1 .. nccmod ],
                             j -> ForAny( ordchars[k],
                                          i -> decmat[i][j] <> 0 ) );
        MakeImmutable( modchars );

        modblocks[k]:= rec( defect   := pblocks.defect[k],
                            ordchars := ordchars[k],
                            modchars := modchars );

      od;

    fi;

    # Return the blocks information.
    return modblocks;
    end );


#############################################################################
##
#M  DecompositionMatrix( <modtbl> )
##
InstallMethod( DecompositionMatrix,
    "for a Brauer table",
    true,
    [ IsBrauerTable ], 0,
    function( modtbl )
    local ordtbl;
    ordtbl:= OrdinaryCharacterTable( modtbl );
    return Decomposition( List( Irr( modtbl ), ValuesOfClassFunction ),
               RestrictedClassFunctions( ordtbl,
                   List( Irr( ordtbl ), ValuesOfClassFunction ), modtbl ),
               "nonnegative" );
    end );


#############################################################################
##
#M  DecompositionMatrix( <modtbl>, <blocknr> )
##
InstallMethod( DecompositionMatrix,
    "for a Brauer table, and a positive integer",
    true,
    [ IsBrauerTable, IsPosInt ], 0,
    function( modtbl, blocknr )

    local ordtbl,    # corresponding ordinary table
          block,     # block information
          fus,       # class fusion from `modtbl' to `ordtbl'
          ordchars,  # restrictions of ord. characters in the block
          modchars;  # Brauer characters in the block

    block:= BlocksInfo( modtbl );

    if blocknr <= Length( block ) then
      block:= block[ blocknr ];
    else
      Error( "<blocknr> must be in the range [ 1 .. ",
             Length( block ), " ]" );
    fi;

    if not IsBound( block.decmat ) then

      if block.defect = 0 then
        block.decmat:= [ [ 1 ] ];
      else
        ordtbl:= OrdinaryCharacterTable( modtbl );
        fus:= GetFusionMap( modtbl, ordtbl );
        ordchars:= List( Irr( ordtbl ){ block.ordchars },
                         chi -> ValuesOfClassFunction( chi ){ fus } );
        modchars:= List( Irr( modtbl ){ block.modchars },
                         ValuesOfClassFunction );
        block.decmat:= Decomposition( modchars, ordchars, "nonnegative" );
      fi;
      MakeImmutable( block.decmat );

    fi;

    return block.decmat;
    end );


#############################################################################
##
#F  LaTeXStringDecompositionMatrix( <modtbl>[, <blocknr>][, <options>] )
##
InstallGlobalFunction( LaTeXStringDecompositionMatrix, function( arg )

    local modtbl,        # Brauer character table, first argument
          blocknr,       # number of the block, optional second argument
          options,       # record with labels, optional third argument
          decmat,        # decomposition matrix
          block,         # block information on 'modtbl'
          collabels,     # indices of Brauer characters
          rowlabels,     # indices of ordinary characters
          phi,           # string used for Brauer characters
          chi,           # string used for ordinary irreducibles
          hlines,        # explicitly wanted horizontal lines
          ulc,           # text for the upper left corner
          r,
          k,
          n,
          rowportions,
          colportions,
          str,           # string containing the text
          i,             # loop variable
          val;           # one value in the matrix

    # Get and check the arguments.
    if   Length( arg ) = 2 and IsBrauerTable( arg[1] )
                           and IsRecord( arg[2] ) then

      options := arg[2];

    elif Length( arg ) = 2 and IsBrauerTable( arg[1] )
                           and IsInt( arg[2] ) then

      blocknr := arg[2];
      options := rec();

    elif Length( arg ) = 3 and IsBrauerTable( arg[1] )
                           and IsInt( arg[2] )
                           and IsRecord( arg[3] ) then

      blocknr := arg[2];
      options := arg[3];

    elif Length( arg ) = 1 and IsBrauerTable( arg[1] ) then

      options := rec();

    else
      Error( "usage: LatexStringDecompositionMatrix(",
             " <modtbl>[, <blocknr>][, <options>] )" );
    fi;

    # Compute the decomposition matrix.
    modtbl:= arg[1];
    if IsBound( options.decmat ) then
      decmat:= options.decmat;
    elif IsBound( blocknr ) then
      decmat:= DecompositionMatrix( modtbl, blocknr );
    else
      decmat:= DecompositionMatrix( modtbl );
    fi;

    # Choose default labels if necessary.
    rowportions:= [ [ 1 .. Length( decmat ) ] ];
    colportions:= [ [ 1 .. Length( decmat[1] ) ] ];

    phi:= "{\\tt Y}";
    chi:= "{\\tt X}";

    hlines:= [];
    ulc:= "";

    # Construct the labels if necessary.
    if IsBound( options.phi ) then
      phi:= options.phi;
    fi;
    if IsBound( options.chi ) then
      chi:= options.chi;
    fi;
    if IsBound( options.collabels ) then
      collabels:= options.collabels;
      if ForAll( collabels, IsInt ) then
        collabels:= List( collabels,
            i -> Concatenation( phi, "_{", String(i), "}" ) );
      fi;
    fi;
    if IsBound( options.rowlabels ) then
      rowlabels:= options.rowlabels;
      if ForAll( rowlabels, IsInt ) then
        rowlabels:= List( rowlabels,
            i -> Concatenation( chi, "_{", String(i), "}" ) );
      fi;
    fi;

    # Distribute to row and column portions if necessary.
    if IsBound( options.nrows ) then
      if IsInt( options.nrows ) then
        r:= options.nrows;
        n:= Length( decmat );
        k:= Int( n / r );
        rowportions:= List( [ 1 .. k ], i -> [ 1 .. r ] + (i-1)*r );
        if n > k*r then
          Add( rowportions, [ k*r + 1 .. n ] );
        fi;
      else
        rowportions:= options.nrows;
      fi;
    fi;
    if IsBound( options.ncols ) then
      if IsInt( options.ncols ) then
        r:= options.ncols;
        n:= Length( decmat[1] );
        k:= Int( n / r );
        colportions:= List( [ 1 .. k ], i -> [ 1 .. r ] + (i-1)*r );
        if n > k*r then
          Add( colportions, [ k*r + 1 .. n ] );
        fi;
      else
        colportions:= options.ncols;
      fi;
    fi;

    # Check for horizontal lines.
    if IsBound( options.hlines ) then
      hlines:= options.hlines;
    fi;

    # Check for text in the upper left corner.
    if IsBound( options.ulc ) then
      ulc:= options.ulc;
    fi;

    Add( hlines, Length( decmat ) );

    # Construct the labels if they are still missing.
    if not IsBound( collabels ) then

      if IsBound( blocknr ) then
        block     := BlocksInfo( modtbl )[ blocknr ];
        collabels := List( block.modchars, String );
      else
        collabels := List( [ 1 .. Length( decmat[1] ) ], String );
      fi;
      collabels:= List( collabels, i -> Concatenation( phi,"_{",i,"}" ) );

    fi;
    if not IsBound( rowlabels ) then

      if IsBound( blocknr ) then
        block     := BlocksInfo( modtbl )[ blocknr ];
        rowlabels := List( block.ordchars, String );
      else
        rowlabels := List( [ 1 .. Length( decmat ) ], String );
      fi;
      rowlabels:= List( rowlabels, i -> Concatenation( chi,"_{",i,"}" ) );

    fi;

    # Construct the string.
    str:= "";

    for r in rowportions do

      for k in colportions do

        # Append the header of the array.
        Append( str,  "\\[\n" );
        Append( str,  "\\begin{array}{r|" );
        for i in k do
          Add( str, 'r' );
        od;
        Append( str, "} \\hline\n" );

        # Append the text in the upper left corner.
        if not IsEmpty( ulc ) then
          if r = rowportions[1] and k = colportions[1] then
            Append( str, ulc );
          else
            Append( str, Concatenation( "(", ulc, ")" ) );
          fi;
        fi;

        # The first line contains the Brauer character numbers.
        for i in collabels{ k } do
          Append( str, " & " );
          Append( str, String( i ) );
          Append( str, "\n" );
        od;
        Append( str, " \\rule[-7pt]{0pt}{20pt} \\\\ \\hline\n" );

        # Append the matrix itself.
        for i in r do

          # The first column contains the numbers of ordinary irreducibles.
          Append( str, String( rowlabels[i] ) );

          for val in decmat[i]{ k } do
            Append( str, " & " );
            if val = 0 then
              Append( str, "." );
            else
              Append( str, String( val ) );
            fi;
          od;

          if i = r[1] or i-1 in hlines then
            Append( str, " \\rule[0pt]{0pt}{13pt}" );
          fi;
          if i = r[ Length( r ) ] or i in hlines then
            Append( str, " \\rule[-7pt]{0pt}{5pt}" );
          fi;

          Append( str, " \\\\\n" );

          if i in hlines then
            Append( str, "\\hline\n" );
          fi;

        od;

        # Append the tail of the array
        Append( str,  "\\end{array}\n" );
        Append( str,  "\\]\n\n" );

      od;

    od;

    Unbind( str[ Length( str ) ] );
    ConvertToStringRep( str );

    # Return the result.
    return str;
end );


#############################################################################
##
##  7. Other Operations for Character Tables
##


#############################################################################
##
#M  IsInternallyConsistent( <tbl> ) . . . . . . . . . . for a character table
##
##  Check consistency of information in the head of the character table
##  <tbl>, and check if the first orthogonality relation is satisfied.
##
InstallMethod( IsInternallyConsistent,
    "for a character table",
    true,
    [ IsCharacterTable ], 0,
    function( tbl )

    local flag,            # `true' if no inconsistency occurred yet
          centralizers,
          order,
          nccl,
          classes,
          orders,
          i, j, k, x,
          powermap,
          characters, map, row, sum,
          tbl_irredinfo;

    flag:= true;

    # Check that `Size', `SizesCentralizers', `SizesConjugacyClasses'
    # are consistent.
    centralizers:= SizesCentralizers( tbl );
    order:= centralizers[1];
    if HasSize( tbl ) then
      if Size( tbl ) <> order then
        Info( InfoWarning, 1,
              "IsInternallyConsistent(", tbl,
              "): centralizer of identity not equal to group order" );
        flag:= false;
      fi;
    fi;

    nccl:= Length( centralizers );
    if HasSizesConjugacyClasses( tbl ) then
      classes:= SizesConjugacyClasses( tbl );
      if classes <> List( centralizers, x -> order / x ) then
        Info( InfoWarning, 1,
              "IsInternallyConsistent(", tbl,
              "): centralizers and class lengths inconsistent" );
        flag:= false;
      fi;
      if Length( classes ) <> nccl then
        Info( InfoWarning, 1,
              "IsInternallyConsistent(", tbl,
              "): number of classes and centralizers inconsistent" );
        flag:= false;
      fi;
    else
      classes:= List( centralizers, x -> order / x );
    fi;

    if Sum( classes, 0 ) <> order then
      Info( InfoWarning, 1,
            "IsInternallyConsistent(", tbl,
            "): sum of class lengths not equal to group order" );
      flag:= false;
    fi;

    if HasOrdersClassRepresentatives( tbl ) then
      orders:= OrdersClassRepresentatives( tbl );
      if nccl <> Length( orders ) then
        Info( InfoWarning, 1,
              "IsInternallyConsistent(", tbl,
              "): number of classes and orders inconsistent" );
        flag:= false;
      else
        for i in [ 1 .. nccl ] do
          if centralizers[i] mod orders[i] <> 0 then
            Info( InfoWarning, 1,
                  "IsInternallyConsistent(", tbl,
                  "): not all representative orders divide the\n",
                  "#I   corresponding centralizer order" );
            flag:= false;
          fi;
        od;
      fi;
    fi;

    if HasComputedPowerMaps( tbl ) then
      powermap:= ComputedPowerMaps( tbl );
      for map in Set( powermap ) do
        if nccl <> Length( map ) then
          Info( InfoWarning, 1,
                "IsInternallyConsistent(", tbl,
                "): lengths of power maps and classes inconsistent" );
          flag:= false;
        fi;
      od;

      # If the power maps of all prime divisors of the order are stored,
      # check if they are consistent with the representative orders.
      if     IsBound( orders )
         and ForAll( Set( FactorsInt( order ) ), x -> IsBound(powermap[x]) )
         and orders <> ElementOrdersPowerMap( powermap ) then
        flag:= false;
        Info( InfoWarning, 1,
              "IsInternallyConsistent(", tbl,
              "): representative orders and power maps inconsistent" );
      fi;
    fi;

    # From here on, we check the irreducible characters.
    if flag = false then
      Info( InfoWarning, 1,
            "IsInternallyConsistent(", tbl,
            "): corrupted table, no test of orthogonality" );
      return false;
    fi;

    if HasIrr( tbl ) then
      characters:= List( Irr( tbl ), ValuesOfClassFunction );
      for i in [ 1 .. Length( characters ) ] do
        row:= [];
        for j in [ 1 .. Length( characters[i] ) ] do
          row[j]:= GaloisCyc( characters[i][j], -1 ) * classes[j];
        od;
        for j in [ 1 .. i ] do
          sum:= row * characters[j];
          if ( i = j and sum <> order ) or ( i <> j and sum <> 0 ) then
            flag:= false;
            Info( InfoWarning, 1,
                  "IsInternallyConsistent(", tbl,
                  "): Scpr( ., X[", i, "], X[", j, "] ) = ",
                  sum / order );
          fi;
        od;
      od;

      if centralizers <> Sum( characters,
                              x -> List( x, y -> y * GaloisCyc(y,-1) ),
                              0 ) then
        flag:= false;
        Info( InfoWarning, 1,
              "IsInternallyConsistent(", tbl,
              "): centralizer orders inconsistent with irreducibles" );
      fi;

#T what about indicators, p-blocks?
    fi;

    return flag;
    end );


#############################################################################
##
#M  IsPSolvableCharacterTable( <tbl>, <p> )
##
InstallMethod( IsPSolvableCharacterTable,
    "for ord. char. table, and zero (call `IsPSolvableCharacterTableOp')",
    true,
    [ IsOrdinaryTable, IsZeroCyc ], 0,
    IsPSolvableCharacterTableOp );

InstallMethod( IsPSolvableCharacterTable,
    "for ord. char. table knowing `IsSolvableCharacterTable', and zero",
    true,
    [ IsOrdinaryTable and HasIsSolvableCharacterTable, IsZeroCyc ], 0,
    function( tbl, zero )
    return IsSolvableCharacterTable( tbl );
    end );

InstallMethod( IsPSolvableCharacterTable,
    "for ord.char.table, and pos.int. (call `IsPSolvableCharacterTableOp')",
    true,
    [ IsOrdinaryTable, IsPosInt ], 0,
    function( tbl, p )
    local known, erg;

    if not IsPrimeInt( p ) then
      Error( "<p> must be zero or a prime integer" );
    fi;

    known:= ComputedIsPSolvableCharacterTables( tbl );

    # Start storing only after the result has been computed.
    # This avoids errors if a calculation had been interrupted.
    if not IsBound( known[p] ) then
      erg:= IsPSolvableCharacterTableOp( tbl, p );
      known[p]:= erg;
    fi;

    return known[p];
    end );


#############################################################################
##
#M  IsPSolvableCharacterTableOp( <tbl>, <p> )
##
InstallMethod( IsPSolvableCharacterTableOp,
    "for an ordinary character table, an an integer",
    true,
    [ IsOrdinaryTable, IsInt ], 0,
    function( tbl, p )

    local nsg,       # list of all normal subgroups
          i,         # loop variable, position in 'nsg'
          n,         # one normal subgroup
          posn,      # position of 'n' in 'nsg'
          size,      # size of 'n'
          nextsize,  # size of smallest normal subgroup containing 'n'
          classes,   # class lengths
          facts;     # set of prime factors of a chief factor

    nsg:= ClassPositionsOfNormalSubgroups( tbl );

    # Go up a chief series, starting with the trivial subgroup
    i:= 1;
    nextsize:= 1;
    classes:= SizesConjugacyClasses( tbl );

    while i < Length( nsg ) do

      posn:= i;
      n:= nsg[ posn ];
      size:= nextsize;

      # Get the smallest normal subgroup containing `n' \ldots
      i:= posn + 1;
      while not IsSubsetSet( nsg[ i ], n ) do i:= i+1; od;

      # \ldots and its size.
      nextsize:= Sum( classes{ nsg[i] }, 0 );

      facts:= Set( FactorsInt( nextsize / size ) );
      if 1 < Length( facts ) and ( p = 0 or p in facts ) then

        # The chief factor `nsg[i] / n' is not a prime power,
        # and our `p' divides its order.
        return false;

      fi;

    od;
    return true;
    end );


#############################################################################
##
#M  ComputedIsPSolvableCharacterTables( <tbl> )
##
InstallMethod( ComputedIsPSolvableCharacterTables,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    tbl -> [] );


#############################################################################
##
#M  Indicator( <tbl>, <n> )
#M  Indicator( <modtbl>, 2 )
##
InstallMethod( Indicator,
    "for a character table, and a positive integer",
    true,
    [ IsCharacterTable, IsPosInt ], 0,
    function( tbl, n )

    local known, erg;

    if IsBrauerTable( tbl ) and n <> 2 then
      TryNextMethod();
    fi;

    known:= ComputedIndicators( tbl );

    # Start storing only after the result has been computed.
    # This avoids errors if a calculation had been interrupted.
    if not IsBound( known[n] ) then
      erg:= IndicatorOp( tbl, Irr( tbl ), n );
      known[n]:= erg;
    fi;

    return known[n];
    end );


#############################################################################
##
#M  Indicator( <tbl>, <characters>, <n> )
##
InstallMethod( Indicator,
    "for a character table, a homogeneous list, and a positive integer",
    true,
    [ IsCharacterTable, IsHomogeneousList, IsPosInt ], 0,
    IndicatorOp );


#############################################################################
##
#M  IndicatorOp( <ordtbl>, <characters>, <n> )
#M  IndicatorOp( <modtbl>, <characters>, 2 )
##
InstallMethod( IndicatorOp,
    "for an ord. character table, a hom. list, and a pos. integer",
    true,
    [ IsOrdinaryTable, IsHomogeneousList, IsPosInt ], 0,
    function( tbl, characters, n )

    local principal, map;

    principal:= List( [ 1 .. NrConjugacyClasses( tbl ) ], x -> 1 );
    map:= PowerMap( tbl, n );
    return List( characters,
                 chi -> ScalarProduct( tbl, chi{ map }, principal ) );
    end );

InstallMethod( IndicatorOp,
    "for a Brauer character table and <n> = 2",
    true,
    [ IsBrauerTable, IsHomogeneousList, IsPosInt ], 0,
    function( modtbl, ibr, n )

    local ordtbl,
          irr,
          ordindicator,
          fus,
          indicator,
          i,
          j,
          odd;

    if n <> 2 then
      Error( "for Brauer table <modtbl> only for <n> = 2" );
    elif Characteristic( modtbl ) = 2 then
      Error( "for Brauer table <modtbl> only in odd characteristic" );
    fi;

    ordtbl:= OrdinaryCharacterTable( modtbl );
    irr:= Irr( ordtbl );
#   ibr:= Irr( modtbl );
    ordindicator:= Indicator( ordtbl, irr, 2 );
    fus:= GetFusionMap( modtbl, ordtbl );

    # compute indicators block by block
    indicator:= [];

    for i in BlocksInfo( modtbl ) do
      if not IsBound( i.decmat ) then
        i.decmat:= Decomposition( ibr{ i.modchars },
                         List( irr{ i.ordchars },
                               x -> x{ fus } ), "nonnegative" );
      fi;
      for j in [ 1 .. Length( i.modchars ) ] do
        if ForAny( ibr[ i.modchars[j] ],
                   x -> not IsInt(x) and GaloisCyc(x,-1) <> x ) then

          # indicator of a Brauer character is 0 iff it has
          # at least one nonreal value
          indicator[ i.modchars[j] ]:= 0;

        else

          # indicator is equal to the indicator of any real ordinary
          # character containing it as constituent, with odd multiplicity
          odd:= Filtered( [ 1 .. Length( i.decmat ) ],
                          x -> i.decmat[x][j] mod 2 <> 0 );
          odd:= List( odd, x -> ordindicator[ i.ordchars[x] ] );
          indicator[ i.modchars[j] ]:= First( odd, x -> x <> 0 );

        fi;
      od;
    od;

    return indicator;
    end );


#############################################################################
##
#M  ComputedIndicators( <tbl> )
##
InstallMethod( ComputedIndicators,
    "for a character table",
    true,
    [ IsCharacterTable ], 0,
    tbl -> [] );


#############################################################################
##
#F  NrPolyhedralSubgroups( <tbl>, <c1>, <c2>, <c3>)  . # polyhedral subgroups
##
InstallGlobalFunction( NrPolyhedralSubgroups, function(tbl, c1, c2, c3)
    local orders, res, ord;

    orders:= OrdersClassRepresentatives( tbl );

    if orders[c1] = 2 then
       res:= ClassMultiplicationCoefficient(tbl, c1, c2, c3)
             * SizesConjugacyClasses( tbl )[c3];
       if orders[c2] = 2 then
          if orders[c3] = 2 then   # V4
             ord:= Length(Set([c1, c2, c3]));
             if ord = 2 then
                res:= res * 3;
             elif ord = 3 then
                res:= res * 6;
             fi;
             res:= res / 6;
             if not IsInt(res) then
                Error("noninteger result");
             fi;
             return rec(number:= res, type:= "V4");
          elif orders[c3] > 2 then   # D2n
             ord:= orders[c3];
             if c1 <> c2 then
                res:= res * 2;
             fi;
             res:= res * Length(ClassOrbit(tbl,c3))/(ord*Phi(ord));
             if not IsInt(res) then
                Error("noninteger result");
             fi;
             return rec(number:= res,
                        type:= Concatenation("D" ,String(2*ord)));
          fi;
       elif orders[c2] = 3 then
          if orders[c3] = 3 then   # A4
             res:= res * Length(ClassOrbit(tbl, c3)) / 24;
             if not IsInt(res) then
                Error("noninteger result");
             fi;
             return rec(number:= res, type:= "A4");
          elif orders[c3] = 4 then   # S4
             res:= res / 24;
             if not IsInt(res) then
                Error("noninteger result");
             fi;
             return rec(number:= res, type:= "S4");
          elif orders[c3] = 5 then   # A5
             res:= res * Length(ClassOrbit(tbl, c3)) / 120;
             if not IsInt(res) then
                Error("noninteger result");
             fi;
             return rec(number:= res, type:= "A5");
          fi;
       fi;
    fi;
end );


#############################################################################
##
#M  ClassMultiplicationCoefficient( <ordtbl>, <c1>, <c2>, <c3> )
##
InstallMethod( ClassMultiplicationCoefficient,
    "for an ord. table, and three pos. integers",
    true,
    [ IsOrdinaryTable, IsPosInt, IsPosInt, IsPosInt ], 10,
    function( ordtbl, c1, c2, c3 )

    local res, chi, char, classes;

    res:= 0;
    for chi in Irr( ordtbl ) do
       char:= ValuesOfClassFunction( chi );
       res:= res + char[c1] * char[c2] * GaloisCyc(char[c3], -1) / char[1];
    od;
    classes:= SizesConjugacyClasses( ordtbl );
    return classes[c1] * classes[c2] * res / Size( ordtbl );
    end );


#############################################################################
##
#F  MatClassMultCoeffsCharTable( <tbl>, <class> )
##
InstallGlobalFunction( MatClassMultCoeffsCharTable, function( tbl, class )
    local nccl;
    nccl:= NrConjugacyClasses( tbl );
    return List( [ 1 .. nccl ],
                 j -> List( [ 1 .. nccl ],
                 k -> ClassMultiplicationCoefficient( tbl, class, j, k ) ) );
end );


#############################################################################
##
#F  ClassStructureCharTable(<tbl>,<classes>)  . gener. class mult. coefficent
##
InstallGlobalFunction( ClassStructureCharTable, function( tbl, classes )

    local exp;

    exp:= Length( classes ) - 2;
    if exp < 0 then
      Error( "length of <classes> must be at least 2" );
    fi;

    return Sum( Irr( tbl ),
                chi -> Product( chi{ classes }, 1 ) / ( chi[1] ^ exp ),
                0 )
           * Product( SizesConjugacyClasses( tbl ){ classes }, 1 )
           / Size( tbl );
end );


#############################################################################
##
##  8. Creating Character Tables
##


#############################################################################
##
#M  CharacterTable( <G> ) . . . . . . . . . . ordinary char. table of a group
#M  CharacterTable( <G>, <p> )  . . . . . characteristic <p> table of a group
#M  CharacterTable( <ordtbl>, <p> )
##
##  We delegate to `OrdinaryCharacterTable' or `BrauerTable'.
##
InstallMethod( CharacterTable,
    "for a group (delegate to `OrdinaryCharacterTable')",
    true,
    [ IsGroup ], 0,
    OrdinaryCharacterTable );

InstallMethod( CharacterTable,
    "for a group, and a prime integer",
    true,
    [ IsGroup, IsInt ], 0,
    function( G, p )
    if p = 0 then
      return OrdinaryCharacterTable( G );
    else
      return BrauerTable( OrdinaryCharacterTable( G ), p );
    fi;
    end );

InstallMethod( CharacterTable,
    "for an ordinary table, and a prime integer",
    true,
    [ IsOrdinaryTable, IsPosInt ], 0,
    BrauerTable );


#############################################################################
##
#M  BrauerTable( <ordtbl>, <p> )  . . . . . . . . . . . . . <p>-modular table
#M  BrauerTable( <G>, <p> )
##
##  Note that Brauer tables are stored in the ordinary table and not in the
##  group.
##
InstallMethod( BrauerTable,
    "for a group, and a prime (delegate to the ord. table of the group)",
    true,
    [ IsGroup, IsPosInt ], 0,
    function( G, p )
    return BrauerTable( OrdinaryCharacterTable( G ), p );
    end );

InstallMethod( BrauerTable,
    "for an ordinary table, and a prime",
    true,
    [ IsOrdinaryTable, IsPosInt ], 0,
    function( ordtbl, p )

    local known, erg;

    if not IsPrimeInt( p ) then
      Error( "<p> must be a prime" );
    fi;

    known:= ComputedBrauerTables( ordtbl );

    # Start storing only after the result has been computed.
    # This avoids errors if a calculation had been interrupted.
    if not IsBound( known[p] ) then
      erg:= BrauerTableOp( ordtbl, p );
      known[p]:= erg;
    fi;

    return known[p];
    end );


#############################################################################
##
#M  BrauerTableOp( <ordtbl>, <p> )  . . . . . . . . . . . . <p>-modular table
##
##  Note that we do not need a method for the first argument a group,
##  since `BrauerTable' delegates this to the ordinary table.
##
##  This is a ``last resort'' method that returns `fail' if <ordtbl> is not
##  <p>-solvable.
##  (It assumes that a method for library tables is of higher rank.)
##
InstallMethod( BrauerTableOp,
    "for ordinary character table, and positive integer",
    true,
    [ IsOrdinaryTable, IsPosInt ], 0,
    function( tbl, p )
    if IsPSolvableCharacterTable( tbl, p ) then
      return CharacterTableRegular( tbl, p );
    else
      return fail;
    fi;
    end );


#############################################################################
##
#M  ComputedBrauerTables( <ordtbl> )  . . . . . . for an ord. character table
##
InstallMethod( ComputedBrauerTables,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    ordtbl -> [] );


#############################################################################
##
#F  CharacterTableRegular( <ordtbl>, <p> )  . restriction to <p>-reg. classes
##
InstallGlobalFunction( CharacterTableRegular,
    function( ordtbl, prime )

    local fusion,
          inverse,
          orders,
          i,
          regular,
          power;

    if not IsPrimeInt( prime ) then
      Error( "<prime> must be a prime" );
    elif IsBrauerTable( ordtbl ) then
      Error( "<ordtbl> is already a Brauer table" );
    fi;

    fusion:= [];
    inverse:= [];
    orders:= OrdersClassRepresentatives( ordtbl );
    for i in [ 1 .. Length( orders ) ] do
      if orders[i] mod prime <> 0 then
        Add( fusion, i );
        inverse[i]:= Length( fusion );
      fi;
    od;

    regular:= rec(
       Identifier                 := Concatenation( Identifier( ordtbl ),
                                         "mod", String( prime ) ),
       UnderlyingCharacteristic   := prime,
       Size                       := Size( ordtbl ),
       OrdersClassRepresentatives := orders{ fusion },
       SizesCentralizers          := SizesCentralizers( ordtbl ){ fusion },
       ComputedPowerMaps          := [],
       OrdinaryCharacterTable     := ordtbl
      );

    # Transfer known power maps.
    # (Missing power maps can be computed later.)
    power:= ComputedPowerMaps( ordtbl );
    for i in [ 1 .. Length( power ) ] do
      if IsBound( power[i] ) then
        regular.ComputedPowerMaps[i]:= inverse{ power[i]{ fusion } };
      fi;
    od;

    regular:= ConvertToCharacterTableNC( regular );
    StoreFusion( regular, rec( map:= fusion, type:= "choice" ), ordtbl );

    return regular;
    end );


#############################################################################
##
#F  ConvertToCharacterTable( <record> ) . . . . create character table object
#F  ConvertToCharacterTableNC( <record> ) . . . create character table object
##
InstallGlobalFunction( ConvertToCharacterTableNC, function( record )

    local names,    # list of component names
          i;        # loop over `SupportedCharacterTableInfo'

    names:= RecNames( record );

    # Make the object.
    if not IsBound( record.UnderlyingCharacteristic ) then
      Error( "<record> needs component `UnderlyingCharacteristic'" );
    elif record.UnderlyingCharacteristic = 0 then
      Objectify( NewType( NearlyCharacterTablesFamily,
                          IsOrdinaryTable and IsAttributeStoringRep ),
                 record );
    else
      Objectify( NewType( NearlyCharacterTablesFamily,
                          IsBrauerTable and IsAttributeStoringRep ),
                 record );
    fi;

    # Enter the properties and attributes.
    for i in [ 1, 4 .. Length( SupportedCharacterTableInfo ) - 2 ] do
      if     SupportedCharacterTableInfo[ i+1 ] in names
         and SupportedCharacterTableInfo[ i+1 ] <> "Irr" then
        Setter( SupportedCharacterTableInfo[i] )( record,
            record!.( SupportedCharacterTableInfo[ i+1 ] ) );
      fi;
    od;

    # Make the lists of character values into character objects.
    if "Irr" in names then
      SetIrr( record, List( record!.Irr,
                            chi -> Character( record, chi ) ) );
    fi;

    # Return the object.
    return record;
end );

InstallGlobalFunction( ConvertToCharacterTable, function( record )

    # Check the argument record.

    if not IsBound( record!.UnderlyingCharacteristic ) then
      Info( InfoCharacterTable, 1,
            "no underlying characteristic stored" );
      return fail;
    fi;

    # If a group is entered, check that the interface between group
    # and table is complete.
    if IsBound( record!.UnderlyingGroup ) then
      if not IsBound( record!.ConjugacyClasses ) then
        Info( InfoCharacterTable, 1,
              "group stored but no conjugacy classes!" );
        return fail;
      elif not IsBound( record!.IdentificationOfClasses ) then
        Info( InfoCharacterTable, 1,
              "group stored but no identification of classes!" );
        return fail;
      fi;
    fi;

#T more checks!

    # Call the no-check-function.
    return ConvertToCharacterTableNC( record );
end );


#############################################################################
##
#F  ConvertToLibraryCharacterTableNC( <record> )
##
InstallGlobalFunction( ConvertToLibraryCharacterTableNC, function( record )

    local names,    # list of component names
          i;        # loop over 'SupportedCharacterTableInfo'

    names:= RecNames( record );

    # Make the object.
    if IsBound( record.isGenericTable ) and record.isGenericTable then
      Objectify( NewType( NearlyCharacterTablesFamily,
                          IsGenericCharacterTableRep ),
                 record );
    else
      ConvertToCharacterTableNC( record );
      SetFilterObj( record, IsLibraryCharacterTableRep );
    fi;

    # Return the object.
    return record;
end );


#############################################################################
##
##  9. Printing Character Tables
##


#############################################################################
##
#M  ViewObj( <tbl> )  . . . . . . . . . . . . . . . . . for a character table
##
InstallMethod( ViewObj,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )
    Print( "CharacterTable( " );
    if HasUnderlyingGroup( tbl ) then
      View( UnderlyingGroup( tbl ) );
    else
      View( Identifier( tbl ) );
    fi;
    Print(  " )" );
    end );

InstallMethod( ViewObj,
    "for a Brauer table",
    true,
    [ IsBrauerTable ], 0,
    function( tbl )
    local ordtbl;
    ordtbl:= OrdinaryCharacterTable( tbl );
    Print( "BrauerTable( " );
    if HasUnderlyingGroup( ordtbl ) then
      View( UnderlyingGroup( ordtbl ) );
    else
      View( Identifier( ordtbl ) );
    fi;
    Print( ", ", UnderlyingCharacteristic( tbl ), " )" );
    end );


#############################################################################
##
#M  PrintObj( <tbl> ) . . . . . . . . . . . . . . . . . for a character table
##
InstallMethod( PrintObj,
    "for an ordinary table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )
    if HasUnderlyingGroup( tbl ) then
      Print( "CharacterTable( ", UnderlyingGroup( tbl ), " )" );
    else
      Print( "CharacterTable( \"", Identifier( tbl ), "\" )" );
    fi;
    end );

InstallMethod( PrintObj,
    "for a Brauer table",
    true,
    [ IsBrauerTable ], 0,
    function( tbl )
    local ordtbl;
    ordtbl:= OrdinaryCharacterTable( tbl );
    if HasUnderlyingGroup( ordtbl ) then
      Print( "BrauerTable( ", UnderlyingGroup( ordtbl ), ", ",
             UnderlyingCharacteristic( tbl ), " )" );
    else
      Print( "BrauerTable( \"", Identifier( ordtbl ),
             "\", ", UnderlyingCharacteristic( tbl ), " )" );
    fi;
    end );


#############################################################################
##
#M  Display( <tbl> )  . . . . . . . . . . . . .  for a nearly character table
#M  Display( <tbl>, <record> )
##
InstallMethod( Display,
    "for a nearly character table",
    true,
    [ IsNearlyCharacterTable ], 0,
    function( tbl )
    Display( tbl, rec() );
    end );

InstallMethod( Display,
    "for a nearly character table with display options",
    true,
    [ IsNearlyCharacterTable and HasDisplayOptions ], 0,
    function( tbl )
    Display( tbl, DisplayOptions( tbl ) );
    end );

InstallOtherMethod( Display,
    "for a nearly character table, and a list",
    true,
    [ IsNearlyCharacterTable, IsList ], 0,
    function( tbl, list )
    Display( tbl, rec( chars:= list ) );
    end );

InstallOtherMethod( Display,
    "for a nearly character table, and a record",
    true,
    [ IsNearlyCharacterTable, IsRecord ], 0,
    function( tbl, options )

    local i, j,              # loop variables
          chars,             # list of characters
          cnr,               # list of character numbers
          cletter,           # character name
          classes,           # list of classes
          powermap,          # list of primes
          centralizers,      # boolean
          cen,               # factorized centralizers
          fak,               # factorization
          prime,             # loop over primes
          primes,            # prime factors of order
          prin,              # column widths
          nam,               # classnames
          col,               # number of columns already printed
          acol,              # nuber of columns on next page
          len,               # width of next page
          ncols,             # total number of columns
          linelen,           # line length
          q,                 # quadratic cyc / powermap entry
          indicator,         # list of primes
          indic,             # indicators
          iw,                # width of indicator column
          letters,           # the alphabet
          ll,                # cardinality of the alphabet
          irrstack,          # list of known cycs
          irrnames,          # list of names for cycs
          colWidth,          # local function
          irrName,           # local function
          stringEntry,       # local function
          cc,                # column number
          charnames,         # list of character names
          charvals,          # matrix of strings of character values
          tbl_powermap,
          tbl_centralizers,
          tbl_irredinfo;

    # compute the width of column 'col'
    colWidth:= function( col )
       local len, width;

       # the class name should fit into the column
       width:= Length( nam[col] );

       # the class names of power classes should fit into the column
       for i in powermap do
         len:= tbl_powermap[i][ col ];
         if IsInt( len ) then
           len:= Length( nam[ len ] );
           if len > width then
             width:= len;
           fi;
         fi;
       od;

       # each character value should fit into the column
       for i in [ 1 .. Length( cnr ) ] do
         len:= Length( charvals[i][ col ] );
         if len > width then
           width:= len;
         fi;
       od;

       # at least one blank should separate the column entries
       return width + 1;

    end;

    # names of irrationalities
    irrName:= function( n )
       local i, name;

       name:= "";
       while 0 < n do
          name:= Concatenation(letters[(n-1) mod ll + 1], name);
          n:= QuoInt(n-1, ll);
       od;
       return name;
    end;

    # function (in one variable) to display a single entry
    if   IsBound( options.StringEntry ) then
      stringEntry:= options.StringEntry;
    else

      # string function as known
      stringEntry:= function( entry )
         local i, val;

         if entry = 0 then
            return ".";
         elif IsCyc( entry ) and not IsInt( entry ) then
            # find shorthand for cyclo
            for i in [ 1 .. Length(irrstack) ] do
               if entry = irrstack[i] then
                  return irrName(i);
               elif entry = -irrstack[i] then
                  return Concatenation("-", irrName(i));
               fi;
               val:= GaloisCyc(irrstack[i], -1);
               if entry = val then
                  return Concatenation("/", irrName(i));
               elif entry = -val then
                  return Concatenation("-/", irrName(i));
               fi;
               val:= StarCyc(irrstack[i]);
               if entry = val then
                  return Concatenation("*", irrName(i));
               elif -entry = val then
                  return Concatenation("-*", irrName(i));
               fi;
               i:= i+1;
            od;
            Add( irrstack, entry );
            Add( irrnames, irrName( Length( irrstack ) ) );
            return irrnames[ Length( irrnames ) ];

         elif ( IsList( entry ) and not IsString( entry ) )
              or IsUnknown( entry ) then
            return "?";
         else
            return String( entry );
         fi;
      end;

    fi;

    irrstack:= [];
    irrnames:= [];
    letters:= [ "A","B","C","D","E","F","G","H","I","J","K","L","M",
                "N","O","P","Q","R","S","T","U","V","W","X","Y","Z" ];
    ll:= Length( letters );

    # default:
    # options
    cletter:= "X";

    # choice of characters
    if IsBound( options.chars ) then
       if IsCyclotomicCollection( options.chars ) then
          cnr:= options.chars;
          chars:= List( Irr( tbl ){ cnr }, ValuesOfClassFunction );
       elif IsInt( options.chars ) then
          cnr:= [ options.chars ];
          chars:= List( Irr( tbl ){ cnr }, ValuesOfClassFunction );
       elif IsHomogeneousList( options.chars ) then
          chars:= options.chars;
          cletter:= "Y";
          cnr:= [ 1 .. Length( chars ) ];
       else
          chars:= [];
       fi;
    else
      chars:= List( Irr( tbl ), ValuesOfClassFunction );
      cnr:= [ 1 .. Length( chars ) ];
    fi;

    if IsBound( options.letter ) and options.letter in letters then
       cletter:= options.letter;
    fi;

    # choice of classes
    if IsBound( options.classes ) then
      if IsInt( options.classes ) then
        classes:= [ options.classes ];
      else
        classes:= options.classes;
      fi;
    else
      classes:= [ 1 .. NrConjugacyClasses( tbl ) ];
    fi;

    # choice of power maps
    tbl_powermap:= ComputedPowerMaps( tbl );
    powermap:= Filtered( [ 2 .. Length( tbl_powermap ) ],
                         x -> IsBound( tbl_powermap[x] ) );
    if IsBound( options.powermap ) then
       if IsInt( options.powermap ) then
          IntersectSet( powermap, [ options.powermap ] );
       elif IsList( options.powermap ) then
          IntersectSet( powermap, options.powermap );
       elif options.powermap = false then
          powermap:= [];
       fi;
    fi;

    # print factorized centralizer orders?
    centralizers:=    not IsBound( options.centralizers )
                   or options.centralizers;

    # print Frobenius-Schur indicators?
    indicator:= [];
    if     IsBound( options.indicator )
       and not ( IsBound( options.chars ) and IsMatrix( options.chars ) ) then
       if options.indicator = true then
          indicator:= [2];
       elif IsRowVector( options.indicator ) then
          indicator:= Set( Filtered( options.indicator, IsPosInt ) );
       fi;
    fi;

    # (end of options handling)

    # line length
    linelen:= SizeScreen()[1] - 1;

    # prepare centralizers
    if centralizers then
       fak:= FactorsInt( Size( tbl ) );
       primes:= Set( fak );
       cen:= [];
       for prime in primes do
          cen[prime]:= [ Number( fak, x -> x = prime ) ];
       od;
    fi;

    # prepare classnames
    nam:= ClassNames( tbl );

    # prepare character names
    if HasCharacterNames( tbl ) and not IsBound( options.chars ) then
      charnames:= CharacterNames( tbl );
    else
      charnames:= [];
      for i in [ 1 .. Length( cnr ) ] do
        charnames[i]:= Concatenation( cletter, ".", String( cnr[i] ) );
      od;
    fi;

    # prepare indicator
    iw:= [0];
    if indicator <> [] and not HasComputedIndicators( tbl ) then
       indicator:= [];
    fi;
    if indicator <> [] then
       indic:= [];
       for i in indicator do
          if IsBound( ComputedIndicators( tbl )[i] ) then
            indic[i]:= [];
            for j in cnr do
              indic[i][j]:= ComputedIndicators( tbl )[i][j];
            od;

            if i = 2 then
              iw[i]:= 2;
            else
              iw[i]:= Maximum( Length(String(Maximum(Set(indic[i])))),
                               Length(String(Minimum(Set(indic[i])))),
                               Length(String(i)) )+1;
            fi;
            iw[1]:= iw[1] + iw[i];
          fi;
       od;
       iw[1]:= iw[1] + 1;
       indicator:= Filtered( indicator, x-> IsBound( indic[x] ) );
    fi;

    if Length( cnr ) = 0 then
      prin:= [ 3 ];
    else
      prin:= [ Maximum( List( charnames, Length ) ) + 3 ];
    fi;

    # prepare list for strings of character values
    charvals:= List( chars, x -> [] );

    # total number of columns
    ncols:= Length(classes) + 1;

    # number of columns already displayed
    col:= 1;

    # A character table has a name.
    Print( Identifier( tbl ), "\n" );

    while col < ncols do

       # determine number of cols for next page
       acol:= 0;
       if indicator <> [] then
          prin[1]:= prin[1] + iw[1];
       fi;
       len:= prin[1];
       while col+acol < ncols and len < linelen do
          acol:= acol + 1;
          if Length(prin) < col + acol then
             cc:= classes[ col + acol - 1 ];
             for i in [ 1 .. Length( cnr ) ] do
               charvals[i][ cc ]:= stringEntry( chars[i][ cc ] );
             od;
             prin[col + acol]:= colWidth( classes[col + acol - 1] );
          fi;
          len:= len + prin[col+acol];
       od;
       if len >= linelen then
          acol:= acol-1;
       fi;

       # Check whether we are able to print at least one column.
       if acol = 0 then
         Error( "line length too small (perhaps resize with `SizeScreen')" );
       fi;

       # centralizers
       if centralizers then
          Print( "\n" );
          tbl_centralizers:= SizesCentralizers( tbl );
          for i in [col..col+acol-1] do
             fak:= FactorsInt( tbl_centralizers[classes[i]] );
             for prime in Set( fak ) do
                cen[prime][i]:= Number( fak, x -> x = prime );
             od;
          od;
          for j in [1..Length(cen)] do
             if IsBound(cen[j]) then
                for i in [col..col+acol-1] do
                   if not IsBound(cen[j][i]) then
                      cen[j][i]:= ".";
                   fi;
                od;
             fi;
          od;

          for prime in primes do
             Print( FormattedString( prime, prin[1] ) );
             for j in [1..acol] do
               Print( FormattedString( cen[prime][col+j-1], prin[col+j] ) );
             od;
             Print( "\n" );
          od;
       fi;

       # class names
       Print( "\n" );
       Print( FormattedString( "", prin[1] ) );
       for i in [ 1 .. acol ] do
         Print( FormattedString( nam[classes[col+i-1]], prin[col+i] ) );
       od;

       # power maps
       for i in powermap do
          Print("\n");
          Print( FormattedString( Concatenation( String(i), "P" ),
                                  prin[1] ) );
          for j in [1..acol] do
             q:= tbl_powermap[i][classes[col+j-1]];
             if IsInt(q) then
                Print( FormattedString( nam[q], prin[col+j] ) );
             else
                Print( FormattedString( "?", prin[col+j] ) );
             fi;
          od;
       od;

       # empty column resp. indicators
       Print( "\n" );
       if indicator <> [] then
          prin[1]:= prin[1] - iw[1];
          Print( FormattedString( "", prin[1] ) );
          for i in indicator do
             Print( FormattedString( i, iw[i] ) );
          od;
       fi;

       # the characters
       for i in [1..Length(chars)] do

          Print( "\n" );

          # character name
          Print( FormattedString( charnames[i], -prin[1] ) );

          # indicators
          for j in indicator do
             if IsBound(indic[j][cnr[i]]) then
                if j = 2 then
                   if indic[j][cnr[i]] = 0 then
                      Print( FormattedString( "o", iw[j] ) );
                   elif indic[j][cnr[i]] = 1 then
                      Print( FormattedString( "+", iw[j] ) );
                   elif indic[j][cnr[i]] = -1 then
                      Print( FormattedString( "-", iw[j] ) );
                   fi;
                else
                   if indic[j][cnr[i]] = 0 then
                      Print( FormattedString( "0", iw[j] ) );
                   else
                      Print( FormattedString( stringEntry(indic[j][cnr[i]]),
                                              iw[j]) );
                   fi;
                fi;
             else
                Print( FormattedString( "", iw[j] ) );
             fi;
          od;
          if indicator <> [] then
            Print(" ");
          fi;
          for j in [ 1 .. acol ] do
            Print( FormattedString( charvals[i][ classes[col+j-1] ],
                                    prin[ col+j ] ) );
          od;
       od;
       col:= col + acol;
       Print("\n");

       # Indicators are printed only with the first portion of columns.
       indicator:= [];

    od;

    # print legend for cyclos
    if not IsEmpty( irrstack ) then
      Print( "\n" );
    fi;
    for i in [1..Length(irrstack)] do
       Print( irrName(i), " = ", irrstack[i], "\n" );
       q:= Quadratic( irrstack[i] );
       if q <> fail then
          Print( "  = ", q.display, " = ", q.ATLAS, "\n");
       fi;
    od;
    end );


#T support Cambridge format!
#T (for that, make the legend printing a separate function,
#T and also the handling of the irrats;
#T probably also the 'stringEntry' default function should become a
#T global variable)


#############################################################################
##
#F  PrintCharacterTable( <tbl>, <varname> )
##
InstallGlobalFunction( PrintCharacterTable, function( tbl, varname )

    local i, info, class, comp;

    # Check the arguments.
    if not IsNearlyCharacterTable( tbl ) then
      Error( "<tbl> must be a nearly character table" );
    elif not IsString( varname ) then
      Error( "<varname> must be a string" );
    fi;

    # Print the preamble.
    Print( varname, ":= function()\n" );
    Print( "local tbl;\n" );
    Print( "tbl:=rec();\n" );

    # Print the values of supported attributes.
    for i in [ 3, 6 .. Length( SupportedCharacterTableInfo ) ] do
      if Tester( SupportedCharacterTableInfo[i-2] )( tbl ) then

        info:= SupportedCharacterTableInfo[i-2]( tbl );

        # The irreducible characters are stored via values lists.
        if SupportedCharacterTableInfo[ i-1 ] = "Irr" then
          info:= List( info, ValuesOfClassFunction );
        fi;

        # Be careful to print strings with enclosing double quotes.
        # (This holds also for *nonempty* strings not in `IsStringRep'.)
        Print( "tbl.", SupportedCharacterTableInfo[ i-1 ], ":=\n" );
        if     IsString( info )
           and ( IsEmptyString( info ) or not IsEmpty( info ) ) then
          Print( "\"", info, "\";\n" );
        elif SupportedCharacterTableInfo[ i-1 ] = "ConjugacyClasses" then
          Print( "[\n" );
          for class in info do
            Print( "ConjugacyClass( tbl.UnderlyingGroup,\n",
                   Representative( class ), "),\n" );
          od;
          Print( "];\n" );
        else
          Print( info, ";\n" );
        fi;

      fi;
    od;

    # Print the values of supported components if available.
    if IsLibraryCharacterTableRep( tbl ) then

      for comp in SupportedLibraryTableComponents do
        if IsBound( tbl!.( comp ) ) then
          info:= tbl!.( comp );
#T           if   comp = "cliffordTable" then
#T             Print( "tbl.", comp, ":=\n\"",
#T                    PrintCliffordTable( tbl ), "\";\n" );
#T           elif     IsString( info )
#T                and ( IsEmptyString( info ) or not IsEmpty( info ) ) then
          if     IsString( info )
             and ( IsEmptyString( info ) or not IsEmpty( info ) ) then
            Print( "tbl.", comp, ":=\n\"",
                   info, "\";\n" );
          else
            Print( "tbl.", comp, ":=\n",
                   info, ";\n" );
          fi;
        fi;
      od;
      Print( "ConvertToLibraryCharacterTableNC(tbl);\n" );

    else
      Print( "ConvertToCharacterTableNC(tbl);\n" );
    fi;

    # Print the rest of the construction.
    Print( "return tbl;\n" );
    Print( "end;\n" );
    Print( varname, ":= ", varname, "();\n" );
end );


#############################################################################
##
##  10. Constructing Character Tables from Others
##


#############################################################################
##
#M  CharacterTableDirectProduct( <ordtbl1>, <ordtbl2> )
##
InstallMethod( CharacterTableDirectProduct,
    "for two ordinary character tables",
    IsIdenticalObj,
    [ IsOrdinaryTable, IsOrdinaryTable ], 0,
    function( tbl1, tbl2 )

    local direct,        # table of the direct product, result
          ncc1,          # no. of classes in 'tbl1'
          ncc2,          # no. of classes in 'tbl2'
          i, j, k,       # loop variables
          vals1,         # list of 'tbl1'
          vals2,         # list of 'tbl2'
          vals_direct,   # corresponding list of the result
          powermap_k,    # 'k'-th power map
          ncc2_i,        #
          fus;           # projection/embedding map

    direct:= ConvertToLibraryCharacterTableNC(
                 rec( UnderlyingCharacteristic := 0 ) );
    SetSize( direct, Size( tbl1 ) * Size( tbl2 ) );
    SetIdentifier( direct, Concatenation( Identifier( tbl1 ), "x",
                                          Identifier( tbl2 ) ) );
    SetSizesCentralizers( direct,
                      KroneckerProduct( [ SizesCentralizers( tbl1 ) ],
                                        [ SizesCentralizers( tbl2 ) ] )[1] );

    ncc1:= NrConjugacyClasses( tbl1 );
    ncc2:= NrConjugacyClasses( tbl2 );

    # Compute class parameters, if present in both tables.
    if HasClassParameters( tbl1 ) and HasClassParameters( tbl2 ) then

      vals1:= ClassParameters( tbl1 );
      vals2:= ClassParameters( tbl2 );
      vals_direct:= [];
      for i in [ 1 .. ncc1 ] do
        for j in [ 1 .. ncc2 ] do
          vals_direct[ j + ncc2 * ( i - 1 ) ]:= [ vals1[i], vals2[j] ];
        od;
      od;
      SetClassParameters( direct, vals_direct );

    fi;

    # Compute element orders.
    vals1:= OrdersClassRepresentatives( tbl1 );
    vals2:= OrdersClassRepresentatives( tbl2 );
    vals_direct:= [];
    for i in [ 1 .. ncc1 ] do
      for j in [ 1 .. ncc2 ] do
        vals_direct[ j + ncc2 * ( i - 1 ) ]:= Lcm( vals1[i], vals2[j] );
      od;
    od;
    SetOrdersClassRepresentatives( direct, vals_direct );

    # Compute power maps for all prime divisors of the result order.
    vals_direct:= ComputedPowerMaps( direct );
    for k in Union( FactorsInt( Size( tbl1 ) ),
                    FactorsInt( Size( tbl2 ) ) ) do
      powermap_k:= [];
      vals1:= PowerMap( tbl1, k );
      vals2:= PowerMap( tbl2, k );
      for i in [ 1 .. ncc1 ] do
        ncc2_i:= ncc2 * (i-1);
        for j in [ 1 .. ncc2 ] do
          powermap_k[ j + ncc2_i ]:= vals2[j] + ncc2 * ( vals1[i] - 1 );
        od;
      od;
      vals_direct[k]:= powermap_k;
    od;

    # Compute the irreducibles.
    SetIrr( direct, List( KroneckerProduct(
                                List( Irr( tbl1 ), ValuesOfClassFunction ),
                                List( Irr( tbl2 ), ValuesOfClassFunction ) ),
                          vals -> Character( direct, vals ) ) );

    # Form character parameters if they exist for the irreducibles
    # in both tables.
    if HasCharacterParameters( tbl1 ) and HasCharacterParameters( tbl2 ) then
      vals1:= CharacterParameters( tbl1 );
      vals2:= CharacterParameters( tbl2 );
      vals_direct:= [];
      for i in [ 1 .. ncc1 ] do
        for j in [ 1 .. ncc2 ] do
          vals_direct[ j + ncc2 * ( i - 1 ) ]:= [ vals1[i], vals2[j] ];
        od;
      od;
      SetCharacterParameters( direct, vals_direct );
    fi;

    # Store projections.
    fus:= [];
    for i in [ 1 .. ncc1 ] do
      for j in [ 1 .. ncc2 ] do fus[ ( i - 1 ) * ncc2 + j ]:= i; od;
    od;
    StoreFusion( direct,
                 rec( map := fus, specification := "1" ),
                 tbl1 );

    fus:= [];
    for i in [ 1 .. ncc1 ] do
      for j in [ 1 .. ncc2 ] do fus[ ( i - 1 ) * ncc2 + j ]:= j; od;
    od;
    StoreFusion( direct,
                 rec( map := fus, specification := "2" ),
                 tbl2 );

    # Store embeddings.
    StoreFusion( tbl1,
                 rec( map := [ 1, ncc2+1 .. (ncc1-1)*ncc2+1 ],
                      specification := "1" ),
                 direct );

    StoreFusion( tbl2,
                 rec( map := [ 1 .. ncc2 ],
                      specification := "2" ),
                 direct );

    # Return the table of the direct product.
    return direct;
    end );


#############################################################################
##
#M  CharacterTableDirectProduct( <modtbl>, <ordtbl> )
##
InstallMethod( CharacterTableDirectProduct,
    "for one Brauer table, and one ordinary character table",
    IsIdenticalObj,
    [ IsBrauerTable, IsOrdinaryTable ], 0,
    function( tbl1, tbl2 )

    local ncc1,     # no. of classes in 'tbl1'
          ncc2,     # no. of classes in 'tbl2'
          ord,      # ordinary table of product,
          reg,      # Brauer table of product,
          fus,      # fusion map
          i, j;     # loop variables

    # Check that the result will in fact be a Brauer table.
    if Size( tbl2 ) mod UnderlyingCharacteristic( tbl1 ) <> 0 then
      Error( "no direct product of Brauer table and p-singular ordinary" );
    fi;

    ncc1:= NrConjugacyClasses( tbl1 );
    ncc2:= NrConjugacyClasses( tbl2 );

    # Make the ordinary and Brauer table of the product.
    ord:= CharacterTableDirectProduct( OrdinaryCharacterTable(tbl1), tbl2 );
    reg:= CharacterTableRegular( ord, UnderlyingCharacteristic( tbl1 ) );

    # Store the irreducibles.
    SetIrr( reg, List(
       KroneckerProduct( List( Irr( tbl1 ), ValuesOfClassFunction ),
                         List( Irr( tbl2 ), ValuesOfClassFunction ) ),
       vals -> Character( reg, vals ) ) );

    # Store projections and embeddings
    fus:= [];
    for i in [ 1 .. ncc1 ] do
      for j in [ 1 .. ncc2 ] do fus[ ( i - 1 ) * ncc2 + j ]:= i; od;
    od;
    StoreFusion( reg, fus, tbl1 );

    fus:= [];
    for i in [ 1 .. ncc1 ] do
      for j in [ 1 .. ncc2 ] do fus[ ( i - 1 ) * ncc2 + j ]:= j; od;
    od;
    StoreFusion( reg, fus, tbl2 );

    StoreFusion( tbl1,
                 rec( map := [ 1, ncc2+1 .. (ncc1-1)*ncc2+1 ],
                      specification := "1" ),
                 reg );

    StoreFusion( tbl2,
                 rec( map := [ 1 .. ncc2 ],
                      specification := "2" ),
                 reg );

    # Return the table.
    return reg;
    end );


#############################################################################
##
#M  CharacterTableDirectProduct( <ordtbl>, <modtbl> )
##
InstallMethod( CharacterTableDirectProduct,
    "for one ordinary and one Brauer character table",
    IsIdenticalObj,
    [ IsOrdinaryTable, IsBrauerTable ], 0,
    function( tbl1, tbl2 )

    local ncc1,     # no. of classes in 'tbl1'
          ncc2,     # no. of classes in 'tbl2'
          ord,      # ordinary table of product,
          reg,      # Brauer table of product,
          fus,      # fusion map
          i, j;     # loop variables

    # Check that the result will in fact be a Brauer table.
    if Size( tbl1 ) mod UnderlyingCharacteristic( tbl2 ) <> 0 then
      Error( "no direct product of Brauer table and p-singular ordinary" );
    fi;

    ncc1:= NrConjugacyClasses( tbl1 );
    ncc2:= NrConjugacyClasses( tbl2 );

    # Make the ordinary and Brauer table of the product.
    ord:= CharacterTableDirectProduct( tbl1, OrdinaryCharacterTable(tbl2) );
    reg:= CharacterTableRegular( ord, UnderlyingCharacteristic( tbl2 ) );

    # Store the irreducibles.
    SetIrr( reg, List(
       KroneckerProduct( List( Irr( tbl1 ), ValuesOfClassFunction ),
                         List( Irr( tbl2 ), ValuesOfClassFunction ) ),
       vals -> Character( reg, vals ) ) );

    # Store projections and embeddings
    fus:= [];
    for i in [ 1 .. ncc1 ] do
      for j in [ 1 .. ncc2 ] do fus[ ( i - 1 ) * ncc2 + j ]:= i; od;
    od;
    StoreFusion( reg, fus, tbl1 );

    fus:= [];
    for i in [ 1 .. ncc1 ] do
      for j in [ 1 .. ncc2 ] do fus[ ( i - 1 ) * ncc2 + j ]:= j; od;
    od;
    StoreFusion( reg, fus, tbl2 );

    StoreFusion( tbl1,
                 rec( map := [ 1, ncc2+1 .. (ncc1-1)*ncc2+1 ],
                      specification := "1" ),
                 reg );

    StoreFusion( tbl2,
                 rec( map := [ 1 .. ncc2 ],
                      specification := "2" ),
                 reg );

    # Return the table.
    return reg;
    end );


#############################################################################
##
#M  CharacterTableDirectProduct( <modtbl1>, <modtbl2> )
##
InstallMethod( CharacterTableDirectProduct,
    "for two Brauer character tables",
    IsIdenticalObj,
    [ IsBrauerTable, IsBrauerTable ], 0,
    function( tbl1, tbl2 )

    local ncc1,     # no. of classes in 'tbl1'
          ncc2,     # no. of classes in 'tbl2'
          ord,      # ordinary table of product,
          reg,      # Brauer table of product,
          fus,      # fusion map
          i, j;     # loop variables

    # Check that the result will in fact be a Brauer table.
    if    UnderlyingCharacteristic( tbl1 )
       <> UnderlyingCharacteristic( tbl2 ) then
      Error( "no direct product of Brauer tables in different char." );
    fi;

    ncc1:= NrConjugacyClasses( tbl1 );
    ncc2:= NrConjugacyClasses( tbl2 );

    # Make the ordinary and Brauer table of the product.
    ord:= CharacterTableDirectProduct( OrdinaryCharacterTable( tbl1 ),
                                       OrdinaryCharacterTable( tbl2 ) );
    reg:= CharacterTableRegular( ord, UnderlyingCharacteristic( tbl1 ) );

    # Store the irreducibles.
    SetIrr( reg, List(
       KroneckerProduct( List( Irr( tbl1 ), ValuesOfClassFunction ),
                         List( Irr( tbl2 ), ValuesOfClassFunction ) ),
       vals -> Character( reg, vals ) ) );

    # Store projections and embeddings
    fus:= [];
    for i in [ 1 .. ncc1 ] do
      for j in [ 1 .. ncc2 ] do fus[ ( i - 1 ) * ncc2 + j ]:= i; od;
    od;
    StoreFusion( reg, fus, tbl1 );

    fus:= [];
    for i in [ 1 .. ncc1 ] do
      for j in [ 1 .. ncc2 ] do fus[ ( i - 1 ) * ncc2 + j ]:= j; od;
    od;
    StoreFusion( reg, fus, tbl2 );

    StoreFusion( tbl1,
                 rec( map := [ 1, ncc2+1 .. (ncc1-1)*ncc2+1 ],
                      specification := "1" ),
                 reg );

    StoreFusion( tbl2,
                 rec( map := [ 1 .. ncc2 ],
                      specification := "2" ),
                 reg );

    # Return the table.
    return reg;
    end );


#############################################################################
##
#M  CharacterTableFactorGroup( <tbl>, <classes> )
##
InstallMethod( CharacterTableFactorGroup,
    "for an ordinary table, and a list of class positions",
    true,
    [ IsOrdinaryTable, IsList and IsCyclotomicCollection ], 0,
    function( tbl, classes )

    local F,              # table of the factor group, result
          N,              # classes of the normal subgroup
          chi,            # loop over irreducibles
          ker,            # kernel of a 'chi'
          size,           # size of 'tbl'
          tclasses,       # class lengths of 'tbl'
          suborder,       # order of the normal subgroup
          factirr,        # irreducibles of 'F'
          factorfusion,   # fusion from 'tbl' to 'F'
          nccf,           # no. of classes of 'F'
          cents,          # centralizer orders of 'F'
          i,              # loop over the classes
          inverse,        # inverse of 'factorfusion'
          p;              # loop over prime divisors

    factirr:= [];
    N:= [ 1 .. NrConjugacyClasses( tbl ) ];
    for chi in Irr( tbl ) do
      ker:= ClassPositionsOfKernel( chi );
      if IsEmpty( Difference( classes, ker ) ) then
        IntersectSet( N, ker );
        Add( factirr, ValuesOfClassFunction( chi ) );
      fi;
    od;

    # Compute the order of the normal subgroup corresponding to `N'.
    size:= Size( tbl );
    tclasses:= SizesConjugacyClasses( tbl );
    suborder:= Sum( tclasses{ N }, 0 );
    if size mod suborder <> 0 then
      Error( "intersection of kernels of irreducibles containing\n",
             "<classes> has an order not dividing the size of <tbl>" );
    fi;

    # Compute the irreducibles of the factor.
    factirr:= CollapsedMat( factirr, [] );
    factorfusion := factirr.fusion;
    factirr      := factirr.mat;

    # Compute the centralizer orders of the factor group.
    # \[ |C_{G/N}(gN)\| = \frac{|G|/|N|}{|Cl_{G/N}(gN)|}
    #    = \frac{|G|:|N|}{\frac{1}{|N|}\sum_{x fus gN} |Cl_G(x)|}
    #    = \frac{|G|}{\sum_{x fus gN} |Cl_G(x)| \]
    nccf:= Length( factirr[1] );
    cents:= [];
    for i in [ 1 .. nccf ] do
      cents[i]:= 0;
    od;
    for i in [ 1 .. Length( factorfusion ) ] do
      cents[ factorfusion[i] ]:= cents[ factorfusion[i] ] + tclasses[i];
    od;
    for i in [ 1 .. nccf ] do
      cents[i]:= size / cents[i];
    od;
    if not ForAll( cents, IsInt ) then
      Error( "not all centralizer orders of the factor are well-defined" );
    fi;

    F:= Concatenation( Identifier( tbl ), "/", String( N ) );
    ConvertToStringRep( F );
    F:= rec(
             UnderlyingCharacteristic := 0,
             Size                     := size / suborder,
             Identifier               := F,
             Irr                      := factirr,
             SizesCentralizers        := cents
            );

    # Transfer necessary power maps of `tbl' to `F'.
    inverse:= ProjectionMap( factorfusion );
    F.ComputedPowerMaps:= [];
    for p in Set( Factors( F.Size ) ) do
      F.ComputedPowerMaps[p]:= factorfusion{ PowerMap( tbl, p ){ inverse } };
    od;

    # Convert the record into a library table.
    ConvertToLibraryCharacterTableNC( F );

    # Store the factor fusion on `tbl'.
    StoreFusion( tbl, rec( map:= factorfusion, type:= "factor" ), F );

    # Return the result.
    return F;
    end );


#############################################################################
##
#M  CharacterTableIsoclinic( <ordtbl> ) . . . . . . . . for an ordinary table
##
InstallMethod( CharacterTableIsoclinic,
    "for an ordinary character table",
    true,
    [ IsOrdinaryTable ], 0,
    function( tbl )
    local classes, half, kernel;

    # Identify the unique normal subgroup of index 2.
    half:= Size( tbl ) / 2;
    classes:= SizesConjugacyClasses( tbl );
    kernel:= Filtered( List( Filtered( Irr( tbl ),
                                       chi -> DegreeOfCharacter( chi ) = 1 ),
                             ClassPositionsOfKernel ),
                       ker -> Sum( classes{ ker }, 0 ) = half );
    if IsEmpty( kernel ) or 1 < Length( kernel ) then
      Error( "normal subgroup of index 2 not uniquely determined,\n",
             "use CharTableIsoclinic( <tbl>, <classes_of_nsg> )" );
    fi;

    # Delegate to the two-argument version.
    return CharacterTableIsoclinic( tbl, kernel[1] );
    end );


#############################################################################
##
#M  CharacterTableIsoclinic( <ordtbl>, <nsg> )
##
InstallMethod( CharacterTableIsoclinic,
    "for an ordinary character table, and a list of classes",
    true,
    [ IsOrdinaryTable, IsList and IsCyclotomicCollection ], 0,
    function( tbl, nsg )

    local classes, orders, centre;

    # Get the unique central subgroup of order 2 in the normal subgroup.
    classes:= SizesConjugacyClasses( tbl );
    orders:= OrdersClassRepresentatives( tbl );
    centre:= Filtered( nsg, x -> classes[x] = 1 and orders[x] = 2 );
    if Length( centre ) <> 1 then
      Error( "central subgroup of order 2 not uniquely determined,\n",
             "use CharTableIsoclinic( <tbl>, <classes>, <centrepos> )" );
    fi;

    # Delegate to the three-argument version.
    return CharacterTableIsoclinic( tbl, nsg, centre[1] );
    end );


#############################################################################
##
#M  CharacterTableIsoclinic( <ordtbl>, <nsg>, <center> )
##
InstallMethod( CharacterTableIsoclinic,
    "for an ordinary character table, a list of classes, and a class pos.",
    true,
    [ IsOrdinaryTable, IsList and IsCyclotomicCollection, IsPosInt ], 0,
    function( tbl, nsg, center )
    local centralizers,    # attribute of `tbl'
          classes,         # attribute of `tbl'
          orders,          # attribute of `tbl'
          size,            # attribute of `tbl'
          i,               # `E(4)'
          j,               # loop variable
          chi,             # one character
          values,          # values of `chi'
          class,
          map,
          linear,          # linear characters of `tbl'
          isoclinic,       # the isoclinic table, result
          outer,           # classes outside the index 2 subgroup
          nonfaith,        # characters of the factor group modulo `center'
          irreds,          # characters of `isoclinic'
          images,
          factorfusion,    # fusion onto factor modulo the central inv.
          p,               # loop over prime divisors of the size of `tbl'
          reg;             # restriction to regular classes

    centralizers:= SizesCentralizers( tbl );
    classes:= SizesConjugacyClasses( tbl );
    orders:= ShallowCopy( OrdersClassRepresentatives( tbl ) );
    size:= Size( tbl );

    # Check `nsg'.
    if Sum( classes{ nsg }, 0 ) <> size / 2 then
      Error( "normal subgroup described by <nsg> must have index 2" );
    fi;

    # Check `center'.
    if not center in nsg then
      Error( "<center> must lie in <nsg>" );
    fi;

    # Make the isoclinic table.
    isoclinic:= Concatenation( "Isoclinic(", Identifier( tbl ), ")" );
    ConvertToStringRep( isoclinic );

    isoclinic:= rec(
        UnderlyingCharacteristic   := 0,
        Identifier                 := isoclinic,
        Size                       := size,
        SizesCentralizers          := centralizers,
        SizesConjugacyClasses      := classes,
        OrdersClassRepresentatives := orders,
        ComputedPowerMaps          := []             );

    # classes outside the normal subgroup
    outer:= Difference( [ 1 .. Length( classes ) ], nsg );

    # Adjust faithful characters in outer classes.
    nonfaith:= [];
    irreds:= [];
    i:= E(4);
    for chi in Irr( tbl ) do
      values:= ValuesOfClassFunction( chi );
      if values[ center ] = values[1] then
        Add( nonfaith, values );
      else
        values:= ShallowCopy( values );
        for class in outer do
          values[ class ]:= i * values[ class ];
        od;
      fi;
      Add( irreds, values );
    od;
    isoclinic.Irr:= irreds;

    # Get the fusion map onto the factor group modulo '[ 1, center ]'.
    factorfusion:= CollapsedMat( nonfaith, [] ).fusion;

    # Adjust the power maps.
    for p in Set( Factors( isoclinic.Size ) ) do

      map:= PowerMap( tbl, p );

      # For p mod 4 in $\{ 0, 1 \}$, the map remains unchanged,
      # since $g^p = h$ and $(gi)^p = hi^p = hi$ then.
      if p mod 4 = 2 then

        # The squares lie in 'nsg'; for $g^2 = h$,
        # we have $(gi)^2 = hz$, so we must take the other
        # preimage under the factorfusion, if exists.
        map:= ShallowCopy( map );
        for class in outer do
          images:= Filtered( Difference( nsg, [ map[class] ] ),
              x -> factorfusion[x] = factorfusion[ map[ class ] ] );
          if Length( images ) = 1 then
            map[ class ]:= images[1];
            orders[ class ]:= 2 * orders[ images[1] ];
          fi;
        od;

      elif p mod 4 = 3 then

        # For $g^p = h$, we have $(gi)^p = hi^p = hiz$, so again
        # we must choose the other preimage under the
        # factorfusion, if exists; the 'p'-th powers lie outside
        # 'nsg' in this case.
        map:= ShallowCopy( map );
        for class in outer do
          images:= Filtered( Difference( outer, [ map[ class ] ] ),
              x -> factorfusion[x] = factorfusion[ map[ class ] ] );
          if Length( images ) = 1 then
            map[ class ]:= images[1];
          fi;
        od;

      fi;

      isoclinic.ComputedPowerMaps[p]:= map;

    od;

    # Convert the record into a library table.
    ConvertToLibraryCharacterTableNC( isoclinic );

    # Return the result.
    return isoclinic;
    end );


#############################################################################
##
#M  CharacterTableIsoclinic( <modtbl> ) . . . . . . . . .  for a Brauer table
##
##  For the isoclinic table of a Brauer table,
##  we transfer the normal subgroup information to the regular classes,
##  and adjust the irreducibles.
##
InstallMethod( CharacterTableIsoclinic,
    "for a Brauer table",
    true,
    [ IsBrauerTable ], 0,
    function( tbl )

    local isoclinic,
          reg,
          factorfusion,
          center,
          outer,
          irreducibles,
          i,
          chi,
          values,
          class;

    isoclinic:= CharacterTableIsoclinic( OrdinaryCharacterTable( tbl ) );
    reg:= CharacterTableRegular( isoclinic, Characteristic( tbl ) );
    factorfusion:= GetFusionMap( reg, isoclinic );
    center:= Position( factorfusion, center );
    outer:= Filtered( [ 1 .. NrConjugacyClasses( reg ) ],
                      x -> factorfusion[x] in outer );

    # Compute the irreducibles as for the ordinary isoclinic table.
    irreducibles:= [];
    i:= E(4);
    for chi in Irr( tbl ) do
      values:= ValuesOfClassFunction( chi );
      if values[ center ] <> values[1] then
        values:= ShallowCopy( values );
        for class in outer do
          values[ class ]:= i * values[ class ];
        od;
      fi;
      Add( irreducibles, values );
    od;
    SetIrr( reg, List( irreducibles, vals -> Character( reg, vals ) ) );

    # Return the result.
    return reg;
    end );


#############################################################################
##
#F  CharacterTableOfNormalSubgroup( <tbl>, <classes> )
##
InstallGlobalFunction( CharacterTableOfNormalSubgroup,
    function( tbl, classes )

    local sizesclasses,   # class lengths of the result
          size,           # size of the result
          nccl,           # no. of classes
          orders,         # repr. orders of the result
          centralizers,   # centralizer orders of the result
          result,         # result table
          err,            # list of classes that must split
          inverse,        # inverse map of `classes'
          p,              # loop over primes
          irreducibles,   # list of irred. characters
          chi,            # loop over irreducibles of `tbl'
          char;           # one character values list for `result'

    if not IsOrdinaryTable( tbl ) then
      Error( "<tbl> must be an ordinary character table" );
    fi;

    sizesclasses:= SizesConjugacyClasses( tbl ){ classes };
    size:= Sum( sizesclasses );

    if Size( tbl ) mod size <> 0 then
      Error( "<classes> is not a normal subgroup" );
    fi;

    nccl:= Length( classes );
    orders:= OrdersClassRepresentatives( tbl ){ classes };
    centralizers:= List( sizesclasses, x -> size / x );

    result:= Concatenation( "Rest(", Identifier( tbl ), ",",
                            String( classes ), ")" );
    ConvertToStringRep( result );

    result:= rec(
        UnderlyingCharacteristic   := 0,
        Identifier                 := result,
        Size                       := size,
        SizesCentralizers          := centralizers,
        SizesConjugacyClasses      := sizesclasses,
        OrdersClassRepresentatives := orders,
        ComputedPowerMaps          := []             );

    err:= Filtered( [ 1 .. nccl ],
                    x-> centralizers[x] mod orders[x] <> 0 );
    if not IsEmpty( err ) then
      Info( InfoCharacterTable, 2,
            "CharacterTableOfNormalSubgroup: classes in " , err,
            " necessarily split" );
    fi;
    inverse:= InverseMap( classes );

    for p in [ 1 .. Length( ComputedPowerMaps( tbl ) ) ] do
      if IsBound( ComputedPowerMaps( tbl )[p] ) then
        result.ComputedPowerMaps[p]:=
            CompositionMaps( inverse,
                CompositionMaps( ComputedPowerMaps( tbl )[p], classes ) );
      fi;
    od;

    # Compute the irreducibles if known.
    irreducibles:= [];
    if HasIrr( tbl ) then

      for chi in Irr( tbl ) do
        char:= ValuesOfClassFunction( chi ){ classes };
        if     Sum( [ 1 .. nccl ],
                  i -> sizesclasses[i] * char[i] * GaloisCyc(char[i],-1), 0 )
               = size
           and not char in irreducibles then
          Add( irreducibles, char );
        fi;
      od;

    fi;

    if Length( irreducibles ) = nccl then

      result.Irr:= irreducibles;

      # Convert the record into a library table.
      ConvertToLibraryCharacterTableNC( result );

    else

      p:= Size( tbl ) / size;
      if IsPrimeInt( p ) and not IsEmpty( irreducibles ) then
        Info( InfoCharacterTable, 2,
              "CharacterTableOfNormalSubgroup: The table must have ",
              p * NrConjugacyClasses( tbl ) -
              ( p^2 - 1 ) * Length( irreducibles ), " classes\n",
              "#I   (now ", Length( classes ), ", after nec. splitting ",
              Length( classes ) + (p-1) * Length( err ), ")" );
      fi;

      Error( "tables in progress not yet supported" );
#T !!

    fi;

    # Store the fusion into `tbl'.
    StoreFusion( result, classes, tbl );

    # Return the result.
    return result;
end );


#############################################################################
##
##  11. Sorted Character Tables
##


#############################################################################
##
#F  PermutationToSortCharacters( <tbl>, <chars>, <degree>, <norm> )
##
InstallGlobalFunction( PermutationToSortCharacters,
    function( tbl, chars, degree, norm )

    local rational, listtosort, i, len;

    if IsEmpty( chars ) then
      return ();
    fi;

    # Rational characters shall precede irrational ones of same degree,
    # and the trivial character shall be the first one.
    rational := function( chi )
      chi:= ValuesOfClassFunction( chi );
      if ForAll( chi, IsRat ) then
        if ForAll( chi, x -> x = 1 ) then
          return -1;
        else
          return 0;
        fi;
      else
        return 1;
      fi;
    end;

    # Compute the permutation.
    listtosort:= [];
    if degree and norm then
      for i in [ 1 .. Length( chars ) ] do
        listtosort[i]:= [ ScalarProduct( chars[i], chars[i] ),
                          DegreeOfCharacter( chars[i] ),
                          rational( chars[i] ), i ];
      od;
    elif degree then
      for i in [ 1 .. Length( chars ) ] do
        listtosort[i]:= [ DegreeOfCharacter( chars[i] ),
                          rational( chars[i] ), i ];
      od;
    elif norm then
      for i in [ 1 .. Length( chars ) ] do
        listtosort[i]:= [ ScalarProduct( chars[i], chars[i] ),
                          rational( chars[i] ), i ];
      od;
    else
      Error( "at least one of <degree> or <norm> must be `true'" );
    fi;
    Sort( listtosort );
    len:= Length( listtosort[1] );
    for i in [ 1 .. Length( chars ) ] do
      listtosort[i]:= listtosort[i][ len ];
    od;
    return Inverse( PermList( listtosort ) );
    end );


#############################################################################
##
#M  CharacterTableWithSortedCharacters( <tbl> )
##
InstallMethod( CharacterTableWithSortedCharacters,
    "for a character table",
    true,
    [ IsCharacterTable ], 0,
    tbl -> CharacterTableWithSortedCharacters( tbl,
             PermutationToSortCharacters( tbl, Irr( tbl ), true, false ) ) );


#############################################################################
##
#M  CharacterTableWithSortedCharacters( <tbl>, <perm> )
##
InstallMethod( CharacterTableWithSortedCharacters,
    "for an ordinary character table, and a permutation",
    true,
    [ IsOrdinaryTable, IsPerm ], 0,
    function( tbl, perm )

    local new, i;

    # Create the new table.
    new:= ConvertToLibraryCharacterTableNC(
                 rec( UnderlyingCharacteristic := 0 ) );

    # Set the permuted attribute values.
    SetIrr( new, Permuted( Irr( tbl ), perm ) );
    if HasCharacterParameters( tbl ) then
      SetCharacterParameters( new,
          Permuted( CharacterParameters( tbl ), perm ) );
    fi;

    # Set the other supported values.
    for i in [ 3, 6 .. Length( SupportedCharacterTableInfo ) ] do
      if Tester( SupportedCharacterTableInfo[ i-2 ] )( tbl )
         and not ( "character" in SupportedCharacterTableInfo[i] ) then
        Setter( SupportedCharacterTableInfo[ i-2 ] )( new,
            SupportedCharacterTableInfo[ i-2 ]( tbl ) );
      fi;
    od;

    # Return the table.
    return new;
    end );


#############################################################################
##
#M  SortedCharacters( <tbl>, <chars> )
##
InstallMethod( SortedCharacters,
    "for a character table, and a homogeneous list",
    true,
    [ IsNearlyCharacterTable, IsHomogeneousList ], 0,
    function( tbl, chars )
    return Permuted( chars,
               PermutationToSortCharacters( tbl, chars, true, true ) );
    end );


#############################################################################
##
#M  SortedCharacters( <tbl>, <chars>, \"norm\" )
#M  SortedCharacters( <tbl>, <chars>, \"degree\" )
##
InstallMethod( SortedCharacters,
    "for a character table, a homogeneous list, and a string",
    true,
    [ IsNearlyCharacterTable, IsHomogeneousList, IsString ], 0,
    function( tbl, chars, string )
    if string = "norm" then
      return Permuted( chars,
                 PermutationToSortCharacters( tbl, chars, false, true ) );
    elif string = "degree" then
      return Permuted( chars,
                 PermutationToSortCharacters( tbl, chars, true, false ) );
    else
      Error( "<string> must be \"norm\" or \"degree\"" );
    fi;
    end );


#############################################################################
##
#F  PermutationToSortClasses( <tbl>, <classes>, <orders> )
##
InstallGlobalFunction( PermutationToSortClasses,
    function( tbl, classes, orders )

    local listtosort, i, len;

    # Compute the permutation.
    listtosort:= [];
    if classes and orders then
      classes:= SizesConjugacyClasses( tbl );
      orders:= OrdersClassRepresentatives( tbl );
      for i in [ 1 .. NrConjugacyClasses( tbl ) ] do
        listtosort[i]:= [ orders[i], classes[i], i ];
      od;
    elif classes then
      classes:= SizesConjugacyClasses( tbl );
      for i in [ 1 .. NrConjugacyClasses( tbl ) ] do
        listtosort[i]:= [ classes[i], i ];
      od;
    elif orders then
      orders:= OrdersClassRepresentatives( tbl );
      for i in [ 1 .. NrConjugacyClasses( tbl ) ] do
        listtosort[i]:= [ orders[i], i ];
      od;
    else
      Error( "<classes> or <orders> must be 'true'" );
    fi;
    Sort( listtosort );
    len:= Length( listtosort[1] );
    for i in [ 1 .. Length( listtosort ) ] do
      listtosort[i]:= listtosort[i][ len ];
    od;
    return Inverse( PermList( listtosort ) );
    end );


#############################################################################
##
#M  CharacterTableWithSortedClasses( <tbl> )
##
InstallMethod( CharacterTableWithSortedClasses,
    "for a character table",
    true,
    [ IsCharacterTable ], 0,
    tbl -> CharacterTableWithSortedClasses( tbl,
               PermutationToSortClasses( tbl, true, true ) ) );


#############################################################################
##
#M  CharacterTableWithSortedClasses( <tbl>, \"centralizers\" )
#M  CharacterTableWithSortedClasses( <tbl>, \"representatives\" )
##
InstallMethod( CharacterTableWithSortedClasses,
    "for a character table, and string",
    true,
    [ IsCharacterTable, IsString ], 0,
    function( tbl, string )
    if   string = "centralizers" then
      return CharacterTableWithSortedClasses( tbl,
                 PermutationToSortClasses( tbl, true, false ) );
    elif string = "representatives" then
      return CharacterTableWithSortedClasses( tbl,
                 PermutationToSortClasses( tbl, false, true ) );
    else
      Error( "<string> must be \"centralizers\" or \"representatives\"" );
    fi;
    end );


#############################################################################
##
#M  CharacterTableWithSortedClasses( <tbl>, <permutation> )
##
InstallMethod( CharacterTableWithSortedClasses,
    "for an ordinary character table, and a permutation",
    true,
    [ IsOrdinaryTable, IsPerm ], 0,
    function( tbl, perm )

    local new, i, attr, fus, tblmaps, permmap, inverse, k;

    # Create the new table.
    new:= ConvertToLibraryCharacterTableNC(
                 rec( UnderlyingCharacteristic := 0 ) );

    # Catch trivial cases.
    if 1^perm <> 1 then
      Error( "<perm> must fix the first class" );
    elif IsOne( perm ) then
      return tbl;
    fi;

    # Set supported attributes that do not need adjustion.
    for i in [ 3, 6 .. Length( SupportedCharacterTableInfo ) ] do
      if Tester( SupportedCharacterTableInfo[ i-2 ] )( tbl )
         and not ( "class" in SupportedCharacterTableInfo[i] ) then
        Setter( SupportedCharacterTableInfo[ i-2 ] )( new,
            SupportedCharacterTableInfo[ i-2 ]( tbl ) );
      fi;
    od;

    # Set known attributes that must be adjusted by simply permuting.
    for attr in [ ClassParameters,
                  OrdersClassRepresentatives,
                  SizesCentralizers,
                  SizesConjugacyClasses,
                ] do
      if Tester( attr )( tbl ) then
        Setter( attr )( new, Permuted( attr( tbl ), perm ) );
      fi;
    od;

    # For each fusion, the map must be permuted.
    for fus in ComputedClassFusions( tbl ) do
      Add( ComputedClassFusions( new ),
           rec( name:= fus.name, map:= Permuted( fus.map, perm ) ) );
    od;

    # Each irreducible character must be permuted.
    if HasIrr( tbl ) then
      SetIrr( new,
          List( Irr( tbl ), chi -> Character( new,
                Permuted( ValuesOfClassFunction( chi ), perm ) ) ) );
    fi;

    # Power maps must be ``conjugated''.
    if HasComputedPowerMaps( tbl ) then

      tblmaps:= ComputedPowerMaps( tbl );
      permmap:= ListPerm( perm );
      inverse:= ListPerm( perm^(-1) );
      for k in [ Length( permmap ) + 1 .. NrConjugacyClasses( tbl ) ] do
        permmap[k]:= k;
        inverse[k]:= k;
      od;
      for k in [ 1 .. Length( tblmaps ) ] do
        if IsBound( tblmaps[k] ) then
          ComputedPowerMaps( new )[k]:= CompositionMaps( permmap,
              CompositionMaps( tblmaps[k], inverse ) );
        fi;
      od;

    fi;

    # The automorphisms of the sorted table are obtained by conjugation.
    if HasAutomorphismsOfTable( tbl ) then
      SetAutomorphismsOfTable( new, GroupByGenerators(
          List( GeneratorsOfGroup( AutomorphismsOfTable( tbl ) ),
                x -> x^perm ), () ) );
    fi;

    # The class permutation must be multiplied with the new permutation.
    if HasClassPermutation( tbl ) then
      SetClassPermutation( new, ClassPermutation( tbl ) * perm );
    else
      SetClassPermutation( new, perm );
    fi;

    # Return the new table.
    return new;
    end );


#############################################################################
##
#F  SortedCharacterTable( <tbl>, <kernel> )
#F  SortedCharacterTable( <tbl>, <normalseries> )
#F  SortedCharacterTable( <tbl>, <facttbl>, <kernel> )
##
InstallGlobalFunction( SortedCharacterTable, function( arg )

    local i, j, tbl, kernels, list, columns, rows, chi, F, facttbl, kernel,
          trans, ker, fus, new;

    # Check the arguments.
    if not ( Length( arg ) in [ 2, 3 ] and IsOrdinaryTable( arg[1] ) and
             IsList( arg[ Length( arg ) ] ) and
             ( Length( arg ) = 2 or IsOrdinaryTable( arg[2] ) ) ) then
      Error( "usage: SortedCharacterTable( <tbl>, <kernel> ) resp.\n",
             "       SortedCharacterTable( <tbl>, <normalseries> ) resp.\n",
             "       SortedCharacterTable( <tbl>, <facttbl>, <kernel> )" );
    fi;

    tbl:= arg[1];

    if Length( arg ) = 2 then

      # Sort w.r.t. kernel or series of kernels.
      kernels:= arg[2];
      if IsEmpty( kernels ) then
        return tbl;
      fi;

      # Regard single kernel as special case of normal series.
      if IsInt( kernels[1] ) then
        kernels:= [ kernels ];
      fi;

      # permutation of classes:
      # `list[i] = k' if `i' is contained in `kernels[k]' but not
      # in `kernels[k-1]'; only the first position contains a zero
      # to ensure that the identity is not moved.
      # If class `i' is not contained in any of the kernels we have
      # `list[i] = infinity'.
      list:= [ 0 ];
      for i in [ 2 .. NrConjugacyClasses( tbl ) ] do
        list[i]:= infinity;
      od;
      for i in [ 1 .. Length( kernels ) ] do
        for j in kernels[i] do
          if not IsInt( list[j] ) then
            list[j]:= i;
          fi;
        od;
      od;
      columns:= Sortex( list );

      # permutation of characters:
      # `list[i] = -(k+1)' if `Irr( <tbl> )[i]' has `kernels[k]'
      # in its kernel but not `kernels[k+1]';
      # if the `i'--th irreducible contains none of `kernels' in its kernel,
      # we have `list[i] = -1',
      # for an irreducible with kernel containing
      # `kernels[ Length( kernels ) ]',
      # the value is `-(Length( kernels ) + 1)'.
      list:= [];
      if HasIrr( tbl ) then
        for chi in Irr( tbl ) do
          i:= 1;
          while     i <= Length( kernels )
                and ForAll( kernels[i], x -> chi[x] = chi[1] ) do
            i:= i+1;
          od;
          Add( list, -i );
        od;
        rows:= Sortex( list );
      else
        rows:= ();
      fi;

    else

      # Sort w.r.t. the table of a factor group.
      facttbl:= arg[2];
      kernel:= arg[3];
      F:= CharacterTableFactorGroup( tbl, kernel );
      trans:= TransformingPermutationsCharacterTables( F, facttbl );
      if trans = fail then
        Info( InfoCharacterTable, 2,
              "SortedCharacterTable: tables of factors not compatible" );
        return fail;
      fi;

      # permutation of classes:
      # `list[i] = k' if `i' maps to the `j'--th class of <F>, and
      # `trans.columns[j] = i'
      list:= OnTuples( GetFusionMap( tbl, F ), trans.columns );
      columns:= Sortex( list );

      # permutation of characters:
      # divide `Irr( <tbl> )' into two parts, those containing
      # the kernel of the factor fusion in their kernel (value 0),
      # and the others (value 1); do not forget to permute characters
      # of the factor group with `trans.rows'.
      if HasIrr( tbl ) then
        ker:= ClassPositionsOfKernel( GetFusionMap( tbl, F ) );
        list:= [];
        for chi in Irr( tbl ) do
          if ForAll( ker, x -> chi[x] = chi[1] ) then
            Add( list, 0 );
          else
            Add( list, 1 );
          fi;
        od;
        rows:= Sortex( list ) * trans.rows;
      else
        rows:= ();
      fi;

      # Delete the fusion to `F' on `tbl'.
      fus:= ComputedClassFusions( tbl );
      Unbind( fus[ Length( fus ) ] );
#T better ?

    fi;

    # Sort and return.
    new:= CharacterTableWithSortedClasses( tbl, columns );
    new:= CharacterTableWithSortedCharacters( new, rows );
    return new;
end );


############################################################################
##
##  12. Storing Normal Subgroup Information
##


##############################################################################
##
#M  NormalSubgroupClassesInfo( <tbl> )
##
InstallMethod( NormalSubgroupClassesInfo,
    "default method, initialization",
    true,
    [ IsOrdinaryTable ], 0,
    tbl -> rec( nsg        := [],
                nsgclasses := [],
                nsgfactors := [] ) );


##############################################################################
##
#M  ClassPositionsOfNormalSubgroup( <tbl>, <N> )
##
InstallGlobalFunction( ClassPositionsOfNormalSubgroup, function( tbl, N )

    local info,
          classes,    # result list
          found,      # `N' already found?
          pos,        # position in `info.nsg'
          G,          # underlying group of `tbl'
          ccl;        # conjugacy classes of `tbl'

    info:= NormalSubgroupClassesInfo( tbl );

    # Search for `N' in `info.nsg'.
    found:= false;
    pos:= 0;
    while ( not found ) and pos < Length( info.nsg ) do
      pos:= pos+1;
      if IsIdenticalObj( N, info.nsg[ pos ] ) then
        found:= true;
      fi;
    od;
    if not found then
      pos:= Position( info.nsg, N );
    fi;

    if pos = fail then

      # The group is not yet stored here, try `NormalSubgroups( G )'.
      G:= UnderlyingGroup( tbl );
      if HasNormalSubgroups( G ) then

        # Identify our normal subgroup.
        N:= NormalSubgroups( G )[ Position( NormalSubgroups( G ), N ) ];

      fi;

      ccl:= ConjugacyClasses( tbl );
      classes:= Filtered( [ 1 .. Length( ccl ) ],
                          x -> Representative( ccl[x] ) in N );

      Add( info.nsgclasses, classes );
      Add( info.nsg       , N       );
      pos:= Length( info.nsg );

    fi;

    return info.nsgclasses[ pos ];
end );


##############################################################################
##
#F  NormalSubgroupClasses( <tbl>, <classes> )
##
InstallGlobalFunction( NormalSubgroupClasses, function( tbl, classes )

    local info,
          pos,        # position of the group in the list of such groups
          G,          # underlying group of `tbl'
          ccl,        # `G'-conjugacy classes in our normal subgroup
          size,       # size of our normal subgroup
          candidates, # bound normal subgroups that possibly are our group
          group,      # the normal subgroup
          repres,     # list of representatives of conjugacy classes
          found,      # normal subgroup already identified
          i;          # loop over normal subgroups

    info:= NormalSubgroupClassesInfo( tbl );

    classes:= Set( classes );
    pos:= Position( info.nsgclasses, classes );
    if pos = fail then

      # The group is not yet stored here, try `NormalSubgroups( G )'.
      G:= UnderlyingGroup( tbl );

      if HasNormalSubgroups( G ) then

        # Identify our normal subgroup.
        ccl:= ConjugacyClasses( tbl ){ classes };
        size:= Sum( ccl, Size, 0 );
        candidates:= Filtered( NormalSubgroups( G ), x -> Size( x ) = size );
        if Length( candidates ) = 1 then
          group:= candidates[1];
        else

          repres:= List( ccl, Representative );
          found:= false;
          i:= 0;
          while not found do
            i:= i+1;
            if ForAll( repres, x -> x in candidates[i] ) then
              found:= true;
            fi;
          od;

          if not found then
            Error( "<classes> does not describe a normal subgroup" );
          fi;

          group:= candidates[i];

        fi;

      elif classes = [ 1 ] then

        group:= TrivialSubgroup( G );

      else

        # The group is not yet stored, we have to construct it.
        repres:= List( ConjugacyClasses( tbl ){ classes }, Representative );
        group := NormalClosure( G, SubgroupNC( G, repres ) );

      fi;

      MakeImmutable( classes );
      Add( info.nsgclasses, classes );
      Add( info.nsg       , group   );
      pos:= Length( info.nsg );

    fi;

    return info.nsg[ pos ];
end );


##############################################################################
##
#F  FactorGroupNormalSubgroupClasses( <tbl>, <classes> )
##
InstallGlobalFunction( FactorGroupNormalSubgroupClasses,
    function( tbl, classes )

    local info,
          f,     # the result
          pos;   # position in list of normal subgroups

    info:= NormalSubgroupClassesInfo( tbl );
    pos:= Position( info.nsgclasses, classes );

    if pos = fail then
      f:= UnderlyingGroup( tbl ) / NormalSubgroupClasses( tbl, classes );
      info.nsgfactors[ Length( info.nsgclasses ) ]:= f;
    elif IsBound( info.nsgfactors[ pos ] ) then
      f:= info.nsgfactors[ pos ];
    else
      f:= UnderlyingGroup( tbl ) / info.nsg[ pos ];
      info.nsgfactors[ pos ]:= f;
    fi;

    return f;
end );


############################################################################
##
##  13. Auxiliary Stuff
##


#T ############################################################################
#T ##
#T #F  Lattice( <tbl> ) . .  lattice of normal subgroups of a c.t.
#T ##
#T Lattice := function( tbl )
#T
#T     local i, j,       # loop variables
#T           nsg,        # list of normal subgroups
#T           len,        # length of 'nsg'
#T           sizes,      # sizes of normal subgroups
#T           max,        # one maximal subgroup
#T           maxes,      # list of maximal contained normal subgroups
#T           actsize,    # actuel size of normal subgroups
#T           actmaxes,
#T           latt;       # the lattice record
#T
#T     # Compute normal subgroups and their sizes
#T     nsg:= ClassPositionsOfNormalSubgroups( tbl );
#T     len:= Length( nsg );
#T     sizes:= List( nsg, x -> Sum( tbl.classes{ x }, 0 ) );
#T     SortParallel( sizes, nsg );
#T
#T     # For each normal subgroup, compute the maximal contained ones.
#T     maxes:= [];
#T     i:= 1;
#T     while i <= len do
#T       actsize:= sizes[i];
#T       actmaxes:= Filtered( [ 1 .. i-1 ], x -> actsize mod sizes[x] = 0 );
#T       while i <= len and sizes[i] = actsize do
#T         max:= Filtered( actmaxes, x -> IsSubset( nsg[i], nsg[x] ) );
#T         for j in Reversed( max ) do
#T           SubtractSet( max, maxes[j] );
#T         od;
#T         Add( maxes, max );
#T         i:= i+1;
#T       od;
#T     od;
#T
#T     # construct the lattice record
#T     latt:= rec( domain          := tbl,
#T                 normalSubgroups := nsg,
#T                 sizes           := sizes,
#T                 maxes           := maxes,
#T                 XGAP            := rec( vertices := [ 1 .. len ],
#T                                         sizes    := sizes,
#T                                         maximals := maxes ),
#T                 operations      := PreliminaryLatticeOps );
#T
#T     # return the lattice record
#T     return latt;
#T end;


#############################################################################
##
#E

