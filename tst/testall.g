#############################################################################
##
#W  testall.g                   GAP library                      Frank Celler
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
##

#############################################################################
##
#F  START_TEST( <id> )  . . . . . . . . . . . . . . . . . . . start test file
##
start_TEST := START_TEST;

START_TIME := 0;
STONE_NAME := "";



START_TEST := function( name )
    FlushCaches();
    RANDOM_SEED(1);
    GASMAN("collect");
    START_TIME := Runtime();
    STONE_NAME := name;
end;


#############################################################################
##
#F  STOP_TEST( <file>, <fac> )  . . . . . . . . . . . . . . .  stop test file
##
stop_TEST := STOP_TEST;

STONE_RTIME := 0;
STONE_STONE := 0;
STONE_FILE  := 0;
STONE_SUM   := 0;
STONE_FSUM  := 0;
STONE_PROD  := 1;
STONE_COUNT := 0;

STOP_TEST := function( file, fac )
    local   time;

    STONE_FILE  := file;
    STONE_RTIME := Runtime() - START_TIME;
    if STONE_RTIME > 500  then
        STONE_STONE := QuoInt( fac, STONE_RTIME );
        STONE_SUM   := STONE_SUM + STONE_RTIME;
        STONE_FSUM  := STONE_FSUM + fac;
        STONE_PROD  := STONE_PROD*STONE_STONE;
        STONE_COUNT := STONE_COUNT + 1;
    else
        STONE_STONE := 0;
    fi;
end;


#############################################################################
##
#F  SHOW_STONES( <next> ) . . . . . . . . . . . . . . . . .  show GAP4 stones
##
STONE_ALL := [];

SHOW_STONES := function( next )
    Print( FormattedString(STONE_FILE,-16), "    ",
           FormattedString(STONE_STONE,8), "       ",
           FormattedString(STONE_RTIME,8) );
    Add( STONE_ALL, STONE_STONE );
    if 0 < next and STONE_FSUM <> 0  then
        Print( "    (next ~ ", Int(STONE_SUM*next*10/STONE_FSUM),
               " sec)\n" );
    else
        Print("\n");
    fi;
end;


#############################################################################
##
#F  TEST_FILES  . . . . . . . . . . . . . . . . . . . . .  list of test files
##
##  the following list contains the filename and  the scaling factor given to
##  `STOP_TEST' at the end of the test file.  The file  names are relative to
##  the test directory.
##
##  The list can be produced using:
##
##  grep -h "STOP_TEST" *.tst | sed -e 's:^gap> STOP_TEST( ":[ ":' | \
##  sed -e 's: );: ],:'
##
TEST_FILES := [
[ "alghom.tst", 65350000 ],
[ "algmat.tst", 1453000000 ],
[ "algsc.tst", 299000000 ],
[ "boolean.tst", 39000 ],
[ "combinat.tst",27000000 ],
#[ "compat3.tst", 10000 ],
[ "ctblfuns.tst", 31000000 ],
[ "ctblmoli.tst", 325000000 ],
[ "ctblmono.tst", 333000000 ],
[ "ctblsolv.tst", 367000000 ],
[ "cyclotom.tst", 5832500 ],
[ "ffe.tst",  18000000],
[ "fldabnum.tst", 90000000 ],
[ "gaussian.tst", 640000 ],
[ "grpconst.tst", 130921000000 ],
[ "grpfree.tst", 5000000 ],
[ "grplatt.tst", 4966000000 ],
[ "grpmat.tst", 1730000000 ],
[ "grppc.tst", 130800000 ],
[ "grppcnrm.tst", 1726000000 ],
[ "grpperm.tst", 2374000000 ],
[ "grpprmcs.tst", 15360000000 ],
[ "listgen.tst", 1440000 ],
[ "mapping.tst", 31000000 ],
[ "matblock.tst", 1200000 ],
[ "matrix.tst", 3964000000],
[ "mgmring.tst", 19000000 ],
[ "modfree.tst", 36000000 ],
[ "morpheus.tst", 588000000 ],
[ "onecohom.tst", 334000000 ],
[ "ratfun.tst", 9000000 ],
[ "relation.tst",48010000  ],
[ "rwspcgrp.tst", 267000000 ],
[ "rwspcsng.tst", 372000000 ],
[ "semigrp.tst",103000000 ],
[ "semicong.tst", 46000000 ],
[ "semirel.tst", 133000000 ],
[ "set.tst", 21000000 ],
[ "unknown.tst", 170000 ],
[ "vspchom.tst", 80550000 ],
[ "vspcmali.tst", 23900000 ],
[ "vspcmat.tst", 36050000 ],
[ "vspcrow.tst", 207000000 ],
# [ "weakptr.tst", 24477500 ], too sensitive to compiler
#               idiosyncracies SL
[ "xgap.tst", 544000000 ],
[ "zlattice.tst", 136000 ],
[ "zmodnz.tst", 21000000],
[ "hash2.tst",  20000000 ],
[ "quogphom.tst", 19000000 ],
[ "eigen.tst", 17000000 ],
[ "solmxgrp.tst", 1044000000 ],
[ "rss.tst", 83900000 ]
];

Sort( TEST_FILES, function(a,b) return a[2] < b[2]; end );

#############################################################################
##
#X  read all test files
##
Print("You should start GAP4 using:  `gap -N -A -x 80 -r -m 100m'. The more\n");
Print("GAP4stones you get, the faster your  system is.  The runtime of\n");
Print("the following tests (in general)  increases.  You should expect\n");
Print("about 100000 GAP4stones on a Pentium 3, 1GHz.\n");
Print("The `next' time is an approximation of the running time for the next test.\n");
Print("\n");
Print("Architecture: ", GAP_ARCHITECTURE, "\n");
Print("\n");
Print("test file         GAP4stones     time(msec)\n");
Print("-------------------------------------------\n");

infoRead1 := InfoRead1;  InfoRead1 := Ignore;
infoRead2 := InfoRead2;  InfoRead2 := Ignore;

TestDir := DirectoriesLibrary("tst");

for i  in [ 1 .. Length(TEST_FILES) ]  do
    name := Filename( TestDir, TEST_FILES[i][1] );
    if i < Length(TEST_FILES)  then
        next := TEST_FILES[i+1][2] / 10^4;
    else
        next := 0;
    fi;
    Print("testing: ",name,"\n");
    ReadTest(name);
    SHOW_STONES(next);
od;

Print("-------------------------------------------\n");
if STONE_COUNT=0 then
  STONE_COUNT:=1;
fi;
Print( FormattedString("total",-16), "    ",
       FormattedString(RootInt(STONE_PROD,STONE_COUNT),8), "       ",
       FormattedString(STONE_SUM,8), "\n" );
Print("\n");

InfoRead1  := infoRead1;
InfoRead2  := infoRead2;
START_TEST := start_TEST;
STOP_TEST  := stop_TEST;


#############################################################################
##
#E  testall.g . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
