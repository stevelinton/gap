@echo off
rem #########################################################################
rem
rem gap.bat                     GAP                          Martin Schoenert
rem
rem This is a  batch file for Windows that starts  GAP.
rem This is the place  where  you  make  all  the  necessary  customizations.
rem Then copy this file to a directory in your search path,  e.g.,  'C:\DOS'.
rem If you later move GAP to another location you must only change this file.
rem


rem #########################################################################
rem
rem GAP_DIR . . . . . . . . . . . . . . . . . . . . directory where GAP lives
rem
rem Set 'GAP_DIR' to the name of the directory where you have installed  GAP,
rem i.e., the directory with the subdirectories  'lib',  'grp',  'doc',  etc.
rem This name must not end  with  the  backslash  directory  separator ('\').
rem The default is  'C:\gap\gap4b5'.
rem You have to change this unless you have installed  GAP in this  location.
rem
set GAP_DIR=C:\gap\gap4b5


rem #########################################################################
rem
rem GAP_MEM . . . . . . . . . . . . . . . . . . . amount of initial workspace
rem
rem Set 'GAP_MEM' to the amount of memory GAP shall use as initial workspace.
rem The default is 12 MByte, which is the minimal reasonable amount of memory.
rem You have to change it if you want  GAP to use a larger initial workspace.
rem If you are not going to run  GAP  in parallel with other programs you may
rem want to set this value close to the  amount of memory your  computer has.
rem
set GAP_MEM=12m

rem #########################################################################
rem
rem GAP . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . run GAP
rem
rem You  probably should  not change  this line,  which  finally starts  GAP.
rem
%GAP_DIR%\bin\gapw95 -m %GAP_MEM% -l %GAP_DIR%; %1 %2 %3 %4 %5 %6 %7 %8




