# warning: this code assumes at most 9 sub-versions.
VERSION := "4.3fix5";
DATE := "June, 2003";
NEED_KERNEL_VERSION:="4.3.5";

#############################################################################
##  
#V  UPDATED_PACKAGES
##
##  This is a record of records, containing information about  packages  that
##  should be updated to certain versions. Each field  of  `UPDATED_PACKAGES'
##  is the name of a package <pkg> (in lowercase letters) that are  required/
##  recommended to be updated to certain versions. 
##
##  Each record `UPDATED_PACKAGES.(<pkg>)' contains the following fields:
##  \beginitems
##  `safeversion'& 
##     the smallest required version number of the package;
##  `message'& 
##     a string that will be printed as  an  explanation  of  the  error  (no
##     trailing `\\n' is necessary);
##  `refuseAutoload'&
##     is  a  flag  that  indicates  whether  the  package  should  still  be
##     autoloaded in the old version (if it is  `true'  autoloading  will  be
##     disabled for versions older than the indicated  `safeversion',  though 
##     the package  can  still be loaded with  `RequirePackage'  provided the
##     `refuseLoad' flag (see next field) is `false');
##  `quietAutoload'&
##     if this flag is set to true, the autoloading process will not produce
##     any warning. (Otherwise, if the package is listed in `ALLPKG', while
##     autoloading a warning will be printed, regardless of whether the
##     package autoloads.)
##     This is only intended for packages that do not autoload or only autoload
##     documentation.
##  `refuseLoad'&
##     is a flag that indicates whether the package should ever be loaded  in
##     the old version (if it is  `true'  loading will be completely disabled
##     for versions older than the indicated `safeversion'); and
##  `urlForUpdate'&
##     is an URL from which an updated version of the package may be fetched.
##  \enditems
BIND_GLOBAL( "UPDATED_PACKAGES", rec( 
anupq := rec(
  safeversion    := "1.3",
  message := 
    "This version is known to be incompatible with the current version of GAP.",
  refuseAutoload := true,                                 
  refuseLoad     := true,                                 
  quietAutoload:=true,
  urlForUpdate   := "http://www.math.rwth-aachen.de/~Greg.Gamble/ANUPQ"
  ),
autpgrp := rec(
  safeversion    := "1.1",
  message := 
    "This version is known to be incompatible with the current version of GAP.",
  refuseAutoload := true,
  refuseLoad     := false,                                 
  urlForUpdate   := "http://www-public.tu-bs.de:8080/~beick/so.html"
  )
) );



if KERNEL_VERSION<>NEED_KERNEL_VERSION then
  Print("\n\n",
        "You are running a GAP kernel which does not fit with the library.\n",
        "Probably you forgot to apply the kernel part or the library part\n",
	"of a bugfix?\n\n");

  if KERNEL_VERSION>NEED_KERNEL_VERSION then
    # kernel newer
    Print("You only installed a new kernel.\n",
    "You also must also install the most recent library bugfix, this is\n",
    "fix",
    KERNEL_VERSION{[1]},"r",KERNEL_VERSION{[3]},"n",
    KERNEL_VERSION{[5..LENGTH(KERNEL_VERSION)]},
    ".zoo (or .zip) or newer!\n\n\n");
  else
    # kernel older
    Print("If you are using Windows, make sure you installed the file\n",
	  "wbin",NEED_KERNEL_VERSION{[1]},"r",NEED_KERNEL_VERSION{[3]},"n",
	  NEED_KERNEL_VERSION{[5..LENGTH(NEED_KERNEL_VERSION)]},
	  ".zoo (or .zip)\n",
	  "Macintosh users make sure the file bin",
	  NEED_KERNEL_VERSION{[1]},"r",NEED_KERNEL_VERSION{[3]},"n",
	  NEED_KERNEL_VERSION{[5..LENGTH(NEED_KERNEL_VERSION)]},
	  "-PPC.sit (or -68k.sit) is installed\n",
	  "Unix users please recompile.\n\n");


  fi;
  Error("Update to correct kernel version!\n\n");
fi;
