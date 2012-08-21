#############################################################################
##
#W  oper.g                      GAP library                     Thomas Breuer
#W                                                             & Frank Celler
#W                                                         & Martin Schoenert
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file defines operations and such.
##
Revision.oper_g :=
    "@(#)$Id$";


#############################################################################
##

#V  CATS_AND_REPS
##
##  a list of filter numbers of categories and representations
##
BIND_GLOBAL( "CATS_AND_REPS", [] );


#############################################################################
##
#V  CONSTRUCTORS
##
BIND_GLOBAL( "CONSTRUCTORS", [] );


#############################################################################
##
#V  IMMEDIATES
##
##  is a list  that  contains at position   <i> the description of all  those
##  immediate methods for that `FILTERS[<i>]' belongs to the requirements.
##
##  So   each entry of  `IMMEDIATES'  is a  zipped list,  where 6 consecutive
##  positions  are ..., and the  position of  the  method itself  in the list
##  `IMMEDIATE_METHODS'.
##
##  Note:
##  1. If a method requires two filters $F_1$ and $F_2$ such that $F_1$
##     implies $F_2$, it will *not* be installed for $F_2$.
##  2. If not all requirements are categories/representations then
##     the category/representation part of the requirements will be ignored;
#T and if only cats are required? Does this make sense?
#T and what about representations that may change?
##     in other words, the only information that may cause to run immediate
##     methods is acquired information.
##  
##
BIND_GLOBAL( "IMMEDIATES", [] );


#############################################################################
##
#V  IMMEDIATE_METHODS
##
##  is a list of functions that are installed as immediate methods.
##
BIND_GLOBAL( "IMMEDIATE_METHODS", [] );


#############################################################################
##
#V  NUMBERS_PROPERTY_GETTERS
##
BIND_GLOBAL( "NUMBERS_PROPERTY_GETTERS", [] );


#############################################################################
##
#V  OPERATIONS
##
##  is a list that stores all {\GAP} operations at the odd positions,
##  and the corresponding list of requirements at the even positions.
##  More precisely, if the operation `OPERATIONS[<n>]' has been declared
##  by several calls of `DeclareOperation',
##  with second arguments <req1>, <req2>, \ldots,
##  each being a list of filters, then `OPERATIONS[ <n>+1 ]' is the list
##  $`[' <flags1>, <flags2>, \ldots, `]'$,
##  where <flagsi> is the list of flags of the filters in <reqi>.
##
BIND_GLOBAL( "OPERATIONS", [] );


#############################################################################
##
#V  SUM_FLAGS
##
BIND_GLOBAL( "SUM_FLAGS", 2000 );


#############################################################################
##

#V  IGNORE_IMMEDIATE_METHODS
##
##  is usually `false'.  Only inside a call of `RunImmediateMethods' it is
##  set to `true', which causes that `RunImmediateMethods' does not suffer
##  from recursion.
##
IGNORE_IMMEDIATE_METHODS := false;


#############################################################################
##
#F  INSTALL_IMMEDIATE_METHOD( <oper>, <name>, <filter>, <rank>, <method> )
##
BIND_GLOBAL( "INSTALL_IMMEDIATE_METHOD",
    function( oper, name, filter, rank, method )

    local   flags,
            relev,
            i,
            rflags,
            wif,
            ignore,
            j,
            k,
            replace;

    # Check whether <oper> really is an operation.
    if not IS_OPERATION(oper)  then
        Error( "<oper> is not an operation" );
    fi;
    
    # Check whether this in fact installs an implication.
    if    FLAGS_FILTER(oper) <> false
      and (method = true or method = RETURN_TRUE)
    then
        Error( "use `InstallTrueMethod' for <oper>" );
    fi;

    # Find the requirements.
    flags := TRUES_FLAGS( FLAGS_FILTER( filter ) );
    if LEN_LIST( flags ) = 0 then
        Error( "no immediate methods without requirements!" );
    elif FLAG1_FILTER( IS_MUTABLE_OBJ ) in flags  then
        Error( "no immediate methods for mutable objects!" );
    fi;
    relev := [];
    for i  in flags  do
        if not i in CATS_AND_REPS  then
            ADD_LIST( relev, i );
        fi;
    od;

    # All requirements are categories/representations.
    # Install the method for one of them.
    if LEN_LIST( relev ) = 0  then
        relev:= [ flags[1] ];
    fi;
    flags:= relev;

    # Remove requirements that are implied by the remaining ones.
    # (Note that it is possible to have implications from a filter
    # to another one with a bigger number.)
    relev  := [];
    rflags := [];
    for i  in flags  do

      # Get the implications of this filter.
      wif:= WITH_IMPS_FLAGS( FLAGS_FILTER( FILTERS[i] ) );

      # If the filter is implied by one in `relev', ignore it.
      # Otherwise add it to `relev', and remove all those that
      # are implied by the new filter.
      ignore:= false;
      for j  in [ 1 .. LEN_LIST( relev ) ]  do
          if IsBound( rflags[j] ) then
              if IS_SUBSET_FLAGS( rflags[j], wif ) then

                  # `FILTERS[i]' is implied by one in `relev'.
                  ignore:= true;
                  break;
              elif IS_SUBSET_FLAGS( wif, rflags[j] ) then

                  # `FILTERS[i]' implies one in `relev'.
                  Unbind( relev[j]  );
                  Unbind( rflags[j] );
              fi;
          fi;
      od;
      if not ignore then
          ADD_LIST( relev, i    );
          ADD_LIST( rflags, wif );
      fi;
    od;

    # We install the method for the requirements in `relev'.
    ADD_LIST( IMMEDIATE_METHODS, method );

    for j  in relev  do

      # adjust `IMM_FLAGS'
      IMM_FLAGS:= SUB_FLAGS( IMM_FLAGS, FLAGS_FILTER( FILTERS[j] ) );
#T here it would be better to subtract a flag list
#T with `true' exactly at position `j'!

      # Find the place to put the new method.
      if not IsBound( IMMEDIATES[j] ) then
          IMMEDIATES[j]:= [];
      fi;
      i := 0;
      while i < LEN_LIST(IMMEDIATES[j]) and rank < IMMEDIATES[j][i+5]  do
          i := i + 7;
      od;
      
      # Now is a good time to see if the method is already there 
      if REREADING then
          replace := false;
          k := i;
          while k < LEN_LIST(IMMEDIATES[j]) and 
            rank = IMMEDIATES[j][k+5] do
              if name = IMMEDIATES[j][k+7] and 
                 oper = IMMEDIATES[j][k+1] and
                 FLAGS_FILTER( filter ) = IMMEDIATES[j][k+4] then
                  replace := true;
                  i := k;
                  break;
              fi;
              k := k+7;
          od;
      fi;
      
      # push the other functions back
      if not REREADING or not replace then
          IMMEDIATES[j]{[i+1..LEN_LIST(IMMEDIATES[j])]+7}
            := IMMEDIATES[j]{[i+1..LEN_LIST(IMMEDIATES[j])]};
      fi;

      # install the new method
      IMMEDIATES[j][i+1] := oper;
      IMMEDIATES[j][i+2] := SETTER_FILTER( oper );
      IMMEDIATES[j][i+3] := FLAGS_FILTER( TESTER_FILTER( oper ) );
      IMMEDIATES[j][i+4] := FLAGS_FILTER( filter );
      IMMEDIATES[j][i+5] := rank;
      IMMEDIATES[j][i+6] := LEN_LIST( IMMEDIATE_METHODS );
      IMMEDIATES[j][i+7] := IMMUTABLE_COPY_OBJ(name);

    od;

end );


#############################################################################
##
#F  InstallImmediateMethod( <opr>, <filter>, <rank>, <method> )
##
##  installs  <method>  as  immediate  method for <opr>,   which  must  be an
##  operation of one argument, with requirement <filter> and rank <rank>.
##
BIND_GLOBAL( "InstallImmediateMethod", function( arg )
    local   name;

    if LEN_LIST(arg) = 4  then
        name := NAME_FUNC(arg[1]);
        INSTALL_IMMEDIATE_METHOD( arg[1], name, arg[2], arg[3], arg[4] );
    elif LEN_LIST(arg) = 5  then
        INSTALL_IMMEDIATE_METHOD( arg[1], arg[2], arg[3], arg[4], arg[5] );
    fi;
end );


#############################################################################
##
#F  TraceImmediateMethods( <flag> )
##
##  If <flag> is true, tracing for all immediate methods is turned on.
##  If <flag> is false it is turned off.
##  (There is no facility to trace *specific* immediate methods.)
##
TRACE_IMMEDIATE_METHODS := false;

BIND_GLOBAL( "TraceImmediateMethods", function( flag )
    if flag  then
        TRACE_IMMEDIATE_METHODS := true;
    else
        TRACE_IMMEDIATE_METHODS := false;
    fi;
end );


#############################################################################
##
#F  RunImmediateMethods( <obj>, <flags> )
##
##  applies immediate  methods  for the   object <obj>  for that  the  `true'
##  position in the Boolean list <flags> mean  that the corresponding filters
##  have been discovered recently.
##  So possible consequences of other filters are not checked.
##
RUN_IMMEDIATE_METHODS_CHECKS := 0;
RUN_IMMEDIATE_METHODS_HITS   := 0;

BIND_GLOBAL( "RunImmediateMethods", function ( obj, flags )

    local   flagspos,   # list of `true' positions in `flags'
            tried,      # list of numbers of methods that have been used
            type,       # type of `obj', used to notice type changes
            j,          # loop over `flagspos'
            imm,        # immediate methods for filter `j'
            i,          # loop over `imm'
            res,        # result of an immediate method
            newflags;   # newly  found filters

    # Avoid recursive calls from inside a setter.
    if IGNORE_IMMEDIATE_METHODS then return; fi;

    # intersect the flags with those for which immediate methods
    # are installed.
    if IS_SUBSET_FLAGS( IMM_FLAGS, flags ) then return; fi;
    flags := SUB_FLAGS( flags, IMM_FLAGS );

    flagspos := SHALLOW_COPY_OBJ(TRUES_FLAGS(flags));
    tried    := [];
    type     := TYPE_OBJ( obj );
    flags    := type![2];

    # Check the immediate methods for all in `flagspos'.
    # (Note that new information is handled via appending to that list.)
    for j  in flagspos  do

        # Loop over those immediate methods
        # - that require `flags[j]' to be `true',
        # - that are applicable to `obj',
        # - whose result is not yet known to `obj',
        # - that have not yet been tried in this call of 
        #   `RunImmediateMethods'.

        if IsBound( IMMEDIATES[j] ) then
#T  the `if' statement can disappear when `IMM_FLAGS' is improved ...
            imm := IMMEDIATES[j];
            for i  in [ 0, 7 .. LEN_LIST(imm)-7 ]  do
    
                if        IS_SUBSET_FLAGS( flags, imm[i+4] )
                  and not IS_SUBSET_FLAGS( flags, imm[i+3] )
                  and not imm[i+6] in tried
                then
    
                    # Call the method, and store that it was used.
                    res := IMMEDIATE_METHODS[ imm[i+6] ]( obj );
                    ADD_LIST( tried, imm[i+6] );
                    RUN_IMMEDIATE_METHODS_CHECKS :=
                        RUN_IMMEDIATE_METHODS_CHECKS+1;
                    if TRACE_IMMEDIATE_METHODS  then
                        Print( "#I  immediate: ", imm[i+7], "\n" );
                    fi;
    
                    if res <> TRY_NEXT_METHOD  then
    
                        # Call the setter, without running immediate methods.
                        IGNORE_IMMEDIATE_METHODS := true;
                        imm[i+2]( obj, res );
                        IGNORE_IMMEDIATE_METHODS := false;
                        RUN_IMMEDIATE_METHODS_HITS :=
                            RUN_IMMEDIATE_METHODS_HITS+1;
                              
                        # If `obj' has noticed the new information,
                        # add the numbers of newly known filters to
                        # `flagspos', in order to call their immediate
                        # methods later.
                        if not IS_IDENTICAL_OBJ( TYPE_OBJ(obj), type ) then

                          type := TYPE_OBJ(obj);

                          newflags := SUB_FLAGS( type![2], IMM_FLAGS );
                          newflags := SUB_FLAGS( newflags, flags );
                          APPEND_LIST_INTR( flagspos,
                                            TRUES_FLAGS( newflags ) );

                          flags := type![2];

                        fi;
                    fi;
                fi;
            od;

        fi;
    od;
end );


#############################################################################
##
#F  INSTALL_METHOD_FLAGS( <opr>, <info>, <rel>, <flags>, <rank>, <method> ) .
##
BIND_GLOBAL( "INSTALL_METHOD_FLAGS",
    function( opr, info, rel, flags, rank, method )
    local   methods,  narg,  i,  k,  tmp, replace, match, j;
    
    # add the number of filters required for each argument
    if opr in CONSTRUCTORS  then
        if 0 < LEN_LIST(flags)  then
            rank := rank - RankFilter( flags[ 1 ] );
        fi;
    else
        for i  in flags  do
            rank := rank + RankFilter( i );
        od;
    fi;

    # get the methods list
    narg := LEN_LIST( flags );
    methods := METHODS_OPERATION( opr, narg );

    # set the name
    if info = false  then
        info := NAME_FUNC(opr);
    else
        k := SHALLOW_COPY_OBJ(NAME_FUNC(opr));
        APPEND_LIST_INTR( k, ": " );
        APPEND_LIST_INTR( k, info );
        info := k;
        CONV_STRING(info);
    fi;
    
    # find the place to put the new method
    i := 0;
    while i < LEN_LIST(methods) and rank < methods[i+(narg+3)]  do
        i := i + (narg+4);
    od;

    # Now is a good time to see if the method is already there 
    if REREADING then
        replace := false;
        k := i;
        while k < LEN_LIST(methods) and 
          rank = methods[k+narg+3] do
            if info = methods[k+narg+4] then
               
                # ForAll not available
                match := false;
                for j in [1..narg] do
                    match := match and methods[k+j+1] = flags[j];
                od;
                if match then
                    replace := true;
                    i := k;
                    break;
                fi;
            fi;
            k := k+narg+4;
        od;
    fi;
    # push the other functions back
    if not REREADING or not replace then
        methods{[i+1..LEN_LIST(methods)]+(narg+4)}
          := methods{[i+1..LEN_LIST(methods)]};
    fi;

    # install the new method
    if   rel = true  then
        methods[i+1] := RETURN_TRUE;
    elif rel = false  then
        methods[i+1] := RETURN_FALSE;
    elif IS_FUNCTION(rel)  then
        if CHECK_INSTALL_METHOD  then
            tmp := NARG_FUNC(rel);
            if tmp <> AINV(1) and tmp <> narg  then
                Error(NAME_FUNC(opr),": <famrel> must accept ",
		      narg, " arguments");
            fi;
        fi;
        methods[i+1] := rel;
    else
        Error(NAME_FUNC(opr),
	      ": <famrel> must be a function, `true', or `false'" );
    fi;

    # install the filters
    for k  in [ 1 .. narg ]  do
        methods[i+k+1] := flags[k];
    od;

    # install the method
    if   method = true  then
        methods[i+(narg+2)] := RETURN_TRUE;
    elif method = false  then
        methods[i+(narg+2)] := RETURN_FALSE;
    elif IS_FUNCTION(method)  then
        if CHECK_INSTALL_METHOD  then
            tmp := NARG_FUNC(method);
            if tmp <> AINV(1) and tmp <> narg  then
               Error(NAME_FUNC(opr),": <method> must accept ",
	             narg, " arguments");
           fi;
       fi;
        methods[i+(narg+2)] := method;
	if CHECK_INSTALL_METHOD  then
            tmp := NARG_FUNC(method);
            if tmp <> AINV(1) and tmp <> narg  then
               Error(NAME_FUNC(opr),"<method> must accept ",
	             narg, " arguments" );
            fi;
        fi;
    else
        Error(NAME_FUNC(opr),
	      ": <method> must be a function, `true', or `false'" );
    fi;
    methods[i+(narg+3)] := rank;

    methods[i+(narg+4)] := IMMUTABLE_COPY_OBJ(info);

    # flush the cache
    CHANGED_METHODS_OPERATION( opr, narg );
end );


#############################################################################
##
#F  INFO_INSTALL( <level>, ... )
##
##  This will delegate to `InfoWarning' as soon as this is available.
##
BIND_GLOBAL( "INFO_INSTALL", function( arg )
    CALL_FUNC_LIST( Print, arg{ [ 2 .. LEN_LIST( arg ) ] } );
end );


#############################################################################
##
#F  INSTALL_METHOD( <oper>, ... ) . . . . . . . . install a method for <oper>
##
BIND_GLOBAL( "INSTALL_METHOD",
    function( opr, info, rel, filters, rank, method, check )
    local   tmp,  req, reqs, match, i, j, k, imp,  flags;

    # check whether <opr> really is an operation
    if not IS_OPERATION(opr)  then
        Error( "<opr> is not an operation" );
    fi;
    
    # check whether this in fact installs an implication
    if    FLAGS_FILTER(opr) <> false
      and (rel = true or rel = RETURN_TRUE)
      and LEN_LIST(filters) = 1
      and (method = true or method = RETURN_TRUE)
    then
        Error(NAME_FUNC(opr), ": use `InstallTrueMethod' for <opr>" );
    fi;

    # check <info>
    if info <> false and not IS_STRING(info)  then
        Error(NAME_FUNC(opr), ": <info> must be a string or `false'" );
    fi;
    
    # compute the flags lists for the filters
    flags := [  ];
    for i  in filters  do
        ADD_LIST( flags, FLAGS_FILTER( i ) );
    od;
    
    # test if <check> is true
    if CHECK_INSTALL_METHOD and check  then

        # find the operation
        req := false;
        for i  in [ 1, 3 .. LEN_LIST(OPERATIONS)-1 ]  do
            if IS_IDENTICAL_OBJ( OPERATIONS[i], opr )  then
                req := OPERATIONS[i+1];
                break;
            fi;
        od;
        if req = false  then
            Error( "unknown operation ", NAME_FUNC(opr) );
        fi;

        # do check with implications
        imp := [];
        for i  in flags  do
            ADD_LIST( imp, WITH_HIDDEN_IMPS_FLAGS( i ) );
        od;

        # Check that the requirements of the method match
        # (at least) one declaration.
        j:= 0;
        match:= false;
        while j < LEN_LIST( req ) and not match do
          j:= j+1;
          reqs:= req[j];
          if LEN_LIST( reqs ) = LEN_LIST( imp ) then
            match:= true;
            for i  in [ 1 .. LEN_LIST(reqs) ]  do
              if not IS_SUBSET_FLAGS( imp[i], reqs[i] )  then
                match:= false;
                break;
              fi;
            od;
            if match then break; fi;
          fi;
        od;

        if not match then

          # If the requirements do not match any of the declarations
          # then something is wrong or `InstallOtherMethod' should be used.
          tmp:= [];
          for i in imp do
            ADD_LIST( tmp, NamesFilter( i ) );
          od;
          Error( "required filters ", tmp,
                 " do not match a declaration of ", NAME_FUNC(opr) );

        else

          # If the requirements match *more than one* declaration
          # then a warning is raised;
          # this is done by calling `INFO_INSTALL',
          # which delegates to `Print' until `InfoWarning' is defined,
          # and delegates to `InfoWarning' (with level 2) afterwards.
          for k in [ j+1 .. LEN_LIST( req ) ] do
            reqs:= req[k];
            if LEN_LIST( reqs ) = LEN_LIST( imp ) then
              match:= true;
              for i  in [ 1 .. LEN_LIST(reqs) ]  do
                if not IS_SUBSET_FLAGS( imp[i], reqs[i] )  then
                  match:= false;
                  break;
                fi;
              od;
              if match then
                INFO_INSTALL( 2,
                      "method installed for ", NAME_FUNC(opr),
                      " matches more than one declaration" );
              fi;
            fi;
          od;

        fi;
    fi;
    
    # Install the method in the operation.
    INSTALL_METHOD_FLAGS( opr, info, rel, flags, rank, method );
end );


#############################################################################
##
#F  InstallMethod( <opr>,[ <info>,] <relation>, <filters>, <rank>, <method> )
##
BIND_GLOBAL( "InstallMethod", function ( arg )
    if 6 = LEN_LIST(arg)  then
        INSTALL_METHOD(arg[1],arg[2],arg[3],arg[4],arg[5],arg[6],true);
    elif 5 = LEN_LIST(arg)  then
        INSTALL_METHOD(arg[1],false,arg[2],arg[3],arg[4],arg[5],true);
    else
      Error("usage: InstallMethod( <opr>, <rel>, <fil>, <rk>, <method>) for ",
	NAME_FUNC(arg[1]));
    fi;
end );


#############################################################################
##
#F  InstallOtherMethod( <opr>,[ <info>,] <relation>, <filters>, <rank>,
#F                      <method> )
##
BIND_GLOBAL( "InstallOtherMethod", function ( arg )
    if 6 = LEN_LIST(arg)  then
        INSTALL_METHOD(arg[1],arg[2],arg[3],arg[4],arg[5],arg[6],false);
    elif 5 = LEN_LIST(arg)  then
        INSTALL_METHOD(arg[1],false,arg[2],arg[3],arg[4],arg[5],false);
    else
        Error( "usage: InstallOtherMethod( <opr>, <rel>, <fil>, <rk>, ",
               "<method> ) for ",NAME_FUNC(arg[1]) );
    fi;
end );


#############################################################################
##
#F  NewOperation( <name>, <filters> )
##
BIND_GLOBAL( "NewOperation", function ( name, filters )
    local   oper,  filt,  filter;

    oper := NEW_OPERATION( name );
    filt := [];
    for filter  in filters  do
        if not IS_OPERATION( filter ) then
          Error( "<filter> must be an operation" );
        fi;
        ADD_LIST( filt, FLAGS_FILTER( filter ) );
    od;
    ADD_LIST( OPERATIONS, oper );
    ADD_LIST( OPERATIONS, [ filt ] );
    return oper;
end );


#############################################################################
##
#F  NewConstructor( <name>, <filters> )
##
BIND_GLOBAL( "NewConstructor", function ( name, filters )
    local   oper,  filt,  filter;

    oper := NEW_CONSTRUCTOR( name );
    filt := [];
    for filter  in filters  do
        if not IS_OPERATION( filter ) then
          Error( "<filter> must be an operation" );
        fi;
        ADD_LIST( filt, FLAGS_FILTER( filter ) );
    od;
    ADD_LIST( CONSTRUCTORS, oper );
    ADD_LIST( OPERATIONS,   oper );
    ADD_LIST( OPERATIONS,   [ filt ] );
    return oper;
end );


#############################################################################
##
#F  DeclareOperation( <name>, <filters> )
##
BIND_GLOBAL( "DeclareOperation", function ( name, filters )

    local gvar, pos, filt, filter;

    if ISB_GVAR( name ) then

      gvar:= VALUE_GLOBAL( name );

      # Check that the variable is in fact an operation.
      if not IS_OPERATION( gvar ) then
        Error( "variable `", name, "' is not bound to an operation" );
      fi;

      # The operation has already been declared.
      # If it was created as attribute or property,
      # and if the new declaration is unary
      # then ask for re-declaration as attribute or property.
      # (Note that the values computed for objects matching the new
      # requirements will be stored.)
      if LEN_LIST( filters ) = 1 and FLAG2_FILTER( gvar ) <> 0 then

        # `gvar' is an attribute (tester) or property (tester).
        pos:= POS_LIST_DEFAULT( FILTERS, gvar, 0 );
        if pos = 0 then

          # `gvar' is an attribute.
          Error( "operation `", name,
                 "' was created as an attribute, use`DeclareAttribute'" );

        elif    INFO_FILTERS[ pos ] in FNUM_TPRS
             or INFO_FILTERS[ pos ] in FNUM_ATTS then

          # `gvar' is an attribute tester or property tester.
          Error( "operation `", name,
                 "' is an attribute tester or property tester" );

        else

          # `gvar' is a property.
          Error( "operation `", name,
                 "' was created as a property, use`DeclareProperty'" );

        fi;

      fi;

      # Add the new requirements.
      filt := [];
      for filter  in filters  do
        if not IS_OPERATION( filter ) then
          Error( "<filter> must be an operation" );
        fi;
        ADD_LIST( filt, FLAGS_FILTER( filter ) );
      od;

      pos:= POS_LIST_DEFAULT( OPERATIONS, gvar, 0 );
      ADD_LIST( OPERATIONS[ pos+1 ], filt );

    else

      # The operation is new.
      BIND_GLOBAL( name, NewOperation( name, filters ) );

    fi;
end );


#############################################################################
##
#F  DeclareOperationKernel( <name>, <filters>, <kernel-oper> )
##
##  This function must not be used to re-declare an operation
##  that has already been declared.
##
BIND_GLOBAL( "DeclareOperationKernel", function ( name, filters, oper )
    local   filt,  filter;

    # This will yield an error if `name' is already bound.
    BIND_GLOBAL( name, oper );

    filt := [];
    for filter  in filters  do
        if not IS_OPERATION( filter ) then
          Error( "<filter> must be an operation" );
        fi;
        ADD_LIST( filt, FLAGS_FILTER( filter ) );
    od;

    ADD_LIST( OPERATIONS, oper );
    ADD_LIST( OPERATIONS, [ filt ] );
end );


#############################################################################
##
#F  DeclareConstructor( <name>, <filters> )
##
BIND_GLOBAL( "DeclareConstructor", function ( name, filters )

    local gvar, pos, filt, filter;

    if ISB_GVAR( name ) then

      gvar:= VALUE_GLOBAL( name );

      # Check that the variable is in fact an operation.
      if not IS_OPERATION( gvar ) then
        Error( "variable `", name, "' is not bound to an operation" );
      fi;

      # The constructor has already been declared.
      # If it was not created as a constructor
      # then ask for re-declaration as an ordinary operation.
      if not gvar in CONSTRUCTORS then
        Error( "operation `", name, "' was not created as a constructor" );
      fi;

      # Add the new requirements.
      filt := [];
      for filter  in filters  do
        if not IS_OPERATION( filter ) then
          Error( "<filter> must be an operation" );
        fi;
        ADD_LIST( filt, FLAGS_FILTER( filter ) );
      od;

      pos:= POS_LIST_DEFAULT( OPERATIONS, gvar, 0 );
      ADD_LIST( OPERATIONS[ pos+1 ], filt );

    else

      # The operation is new.
      BIND_GLOBAL( name, NewConstructor( name, filters ) );

    fi;
end );


#############################################################################
##
#F  DeclareConstructorKernel( <name>, <filter>, <kernel-oper> )
##
##  This function must not be used to re-declare a constructor
##  that has already been declared.
##
BIND_GLOBAL( "DeclareConstructorKernel", function ( name, filters, oper )
    local   filt,  filter;

    # This will yield an error if `name' is already bound.
    BIND_GLOBAL( name, oper );

    filt := [];
    for filter  in filters  do
        if not IS_OPERATION( filter ) then
          Error( "<filter> must be an operation" );
        fi;
        ADD_LIST( filt, FLAGS_FILTER( filter ) );
    od;

    ADD_LIST( CONSTRUCTORS, oper );
    ADD_LIST( OPERATIONS,   oper );
    ADD_LIST( OPERATIONS,   [ filt ] );
end );


#############################################################################
##
#F  InstallAttributeFunction( <func> )  . . . run function for each attribute
##
##  `InstallAttributeFunction' installs <func>, so that
##  `<func>( <name>, <filter>, <getter>, <setter>, <tester>, <mutflag> )'
##  is called for each attribute.
##
BIND_GLOBAL( "ATTRIBUTES", [] );

BIND_GLOBAL( "ATTR_FUNCS", [] );

BIND_GLOBAL( "InstallAttributeFunction", function ( func )
    local   attr;
    for attr in ATTRIBUTES do
        func( attr[1], attr[2], attr[3], attr[4], attr[5], attr[6] );
    od;
    ADD_LIST( ATTR_FUNCS, func );
end );

BIND_GLOBAL( "RUN_ATTR_FUNCS",
    function ( filter, getter, setter, tester, mutflag )
    local    name, func;
    name:= NAME_FUNC( getter );
    for func in ATTR_FUNCS do
        func( name, filter, getter, setter, tester, mutflag );
    od;
    ADD_LIST( ATTRIBUTES, [ name, filter, getter, setter, tester, mutflag ] );
end );


#############################################################################
##
#F  DeclareAttributeKernel( <name>, <filter>, <getter> )  . . . new attribute
##
##  This function must not be used to re-declare an attribute
##  that has already been declared.
##
BIND_GLOBAL( "DeclareAttributeKernel", function ( name, filter, getter )
    local setter, tester, nname;

    # This will yield an error if `name' is already bound.
    BIND_GLOBAL( name, getter );

    # construct setter and tester
    setter := SETTER_FILTER( getter );
    tester := TESTER_FILTER( getter );

    # add getter, setter and tester to the list of operations
    ADD_LIST( OPERATIONS, getter );
    ADD_LIST( OPERATIONS, [ [ FLAGS_FILTER(filter) ] ] );
    ADD_LIST( OPERATIONS, setter );
    ADD_LIST( OPERATIONS,
              [ [ FLAGS_FILTER( filter ), FLAGS_FILTER( IS_OBJECT ) ] ] );
    ADD_LIST( OPERATIONS, tester );
    ADD_LIST( OPERATIONS, [ [ FLAGS_FILTER(filter) ] ] );

    # store the information about the filter
    FILTERS[ FLAG2_FILTER( tester ) ] := tester;
    IMM_FLAGS:= AND_FLAGS( IMM_FLAGS, FLAGS_FILTER( tester ) );
    INFO_FILTERS[ FLAG2_FILTER( tester ) ] := 5;

    # clear the cache because <filter> is something old
    InstallHiddenTrueMethod( filter, tester );
    CLEAR_HIDDEN_IMP_CACHE( tester );

    # run the attribute functions
    RUN_ATTR_FUNCS( filter, getter, setter, tester, false );

    # store the ranks
    RANK_FILTERS[ FLAG2_FILTER( tester ) ] := 1;

    # and make the remaining assignments
    nname:= "Set"; APPEND_LIST_INTR( nname, name );
    BIND_GLOBAL( nname, setter );
    nname:= "Has"; APPEND_LIST_INTR( nname, name );
    BIND_GLOBAL( nname, tester );

end );


#############################################################################
##
#F  NewAttribute( <name>, <filter> [,"mutable"] [,<rank>] ) . . new attribute
##
##  is a new attribute getter with name  <name> that is applicable to objects
##  with the property <filter>.  If the optional third argument is given then
##  there are  two possibilities.  Either it is  an integer <rank>,  then the
##  attribute tester has this rank.  Or it  is the string "mutable", then the
##  values of the attribute shall be mutable; more precisely, when a value of
##  such a mutable attribute is set then this value itself is stored, not an
##  immutable copy of it.
##  (So it is the user's responsibility to set an object that is in fact
##  mutable.)
#T in the current implementation, one can overwrite values of mutable
#T attributes; is this really intended?
#T if yes then it should be documented!
##
##  If no third argument is given then the rank of the tester is 1.
##
BIND_GLOBAL( "NewAttribute", function ( arg )
    local   name, filter, flags, mutflag, getter, setter, tester;

    # construct getter, setter and tester
    name   := arg[1];
    filter := arg[2];

    if not IS_OPERATION( filter ) then
      Error( "<filter> must be an operation" );
    fi;
    flags:= FLAGS_FILTER( filter );

    # the mutability flags is the third one (which can also be the rank)
    mutflag := LEN_LIST(arg) = 3 and arg[3] = "mutable";

    # construct a new attribute
    if mutflag then
        getter := NEW_MUTABLE_ATTRIBUTE( name );
    else
        getter := NEW_ATTRIBUTE( name );
    fi;

    # store the information about the filter
    INFO_FILTERS[ FLAG2_FILTER(getter) ] := 6;

    # add getter, setter and tester to the list of operations
    setter := SETTER_FILTER( getter );
    tester := TESTER_FILTER( getter );

    ADD_LIST( OPERATIONS, getter );
    ADD_LIST( OPERATIONS, [ [ flags ] ] );
    ADD_LIST( OPERATIONS, setter );
    ADD_LIST( OPERATIONS, [ [ flags, FLAGS_FILTER( IS_OBJECT ) ] ] );
    ADD_LIST( OPERATIONS, tester );
    ADD_LIST( OPERATIONS, [ [ flags ] ] );

    # install the default functions
    FILTERS[ FLAG2_FILTER( tester ) ] := tester;
    IMM_FLAGS:= AND_FLAGS( IMM_FLAGS, FLAGS_FILTER( tester ) );

    # the <tester> is newly made, therefore  the cache cannot contain a  flag
    # list involving <tester>
    InstallHiddenTrueMethod( filter, tester );
    # CLEAR_HIDDEN_IMP_CACHE();

    # run the attribute functions
    RUN_ATTR_FUNCS( filter, getter, setter, tester, mutflag );

    # store the rank
    if LEN_LIST( arg ) = 3 and IS_INT( arg[3] ) then
        RANK_FILTERS[ FLAG2_FILTER( tester ) ] := arg[3];
    else
        RANK_FILTERS[ FLAG2_FILTER( tester ) ] := 1;
    fi;

    # and return the getter
    return getter;
end );


#############################################################################
##
#F  DeclareAttribute( <name>, <filter> [,"mutable"] [,<rank>] ) new attribute
##
BIND_GLOBAL( "DeclareAttribute", function ( arg )

    local attr, name, nname, gvar, pos, filter;

    name:= arg[1];

    if ISB_GVAR( name ) then

      gvar:= VALUE_GLOBAL( name );

      # Check that the variable is in fact an operation.
      if not IS_OPERATION( gvar ) then
        Error( "variable `", name, "' is not bound to an operation" );
      fi;

      # The attribute has already been declared.
      # If it was not created as an attribute
      # then ask for re-declaration as an ordinary operation.
      # (Note that the values computed for objects matching the new
      # requirements cannot be stored.)
      if FLAG2_FILTER( gvar ) = 0 or gvar in FILTERS then

        # `gvar' is not an attribute (tester) and not a property (tester),
        # or `gvar' is a filter;
        # in any case, `gvar' is not an attribute.
        Error( "operation `", name, "' was not created as an attribute,",
               " use`DeclareOperation'" );

      fi;

      # Add the new requirements.
      filter:= arg[2];
      if not IS_OPERATION( filter ) then
        Error( "<filter> must be an operation" );
      fi;

      pos:= POS_LIST_DEFAULT( OPERATIONS, gvar, 0 );
      ADD_LIST( OPERATIONS[ pos+1 ], [ FLAGS_FILTER( filter ) ] );

    else

      # The attribute is new.
      attr:= CALL_FUNC_LIST( NewAttribute, arg );
      BIND_GLOBAL( name, attr );
      nname:= "Set"; APPEND_LIST_INTR( nname, name );
      BIND_GLOBAL( nname, SETTER_FILTER( attr ) );
      nname:= "Has"; APPEND_LIST_INTR( nname, name );
      BIND_GLOBAL( nname, TESTER_FILTER( attr ) );

    fi;
end );


#############################################################################
##
#M  default attribute getter and setter methods
##
##  There are the following three default getter methods.
##  The first requires only `IsObject', and signals what categories the
##  attribute requires.
##  The second requires the category part of the attribute's requirements,
##  tests the property getters of the requirements,
##  and --if they are `true' and afterwards stored in the object-
##  calls the attribute operation again.
##  The third requires the attribute's requirements,
##  and signals that no method was found.
##  All these methods are installed with rank zero,
##  the succession of their installation makes sure that they are ordered
##  correctly.
##
##  The default setter method does nothing.
##
##  Note that we do *not* install any  default getter method for an attribute
##  that requires only `IsObject'.
##  (The error message is printed by the method selection in this case.)
##  Also the second and third default method are installed only
##  if the property getter part of the attribute's requirements
##  is nontrivial.
##  
InstallAttributeFunction(
    function ( name, filter, getter, setter, tester, mutflag )

    local flags, rank, cats, props, i;

    if not IS_IDENTICAL_OBJ( filter, IS_OBJECT ) then

        flags := FLAGS_FILTER( filter );

        InstallOtherMethod( getter,
            "default method requiring `IsObject' that checks categories",
            true,
            [ IS_OBJECT ], 0,
            function ( obj )
            local filt, hascats, i;
            filt:= [];
            hascats:= true;
            for i in [ 1 .. LEN_FLAGS(flags) ] do
                if ELM_FLAGS(flags,i) and i in CATS_AND_REPS  then
                    if not FILTERS[i]( obj ) then
                        hascats:= false;
                    fi;
                    ADD_LIST( filt, NAME_FUNC( FILTERS[i] ) );
                fi;
            od;
            if not hascats then
                Error( "argument for `", name,
                       "' must have categories `", filt, "'" );
            else
                Error( "no method found for operation ", name );
            fi;
	    # catch `return'
	    repeat
	      Error("you cannot use `return;' here, use `quit;'");
	    until false;
	  end
        );

        rank  := 0;
        cats  := IS_OBJECT;
        props := [];
        for i in [ 1 .. LEN_FLAGS( flags ) ] do
            if ELM_FLAGS( flags, i ) then
                if i in CATS_AND_REPS  then
                    cats := cats and FILTERS[i];
                    rank := rank - RankFilter( FILTERS[i] );
                elif i in NUMBERS_PROPERTY_GETTERS  then
                    ADD_LIST( props, FILTERS[i] );
                fi;
            fi;
        od;

        if 0 < LEN_LIST( props ) then

          InstallOtherMethod( getter,
              "default method requiring categories and checking properties",
              true,
              [ cats ], rank,
              function ( obj )
              local prop;
              for prop in props do
                if not ( prop( obj ) and Tester( prop )( obj ) ) then
                  Error( "<obj> must have+store all properties in <props>" );
		  # catch `return'
		  repeat
		    Error("you cannot use `return;' here, use `quit;'");
		  until false;
                fi;
              od;
              return getter( obj );
              end );
  
          InstallMethod( getter,
              "default method for requirements of the attribute",
              true,
              [ filter ], - RankFilter( filter ),
              function ( obj )
              Error( "no method found for operation ", name );
              end );

        fi;
    fi;
    end );

InstallAttributeFunction(
    function ( name, filter, getter, setter, tester, mutflag )
    InstallOtherMethod( setter,
        "default method, does nothing",
        true,
        [ IS_OBJECT, IS_OBJECT ], 0,
        function ( obj, val )
        end );
    end );


#############################################################################
##
#F  DeclarePropertyKernel( <name>, <filter>, <getter> ) . . . .  new property
##
##  This function must not be used to re-declare a property
##  that has already been declared.
##
BIND_GLOBAL( "DeclarePropertyKernel", function ( name, filter, getter )
    local setter, tester, nname;

    # This will yield an error if `name' is already bound.
    BIND_GLOBAL( name, getter );

    # construct setter and tester
    setter := SETTER_FILTER( getter );
    tester := TESTER_FILTER( getter );

    # store the property getters
    ADD_LIST( NUMBERS_PROPERTY_GETTERS, FLAG1_FILTER( getter ) );

    # add getter, setter and tester to the list of operations
    ADD_LIST( OPERATIONS, getter );
    ADD_LIST( OPERATIONS, [ [ FLAGS_FILTER(filter) ] ] );
    ADD_LIST( OPERATIONS, setter );
    ADD_LIST( OPERATIONS,
              [ [ FLAGS_FILTER( filter ), FLAGS_FILTER( IS_BOOL ) ] ] );
    ADD_LIST( OPERATIONS, tester );
    ADD_LIST( OPERATIONS, [ [ FLAGS_FILTER(filter) ] ] );

    # install the default functions
    FILTERS[ FLAG1_FILTER( getter ) ]:= getter;
    IMM_FLAGS:= AND_FLAGS( IMM_FLAGS, FLAGS_FILTER( getter ) );
    FILTERS[ FLAG2_FILTER( getter ) ]:= tester;
    INFO_FILTERS[ FLAG1_FILTER( getter ) ]:= 7;
    INFO_FILTERS[ FLAG2_FILTER( getter ) ]:= 8;

    # clear the cache because <filter> is something old
    InstallHiddenTrueMethod( tester, getter );
    CLEAR_HIDDEN_IMP_CACHE( getter );
    InstallHiddenTrueMethod( filter, tester );
    CLEAR_HIDDEN_IMP_CACHE( tester );

    # run the attribute functions
    RUN_ATTR_FUNCS( filter, getter, setter, tester, false );

    # store the ranks
    RANK_FILTERS[ FLAG1_FILTER( getter ) ] := 1;
    RANK_FILTERS[ FLAG2_FILTER( getter ) ] := 1;

    # and make the remaining assignments
    nname:= "Set"; APPEND_LIST_INTR( nname, name );
    BIND_GLOBAL( nname, setter );
    nname:= "Has"; APPEND_LIST_INTR( nname, name );
    BIND_GLOBAL( nname, tester );
end );


#############################################################################
##
#F  NewProperty( <name>, <filter> [,<rank>] ) . . . . . . . . .  new property
##
##  is a new property  getter with name <name>  that is applicable to objects
##  with property <filter>.  If  the optional argument  <rank> is  given then
##  the property getter has this rank, otherwise its rank is 1.
##
BIND_GLOBAL( "NewProperty", function ( arg )
    local   name, filter, flags, getter, setter, tester;

    name   := arg[1];
    filter := arg[2];

    if not IS_OPERATION( filter ) then
      Error( "<filter> must be an operation" );
    fi;
    flags:= FLAGS_FILTER( filter );

    # construct getter, setter and tester
    getter := NEW_PROPERTY(  name );
    setter := SETTER_FILTER( getter );
    tester := TESTER_FILTER( getter );

    # add getter, setter and tester to the list of operations
    ADD_LIST( OPERATIONS, getter );
    ADD_LIST( OPERATIONS, [ [ flags ] ] );
    ADD_LIST( OPERATIONS, setter );
    ADD_LIST( OPERATIONS, [ [ flags, FLAGS_FILTER( IS_BOOL ) ] ] );
    ADD_LIST( OPERATIONS, tester );
    ADD_LIST( OPERATIONS, [ [ flags ] ] );

    # store the property getters
    ADD_LIST( NUMBERS_PROPERTY_GETTERS, FLAG1_FILTER( getter ) );

    # install the default functions
    FILTERS[ FLAG1_FILTER( getter ) ] := getter;
    IMM_FLAGS:= AND_FLAGS( IMM_FLAGS, FLAGS_FILTER( getter ) );
    FILTERS[ FLAG2_FILTER( getter ) ] := tester;
    INFO_FILTERS[ FLAG1_FILTER( getter ) ] := 9;
    INFO_FILTERS[ FLAG2_FILTER( getter ) ] := 10;

    # the <tester> and  <getter> are newly  made, therefore the cache cannot
    # contain a flag list involving <tester> or <getter>
    InstallHiddenTrueMethod( tester, getter );
    InstallHiddenTrueMethod( filter, tester );
    # CLEAR_HIDDEN_IMP_CACHE();

    # run the attribute functions
    RUN_ATTR_FUNCS( filter, getter, setter, tester, false );

    # store the rank
    if LEN_LIST( arg ) = 3 and IS_INT( arg[3] ) then
        RANK_FILTERS[ FLAG1_FILTER( getter ) ]:= arg[3];
    else
        RANK_FILTERS[ FLAG1_FILTER( getter ) ]:= 1;
    fi;
    RANK_FILTERS[ FLAG2_FILTER( tester ) ]:= 1;

    # and return the getter
    return getter;
end );


#############################################################################
##
#F  DeclareProperty( <name>, <filter> [,<rank>] ) . . . . . . .  new property
##
BIND_GLOBAL( "DeclareProperty", function ( arg )

    local prop, name, nname, gvar, pos, filter;

    name:= arg[1];

    if ISB_GVAR( name ) then

      gvar:= VALUE_GLOBAL( name );

      # Check that the variable is in fact an operation.
      if not IS_OPERATION( gvar ) then
        Error( "variable `", name, "' is not bound to an operation" );
      fi;

      # The property has already been declared.
      # If it was not created as a property
      # then ask for re-declaration as an ordinary operation.
      # (Note that the values computed for objects matching the new
      # requirements cannot be stored.)
      if FLAG1_FILTER( gvar ) = 0 or FLAG2_FILTER( gvar ) = 0 then

        # `gvar' is not a property (tester).
        Error( "operation `", name, "' was not created as a property,",
               " use`DeclareOperation'" );

      fi;

      # Add the new requirements.
      filter:= arg[2];
      if not IS_OPERATION( filter ) then
        Error( "<filter> must be an operation" );
      fi;

      pos:= POS_LIST_DEFAULT( OPERATIONS, gvar, 0 );
      ADD_LIST( OPERATIONS[ pos+1 ], FLAGS_FILTER( filter ) );

    else

      # The property is new.
      prop:= CALL_FUNC_LIST( NewProperty, arg );
      BIND_GLOBAL( name, prop );
      nname:= "Set"; APPEND_LIST_INTR( nname, name );
      BIND_GLOBAL( nname, SETTER_FILTER( prop ) );
      nname:= "Has"; APPEND_LIST_INTR( nname, name );
      BIND_GLOBAL( nname, TESTER_FILTER( prop ) );

    fi;
end );


#############################################################################
##
#F  KeyDependentFOA( <name>, <dom-req>, <key-req>, <key-test> )
##
##  There are several functions that require as first argument a domain,
##  e.g., a  group, and as second argument something much simpler,
##  e.g., a prime.
##  `SylowSubgroup' is an example.
##  Since its value depends on two arguments, it cannot be an attribute,
##  yet one would like to store the Sylow subgroups once they have been
##  computed.
##  The idea is to store them in a list, which is then regarded as an
##  attribute of the group, called `ComputedSylowSubgroups'.
##  The name implies that the value of this attribute may change in the
##  course of a {\GAP} session, whenever a newly-computed Sylow subgroup is
##  put into the list.
##  Therefore, this is a *mutable attribute*
##  (see~"prg:Creating Attributes and Properties" in ``Programming in GAP'').
##  
##  The list contains primes in its odd positions and the corresponding Sylow
##  subgroups in its even positions.
##  More precisely, if `<p> = ComputedSylowSubgroups( <G> )[ <even> - 1 ]'
##  then `ComputedSylowSubgroups( <G> )[ <even> ]' holds the value
##  of `SylowSubgroup( <G>, <p> )'.
##  The pairs are sorted in increasing order of <p>,
##  in particular at most one Sylow <p> subgroup of <G> is stored for each
##  prime <p>.
##  This attribute value is maintained by the function `SylowSubgroup',
##  which calls the operation `SylowSubgroupOp( <G>, <p> )' to do the real
##  work, if the prime <p> cannot be found in the list.
##  
##  The same mechanism works for other functions as well, e.g., for `PCore',
##  but also for `HallSubgroup',
##  where the second argument is not a prime but a set of primes.
##  
##  `KeyDependentFOA' declares function, operation, and attribute
##  as described above, with names <name>, `<name>Op', and `Computed<name>s'.
##  <dom-req> and <key-req> specify the required filters for the first and
##  second argument of the operation `<name>Op',
##  which are needed to create this operation with `NewOperation'
##  (see~"prg:NewOperation").
##  <dom-req> is also the required filter for the corresponding attribute
##  `Computed<name>s'.
##  The fourth argument <key-test> is in general a function to which the
##  second argument <info> of `<name>(  <D>, <info> )' will be passed.
##  This function can perform tests on <info>,
##  and raise an error if appropriate.
##  
##  For example, to set up the three objects `SylowSubgroup',
##  `SylowSubgroupOp', and `ComputedSylowSubgroups' together,
##  the declaration file ``lib/grp.gd'' contains the following line of code.
##  \begintt
##  KeyDependentFOA( "SylowSubgroup", IsGroup, IsPosInt, "prime" );
##  \endtt
##  In this example, <key-test> has the value `"prime"',
##  which is silently replaced by a function that tests whether its argument
##  is a prime integer.
##  
##  \beginexample
##  gap> s4 := Group((1,2,3,4),(1,2));;
##  gap> SylowSubgroup( s4, 5 );;  ComputedSylowSubgroups( s4 );
##  [ 5, Group(()) ]
##  gap> SylowSubgroup( s4, 2 );;  ComputedSylowSubgroups( s4 );
##  [ 2, Group([ (3,4), (1,2), (1,3)(2,4) ]), 5, Group(()) ]
##  gap> SylowSubgroup( s4, 6 );                                
##  Error SylowSubgroup: <p> must be a prime at
##  Error( name, ": <p> must be a prime" );
##  keytest( key ); called from
##  <function>( <arguments> ) called from read-eval-loop
##  Entering break read-eval-print loop, you can 'quit;' to quit to outer \
##  loop,
##  or you can return to continue
##  brk> quit;
##  \endexample
##  
##  Thus the prime test need not be repeated in the methods for the operation
##  `SylowSubgroupOp' (which are installed to do the real work).
##  Note that no methods can/need be installed for `SylowSubgroup' and
##  `ComputedSylowSubgroups'.
##  
IsPrimeInt := "2b defined";

BIND_GLOBAL( "KeyDependentFOA", function( name, domreq, keyreq, keytest )
    local str, nname, oper, attr, func;
    
    if keytest = "prime"  then
      keytest := function( key )
          if not IsPrimeInt( key ) then
            Error( name, ": <p> must be a prime" );
          fi;
      end;
    fi;

    # Create the two-argument operation.
    str:= SHALLOW_COPY_OBJ( name );
    APPEND_LIST_INTR( str, "Op" );

    DeclareOperation( str, [ domreq, keyreq ] );
    oper:= VALUE_GLOBAL( str );

    # Create the mutable attribute and install its default method.
    str:= "Computed";
    APPEND_LIST_INTR( str, name );
    APPEND_LIST_INTR( str, "s" );
    DeclareAttribute( str, domreq, "mutable" );
    attr:= VALUE_GLOBAL( str );

    InstallMethod( attr, "default method", true, [ domreq ], 0, D -> [] );

    # Create the wrapper function that mainly calls the operation.
    func:= function( D, key )
        local known, i, erg;
        
        keytest( key );
        known:= attr( D );
        i:= 1;
        while i < LEN_LIST( known ) and known[i] < key do
          i:= i + 2;
        od;

	# Start storing only after the result has been computed.
        # This avoids errors if a calculation had been interrupted.

        if LEN_LIST( known ) < i or known[i] <> key then
	  erg := oper( D, key );
          known{ [ i + 2 .. LEN_LIST( known ) + 2 ] }:=
            known{ [ i .. LEN_LIST( known ) ] };
          known[  i  ]:= key;
          known[ i+1 ]:= erg;
        fi;
        return known[ i+1 ];
    end;
    BIND_GLOBAL( name, func );
end );


#############################################################################
##

#F  InstallAtExit( <func> ) . . . . . . . . . . function to call when exiting
##
BIND_GLOBAL( "InstallAtExit", function( func )

    if not IS_FUNCTION(func)  then
        Error( "<func> must be a function" );
    fi;
    if CHECK_INSTALL_METHOD  then
        if not NARG_FUNC(func) in [ -1, 0 ]  then
            Error( "<func> must accept zero arguments" );
        fi;
    fi;
    ADD_LIST( AT_EXIT_FUNCS, func );

end );


#############################################################################
##
#O  ViewObj( <obj> )  . . . . . . . . . . . . . . . . . . . .  view an object
##
##  `ViewObj' prints information about the object <obj>.
##  This information is thought to be short and human readable,
##  in particular *not* necessarily detailed enough for defining <obj>,
##  an in general *not* {\GAP} readable.
##
##  More detailed information can be obtained by `PrintObj',
##  and {\GAP} readable data can be produced with `SaveObj'.
##
##DeclareOperation( "ViewObj", [ IS_OBJECT ] );

##ViewObj := VIEW_OBJ;

DeclareOperationKernel( "ViewObj", [ IS_OBJECT ], VIEW_OBJ );


#############################################################################
##
#M  ViewObj( <obj> )  . . . . . . . . . . . . default methods uses `PrintObj'
##
InstallMethod( ViewObj,
    "default method using `PrintObj'",
    true,
    [ IS_OBJECT ],
    0,
    PRINT_OBJ );


#############################################################################
##
#F  View( <obj1>, ... ) . . . . . . . . . . . . . . . . . . . .  view objects
##
BIND_GLOBAL( "View", function( arg )
    local   obj;

    for obj  in arg  do
        ViewObj(obj);
    od;
end );


#############################################################################
##
#F  ViewLength( <len> )
##
##  `View' will usually display objects in short form if they would need
##  more than <len> lines.
##  The default is 3.
##
VIEWLEN := 3;

BIND_GLOBAL( "ViewLength", function(arg)
  if LEN_LIST( arg ) = 0 then
    return VIEWLEN;
  else
    VIEWLEN:= arg[1];
  fi;
end );


#############################################################################
##
#O  TeXObj( <obj> ) . . . . . . . . . . . . . . . . . . . . . . TeX an object
##
DeclareOperation( "TeXObj", [ IS_OBJECT ] );


#############################################################################
##
#F  TeX( <obj1>, ... )  . . . . . . . . . . . . . . . . . . . . . TeX objects
##
BIND_GLOBAL( "TeX", function( arg )
    local   str,  res,  obj;

    str := "";
    for obj  in arg  do
        res := TeXObj(obj);
        APPEND_LIST_INTR( str, res );
        APPEND_LIST_INTR( str, "%\n" );
    od;
    CONV_STRING(str);
    return str;
end );


#############################################################################
##
#O  LaTeXObj( <obj> ) . . . . . . . . . . . . . . . . . . . . LaTeX an object
##
DeclareOperation( "LaTeXObj", [ IS_OBJECT ] );


#############################################################################
##
#F  LaTeX( <obj1>, ... )  . . . . . . . . . . . . . . . . . . . LaTeX objects
##
BIND_GLOBAL( "LaTeX", function( arg )
    local   str,  res,  obj;

    str := "";
    for obj  in arg  do
        res := LaTeXObj(obj);
        APPEND_LIST_INTR( str, res );
        APPEND_LIST_INTR( str, "%\n" );
    od;
    CONV_STRING(str);
    return str;
end );


#############################################################################
##
#F  TraceMethods( <oprs> )
##
##  After the call of `TraceMethods' with a list <oprs> of operations,
##  whenever a method of one of the operations in <oprs> is called the
##  information string used in the installation of the method is printed.
##
BIND_GLOBAL( "TraceMethods", function( arg )
    local   fun;

    if IS_LIST(arg[1])  then
        arg := arg[1];
    fi;
    for fun  in arg  do
        TRACE_METHODS(fun);
    od;

end );


#############################################################################
##
#F  UntraceMethods( <oprs>)
##
##  turns the tracing off for all operations in <oprs>.
##
BIND_GLOBAL( "UntraceMethods", function( arg )
    local   fun;

    if IS_LIST(arg[1])  then
        arg := arg[1];
    fi;
    for fun  in arg  do
        UNTRACE_METHODS(fun);
    od;

end );


#############################################################################
##
#F  DeclareGlobalFunction( <name>, <info> ) . .  create a new global function
#F  InstallGlobalFunction( <oper>, <func> ) . . . . install a global function
##
##  Global functions of the {\GAP} library must be distinguished from other
##  global variables (see `variable.g') because of the completion mechanism.
##
BIND_GLOBAL( "DeclareGlobalFunction", function( arg )
    local   name;

    name := arg[1];
    BIND_GLOBAL( name, NEW_OPERATION_ARGS( name ) );
end );

BIND_GLOBAL( "InstallGlobalFunction", function( arg )
    local   oper,  info,  func;

    if LEN_LIST(arg) = 3  then
        oper := arg[1];
        info := arg[2];
        func := arg[3];
    else
        oper := arg[1];
        func := arg[2];
    fi;
    INSTALL_METHOD_ARGS( oper, func );
end );


#############################################################################
##
#F  RedispatchOnCondition(<oper>,<fampred>,<reqs>,<cond>,<val>)
##
##  This function installs a method for operation <oper> under the
##  conditions <fampred> and <reqs> which has (absolute) value <val>.
##  If not all the filters in <cond> are already known,
##  they are explicitly tested and if they are fulfilled the operation is
##  dispatched again. Otherwise the method exits with `TryNextMethod'. This
##  can be used to enforce tests like `IsFinite' in situations when all
##  existing methods require this property.
##  <cond> may have unbound entries in which case the corresponding argument
##  is ignored.
##
CallFuncList:="2b defined";
BIND_GLOBAL("RedispatchOnCondition",function(oper,fampred,reqs,cond,val)
local re,i;
  # force value 0 (unless offset).
  for i in reqs do
    val:=val-SIZE_FLAGS(WITH_HIDDEN_IMPS_FLAGS(FLAGS_FILTER(i)));
  od;
  InstallOtherMethod(oper,"fallback method to test conditions",
                     fampred,reqs,val,
  function(arg)
    re:=false;
    for i in [1..LEN_LIST(reqs)] do
      re:=re or (IsBound(cond[i]) and (not Tester(cond[i])(arg[i]))
        and cond[i](arg[i])); # force test
    od;
    if re then
      # at least one property was found out, redispatch
      return CallFuncList(oper,arg);
    else
      TryNextMethod(); # all filters hold already, go away
    fi;
  end);

end);


#############################################################################
##
#E
##

