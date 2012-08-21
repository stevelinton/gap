#############################################################################
##
#W  Makefile                    GAP autodoc                  Alexander Hulpke
##
#H  @(#)$Id$
##
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##

BUILD = ../../etc/buildman.pe

default: ._all

all:
	rm ._*
	make ._all

test: 
	$(BUILD) -f config.testall

._all: ../ref/manual.dvi
	touch ._all

../ref/manual.dvi: ._coll ._basic ._groups ._grppc ._rings ._number \
	._mapping ._oper ._ratfun ._grplib ._alg ._linalg ._fp \
	._install ._environ ._options
	(cd ../ref;tex manual)
	fgrep "undefined" ../ref/manual.log

._coll: config.coll coll.msk lists.msk string.msk record.msk domain.msk\
	combinat.msk boolean.msk
	$(BUILD) -f config.coll
	touch ._coll

._basic: config.basic addmagma.msk magma.msk monoid.msk semigrp.msk
	$(BUILD) -f  config.basic
	touch ._basic

._groups: config.groups groups.msk grpprod.msk grpmat.msk
	$(BUILD) -f config.groups
	touch ._groups

._grppc: config.grppc grppc.msk pcgs.msk
	$(BUILD) -f config.grppc
	touch ._grppc

._fp: config.fp wordass.msk grpfp.msk pres.msk
	$(BUILD) -f config.fp
	touch ._fp

._rings: config.rings rings.msk module.msk fields.msk fieldfin.msk \
	fldabnum.msk vspc.msk
	$(BUILD) -f config.rings
	touch ._rings

._linalg: config.linalg vspc.msk vector.msk matrix.msk matint.msk
	$(BUILD) -f config.linalg
	touch ._linalg

._number: config.number integers.msk numtheor.msk rational.msk cyclotom.msk \
	padics.msk
	$(BUILD) -f config.number
	touch ._number

._mapping: config.mapping mapping.msk grphomom.msk
	$(BUILD) -f config.mapping
	touch ._mapping

._oper: config.oper grpoper.msk grpperm.msk permutat.msk
	$(BUILD) -f config.oper
	touch ._oper

._options: config.options options.msk
	$(BUILD) -f config.options
	touch ._options

._ratfun: config.ratfun ratfun.msk algfld.msk
	$(BUILD) -f config.ratfun
	touch ._ratfun

._grplib: config.grplib grplib.msk
	$(BUILD) -f config.grplib
	touch ._grplib

._alg: config.alg algebra.msk alglie.msk
	$(BUILD) -f config.alg
	touch ._alg

._environ: config.environ debug.msk objects.msk types.msk
	$(BUILD) -f config.environ
	touch ._environ

._install: config.install install.msk run.msk sharepkg.msk
	$(BUILD) -f config.install
	touch ._install

