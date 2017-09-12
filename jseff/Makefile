include ./Makefile.conf
-include ./Makefile.local

all: toplevel.js

OCPINDENT=$(shell ocamlfind query ocp-indent -format "-package %p.lib" 2> /dev/null)
HIGLO=$(shell ocamlfind query higlo.ocaml -format "-package %p -rectypes" 2> /dev/null)

OPTCOMP_OPT=
ifneq ($(OCPINDENT),)
OPTCOMP_OPT+= -let ocpindent=true
endif

ifneq ($(HIGLO),)
OPTCOMP_OPT+= -let higlo=true
endif

ifneq ($(NO_SYNTAXES),1)
#SYNTAXES=js_of_ocaml.syntax
#	lwt.syntax \
#	js_of_ocaml.deriving.syntax deriving.syntax.std
endif

JSFILES= +weak.js +toplevel.js +nat.js

PACKAGES= \
	lwt tyxml.functor \
	js_of_ocaml \
	js_of_ocaml.deriving \
	js_of_ocaml.tyxml \
	js_of_ocaml.toplevel

#-jsopt "--pretty --disable shortvar"
MKTOP=jsoo_mktop -verbose $(SAFESTRING) \
	${addprefix -top-syntax , ${SYNTAXES}} \
	-dont-export-unit gc \
	${addprefix -export-package , ${PACKAGES}} \
	${addprefix -export-unit , html_types html_sigs xml_wrap } \

TOPLEVEL_NAME=toplevel
TOPLEVEL_OBJS=toplevel.cmo
$(TOPLEVEL_NAME).js: $(TOPLEVEL_OBJS)
	$(MKTOP) \
	$(BER) \
	$(OCPINDENT) $(HIGLO) \
	effApi.cmo \
	$(TOPLEVEL_OBJS) \
	${addprefix -jsopt , ${JSFILES}} \
	${addprefix -jsopt , -I ./ --file examples.eff} \
	${addprefix -jsopt , -I ./ --file pervasives.eff} \
	-package base64 \
	-o $(TOPLEVEL_NAME).byte \

effApi.cmo:
	cd .. && ocamlbuild -no-hygiene effApi.cmo
	/bin/cp ../_build/effApi.cm[io] .

%.cmis.js:
	jsoo_mkcmis $*

%.cmo:%.ml effApi.cmo
	ocamlfind ocamlc -c -syntax camlp4o $(SAFESTRING) \
		-package optcomp,js_of_ocaml.syntax,lwt,js_of_ocaml.tyxml,js_of_ocaml.toplevel \
		-package base64 \
		$(OCPINDENT) $(HIGLO) \
		${addprefix -ppopt , ${OPTCOMP_OPT}} \
		effApi.cmo \
		$< -c $@
clean::
	rm -f *.cm[io] *.byte *.native *.js
