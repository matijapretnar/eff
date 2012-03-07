AC_INIT(eff,3.0)
AC_CONFIG_AUX_DIR([build-aux])
AC_CONFIG_MACRO_DIR([build-aux])
AM_MAINTAINER_MODE
AM_INIT_AUTOMAKE([foreign no-dependencies])

AC_PROG_OCAML

if test "$OCAMLBUILD" = "no"; then
  AC_MSG_ERROR([You must install OCaml with ocamlbuild utility])
fi

AC_CHECK_TOOL([OCAMLMENHIR],[menhir],[no])
if test "$OCAMLMENHIR" = "no"; then
  AC_MSG_ERROR([You must install the Ocaml menhir parser generator])
fi

AC_CHECK_TOOLS([WRAPPER],[rlwrap ledit],[no])

AC_SUBST([WRAPPER])

if test "$WRAPPER" = "no"; then
   AC_MSG_WARN([No line-editing wrapper found])
fi

if test "$OCAMLBEST" = "opt"; then
  BUILDBEST=native
else
  BUILDBEST=byte
fi

echo "let version = \"$PACKAGE_VERSION\";;" > src/version.ml

AC_SUBST([BUILDBEST])

AC_CONFIG_FILES([Makefile])
AC_OUTPUT