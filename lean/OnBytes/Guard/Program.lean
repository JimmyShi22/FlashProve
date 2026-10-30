-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Guard/Program.lean: the root's main is one call of the function "programFront", and the
guards on the compiled code of verify-on-bytes; this repository builds no stand-alone program
from it.

This file is never linked into a program, and nothing imports it. It stops compiling, and with it
the default build, if, in what this file imports,
 * main is not one call of OnBytes.Shell.programFront, or a function of "judges" is not below main;
 * a compiler rule on record is no theorem or rests on another axiom than the three standard ones;
 * something below main has compiled code that is not made from its definition and is on no list, or
   a listed name is not below main;
 * a constant of this library has the name of a compiler's helper constant and is not one, or any
   constant has a name like a declaration that Lean's compiler makes;
 * Lean's map from names to modules gives a constant of this library to another module;
 * a module of this library has an entry in Lean's tables of initialisers, of export names, or of
   the marks implemented_by and extern;
 * something below main mentions a file mode other than "read";
 * compiled code below main calls back into its own recursion otherwise than by a last call to
   itself, and the constant behind it is on no list;
 * a module below the program's root has Lean, Lake or a package's name as the first part of its
   name;
 * a constant of this library in a module below the root is an axiom, opaque, unsafe or partial, and
   does not bear the name of one of Lean's helper constants.
The guards catch a slip and the plain written forms. They do not stop someone who runs code at
compile time in a file below the root. That main is "program", of which the theorems on the program
are stated, is not held here: OnBytes/Shell/AtMain.lean, main_eq.

A build of OnBytes/Main.lean alone compiles neither this file nor any file of
theorems that it does not import. Lean elaborates these lines after that text's modules,
so a notation or a name declared there is in force here (reasoned, not tried). What would show a
change is this file's output: "the cone of [main]" and the two equal counts of command 5. A person
has to read these; no program does.

What each command checks, the equation main_eq, code that runs before main, and the limits:
OnBytes/Guard/README.md. Csimp.lean, Cone.lean and Test.lean have their own limits in their heads.
-/
import OnBytes.Guard.Core
import OnBytes.Main

set_option autoImplicit false

namespace OnBytes.Guard

/-- The executable's main is "programFront": an equation between terms, which says nothing of
compiled code (OnBytes/Guard/README.md, "The equation main_eq"). That "programFront" is "program",
of which the theorems on the program are stated, is no unfolding: it is the theorem programFront_eq
(OnBytes/Shell/FrontSame.lean). -/
theorem main_eq : _root_.main = OnBytes.Shell.programFront := rfl

end OnBytes.Guard

-- the three standard axioms are printed because proofs inside the program's definitions use them
#print axioms OnBytes.Guard.main_eq
#guard_csimp [] 0  -- command 1
#guard_cone [``main] []  -- command 2
#guard_pinned [``main] []  -- command 3
#guard_compiled [``main] []  -- command 4
#guard_core [``main] OnBytes.Guard.coreOfProgram  -- command 5
#guard_has [``main] OnBytes.Guard.judges  -- command 6
#guard_entry ``main ``OnBytes.Shell.programFront  -- command 7
#guard_twins "_unsafe_rec" "partial" 1  -- command 8
#guard_tables [``Lean.regularInitAttr, ``Lean.builtinInitAttr, ``Lean.exportAttr,  -- command 9
  ``Lean.Compiler.implementedByAttr, ``Lean.externAttr] []
#guard_ctors [``main] ``IO.FS.Mode [``IO.FS.Mode.read]  -- command 10
#guard_parts ["_boxed", "_closed_", "_lam_", "_elam", "_at_", "_redArg"]  -- command 11
#guard_homes []  -- command 12
#guard_rings [``main] OnBytes.Guard.ringsOfProgram  -- command 13
#guard_imports `OnBytes.Main OnBytes.Guard.barredOfProgram  -- command 14
#guard_plain `OnBytes.Main "_unsafe_rec" []  -- command 15
