# The guards on the compiled code of verify-on-bytes

Terms: [TERMS.md](../../TERMS.md).

OnBytes/Guard/Program.lean calls fifteen guard commands when the library is built. This page says
what each checks, why, what to do when it rejects, and what it does not reach.

The guards are about `verify-on-bytes`, the Lean text below `OnBytes.Main`: a hand translation of
`cp_verify` into Lean, from which this repository builds no stand-alone program; one test
(`tools/accepts/`) compiles it and has Lean load the compiled code while it evaluates files of
`lean/Ask/`. It is not `verify`, the Lean verifier that is proved sound in the random-oracle model,
at exact match ([lean/THEOREM.md](../../THEOREM.md)). Below, "the program" is a stand-alone program
built from that text; this repository builds none, and the runs told here were made with builds of
copies of the sources that differ from this repository's. No soundness theorem reaches a call that
checks a real proof, and no theorem bounds the chance that the program accepts a false file. The
program follows `cp_verify`'s source text, so the two programs are not independent
([OnBytes/LIMITS.md](../LIMITS.md), point 3).

## In short

A theorem is about definitions; a program runs compiled code. Lean lets the two differ where a
constant carries a mark: a rule for the compiler (csimp), implemented_by, extern, opaque, unsafe or
partial. The commands look for such marks and for some other ways in which the compiled program
could part from the definitions that the theorems are about. If a command rejects something,
Program.lean does not compile and the default build fails.

"Below main", or main's cone, is every constant that main's definition reaches through the kernel's
terms (Cone.lean). "Reached from main" is said of compiled code: every compiled declaration that
calls and closures reach from main's own. "Below the root" is the module OnBytes.Main and all that
it imports, directly or through others.

### What a green build does not tell

These limits hold of all the commands. Each command's own limits stand below; commands 1 and 2 and
the tests have more in the heads of Csimp.lean, Cone.lean and Test.lean.

- The commands do not compare compiled code with a definition. They read marks and rules that Lean
  has on record, and compare the names that the compiler's output calls with the names in the
  kernel's terms.
- They catch a slip and the plain written forms. They do not stop someone who runs code at compile
  time in a file below the root. scripts/check.py searches the text of these files for the plain
  forms of such code (scripts/RULES.txt, "The program's source"; what the search misses: "What the
  rule on the program's source does not catch"). It lets one line through, a notation that is local
  to Run/Blake2b/LoadThm.lean, which three theorems of that file use, in their statements or in
  their proofs. check.py holds the sha256 of that file. That the notation stands in no definition is
  by a search of that file's text; no program of the library checks this.
- Not all written forms are caught: see command 9 on a definition without parameters, and commands 1
  to 4 on a rule marked local.
- Nothing here covers Lean's compiler, runtime and C compiler, the linker, the C code behind the
  marks in Lean's core, or whether the program that is run was built from these sources.
- No command looks for the attribute cpass (a compiler pass) or for a constant folder.
- A constant counts as this library's unless the first part of its module's name is one of thirteen
  that are Lean's or a package's (Basic.lean). So the guards rely on command 12, and on
  lakefile.toml.
- The cases that commands 8, 9, 11, 12 and 14 are there to shut are read off the source of Lean
  4.29.1, not tried.

## The guard file: Program.lean

Program.lean is never linked into a program, and nothing imports it. It states main_eq and then
calls the commands on the main of verify-on-bytes, after everything that the program imports.

### The equation main_eq

A stand-alone program built from that text starts at the root's main (OnBytes/Main.lean). main_eq
(OnBytes.Guard.main_eq) says that main is OnBytes.Shell.programFront (OnBytes/Shell/Front.lean), by
unfolding: with it, a theorem about "programFront" becomes one about main by one rewriting, which
the reader does. A list of theorems by name cannot tell which program's main is meant, so the
equation is checked by compiling Program.lean. The theorems on the program are stated of "program"
(OnBytes/Shell/Checks.lean), which main does not call. They reach main by a second equation,
programFront_eq (OnBytes/Shell/FrontSame.lean), which is no unfolding: it rests on four theorems of
OnBytes/ChecksWithHashAsArgument/M/AtPort/Spine.lean, at formatHashFastForm (the first at
secondHashFunctionTree too) and at no other function; the fourth is stated as a relation that
unfolds to an equation. OnBytes/Shell/AtMain.lean joins the two into main = program
(OnBytes.Shell.main_eq; OnBytes/LIMITS.md, point 24).

main_eq is an equation between terms. It also holds for a main that carries an attribute which puts
other code in its place (implemented_by, extern); that goes through a Lean function which is the
identity for the kernel and acts when compiled (dbgTrace and the like); or whose file, or a module
below it, declares more than main. The commands cover these cases as far as they go. That main_eq
has no proof by rfl over a main that does not unfold to "programFront" is reasoned, not tried.

### Code that runs before main

The attribute init (and "initialize", which is the same attribute) has two forms. "@[init] def a :
IO Unit" runs before main whether or not anything below main mentions it. "@[init f] def c : T := v"
sets c at start-up from f, and c can be below main: the theorems see v, the program sees what f
returned. Command 2 rejects such a c only if it is opaque. Of commands 1 to 7 only 7 looks for init,
on main. Command 9 looks for it in every module of this library that Program.lean imports; a third
way, which it does not see, stands under its limits. (Read off the source of Lean 4.29.1, not tried:
Lean/Compiler/InitAttr.lean:57-70; LCNF/ToDecl.lean:130-133; IR/ToIR.lean:182-187 with
IR/Basic.lean:386-388; IR/EmitC.lean:901-916.)

### Limits

- Whether such a program's entry calls the compiled "programFront", and only that, depends on the
  compiler and the linker. Command 4 reads the compiler's output, not what the C compiler or the
  linker produce.
- Lean elaborates the lines of Program.lean after the modules that the file imports. A notation that
  is not local, an instance or a name declared there is in force (reasoned, not tried: a notation
  could make one token of "[``main]" and point the commands at another constant).
- What would show that the commands looked at another constant than main, or below another module
  than the root, is only printed: the line "the cone of [main]", the two equal counts of command 5
  and, for commands 14 and 15, the root's name and their counts. No program reads these lines,
  command 1's count of rules or the guard file's own literals: the reader has to.
- The guards must have run. A build of the program alone compiles neither Program.lean nor any file
  of theorems that the program does not import. An explicit list of modules to build must name
  Program.lean.

## Commands 1 to 4: Csimp.lean, Cone.lean, Cmd.lean

1. `#guard_csimp` (Csimp.lean): every compiler rule on record is a theorem that depends only on the
   three standard axioms. The command can let listed rules of a package through unproved. A proved
   rule of this library is printed, not rejected; command 3 counts a constant below main that such a
   rule replaces as this library's.
2. `#guard_cone` (Cone.lean): prints every constant below main whose compiled code is not made from
   its definition, and rejects any that belongs to this library and is not on its list.
3. `#guard_pinned` (Cmd.lean): below main, except for Lean core's constants, every constant that a
   rule replaces, or that carries a mark, must be on the command's list, or be the function that the
   rule of a listed constant puts in its place.
4. `#guard_compiled` (Cmd.lean): visits the compiler's output reached from main, the declarations
   from which the C files are written. It rejects every declaration, unless it is Lean core's, that
   is made from a constant that carries a mark, or that a stand-in mark or a rule puts in another's
   place, or that has no body. It also rejects a function of this library or of a package that the
   compiled code can call although no kernel term below main mentions it, except for fragments that
   the compiler itself has made.

Program.lean passes each of the four the empty list. For command 3 that means that no constant of a
package may be there: the program imports no package. Command 3 follows the kernel's terms, command
4 what the program can call. A constant counts as Lean core's if it is declared there and no rule or
stand-in function of a package or of this library replaces it. The traversal enters no types and no
theorems, and an extern or partial constant of Lean's core or of a package is a leaf (Cone.lean).

**The tests on listed recursors.** Mathlib adds code and a compiler rule for some recursors of
Lean's core, and some of these rules are not theorems (Allow.lean); a program that imports Mathlib
has to list them. For each listed recursor command 3 tests: (a) it is a recursor declared in Lean's
core; (b) it has exactly one rule on record, the pair of the recursor and the rule's module is
listed in Allow.lean, and the rule's right side is declared in that module; (c) below main it is
mentioned only by functions that Lean itself treats as case splits (Lean.isCasesOnLike), List.rec
also by the functions in "namersByName"; (e) T.brecOn is mentioned only by constants that Lean's
structural-recursion elaborator has on record. There is no (d). A listed name that is not below main
is an error. While the guard file's list is empty, only the last part of (e), on who mentions
List.below, has something to test. None of these tests is itself tested. (Lean 4.29.1:
Lean/AuxRecursor.lean:59-64, Lean/Meta/CasesInfo.lean:13-31 and :57,
Lean/Compiler/LCNF/ToLCNF.lean:812.)

### Limits

- Commands 1, 2 and 3 read what Lean has on record after main's imports. Code that runs while a file
  below the root is compiled could change the state from which the compiler takes its rules and
  leave nothing on record; these three would see nothing. That is why command 4 compares the
  compiler's output with the kernel's cone.
- Command 4 does not see a stand-in function that is marked for inlining: it leaves no name in the
  compiled code. Commands 2 and 3 reject it if the mark is on record; if nothing is, none of the
  four sees it.
- Command 4 passes a function that is put in another's place, with nothing left on record, if it is
  also mentioned anywhere below main, even in dead code.
- Command 4 accepts, counts and prints compiler-made fragments ("pieces" in the code and the printed
  lines): closed terms (`f._closed_N`) and inner functions (`f._lam_N`). It knows them only by the
  form of their names. Equal fragments share the name of the function that was compiled first, which
  main need not use. What a fragment calls is checked; which function calls it, and that its code
  equals a fragment of a function below main, is not. So a call to a fragment that did not come from
  the compiler's two caches would pass, with any computation by Lean core's functions inside it; the
  fragments of an inlined stand-in function pass in this way. Whether a rule's right side can
  mention a fragment directly is not known.
- A boxed numeral (`f._boxed_const_N`), shared in the same way, is accepted only if its compiled
  body, read from the record from which Lean prints the C file, does nothing but take one numeral,
  box it and return it. An initialiser on record for the name would put something else in its place;
  command 9 rejects those. No guard ties a numeral in compiled code to the kernel's term. Where f is
  a stranger, that is, neither Lean core's nor below main, the command rejects every other body
  under such a name, and so the second shape that the compiler lifts there, a constant without
  arguments. There it also rejects a fourth kind of shared fragment, `f._elam_N`.
- Except for a stand-in function whose mark is on record, each of these needs code, in a file below
  the root, that runs while that file is compiled. These commands do not look for such code.
- Tests (c) and (e) read a tag and a record that are public in Lean, so code of this library could
  set them.
- Not covered: a rule marked local in an imported file, which is not on record afterwards
  (Csimp.lean's head); code that runs before main (commands 7, 9 and 15).
- What is said of fragments is read off the source of Lean 4.29.1
  (Lean/Compiler/LCNF/ExtractClosed.lean:124-128, LambdaLifting.lean:105-112 and :213-222,
  AuxDeclCache.lean:27-37, ExplicitBoxing.lean:137; Lean/Compiler/IR/CompilerM.lean:82-105,
  IR/EmitC.lean:879-882).

### When a command rejects a name

Read the printed names. A package's name may be added to the guard file's list by someone who has
looked at what it stands for, with the reason next to it. A name of this library may not.

## Commands 5 to 15: Core.lean

Core.lean imports no program, and no program imports it. Commands 8, 9, 11, 12, 14 and 15 read the
compiled environment, not source text, so what misleads a search of the text does not mislead them.

### Command 5

- **Checks.** `#guard_core roots list`: Lean core's constants below main whose compiled code is not
  made from their definition are exactly the names in the list "coreOfProgram", each once.
- **Why.** What such a constant does at run time is written in C or in another function, not in the
  term that the kernel sees. Some reach outside the program; a few debugging helpers are the
  identity function for the kernel, while their compiled code waits or prints.
- **The list** was generated by the command itself, run on an empty list. It is written out in
  Core.lean, where no program is imported: a list assembled in the guard file would be elaborated
  after the program's modules, where an instance of theirs could lengthen it (reasoned, not tried).
- **If it rejects a new name:** find out what the constant does at run time (Lean's source gives the
  C function for extern and the function for implemented_by). If the program is meant to do that,
  add the name in the same change. Remove a listed name that it reports as gone.
- **Limits.** The list says that the program may, for example, read a file, not which file or where
  in the program. It does not cover what the C code of a listed name does, a mark or a rule on a
  definition of this library (commands 2, 3 and 4), or what only the compiler's output reaches:
  command 4 visits that, without a closed list for Lean core's constants. (Lean 4.29.1, asked for a
  variant of main that calls "program" directly, showed two such constants,
  Array.getInternalBorrowed and Array.ugetBorrowed; it was not asked for this repository's main,
  which calls "programFront", and no command checks or prints this.) One listed name behaves like
  the debugging helpers: panicCore, which reads of arrays and strings use, is for the kernel the
  default value of its type and, compiled, prints a message (Init/Prelude.lean:3651-3664). So the
  list is free of debugging helpers only if that means the six functions under that title in
  Init/Util.lean. Names are compared by their printed form.

### Command 6

- **Checks.** `#guard_has roots names`: each function of the list "judges" is below main.
- **Limits.** A name anywhere in the cone passes: the command does not show that main calls the
  function on the way to its verdict, or uses its result. For example,
  OnBytes.Model.Verify.wholeCall, keyCall, leafCall and planBytes, which are not on the list (their
  namesakes in the namespace OnBytes.TwoPort.M.Model.Verify are), are below main, because checksAt
  (OnBytes/Shell/Front.lean) is written as modelChecks with four fields replaced; no call reaches a
  verdict through them (by a search of the text below the root). A name on command 5's list that
  only they use is not reported as gone. formatHashFastForm and secondHashFunctionTree are on the
  list "judges" and would be below main whatever checksAt is given: the command does not show which
  hash functions are laid into the checks.

### Command 7

- **Checks.** `#guard_entry main f`: the kernel's term of main is "fun args => f args", or f, and
  main has no entry in Lean's records for implemented_by, extern, export, init or csimp.
- **Why.** An equation "main = f" by rfl holds for every main that unfolds to f.
- **Limits.** Not covered: what f does; what else the root's file declares; what the compiler and
  the linker make of the call; a helper constant for main or for f (command 8).

### Command 8

- **Checks.** `#guard_twins part class floor`: every constant of this library whose name ends in
  "_unsafe_rec" is one of Lean's own helper constants ("twin" in the command's name, "companion" in
  the messages). That is: it is a definition of the kernel's safety class "partial"; the name before
  the last dot is a safe definition or a theorem; both are in the same module; both have the same
  type and universe parameters. The command fails if it finds fewer than the floor.
- **Why.** For a recursive definition that gets compiled code, and for a "partial def", Lean adds
  such a constant for its compiler. The code generator compiles a definition from it if it exists,
  and does not ask who made it (read, not tried). So a hand-written one would be compiled in place
  of the definition that the theorems are about, while main_eq and commands 2, 3, 5 and 7, which
  read a definition's own term, pass. Command 4 visits the code that was really compiled, but
  rejects there only what it rejects everywhere: functions of the cone with other arguments, and any
  function of Lean's core, pass.
- **If it rejects a name:** the constant was written by hand or made by a program. Remove it; there
  is no list of exceptions. It also rejects three harmless texts, in any module of this library that
  the guard file imports: a "partial def" (the error then shows a name that the author never wrote);
  a deriving handler that writes one; a recursive definition whose type contains a "let".
- **Limits.** A constant of that name with the class "partial" and a different body passes. Lean
  makes such a constant in one place, always with that class (by a search of the toolchain's Lean
  sources), and none of its declaration forms gives that class to a chosen name; code that calls
  addDecl at compile time can, whether it is this library's or a package's; below the root command
  14 bars the import that such a call needs (read, not tried). Not read: Lean's C++ sources; the
  packages' sources, and so their attributes and commands that declare a constant under a name that
  the author chooses. Not followed: a constant that existed while a file was compiled and did not
  reach the compiled file. Constants of Lean and of the packages are not checked. (Lean 4.29.1:
  Lean/Compiler/LCNF/ToDecl.lean:84-86 and :111; Lean/Elab/PreDefinition/Basic.lean:283-300.)

### Command 9

- **Checks.** `#guard_tables tables asOurs`: no module of this library that the guard file imports
  has an entry in five tables of Lean: the two of initialisers, that of export names, and those of
  the marks implemented_by and extern. It also rejects such a module with a "module" header, because
  the public part of such a file leaves entries out, and fails for a table in which the other
  modules have no entry.
- **Why.** Each use of init leaves an entry in one of the first two tables, and Lean's import finds
  a module's initialisers through these entries (read, not tried; nor is it tried that an init in a
  file of this library leaves an entry). The attribute export gives a definition a chosen name in
  the C code. Commands 2 to 4 do not count it as a mark, and command 7 looks for it on main alone;
  what such a name can do when the program is linked is not known. Commands 2 to 5 and 7 ask Lean
  for the two marks by a constant's name, through the map of command 12; this command goes by the
  module's own record, and so does not hang on that map.
- **If it rejects a module:** the module declares an initialiser, gives a definition an export name,
  or puts one of the two marks on a definition. Remove it. There is no list of exceptions, also not
  for a constant that the lists of commands 2 to 4 name.
- **Limits.** There is a third way in which code of this library runs before main, and command 9
  does not see it: a definition without parameters is computed when its module is loaded, whether or
  not anything calls it, and leaves no entry in either table (read, not tried). Outside main's cone
  no command checks its body. As far as this was followed, with safe code it can write to standard
  error, wait, or never return; a line on standard error can imitate the words of a verdict. With
  unsafe or extern it can do any input and output before main. This command rejects extern there;
  command 15 rejects an unsafe constant in the modules of this library below the root;
  scripts/check.py rejects unsafe in every file of the library, by its search of the text, but for
  listed lines, and by its audit of the compiled files (scripts/README.md, "audit"). The command
  counts entries and does not read them. It does not see the file in which it is called, or a table
  that it is not given. (Lean 4.29.1: Lean/Environment.lean:1784 and :1830-1841;
  Lean/Attributes.lean:263-277; Lean/Compiler/InitAttr.lean:178; Lean/Compiler/IR/EmitC.lean:901,
  :917-919, :941-942.)

### Command 10

- **Checks.** `#guard_ctors roots type allowed`: of the constructors of the given inductive type,
  taken from Lean's own record of the type, those below main are exactly the allowed ones. The guard
  file names IO.FS.Mode and allows only "read".
- **Why.** Command 5's list has IO.FS.Handle.mk, which opens a file, and opening in a writing mode
  creates or empties a file. With commands 2 to 5 this command is what "the program opens files only
  for reading" rests on.
- **If it rejects a constructor:** something below main mentions another mode. Find it and remove
  it.
- **Limits.** It shows that no other mode is mentioned below main, not where "read" is used or which
  file is opened. It follows the kernel's terms, with the limits of the traversal (Cone.lean) and of
  commands 1 to 3. It does not cover the program's output to standard output and standard error, or
  what the C code of a listed constant does.

### Command 11

- **Checks.** `#guard_parts starts`: no constant of the environment, Lean's own included, has a name
  with a part that begins with one of the given strings. The guard file gives the beginnings of the
  names that Lean's compiler makes for the declarations that it derives from a function's code:
  `f._closed_N`, `f._lam_N`, `f._elam_N`, `f._boxed_const_N`, `f._boxed`, `f._redArg` and
  `g._at_.f.spec_N` (Lean 4.29.1: Lean/Compiler/LCNF/Specialize.lean:317-320).
- **Why.** These are compiled declarations and no constants: the kernel never sees them. A constant
  written under such a name can meet the compiler's declaration, and the C file can then hold the
  written constant's value where the compiler's declaration was meant, while commands 1 to 10 pass
  (read, not tried).
- **If it rejects a name of this library:** give the constant another name. There is no list of
  exceptions. If another version of Lean has such a constant of its own, the command has to be
  reconsidered.
- **Limits.** It knows the beginnings that it is given; another version of Lean may name its
  declarations otherwise. Not followed: a constant that existed while a file was compiled and did
  not reach the compiled file.

### Command 12

- **Checks.** `#guard_homes asOurs`: Lean's map from names to modules gives every constant that a
  module of this library declares, by the module's own list in its compiled file, to that module.
- **Why.** Commands 1 to 5 and 8 decide by that map whether a constant is this library's
  (Basic.lean, originOf). The map also holds the names of the compiled declarations of every
  imported module, and the module that comes first keeps a name. The guard file imports all of Lean
  before the program. So a constant of this library under the whole name of a compiled declaration
  of Lean's would count as Lean's, and the other commands would step over it (read, not tried: Lean
  4.29.1, Lean/Environment.lean:1170-1172 and :2235-2238).
- **If it rejects a name:** look at who declares it. It also rejects a harmless case: a lemma that
  Lean makes on demand for a definition (f.eq_1, f.congr_simp) can be made in two modules, and the
  second one is not at home. Make the lemma where the definition is, or let one of the two modules
  import the other.
- **Limits.** It trusts the compiled files' own lists, and does not see the file in which it is
  called.

### Command 13

- **Checks.** `#guard_rings roots list`: the deep declarations among those reached from main are
  made from exactly the constants of two closed lists. A declaration is deep if it calls itself from
  a place that is not the last, or calls another declaration of its ring of recursion from any
  place. "ringsBounded" holds the constants whose depth, at the callers that the source has, is
  bounded or is a logarithm; "ringsOpen" holds seven more: six for which no bound is known at every
  caller, and Fmt.Dr.times. The two tables at the end of this page have a row for each name.
- **Why.** A recursion that goes on after the call needs stack for every level, so one that is as
  deep as a file is long ends the program with a stack overflow. That is no wrong verdict, but it is
  a way for a file to stop the verifier. Lean's compiler makes a loop only of a last call of a
  declaration to itself (read off the source of Lean 4.29.1: Lean/Compiler/IR/EmitUtil.lean:18-21,
  IR/EmitC.lean:797-804); what becomes of a last call to another declaration is the C compiler's
  choice.
- **If it rejects a new name:** find out over what the recursion runs. If a constant of the format
  or a test on a public number bounds its depth, add the name to the first list. If it is as deep as
  a file says, write the function as a loop, or add it to the second list and say so where the
  program's limits are told (OnBytes/LIMITS.md, point 18). Remove a listed name that it reports as
  gone.
- **Limits.** The command is a floor, not a proof that the program ends or that its stack suffices.
  It does not know over what a recursion runs: the bounds behind the first list were read off the
  code and are checked by nothing. A name on a list lets every caller through, and every change of
  that function's text: a new call of List.zip, whose compiled code is of this kind, is not seen. A
  call through a closure that is held in a variable makes no arrow, so a ring that closes through
  one is not found. A declaration without a body on record (C code) is a leaf.
- **The loops of the texts over a monad.** The checks on a model's files run the loops of
  OnBytes/ChecksWithHashAsArgument/M/Chain/EngineM.lean (levelLoopM, walkM, leavesLoopM,
  storedLoopM, opensLoopM, foldRoundsM) and their like. In the source each calls itself behind a
  bind, not in the last place: it is a loop in the compiled code only if the compiler specialises
  the function at the identity monad and unfolds the bind. None of the six is on either list, so
  where Program.lean compiles the command has found none of them deep; it counts the loops and does
  not name them, so that these six are among those counted is concluded, not seen. If it comes to
  reject them, they need a bound read off the code before they go on the first list: the depth of
  foldRoundsM would be the number of rounds of a chain, which is as long as the chain's description
  and runs to tens of thousands at the full size.

### Command 14

- **Checks.** `#guard_imports root barred`: neither the root module nor any module that it imports,
  directly or through others, has a name whose first part is barred. The guard file names
  OnBytes.Main and bars Lean, Lake and the nine packages ("barredOfProgram").
- **Why.** The other guards do not look for code that runs at compile time in a file below the root.
  Four forms of such code, as Lean's own commands write them, need the library in which Lean's
  elaborator and compiler are written, whose modules' names begin with Lean: an elaborator, run_cmd,
  a compiler pass, a call that adds a declaration.
- **If it rejects a module:** the error shows which module below the root imports it. Remove that
  import. A file of theorems or guards that needs Lean's library belongs outside the files below the
  root.
- **Limits.** Other code at compile time needs no such import and stays possible: macros, syntax and
  notations; #eval, which can do any input and output while the file is compiled and leaves no
  constant; initialize, whose traces commands 9 and 15 reject. scripts/check.py searches the text
  for these. That the four forms need the import is read, not tried. Not followed: a file that
  declares, under Lean's own names, the types by which Lean knows an elaborator or a compiler pass.
  The command trusts the compiled files' own import lists. It says nothing of the modules under Init
  and Std, which the program does import. That OnBytes.Main is the module from which such a program
  is built is the guard file's literal; no command checks it.

### Command 15

- **Checks.** `#guard_plain root part asOurs`: in the modules of this library below the root, by
  each module's own list in its compiled file, no constant is an axiom, opaque or unsafe, and none
  is of the class partial, except those with the last name part of Lean's helper constants, which
  command 8 judges.
- **Why.** Commands 2 and 3 look for such constants below main only, and a definition without
  parameters is computed whether or not main reaches it (command 9, limits).
- **If it rejects a constant:** write it as a plain definition, or, if it is an axiom, state it as a
  theorem and prove it. A function written with the keyword partial, and a constant set by
  initialize, are shown as opaque. Moving the constant out of the files below the root satisfies
  this command, but scripts/check.py rejects these kinds in every file of the library.
- **Limits.** It looks at the modules below the root, not at everything that the guard file imports.
  It reads a constant's kind on record, not its body: a plain definition outside main's cone can
  call a constant of Lean's core that is opaque or extern, or whose compiled code is another
  function (implemented_by), which may be unsafe. It does not see the marks implemented_by and
  extern on a constant of this library (commands 2, 3 and 9). The helper constants are judged only
  if commands 8 and 15 are given the same last part; the guard file writes it twice. It does not ask
  on which axioms a theorem or a definition rests: sorry rests on an axiom of Lean's core, not of
  this library. It trusts the compiled files' own lists.

### How the commands are tested

Test.lean calls the check behind each command on small definitions with one fault each (for commands
14 and 15 on modules of Lean and of this folder), and does not compile unless the check refuses for
that fault. Its head says which refusals it cannot exercise. That the guard file's own literals are
the right ones is not tested: read them.

## The bounds behind "ringsBounded" (command 13)

For each name of the list: the greatest depth of its recursion at the callers that the source has
below main, and what is counted. The rows do not all count alike: for a walk down a list some give
the list's length, others one more, for the last call, on the empty list. Many rows also name the
test or the constant that holds the number; a row that names none does not say that there is none.

Each bound was read off the code; nothing was run. A bound that was read off the code can be wrong:
a second reading of the rows, at the code, found four too small (ioppStages, solveLater, scanLine,
sayAll); the table has the larger figures. For nine names the bound was not followed to a test or a
constant (listOfGroups, hearMany, spreadTo, choicePairs, denseIndex, denseNumber, dotSteps and the
two of Lean's merge sort), for three only in part (rdItems, reqMoments, squaresOf), and some of the
other rows lean on one step that was not opened. No program checks a bound and no command holds it:
a new caller, or a change of the function, can make a row untrue while every guard stays green.

| constant | depth at most | held by |
|---|---|---|
| `Fmt.drawFN` | 6 | its one caller, Fmt.drawF, passes 6 |
| `Fmt.leNat` | 8 | its count of bytes: 4 at two callers; a nonce of 1 to 8 bytes, tested before a byte is read; a listed position of at most 8 bytes |
| `Fmt.rdItems` | 10 | the items of parameter bytes and of statements, which the program spells itself and never reads from a file; no test counts them |
| `Fmt.rdMany` | 11 | a constant at both callers (11 and 8) |
| `OnBytes.Lkp.cubesLoop` | 130 | a constant that cubesOf passes |
| `OnBytes.Lkp.keyTrees` | 256 | the parts of one lookup; Plan.lookupOfShape refuses more |
| `OnBytes.Lkp.liveLoop` | 64 | a constant that liveBlocks passes |
| `OnBytes.Lkp.partSteps` | 255 | the parts less one: as keyTrees |
| `OnBytes.Lkp.tieSteps` | 63 | the planes less one; Lkp.Public.sizesOK asks for fewer than 64 planes |
| `OnBytes.Model.Head.callsFrom` | 7 | Head.callsOf tests that there are at most 6 lines before it makes the call |
| `OnBytes.Model.Head.lineSegs` | 10 | each word must be one of the nine names of Head.segments and not seen before |
| `OnBytes.Model.Layer.layParts` | 64 | a test on the request's matrix (the refusal shape-request-matrix) |
| `OnBytes.Model.Layer.layTables` | 24 | the program's own families of tables |
| `OnBytes.Model.Layer.layTensors` | 32 | the program's own list of tensors |
| `OnBytes.Model.Layer.plansFrom` | 28 | the number of groups (the refusal plan-groups-base) |
| `OnBytes.Model.Layer.takeCalls` | 35 | a line is followed into the next only if it has taken a segment not taken before, of at most 34 |
| `OnBytes.Model.Layer.takeSegments` | 35 | as takeCalls, for a word |
| `OnBytes.Model.Stages.leastWork` | 3 | the number of stages |
| `OnBytes.Model.Verify.withReply` | 57 | the links of a chain, tested before the one caller calls (the refusals plan-link and plan-groups-base) |
| `OnBytes.Model.WsLay.place` | 3 | the groups of one unit, written out in the text at every call |
| `OnBytes.Model.piecesBelow` | 41 | its counter starts at a constant, topBit + 1 |
| `OnBytes.Model.piecesOfSize` | 34 | the segments of one call: at most 9 in the head; in the layers at most the constant list's length (this half was not confirmed) |
| `OnBytes.Model.t2BLLoop` | 9 | its own fuel, log2 tau + 1, with tau at most 256 |
| `OnBytes.Model.wsDigits` | 4 | the digits of a weight, 2 or 4, written out in the text |
| `OnBytes.Params.ioppStages` | 22 | the group and the later stages: see solveLater; two further callers (Params/Derive.lean, Plan/Ranges.lean) pass the stages of a group's line; that such a line always comes from a parameter file was not followed |
| `OnBytes.Params.listOfGroups` | 2 | every caller writes the list out in its text |
| `OnBytes.Params.reqMoments` | 4 | the moments that the link's sub-proof declares, which the model's code writes (3 or 4), not a file; Plan/ReqFrame.lean, takeGroup, refuses a line whose moment is not below that number |
| `OnBytes.Params.solveLater` | 21 | one call for each later stage: at most 8 from a parameter file (see stagesOf). In the test calls product and links the stages are the public file's lines "stage", which no test counts; but each stage but the last must cut a row of at most 2^20 entries at least in half, so the walk ends after at most 20 and the last |
| `OnBytes.Params.stagesOf` | 8 | Params/File.lean, groupLines, refuses a line of stages of more than 32 numbers, four to a stage, before the call |
| `OnBytes.Plan.scanLine` | 15 | it walks one of two constant lists (15 and 7 members: the 14 or 6 items of a line, and one more byte, which must not be there), not the line |
| `OnBytes.Proof.toyClaimRows` | 2 | Proof.readClaims refuses a claims file whose second word is not 2 |
| `OnBytes.Psc.hearMany` | 80 | the variables of one sumcheck |
| `OnBytes.Shell.needAll` | 7 | the paths of a call on test files: 2, 3, 4 or 7, from the command's form |
| `OnBytes.Shell.sayAll` | 14 | the lines before a call's last: in a whole call the heading, at most 2 causes, 5 lines, at most 3 stages' notes and 3 lines |
| `OnBytes.Tensor.spreadTo` | 63, or somewhat more | the variables of a tensor, at most 63; at one caller (a group's mask table, Iop/Ground.lean) more by the logarithm of a number of mask rows |
| `OnBytes.Wf.weightsFrom` | 80 | the aligned blocks of rows that cover one run's stretch |
| `OnBytes.choicePairs` | about 130 | the inserted variables, from the index bits of a table |
| `OnBytes.denseIndex` | 63 | the dense variables of a tensor |
| `OnBytes.denseNumber` | 63 | as denseIndex |
| `OnBytes.dotSteps` | 60 | the variables of a tensor |
| `OnBytes.foldRounds` | 60 | the row variables of a fold. In a proximity test: stageOk, tested before the first fold. At the other caller (Iop/Req.lean, close): reqShapeOk asks at most 60 of every link's group, ReqFrame.start demands it before the first link, and close demands that the layout's number be the group's before the call |
| `OnBytes.productIndex` | 65 | the length of the list that squaresOf made in the same call: see there |
| `OnBytes.recvVectors` | 2 | the rows of the last stage's complex |
| `OnBytes.squaresOf` | 65 | the logarithm of a sum of two numbers of a code, each a word of 64 bits where parameter bytes are read; whether they can be larger elsewhere was not followed |
| `OnBytes.stretchBlocks` | 62 | its own fuel, 2 kRow + 2, with kRow at most 30 (LinShape.ok) |
| `_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR₂.run` | 64 | each call halves the list (by the shape of the algorithm; Lean's source of it was not read) |
| `_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR₂.run'` | 64 | the same ring |

## The names of "ringsOpen" (command 13)

For six of these seven names no bound is known at every caller below main; the seventh,
Fmt.Dr.times, is bounded at 64, by reading of its one caller, not machine-checked. A file that
drives one of the six deep enough ends the program with a stack overflow; it cannot turn a refusal
into a yes. That end was seen in runs on files made for the purpose; the programs that were run were
built from copies of the sources that differ from this repository's; none from this repository's.
Lean's runtime printed "Stack overflow detected. Aborting." and the process ended with the exit code
134, which is none of the program's own.

The numbers of callers are by the compiler's record. What else is said of each name was read off the
code, and no program checks it. Two clauses rest on a single reading: the 64 of Fmt.Dr.times, and
what the keys of the hash map are.

| constant | over what the recursion runs, and what is open |
|---|---|
| `Fmt.Dr.times` | its count. Its one caller below main is Fmt.drawSeed, which passes the logarithm of a number read from one word of eight bytes: at most 64 |
| `List.foldr` | the compiled List.sum on numbers: as deep as the list that is summed. Twelve declarations reached from a variant of main that calls "program" directly called that sum; they were not counted for this repository's main, which calls "programFront", and were not sorted one by one |
| `List.hasDecEq` | equality of two lists, as deep as they are long. It is reached from the derived equality of Model.Stages.StageEnd alone; how long the list there can be was not followed |
| `List.zipWith` | the compiled List.zip: as deep as the shorter list. Twenty-two declarations reached from a variant of main that calls "program" directly called it (not counted for this repository's main, which calls "programFront"; by reading, not machine-checked, OnBytes/ChecksWithHashAsArgument/M/Model/VerifyStages.lean, requestRun, is a further caller). At some of the twenty-two the lists are bounded; the others were not sorted |
| `OnBytes.Psc.hidingWalk` | the variables of one sumcheck. Whether the bound of OnBytes.Psc.hearMany in the table above (80) holds here too is open: two readings of the code differ |
| `OnBytes.Send.seedsOf` | the answers to a sample: at most 4 in the model's chains (Params/File.lean refuses a line answers that is not from 1 to 4). In the calls on test files the number is the run's own, and what bounds it there was not followed |
| `Std.DHashMap.Internal.AssocList.replace` | one bucket of the hash map of OnBytes/Chain/Index.lean (Idx.put). The keys are places of a tree's vertices, which follow from the drawn positions, not bytes of a file. No test bounds a bucket; it is short unless many keys fall into one |
