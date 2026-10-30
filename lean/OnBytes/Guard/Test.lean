-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Guard/Test.lean: each guard command is seen to refuse, whenever the library is built.

A guard that never refuses guards nothing. This file calls the checks behind the fifteen guard
commands on small definitions of its own, each with one fault, and fails to compile unless the check
refuses and its message holds the words that belong to that fault. Beside each group a faultless
case must pass. The definitions are elaborated and compiled, and never run: nothing imports this
file, and it is linked into no program. It is compiled with the library, whose Lake entry takes in
every module under OnBytes/ and which is the default target.

Faults that a file of this library may not hold. No definition here carries a mark that puts other
code in its place, is left without a body for the kernel, or is taken on trust; none is a rule for
the compiler; none has a name like a compiler-made piece. Such a declaration should stand in no file
of the library, tests included. scripts/check.py rejects the first four kinds in every file (its
search of the text, but for listed lines, and its audit of the compiled files: scripts/README.md,
"audit"); command 11 refuses the fifth in what the guard file imports. These faults are planted in a
copy of the environment instead: a hand-made compiled declaration, a mark, a rule, or a constant
that the kernel checks and nobody compiles. The check reads the copy and the copy is dropped
("inCopy"). Lean compiles nothing from what is planted, and nothing of it reaches this file's
compiled form. So these trials show what the guards do with such a record. They do not show what
Lean's compiler does with such a text.

What is not exercised. Of command 1: a rule whose proof rests on another axiom, a rule on record
without a constant, and the clauses on rules of a package that are no theorems. Of commands 2 to 4:
a constant of this library that is extern, opaque, an axiom, unsafe or partial (only implemented_by
and a rule are planted). Of command 2: its list of exceptions. Of command 3: tests (a) to (e) on
listed recursors. Of command 4: a body nested too deep, and a declaration without a body. Of command
7: the marks extern, export, init and a rule. Of command 8: a companion of the real name part with a
fault (it is exercised with invented last parts, with both classes), and universe parameters that
differ. Of command 9: a "module" header; its refusal is seen by counting Lean's own modules as this
library's for one call, and so is command 12's. Of commands 9 and 12: the test on the sizes in the
header. Of commands 11 and 12: "a check of nothing". Of command 13: a body nested too deep. Of
commands 2, 3, 4 and 13: "the walk did not end". Of commands 14 and 15: the test on the sizes in the
header, and an import of a module that is not among the imported ones. Of command 15: a fault in a
module of this library (its refusal is seen by counting Lean's first module as this library's for
one call, and with an invented last part). Of commands 9, 12 and 15: a module of a package, since
none is in this file's environment. That the guard file's own literals are the right ones is not
tested: read them.
-/
import OnBytes.Guard.Core

set_option autoImplicit false

namespace OnBytes.Guard.Test

open Lean Elab Command

/-- Runs a check that must refuse. Fails if the check passes, or if the refusal's message does not
contain the given words. What the check printed is dropped. -/
def mustRefuse (words : String) (check : CommandElabM Unit) : CommandElabM Unit := do
  let before := (← get).messages
  let said ← try check; pure none catch e => pure (some (← e.toMessageData.toString))
  modify fun s => { s with messages := before }
  match said with
  | none => throwError "a check that must refuse has passed; it was to say: {words}"
  | some m =>
    unless (m.splitOn words).length > 1 do
      throwError "a check refused, but not for the fault under test. Wanted: {words}. Said: {m}"

/-- Runs a check that must pass. What the check printed is dropped. -/
def mustPass (check : CommandElabM Unit) : CommandElabM Unit := do
  let before := (← get).messages
  check
  modify fun s => { s with messages := before }

/-! ## The two helpers themselves -/

run_cmd mustPass (pure ())
run_cmd mustRefuse "a check that must refuse has passed" (mustRefuse "any words" (pure ()))
run_cmd mustRefuse "not for the fault under test" (mustRefuse "these words" (throwError "others"))
run_cmd mustRefuse "the very words" (mustPass (throwError "the very words"))

/-! ## The definitions under test -/

/-- A function whose term mentions no constant except the type Nat. -/
def plain (n : Nat) : Nat := n

/-- Stands for a program's entry function. -/
def entryFn (_ : List String) : IO UInt32 := pure 0

/-- A root that is one call of the entry function. -/
def rootCall (args : List String) : IO UInt32 := entryFn args

/-- A root that is the entry function itself. -/
def rootSame : List String → IO UInt32 := entryFn

/-- A root that changes the arguments first. -/
def rootOtherArgs (args : List String) : IO UInt32 := entryFn (args ++ args)

/-- A root that does something after the call. -/
def rootAfter (args : List String) : IO UInt32 := do
  let r ← entryFn args
  pure (r + 1)

/-- Opens a file for reading. -/
def opensToRead (p : String) : IO IO.FS.Handle := IO.FS.Handle.mk p .read

/-- Opens a file for writing. -/
def opensToWrite (p : String) : IO IO.FS.Handle := IO.FS.Handle.mk p .write

/-- Opens a file for writing, through a function of this file. -/
def opensToWriteByHelper (p : String) : IO IO.FS.Handle := opensToWrite p

/-- Writes a file through a function of Lean's core. -/
def writesByCore (p : String) : IO Unit := IO.FS.writeFile p ""

/-- A definition with a companion that passes. (A companion is a second constant whose name is the
definition's name and one more part: command 8, OnBytes/Guard/Core.lean.) -/
def pairGood : Nat := 1

/-- The companion that passes: a safe definition of the same module and type. -/
def pairGood._t_good : Nat := 2

/-- A companion with no constant in front of the dot. -/
def noSuchBase._t_orphan : Nat := 0

/-- A definition whose companion has another type. -/
def pairType : Nat := 1

/-- The companion of another type. -/
def pairType._t_type : Bool := true

/-- A type, for a companion in front of whose dot stands neither a definition nor a theorem. -/
structure Box where
  /-- its one field -/
  v : Nat

/-- The companion of a type. -/
def Box._t_base : Type := Nat

/-- A definition whose companion is a theorem. -/
def pairKind : True := trivial

/-- The companion that is no definition. -/
theorem pairKind._t_kind : True := trivial

end OnBytes.Guard.Test

/-- A companion of a definition that another module declares. -/
def OnBytes.Guard.stdAxioms._t_module : List Lean.Name := []

namespace OnBytes.Guard.Test

open Lean Elab Command

/-! ## Commands 1 to 4 -/

run_cmd mustPass (checkCsimp [] 0)
run_cmd mustRefuse "rules of this library are on record" (checkCsimp [] 1)

run_cmd mustPass (checkCone [``plain] [])
run_cmd mustRefuse "no function to start from" (checkCone [] [])
run_cmd mustRefuse "does not exist" (checkCone [`OnBytes.Guard.Test.noSuchName] [])

run_cmd mustPass (checkPinned [``plain] [])
run_cmd mustRefuse "no function to start from" (checkPinned [] [])
run_cmd mustRefuse "strike them from the list" (checkPinned [``plain] [``Nat.add])

run_cmd mustPass (checkCompiled [``rootCall] [])
run_cmd mustRefuse "no function to start from" (checkCompiled [] [])
run_cmd mustRefuse "has no compiled code on record" (checkCompiled [``pairKind._t_kind] [])

/-! ### The boxed numeral of command 4 -/

/-- A compiled declaration with the given parameters and body. -/
def declOf (xs : Array IR.Param) (b : IR.FnBody) : IR.Decl := .fdecl `t xs .object b {}

/-- The body "take the numeral 0, box it, return it". -/
def boxedZero : IR.FnBody :=
  .vdecl ⟨1⟩ .uint64 (.lit (.num 0)) (.vdecl ⟨2⟩ .object (.box .uint64 ⟨1⟩) (.ret (.var ⟨2⟩)))

#guard isBoxedNumeral (declOf #[] boxedZero)
-- with a parameter
#guard !isBoxedNumeral (declOf #[{ x := ⟨3⟩, borrow := false, ty := .object }] boxedZero)
-- a string in place of the numeral
#guard !isBoxedNumeral (declOf #[]
  (.vdecl ⟨1⟩ .object (.lit (.str "a")) (.vdecl ⟨2⟩ .object (.box .uint64 ⟨1⟩) (.ret (.var ⟨2⟩)))))
-- a call in place of the numeral
#guard !isBoxedNumeral (declOf #[]
  (.vdecl ⟨1⟩ .uint64 (.fap `f #[]) (.vdecl ⟨2⟩ .object (.box .uint64 ⟨1⟩) (.ret (.var ⟨2⟩)))))
-- another variable is boxed
#guard !isBoxedNumeral (declOf #[]
  (.vdecl ⟨1⟩ .uint64 (.lit (.num 0)) (.vdecl ⟨2⟩ .object (.box .uint64 ⟨7⟩) (.ret (.var ⟨2⟩)))))
-- another variable is returned
#guard !isBoxedNumeral (declOf #[]
  (.vdecl ⟨1⟩ .uint64 (.lit (.num 0)) (.vdecl ⟨2⟩ .object (.box .uint64 ⟨1⟩) (.ret (.var ⟨1⟩)))))
-- a step more between the box and the return
#guard !isBoxedNumeral (declOf #[]
  (.vdecl ⟨1⟩ .uint64 (.lit (.num 0)) (.vdecl ⟨2⟩ .object (.box .uint64 ⟨1⟩)
    (.vdecl ⟨3⟩ .object (.fap `f #[.var ⟨2⟩]) (.ret (.var ⟨2⟩))))))

/-- The table that has each of the declarations on record under its own name. -/
def tableOf (ds : List IR.Decl) : Std.HashMap Name IR.Decl :=
  Std.HashMap.ofList (ds.map fun d => (d.name, d))

/-- A compiled declaration without parameters, under the name n. -/
def named (n : Name) (b : IR.FnBody) : IR.Decl := .fdecl n #[] .object b {}

/-- The body "call f without arguments and return what it gives". -/
def callOf (f : Name) : IR.FnBody := .vdecl ⟨1⟩ .object (.fap f #[]) (.ret (.var ⟨1⟩))

/-- The body "return the string a". -/
def aString : IR.FnBody := .vdecl ⟨1⟩ .object (.lit (.str "a")) (.ret (.var ⟨1⟩))

-- the decision itself: a name that ends like a boxed numeral's goes by the body alone
#guard isLetThrough (tableOf [named `a.b._boxed_const_1 boxedZero]) `a.b `a.b._boxed_const_1
#guard !isLetThrough (tableOf [named `a.b._boxed_const_1 aString]) `a.b `a.b._boxed_const_1
#guard !isLetThrough (tableOf []) `a.b `a.b._boxed_const_1
#guard !isLetThrough (tableOf [named `a.b._boxed_const_2 boxedZero]) `a.b `a.b._boxed_const_1
-- also where another part of the name is of a kind that goes by the name (_closed_, _lam_)
#guard isLetThrough (tableOf [named `a.b._closed_0._boxed_const_1 boxedZero]) `a.b
  `a.b._closed_0._boxed_const_1
#guard !isLetThrough (tableOf [named `a.b._closed_0._boxed_const_1 aString]) `a.b
  `a.b._closed_0._boxed_const_1
-- the two kinds _closed_ and _lam_ go by the name
#guard isLetThrough (tableOf []) `a.b `a.b._closed_0
#guard isLetThrough (tableOf []) `a.b `a.b._lam_0
-- but not with a boxed numeral's part further to the left
#guard !isLetThrough (tableOf []) `a.b `a.b._boxed_const_1._closed_0
#guard !isLetThrough (tableOf [named `a.b._boxed_const_1._lam_0 boxedZero]) `a.b
  `a.b._boxed_const_1._lam_0
#guard !isLetThrough (tableOf [named `a.b boxedZero]) `a.b `a.b
#guard !isLetThrough (tableOf [named `a.c._closed_0 boxedZero]) `a.b `a.c._closed_0

#guard isBoxedName `a.b `a.b._boxed_const_1
#guard isBoxedName `a.b `a.b._closed_0._boxed_const_1
#guard !isBoxedName `a.b `a.b
#guard !isBoxedName `a.b `a.c._boxed_const_1
#guard !isBoxedName `a.b `a.b._boxed_const_1.more

/-! ### Command 4 on hand-made compiled code

The check reads Lean's record of compiled declarations. Here hand-made declarations are put on that
record in a copy of the environment; the check runs on the copy, and the copy is dropped. Lean
compiles nothing from what is planted, and nothing of it reaches this file's compiled form. -/

/-- Runs a check in a changed copy of the environment. The copy is dropped afterwards. -/
def inCopy (plant : Environment → Except String Environment) (check : CommandElabM Unit) :
    CommandElabM Unit := do
  let saved ← getEnv
  try
    match plant saved with
    | .ok e => setEnv e
    | .error m => throwError "the test could not plant its fault: {m}"
    check
  finally setEnv saved

/-- The copy also has these compiled declarations on record. -/
def withCode (ds : List IR.Decl) : Environment → Except String Environment :=
  fun e => .ok (ds.foldl (fun e d => IR.declMapExt.addEntry e d) e)

/-- The copy also has the constant n, the number 0, checked by the kernel and not compiled. -/
def withConst (n : Name) (e : Environment) : Except String Environment :=
  let d := mkDefinitionValEx n [] (mkConst ``Nat) (mkRawNatLit 0) .abbrev .safe [n]
  match e.addDeclCore 0 (.defnDecl d) none with
  | .ok e => .ok e
  | .error _ => .error s!"the kernel did not take {n}"

/-- The root of these trials: a theorem, so its cone is itself and it has no code of its own. -/
def root : Name := ``pairKind._t_kind

/-- The name of a boxed numeral under "plain", a function that the root's cone does not hold. -/
def boxed1 : Name := .str ``plain "_boxed_const_1"

/-- The check on a root whose hand-made code calls f, with the declarations ds on record. -/
def onCall (f : Name) (ds : List IR.Decl) : CommandElabM Unit :=
  inCopy (withCode (named root (callOf f) :: ds)) (checkCompiled [root] [])

-- the helper drops its copy, also behind a refusal
run_cmd mustRefuse "has no compiled code on record" (checkCompiled [root] [])
run_cmd mustPass (onCall boxed1 [named boxed1 boxedZero])
run_cmd mustRefuse "has no compiled code on record" (checkCompiled [root] [])
run_cmd mustRefuse "the test could not plant its fault" (inCopy (fun _ => .error "so") (pure ()))

-- a stranger: the code calls a function of this file that the kernel's cone lacks
run_cmd mustRefuse "A STRANGER" (onCall ``plain [])
-- the name of a boxed numeral over another body: a string; a call; a parameter; a step more
run_cmd mustRefuse "A STRANGER" (onCall boxed1 [named boxed1 aString])
run_cmd mustRefuse "A STRANGER" (onCall boxed1 [named boxed1 (callOf ``entryFn)])
run_cmd mustRefuse "A STRANGER" (onCall boxed1
          [.fdecl boxed1 #[{ x := ⟨3⟩, borrow := false, ty := .object }] .object boxedZero {}])
run_cmd mustRefuse "A STRANGER" (onCall boxed1 [named boxed1
          (.vdecl ⟨1⟩ .uint64 (.lit (.num 0)) (.vdecl ⟨2⟩ .object (.box .uint64 ⟨1⟩)
            (.vdecl ⟨3⟩ .object (.fap ``entryFn #[.var ⟨2⟩]) (.ret (.var ⟨2⟩)))))])
-- the same where another part of the name is of a kind that goes by the name
run_cmd mustPass (onCall (.str (.str ``plain "_closed_0") "_boxed_const_1")
          [named (.str (.str ``plain "_closed_0") "_boxed_const_1") boxedZero])
run_cmd mustRefuse "A STRANGER" (onCall (.str (.str ``plain "_closed_0") "_boxed_const_1")
          [named (.str (.str ``plain "_closed_0") "_boxed_const_1") aString])
-- the two kinds _closed_ and _lam_ pass by the name, whatever the body
run_cmd mustPass (onCall (.str ``plain "_closed_0") [named (.str ``plain "_closed_0") aString])
run_cmd mustPass (onCall (.str ``plain "_lam_0") [named (.str ``plain "_lam_0") aString])
-- a constant that somebody wrote under such a name is no piece
run_cmd mustRefuse "A STRANGER" (inCopy (fun e => (withConst boxed1 e).bind
          (withCode [named root (callOf boxed1), named boxed1 boxedZero]))
            (checkCompiled [root] []))
run_cmd mustRefuse "A STRANGER" (inCopy (fun e => (withConst (.str ``plain "_closed_0") e).bind
          (withCode [named root (callOf (.str ``plain "_closed_0")),
            named (.str ``plain "_closed_0") aString])) (checkCompiled [root] []))
-- called but not on record; no constant behind the name
run_cmd mustRefuse "cannot judge these declarations" (onCall boxed1 [])
run_cmd mustRefuse "cannot judge these declarations"
          (onCall `noSuchBase.f [named `noSuchBase.f aString])

/-! ### Commands 1 to 5 and 7 on a mark or a rule

No file of this library may hold a definition with a mark, or a rule for the compiler. Here a mark
or a rule is put on Lean's record in a copy of the environment, after the definitions that it names
have been compiled; the check reads the copy, and the copy is dropped. Lean compiles nothing under
it. -/

/-- The copy has on record that g is to be compiled in the place of c, without an equation. -/
def withStandIn (c g : Name) (e : Environment) : Except String Environment :=
  Compiler.implementedByAttr.setParam e c g

/-- The copy has on record the rule t: f is compiled as g. -/
def withRule (f g t : Name) (e : Environment) : Except String Environment :=
  .ok (Compiler.CSimp.ext.addEntry e { fromDeclName := f, toDeclName := g, thmName := t })

/-- A second writing of "plain". -/
def plainToo (n : Nat) : Nat := n

/-- The equation between the two, as a definition: no theorem. -/
def equationAsDef : @plain = @plainToo := rfl

/-- The equation between the two, as a theorem. -/
theorem equationAsThm : @plain = @plainToo := rfl

/-- A function that calls "plain". -/
def usesPlain (n : Nat) : Nat := plain n

run_cmd mustRefuse "refuses these constants of this library"
          (inCopy (withStandIn ``entryFn ``rootSame) (checkCone [``rootCall] []))
run_cmd mustRefuse "the pinned guard refuses these constants"
          (inCopy (withStandIn ``entryFn ``rootSame) (checkPinned [``rootCall] []))
run_cmd mustRefuse "has an entry in Lean's records of"
          (inCopy (withStandIn ``rootCall ``rootSame) (checkEntry ``rootCall ``entryFn))
-- a name that is not Lean core's cannot stand on the closed list: the marked constant has a row,
-- which counts as this library's, so the list's entry has no user
run_cmd mustRefuse "strike them" (inCopy (withStandIn ``entryFn ``rootSame)
          (checkCore [``rootCall] ["OnBytes.Guard.Test.entryFn"]))
run_cmd mustRefuse "a rule of this library that is not a theorem"
          (inCopy (withRule ``plain ``plainToo ``equationAsDef) (checkCsimp [] 0))
run_cmd mustPass (inCopy (withRule ``plain ``plainToo ``equationAsThm) (checkCsimp [] 1))
run_cmd mustRefuse "the pinned guard refuses these constants"
          (inCopy (withRule ``plain ``plainToo ``equationAsThm) (checkPinned [``usesPlain] []))

/-- The copy also has the constant n, another name for the constant c, checked by the kernel and not
compiled. -/
def withAlias (n c : Name) (e : Environment) : Except String Environment :=
  match e.find? c with
  | none => .error s!"{c} does not exist"
  | some ci =>
    let d := mkDefinitionValEx n [] ci.type (mkConst c) .abbrev .safe [n]
    match e.addDeclCore 0 (.defnDecl d) none with
    | .ok e => .ok e
    | .error _ => .error s!"the kernel did not take {n}"

/-- The root of the next two trials: it exists in the dropped copies alone. -/
def rootInCopy : Name := `OnBytes.Guard.Test.rootInCopy.made

-- command 4. A control first: a root whose cone holds a function, and whose hand-made code calls
-- it, passes. Then: the root's cone holds the marked function and, through the mark, its stand-in;
-- the code calls the stand-in; the refusal's words are those of the mark, not of a stranger.
run_cmd mustPass (inCopy (fun e => (withAlias rootInCopy ``rootSame e).bind
          (withCode [named rootInCopy (callOf ``rootSame)])) (checkCompiled [rootInCopy] []))
run_cmd mustRefuse "without an equation"
          (inCopy (fun e => ((withStandIn ``entryFn ``rootSame e).bind
          (withAlias rootInCopy ``entryFn)).bind
            (withCode [named rootInCopy (callOf ``rootSame)])) (checkCompiled [rootInCopy] []))
-- the same with a rule of this library, though it is a theorem
run_cmd mustRefuse "by the rule"
          (inCopy (fun e => ((withRule ``plain ``plainToo ``equationAsThm e).bind
          (withAlias rootInCopy ``plain)).bind
            (withCode [named rootInCopy (callOf ``plainToo)])) (checkCompiled [rootInCopy] []))
-- the command's list of exceptions goes by the constant behind a name
run_cmd mustPass (inCopy (withCode [named root (callOf ``plain)]) (checkCompiled [root] [``plain]))

/-! ### The reader of compiled bodies -/

#guard callsOf 0 (callOf `f) #[] == none
#guard callsOf 9 (callOf `f) #[] == some #[`f]
-- a closure taken
#guard callsOf 9 (.vdecl ⟨1⟩ .object (.pap `g #[]) (.ret (.var ⟨1⟩))) #[] == some #[`g]
-- a call inside the body of a join point, and one behind it
#guard callsOf 9 (.jdecl ⟨1⟩ #[] (callOf `f) (callOf `g)) #[] == some #[`f, `g]
-- a call in each arm of a case
#guard callsOf 9 (.case `T ⟨1⟩ .object
  #[.ctor { name := `c, cidx := 0, size := 0, usize := 0, ssize := 0 } (callOf `f),
    .default (callOf `g)]) #[] == some #[`f, `g]
#guard isPiece `a.b `a.b._closed_0
#guard isPiece `a.b `a.b._lam_0._boxed
#guard !isPiece `a.b `a.b
#guard !isPiece `a.b `a.c._lam_0
#guard !isPiece `a.b `a.b._boxed_const_1

/-! ## Command 5 -/

run_cmd mustPass (checkCore [``plain] [])
run_cmd mustRefuse "no function to start from" (checkCore [] [])
run_cmd mustRefuse "the closed list does not name them" (checkCore [``opensToRead] [])
run_cmd mustRefuse "strike them" (checkCore [``plain] ["Nat.add"])
run_cmd mustRefuse "more than once" (checkCore [``plain] ["Nat.add", "Nat.add"])

/-! ## Command 6 -/

run_cmd mustPass (checkHas [``rootCall] [``entryFn])
run_cmd mustRefuse "not in the cone of" (checkHas [``rootCall] [``plain])
run_cmd mustRefuse "or no name" (checkHas [``rootCall] [])
run_cmd mustRefuse "or no name" (checkHas [] [``entryFn])

/-! ## Command 7 -/

run_cmd mustPass (checkEntry ``rootCall ``entryFn)
run_cmd mustPass (checkEntry ``rootSame ``entryFn)
run_cmd mustRefuse "is not one call of" (checkEntry ``rootOtherArgs ``entryFn)
run_cmd mustRefuse "is not one call of" (checkEntry ``rootAfter ``entryFn)
run_cmd mustRefuse "is not one call of" (checkEntry ``rootCall ``plain)
run_cmd mustRefuse "is no definition" (checkEntry ``pairKind._t_kind ``entryFn)

/-! ## Command 8 -/

run_cmd mustPass (checkTwins "_t_good" "safe" 1)
run_cmd mustRefuse "was told to find at least" (checkTwins "_t_good" "safe" 2)
run_cmd mustRefuse "no constant has the name in front of the dot" (checkTwins "_t_orphan" "safe" 1)
run_cmd mustRefuse "has another type" (checkTwins "_t_type" "safe" 1)
run_cmd mustRefuse "it is no definition of the kernel's class" (checkTwins "_t_kind" "safe" 1)
run_cmd mustRefuse "is declared in another module" (checkTwins "_t_module" "safe" 1)
run_cmd mustRefuse "neither a safe definition nor a theorem" (checkTwins "_t_base" "safe" 1)
run_cmd mustRefuse "a class that it does not know" (checkTwins "_t_good" "other" 1)
run_cmd mustRefuse "no last part of a name" (checkTwins "" "safe" 1)
-- the class and the part that the guard file names: a safe definition under a companion's name is
-- what a hand-written one would be; Lean's own companions of this folder's recursive functions pass
run_cmd mustRefuse "it is no definition of the kernel's class partial"
          (checkTwins "_t_good" "partial" 1)
run_cmd mustPass (checkTwins "_unsafe_rec" "partial" 1)

/-! ## Command 9 -/

run_cmd mustPass (checkTables [``Lean.regularInitAttr, ``Lean.builtinInitAttr] [])
run_cmd mustRefuse "entries in"
          (checkTables [``Lean.regularInitAttr, ``Lean.builtinInitAttr] [`Lean])
run_cmd mustRefuse "is the table's name right" (checkTables [`OnBytes.Guard.Test.noSuchTable] [])
run_cmd mustRefuse "was given no table" (checkTables [] [])

run_cmd mustPass (checkTables [``Lean.exportAttr] [])
run_cmd mustRefuse "entries in" (checkTables [``Lean.exportAttr] [`Init])
run_cmd mustPass (checkTables [``Lean.Compiler.implementedByAttr, ``Lean.externAttr] [])
run_cmd mustRefuse "entries in" (checkTables [``Lean.Compiler.implementedByAttr] [`Init])
run_cmd mustRefuse "entries in" (checkTables [``Lean.externAttr] [`Init])

/-! ## Command 10 -/

run_cmd mustPass (checkCtors [``opensToRead] ``IO.FS.Mode [``IO.FS.Mode.read])
run_cmd mustRefuse "which the call does not allow"
          (checkCtors [``opensToWrite] ``IO.FS.Mode [``IO.FS.Mode.read])
run_cmd mustRefuse "which the call does not allow"
          (checkCtors [``opensToWriteByHelper] ``IO.FS.Mode [``IO.FS.Mode.read])
run_cmd mustRefuse "which the call does not allow"
          (checkCtors [``writesByCore] ``IO.FS.Mode [``IO.FS.Mode.read])
run_cmd mustRefuse "strike them"
          (checkCtors [``opensToRead] ``IO.FS.Mode [``IO.FS.Mode.read, ``IO.FS.Mode.write])
run_cmd mustRefuse "no constructor of" (checkCtors [``opensToRead] ``IO.FS.Mode [``Nat.zero])
run_cmd mustRefuse "is no inductive type" (checkCtors [``opensToRead] ``Nat.add [])
run_cmd mustRefuse "no function to start from" (checkCtors [] ``IO.FS.Mode [``IO.FS.Mode.read])

/-! ## Command 11 -/

/-- The beginnings that the guard file names. -/
def realStarts : List String := ["_boxed", "_closed_", "_lam_", "_elam", "_at_", "_redArg"]

/-- A private definition: its full name has a number among its parts. -/
private def hidden._t_private : Nat := 0

run_cmd mustPass (checkParts ["_no_constant_has_such_a_part_"])
run_cmd mustRefuse "begins like the name of a piece" (checkParts ["_t_good"])
run_cmd mustRefuse "begins like the name of a piece" (checkParts ["_no_such_", "_t_orph"])
-- a constant of an imported module of this library; one of Lean's core; one with a private name
run_cmd mustRefuse "begins like the name of a piece" (checkParts ["stdAxiom"])
run_cmd mustRefuse "begins like the name of a piece" (checkParts ["propex"])
run_cmd mustRefuse "begins like the name of a piece" (checkParts ["_t_private"])
run_cmd mustRefuse "or an empty one" (checkParts [])
run_cmd mustRefuse "or an empty one" (checkParts ["_closed_", ""])
-- the beginnings that the guard file names, on constants that exist in a dropped copy alone
run_cmd mustPass (checkParts realStarts)
run_cmd mustRefuse "begins like the name of a piece" (inCopy (withConst boxed1)
          (checkParts realStarts))
run_cmd mustRefuse "begins like the name of a piece" (inCopy (withConst (.str ``plain "_closed_3"))
          (checkParts realStarts))
run_cmd mustRefuse "begins like the name of a piece"
          (inCopy (withConst (.str (.str ``plain "_lam_0") "more"))
            (checkParts realStarts))
run_cmd mustRefuse "begins like the name of a piece" (inCopy (withConst (.str ``plain "_elam_2"))
          (checkParts realStarts))
run_cmd mustRefuse "begins like the name of a piece"
          (inCopy (withConst (.str (.str (.str ``plain "_at_") "f") "spec_0"))
            (checkParts realStarts))
run_cmd mustRefuse "begins like the name of a piece" (inCopy (withConst (.str ``plain "_redArg"))
          (checkParts realStarts))
run_cmd mustRefuse "begins like the name of a piece" (inCopy (withConst (.str ``plain "_boxed"))
          (checkParts realStarts))
#guard hasPartLike ["_lam_"] (.num `a._lam_0 3)
#guard hasPartLike ["_lam_"] `a._lam_0.b
#guard !hasPartLike ["_lam_"] `a.lam_0.b
#guard !hasPartLike ["_lam_"] `a.x_lam_0

/-! ## Command 12 -/

run_cmd mustPass (checkHomes [])
-- Lean makes some lemmas on demand, and more than one of its own modules can hold the same one: so
-- the check refuses when Lean's own modules are counted as this library's for one call
run_cmd mustRefuse "gives the name to another module" (checkHomes [`Init])

/-! ## Command 13 -/

/-- The body "call f, then call g and return what g gives". -/
def thenCallOf (f g : Name) : IR.FnBody := .vdecl ⟨1⟩ .object (.fap f #[]) (callOf g)

-- the reader of places: a call whose result is returned at once is in the last place
#guard placesOf 9 (callOf `f) #[] == some #[(`f, true)]
#guard placesOf 0 (callOf `f) #[] == none
-- another variable is returned; a step follows the call; a closure is taken
#guard placesOf 9 (.vdecl ⟨1⟩ .object (.fap `f #[]) (.ret (.var ⟨2⟩))) #[] == some #[(`f, false)]
#guard placesOf 9 (.vdecl ⟨1⟩ .object (.fap `f #[]) (callOf `g)) #[] ==
  some #[(`f, false), (`g, true)]
#guard placesOf 9 (.vdecl ⟨1⟩ .object (.pap `f #[]) (.ret (.var ⟨1⟩))) #[] == some #[(`f, false)]
-- a count is lowered between the call and the return: not the last place
#guard placesOf 9
  (.vdecl ⟨1⟩ .object (.fap `f #[]) (.dec ⟨2⟩ 1 true false (.ret (.var ⟨1⟩)))) #[] ==
  some #[(`f, false)]
-- both parts of a join point, and every arm of a case, are read
#guard placesOf 9 (.jdecl ⟨7⟩ #[] (callOf `f) (callOf `g)) #[] == some #[(`f, true), (`g, true)]
#guard placesOf 9 (.case `T ⟨1⟩ .object
  #[.ctor { name := `c, cidx := 0, size := 0, usize := 0, ssize := 0 } (callOf `f),
    .default (thenCallOf `g `h)]) #[] == some #[(`f, true), (`g, false), (`h, true)]

-- the rings: 0 and 1 point at each other; 2 points at itself; 3 points at 0 and nothing at 3
#guard (ringsOf #[#[1], #[0], #[2], #[0]]).2.toList.mergeSort == [1, 1, 2]
#guard let r := (ringsOf #[#[1], #[0], #[2], #[0]]).1
  r[0]! == r[1]! && r[0]! != r[2]! && r[0]! != r[3]!
-- a ring of three, and a line of three
#guard (ringsOf #[#[1], #[2], #[0]]).2 == #[3]
#guard (ringsOf #[#[1], #[2], #[]]).2 == #[1, 1, 1]
#guard (ringsOf #[]).2 == #[]

/-- A second theorem without code of its own, for a ring of two. -/
def second : Name := ``equationAsThm

-- a declaration that calls itself in the last place is a loop
run_cmd mustPass (inCopy (withCode [named root (callOf root)]) (checkRings [root] []))
-- one that calls itself and then goes on is deep
run_cmd mustRefuse "does not name them"
          (inCopy (withCode [named root (thenCallOf root ``plain)]) (checkRings [root] []))
run_cmd mustPass (inCopy (withCode [named root (thenCallOf root ``plain)])
          (checkRings [root] [toString root]))
-- a ring of two: the first calls the second and goes on; the second calls the first at its end:
-- both are deep, since the compiler makes a loop only of a call of a declaration to itself
run_cmd mustRefuse "does not name them"
          (inCopy (withCode [named root (thenCallOf second ``plain), named second (callOf root)])
            (checkRings [root] []))
run_cmd mustRefuse "does not name them"
          (inCopy (withCode [named root (thenCallOf second ``plain), named second (callOf root)])
            (checkRings [root] [toString root]))
run_cmd mustPass
          (inCopy (withCode [named root (thenCallOf second ``plain), named second (callOf root)])
            (checkRings [root] [toString root, toString second]))
-- a ring of two in which both calls stand in the last place
run_cmd mustRefuse "does not name them"
          (inCopy (withCode [named root (callOf second), named second (callOf root)])
            (checkRings [root] []))
run_cmd mustPass (inCopy (withCode [named root (callOf second), named second (callOf root)])
          (checkRings [root] [toString root, toString second]))
-- a declaration that takes itself as a closure and returns it
run_cmd mustRefuse "does not name them"
          (inCopy (withCode [named root (.vdecl ⟨1⟩ .object (.pap root #[]) (.ret (.var ⟨1⟩)))])
            (checkRings [root] []))
-- a call that goes on, but into no ring
run_cmd mustPass (inCopy (withCode [named root (thenCallOf second ``plain), named second aString])
          (checkRings [root] []))
-- a piece of the compiler's counts for the constant from which it is made
run_cmd mustRefuse "does not name them"
          (inCopy (withCode [named root (callOf (.str ``plain "_lam_0")),
            named (.str ``plain "_lam_0") (thenCallOf (.str ``plain "_lam_0") ``entryFn)])
            (checkRings [root] []))
run_cmd mustPass (inCopy (withCode [named root (callOf (.str ``plain "_lam_0")),
            named (.str ``plain "_lam_0") (thenCallOf (.str ``plain "_lam_0") ``entryFn)])
          (checkRings [root] [toString ``plain]))
-- faults of the list and of the call
run_cmd mustRefuse "strike them" (inCopy (withCode [named root (callOf root)])
          (checkRings [root] [toString root]))
run_cmd mustRefuse "more than once" (inCopy (withCode [named root (thenCallOf root ``plain)])
          (checkRings [root] [toString root, toString root]))
run_cmd mustRefuse "no function to start from" (checkRings [] [])
run_cmd mustRefuse "has no compiled code on record" (checkRings [root] [])

/-! ## Commands 14 and 15 -/

-- the modules below a module of Lean's core: itself among them; none that it does not import
run_cmd do
  let env ← getEnv
  match modulesBelow env `Init.Prelude with
  | .ok b => unless b.size == 1 do throwError "Init.Prelude has {b.size} modules below it"
  | .error e => throwError e
-- this file imports OnBytes.Guard.Core alone, so every module of its environment lies below that
-- one, each once: a walk that ends early, or takes a module twice, gives another number
run_cmd do
  let env ← getEnv
  match modulesBelow env `OnBytes.Guard.Core with
  | .ok b => unless b.size == env.header.moduleNames.size do
      throwError "the walk reached {b.size} of {env.header.moduleNames.size} modules"
  | .error e => throwError e
run_cmd do
  let env ← getEnv
  match modulesBelow env `No.Such.Module with
  | .ok _ => throwError "a module that does not exist has modules below it"
  | .error _ => pure ()
-- this folder's first file imports Lean, and so has modules under Lean below it
run_cmd mustRefuse "OnBytes.Guard.Basic imports Lean"
          (checkImports `OnBytes.Guard.Basic [`Lean])
-- by the first part of a name: the module Lean itself is not below this one
run_cmd mustRefuse "and so is the root's" (checkImports `Lean.Elab.Command [`Lean])
run_cmd mustPass (checkImports `Init.Prelude [`Lean])
run_cmd mustPass (checkImports `OnBytes.Guard.Basic [`NoSuchPart])
run_cmd mustPass (checkImports `Init.Prelude barredOfProgram)
-- the guard file's own list bars Lean
run_cmd mustRefuse "OnBytes.Guard.Basic imports Lean"
          (checkImports `OnBytes.Guard.Basic barredOfProgram)
run_cmd do
  for p in `Lake :: packageRoots do
    unless barredOfProgram.contains p do throwError "barredOfProgram does not bar {p}"
run_cmd mustRefuse "no first part to bar" (checkImports `Init.Prelude [])
run_cmd mustRefuse "is not among the modules that this file imports"
          (checkImports `No.Such.Module [`Lean])

/-- The record of a constant of the environment. -/
def recordOf (c : Name) : CommandElabM ConstantInfo := do
  let some ci := (← getEnv).find? c | throwError "{c} does not exist"
  return ci

-- an unsafe axiom counts as an axiom, an unsafe opaque constant as opaque
run_cmd do
  for (c, k) in [(``propext, some "an axiom"), (``IO.getStdout, some "opaque"),
      (``unsafeCast, some "unsafe"), (``lcProof, some "an axiom"),
      (``ptrAddrUnsafe, some "opaque"), (``Nat.add, none), (``Nat.add_comm, none)] do
    let got := oddKind (← recordOf c)
    unless got == k do throwError "{c}: {got}, and not {k}"
-- the helper constant that Lean made for placesOf is of the class partial
run_cmd do
  let got := oddKind (← recordOf (.str ``placesOf "_unsafe_rec"))
  unless got == some "partial" do throwError "the helper constant: {got}"
-- who is let through: a definition of the class partial with the given last part, and nobody else
run_cmd do
  for (c, p, k) in [(``propext, "propext", false), (``IO.getStdout, "getStdout", false),
      (``unsafeCast, "unsafeCast", false), (``Nat.add, "add", false),
      (.str ``placesOf "_unsafe_rec", "_unsafe_rec", true),
      (.str ``placesOf "_unsafe_rec", "_other", false)] do
    let got := excused p (← recordOf c)
    unless got == k do throwError "{c} with the last part {p}: {got}, and not {k}"
-- Lean's own first module, counted as this library's for one call, has axioms and opaque constants
run_cmd mustRefuse "each is an axiom, opaque, unsafe or partial"
          (checkPlain `Init.Prelude "_unsafe_rec" [`Init])
run_cmd mustRefuse "a check of nothing" (checkPlain `Init.Prelude "_unsafe_rec" [])
-- the files below Core.lean hold none, but for Lean's helper constants
run_cmd mustPass (checkPlain `OnBytes.Guard.Core "_unsafe_rec" [])
run_cmd mustRefuse "_unsafe_rec: partial, in OnBytes.Guard"
          (checkPlain `OnBytes.Guard.Core "_no_such_part" [])
run_cmd mustRefuse "is not among the modules that this file imports"
          (checkPlain `No.Such.Module "_unsafe_rec" [])

end OnBytes.Guard.Test
