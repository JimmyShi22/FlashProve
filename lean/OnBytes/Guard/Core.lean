-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Guard/Core.lean: guard commands 5 to 15, and their lists.

These are programs that run while the library is built; nothing here is compiled into a verifier.
OnBytes/Guard/Program.lean calls all fifteen for verify-on-bytes; this repository builds no
stand-alone program from it. If a command rejects something, that file does not compile and the
default build fails. "Below main" is main's cone: what main's definition reaches through the
kernel's terms (Cone.lean); in 13, through compiled code.
"Below the root", in 14 and 15, is the program's root module and all that it imports, directly or
through others.

 5  #guard_core: Lean core's constants below main whose compiled code is not made from their
    definition are exactly the names of the closed list "coreOfProgram".
 6  #guard_has: each function of the list "judges" is somewhere below main, used or not.
 7  #guard_entry: main's term is one call of the named function, and main carries no mark.
 8  #guard_twins: a constant of this library with the name of a compiler's helper constant is one.
 9  #guard_tables: no module of this library has an entry in the named tables of Lean.
10  #guard_ctors: of a type's constructors, exactly the named ones are below main.
11  #guard_parts: no constant has a name like a declaration that Lean's compiler makes.
12  #guard_homes: Lean's map from names to modules gives each constant of this library to the module
    that declares it.
13  #guard_rings: the compiled declarations below main that call back into their own recursion,
    otherwise than by a last call to themselves, are made from exactly the constants of the two
    closed lists "ringsBounded" and "ringsOpen".
14  #guard_imports: no module below the root has a name whose first part is barred.
15  #guard_plain: no constant of this library in a module below the root is an axiom, opaque, unsafe
    or partial, but for the helper constants of 8.

The guards catch a slip and the plain written forms. They do not stop someone who runs code at
compile time in a file that the program's root imports. scripts/check.py searches the text of these
files for the plain forms of such code (scripts/RULES.txt, "The program's source").

What each command checks in full, why it is there, what to do when it rejects, and its limits:
OnBytes/Guard/README.md.
-/
import OnBytes.Guard.Cmd

set_option autoImplicit false

namespace OnBytes.Guard

open Lean Elab Command

/-- **The check.** Of the constants that "rowOf" lists in the cone of the roots, those that are Lean
core's own must be exactly the names of the list, by their printed form (some are private names,
which cannot be written as names). -/
def checkCore (roots : List Name) (allowed : List String) : CommandElabM Unit := do
  let env ← getEnv
  if roots.isEmpty then throwError "the guard on Lean core's names was given no function to start \
    from"
  match coneOf env roots with
  | .error e => throwError "the guard on Lean core's names: {e}"
  | .ok cone =>
    let core := ((cone.filterMap (rowOf env)).filter fun r => r.2 == .core).map fun r =>
      (toString r.1.name, ", ".intercalate r.1.why)
    let core := core.qsort fun a b => a.1 < b.1
    let new := core.filter fun r => !allowed.contains r.1
    let gone := allowed.filter fun n => !core.any fun r => r.1 == n
    let twice := (allowed.filter fun n => allowed.count n > 1).eraseDups
    logInfo m!"Lean core's own in the cone of {roots}: {core.size} listed constants; the closed \
      list has {allowed.length} names"
    unless twice.isEmpty do
      throwError "the guard on Lean core's names: these names stand on the list more than \
        once:\n{lines (twice.map fun (s : String) => s.toName).toArray}"
    unless gone.isEmpty do
      throwError "the guard on Lean core's names: these names are on the list but this cone does \
        not list them: strike them (a name without a user is an exception that nobody \
        needs):\n{"\n".intercalate (gone.map fun s => "  " ++ s)}"
    unless new.isEmpty do
      throwError "the guard on Lean core's names refuses these constants: they are Lean core's \
        own, they are in the cone of {roots}, their compiled code is not made from their \
        definition, \
        and the closed list does not name them:\n{"\n".intercalate (new.toList.map fun r => "  \
          " ++ r.1 ++ ": " ++ r.2)}"

/-- #guard_core roots allowed: a term of type List Lean.Name and one of type List String. -/
macro "#guard_core " r:term:max a:term:max : command => `(run_cmd OnBytes.Guard.checkCore $r $a)

/-- **The check.** Every one of the names is in the cone of the roots, as "coneOf"
(OnBytes/Guard/Cmd.lean) traverses it. -/
def checkHas (roots names : List Name) : CommandElabM Unit := do
  if roots.isEmpty || names.isEmpty then throwError "the guard on what a program calls was given \
    no function to start from, or no name"
  match coneOf (← getEnv) roots with
  | .error e => throwError "the guard on what a program calls: {e}"
  | .ok cone =>
    let missing := names.filter fun n => !cone.contains n
    unless missing.isEmpty do throwError "the guard on what a program calls refuses: not in the \
      cone of {roots}: {missing}"
    logInfo m!"in the cone of {roots} ({cone.size} constants): all {names.length}: {names}"

/-- #guard_has roots names: both are terms of type List Lean.Name. -/
macro "#guard_has " r:term:max a:term:max : command => `(run_cmd OnBytes.Guard.checkHas $r $a)

/-- **The check.** The term of "root" is one call of "entry" and nothing else, and "root" has no
entry in Lean's records of implemented_by, extern, export, init and csimp. The check reads the term
that the kernel has and Lean's own records, not the file's text. -/
def checkEntry (root entry : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some (.defnInfo d) := env.find? root | throwError "the guard on a program's entry: {root} \
    is no definition"
  let one := match d.value with
    | .lam _ _ (.app (.const c _) (.bvar 0)) _ => c == entry
    | .const c _ => c == entry
    | _ => false
  unless one do throwError "the guard on a program's entry refuses: the term of {root} is not one \
    call of {entry} and nothing else:\n{d.value}"
  let mut marks : Array String := #[]
  if (Compiler.getImplementedBy? env root).isSome then marks := marks.push "implemented_by"
  if isExtern env root then marks := marks.push "extern"
  if (getExportNameFor? env root).isSome then marks := marks.push "export"
  if (getInitFnNameFor? env root).isSome || isIOUnitInitFn env root then marks := marks.push "init"
  if ((Compiler.CSimp.ext.getState env).map.find? root).isSome then marks := marks.push "a rule \
    for the compiler"
  unless marks.isEmpty do throwError "the guard on a program's entry refuses: {root} has an entry \
    in Lean's records of: {marks}"
  logInfo m!"{root} is one call of {entry}, as a term; no entry for it in Lean's records of \
    implemented_by, extern, export, init, csimp"

/-- #guard_entry root entry: two names, each with two backticks. -/
macro "#guard_entry " r:term:max e:term:max : command => `(run_cmd OnBytes.Guard.checkEntry $r $e)

/-- **The check.** Takes every constant of the environment that is this library's (the file that is
being compiled counts as this library's) and whose name's last part is "part". Each must be a
definition of the class "cls" ("partial" or "safe"), and the name before its last dot must be a safe
definition or a theorem of the same module, type and level parameters. There must be at least
"floor" of them. -/
def checkTwins (part cls : String) (floor : Nat) : CommandElabM Unit := do
  let env ← getEnv
  if part.isEmpty then throwError "the guard on companions was given no last part of a name"
  unless cls == "partial" || cls == "safe" do throwError "the guard on companions was given a \
    class that it does not know: {cls}"
  let (n, bad) := env.constants.fold (fun ((n, bad) : Nat × Array String) c ci =>
    match c with
    | .str base s =>
      if s != part || originOf env c != .own then (n, bad) else
        let ofClass : Bool := match ci with
          | .defnInfo d => if cls == "safe" then d.safety == .safe else ci.isPartial
          | _ => false
        let why : List String :=
          (if ofClass then [] else ["it is no definition of the kernel's class " ++ cls]) ++
          (match env.find? base with
            | none => ["no constant has the name in front of the dot"]
            | some pi =>
              (match pi with
                | .defnInfo d => if d.safety == .safe then [] else ["in front of the dot stands \
                  neither a safe definition nor a theorem"]
                | .thmInfo _ => []
                | _ => ["in front of the dot stands neither a safe definition nor a theorem"]) ++
              (if moduleOf env base == moduleOf env c then [] else ["the constant in front of the \
                dot is declared in another module"]) ++
              (if pi.type == ci.type && pi.levelParams == ci.levelParams then [] else ["the \
                constant in front of the dot has another type"]))
        (n + 1, if why.isEmpty then bad else bad.push ("  " ++ toString c ++ ": " ++ "; \
          ".intercalate why))
    | _ => (n, bad)) (0, #[])
  logInfo m!"constants of this library whose name's last part is {part}: {n}; of these a \
    definition of the class {cls} beside a safe definition or a theorem of the same module and \
    type: {n - bad.size}"
  unless bad.isEmpty do
    throwError "the guard on companions refuses {bad.size} constants of this library whose name's \
      last part is {part} (why, and what to do: OnBytes/Guard/README.md, command 8):\n{
      "\n".intercalate (bad.qsort (· < ·)).toList}"
  if n < floor then
    throwError "the guard on companions refuses: it found {n} constants of this library whose \
      name's last part is {part}, and was told to find at least {floor}: does the call name the \
      right part? (OnBytes/Guard/README.md, command 8)"

/-- #guard_twins part cls floor: two strings and a number. -/
macro "#guard_twins " p:term:max c:term:max f:term:max : command =>
  `(run_cmd OnBytes.Guard.checkTwins $p $c $f)

/-- **The check.** No imported module that is this library's, or whose name's first part is in
"asOurs", has an entry under one of the named tables in the record of its compiled file; every named
table has entries in the other modules; no module of this library was written with a "module"
header. -/
def checkTables (tables asOurs : List Name) : CommandElabM Unit := do
  let env ← getEnv
  if tables.isEmpty then throwError "the guard on Lean's tables was given no table"
  let names := env.header.moduleNames
  let datas := env.header.moduleData
  unless names.size == datas.size do throwError "the guard on Lean's tables: the environment's \
    header has {names.size} module names and {datas.size} records"
  let mut ours := 0
  let mut bad : Array String := #[]
  let mut elsewhere : List (Name × Nat) := tables.map fun t => (t, 0)
  for i in [0:names.size] do
    let m := names[i]!
    let d := datas[i]!
    let own := !(coreRoots.contains m.getRoot || packageRoots.contains m.getRoot)
    if own || asOurs.contains m.getRoot then
      ours := ours + 1
      if own && d.isModule then bad := bad.push ("  " ++ toString m ++ ": written with a \
        \"module\" header: what such a file saves in a table may be filtered")
      for (t, es) in d.entries do
        if tables.contains t && es.size > 0 then bad := bad.push ("  " ++ toString m ++ ": \
          entries in " ++ toString t ++ ": " ++ toString es.size)
    else
      for (t, es) in d.entries do
        if tables.contains t then
          elsewhere := elsewhere.map fun (x, k) => if x == t then (x, k + es.size) else (x, k)
  logInfo m!"Lean's tables {toString tables}: imported modules that count as this library's: \
    {ours} (counted so for this call alone, by the first part of their names: {toString asOurs}); \
    findings: {bad.size}; entries in the other modules: {toString elsewhere}"
  unless bad.isEmpty do
    throwError "the guard on Lean's tables refuses; {bad.size} findings, at most 12 shown (why, \
      and what to do: OnBytes/Guard/README.md, command 9):\n{
      "\n".intercalate (bad.toList.take 12)}"
  let empty := (elsewhere.filter fun (_, k) => k == 0).map (·.1)
  unless empty.isEmpty do
    throwError "the guard on Lean's tables refuses: no other module of the environment has an \
      entry in {empty}: is the table's name right? A call that matches nothing guards nothing"

/-- #guard_tables tables asOurs: two terms of type List Lean.Name; the second is empty except in a
test. -/
macro "#guard_tables " t:term:max a:term:max : command => `(run_cmd OnBytes.Guard.checkTables $t $a)

/-- **The check.** Of the constructors of the inductive type "type", as Lean's own record of the
type lists them, those that are in the cone of the roots are exactly the names in "allowed". -/
def checkCtors (roots : List Name) (type : Name) (allowed : List Name) : CommandElabM Unit := do
  let env ← getEnv
  if roots.isEmpty then throwError "the guard on a type's constructors was given no function to \
    start from"
  let some (.inductInfo t) := env.find? type | throwError "the guard on a type's constructors: \
    {type} is no inductive type"
  let odd := allowed.filter fun n => !t.ctors.contains n
  unless odd.isEmpty do throwError "the guard on a type's constructors: no constructor of {type}: \
    {odd}"
  match coneOf env roots with
  | .error e => throwError "the guard on a type's constructors: {e}"
  | .ok cone =>
    let there := t.ctors.filter fun n => cone.contains n
    let new := there.filter fun n => !allowed.contains n
    let gone := allowed.filter fun n => !there.contains n
    unless new.isEmpty do throwError "the guard on a type's constructors refuses: in the cone of \
      {roots} stand these constructors of {type}, which the call does not allow: {new}"
    unless gone.isEmpty do throwError "the guard on a type's constructors refuses: allowed, but \
      not in the cone of {roots}: {gone}: strike them (a name without a user is an exception that \
      nobody needs)"
    logInfo m!"of the {t.ctors.length} constructors of {type}, in the cone of {roots} \
      ({cone.size} constants): {there}"

/-- #guard_ctors roots type allowed: a list of names, a name, a list of names. -/
macro "#guard_ctors " r:term:max t:term:max a:term:max : command =>
  `(run_cmd OnBytes.Guard.checkCtors $r $t $a)

/-- Does a part of the name begin with one of the strings? -/
def hasPartLike (starts : List String) : Name → Bool
  | .anonymous => false
  | .str p s => starts.any (fun x => s.startsWith x) || hasPartLike starts p
  | .num p _ => hasPartLike starts p

/-- **The check.** No constant of the environment, whatever its origin, has a name with a part that
begins with one of the strings. -/
def checkParts (starts : List String) : CommandElabM Unit := do
  let env ← getEnv
  if starts.isEmpty || starts.any (·.isEmpty) then throwError "the guard on the compiler's names \
    was given no beginning of a part of a name, or an empty one"
  let (n, bad) := env.constants.fold (fun ((n, bad) : Nat × Array Name) c _ =>
    (n + 1, if hasPartLike starts c then bad.push c else bad)) (0, #[])
  logInfo m!"constants of the environment: {n}; of these with a part of the name that begins with \
    one of {starts}: {bad.size}"
  if n == 0 then throwError "the guard on the compiler's names refuses: it found no constant at \
    all: a check of nothing"
  unless bad.isEmpty do
    throwError "the guard on the compiler's names refuses {bad.size} constants: a part of the name \
      begins like the name of a piece that Lean's compiler makes (why, and what to do: \
      OnBytes/Guard/README.md, command 11); at most 12 are \
      shown:\n{lines ((bad.qsort Name.lt).toList.take 12).toArray}"

/-- #guard_parts starts: a term of type List String. -/
macro "#guard_parts " p:term:max : command => `(run_cmd OnBytes.Guard.checkParts $p)

/-- **The check.** For every imported module that is this library's, or whose name's first part is
in "asOurs": every name in the module's own list of constants, as its compiled file has it, is given
to that very module by Lean's map from names to modules. -/
def checkHomes (asOurs : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let names := env.header.moduleNames
  let datas := env.header.moduleData
  unless names.size == datas.size do throwError "the guard on where names are at home: the \
    environment's header has {names.size} module names and {datas.size} records"
  let mut ours := 0
  let mut all := 0
  let mut astray : Array String := #[]
  for i in [0:names.size] do
    let m := names[i]!
    let own := !(coreRoots.contains m.getRoot || packageRoots.contains m.getRoot)
    if own || asOurs.contains m.getRoot then
      ours := ours + 1
      for c in datas[i]!.constNames do
        all := all + 1
        unless (env.getModuleIdxFor? c).map (·.toNat) == some i do
          astray := astray.push ("  " ++ toString c ++ ": declared in " ++ toString m ++
            ", given to " ++ toString (moduleOf env c))
  logInfo m!"imported modules that count as this library's: {ours} (counted so for this call \
    alone, by the first part of their names: {toString asOurs}); names in their own lists of \
    constants: {all}; of these given to another module by Lean's map: {astray.size}"
  if all == 0 then throwError "the guard on where names are at home refuses: it found no constant \
    of this library in an imported module: a check of nothing"
  unless astray.isEmpty do
    throwError "the guard on where names are at home refuses {astray.size} constants: Lean's map \
      gives the name to another module than the one that declares it, so the other guards would \
      take it for somebody else's (why, and what to do: OnBytes/Guard/README.md, command 12); at \
      most 12 are shown:\n{"\n".intercalate ((astray.qsort (· < ·)).toList.take 12)}"

/-- #guard_homes asOurs: a term of type List Lean.Name; empty except in a test. -/
macro "#guard_homes " a:term:max : command => `(run_cmd OnBytes.Guard.checkHomes $a)

/-- The positions, in the environment's list of modules, of the module "root" and of every module
that it imports, directly or through others, by the import lists in the modules' own compiled files.
An error if the header's names and records differ in number, if the root is not among the modules of
the environment, or if an import names a module that is not. -/
def modulesBelow (env : Environment) (root : Name) : Except String (Array Nat) := do
  let names := env.header.moduleNames
  let datas := env.header.moduleData
  unless names.size == datas.size do
    throw s!"the header has {names.size} names of modules and {datas.size} records"
  let mut idx : Std.HashMap Name Nat := {}
  for i in [0:names.size] do idx := idx.insert names[i]! i
  let some r := idx[root]?
    | throw s!"{root} is not among the modules that this file imports: does the call name the \
        program's root module?"
  let mut seen := (Array.replicate names.size false).set! r true
  let mut queue : Array Nat := #[r]
  -- a module enters the queue once, so the queue is never longer than the list of names
  for k in [0:names.size] do
    if k ≥ queue.size then break
    for imp in datas[queue[k]!]!.imports do
      let some j := idx[imp.module]?
        | throw s!"{names[queue[k]!]!} imports {imp.module}, which is not among the modules that \
            this file imports"
      unless seen[j]! do
        seen := seen.set! j true
        queue := queue.push j
  return queue

/-- **The check.** No module below "root", the root among them, has a name whose first part is in
"barred". -/
def checkImports (root : Name) (barred : List Name) : CommandElabM Unit := do
  let env ← getEnv
  if barred.isEmpty then throwError "the guard on imports was given no first part to bar"
  let below ← match modulesBelow env root with
    | .ok b => pure b
    | .error e => throwError "the guard on imports: {e}"
  let names := below.map (env.header.moduleNames[·]!)
  let parts := names.foldl (fun (a : Array (Name × Nat)) m =>
    match a.findIdx? (·.1 == m.getRoot) with
    | some i => a.modify i fun x => (x.1, x.2 + 1)
    | none => a.push (m.getRoot, 1)) #[]
  logInfo m!"modules below {root}, itself among them: {names.size}; by the first part of their \
    names: {parts.toList}"
  let bad := names.filter fun m => barred.contains m.getRoot
  unless bad.isEmpty do
    -- the imports that lead from a module that is not barred to one that is
    let arrows := below.foldl (init := (#[] : Array String)) fun a i =>
      let m := env.header.moduleNames[i]!
      if barred.contains m.getRoot then a else
        env.header.moduleData[i]!.imports.foldl (init := a) fun a imp =>
          if barred.contains imp.module.getRoot then a.push s!"  {m} imports {imp.module}" else a
    if arrows.isEmpty then
      throwError "the guard on imports refuses {bad.size} modules below {root}: the first part of \
        their names is one of {barred}, and so is the root's (why: OnBytes/Guard/README.md, \
        command 14)"
    throwError "the guard on imports refuses {bad.size} modules below {root}: the first part of \
      their names is one of {barred}. These imports bring them in; remove them (why: \
      OnBytes/Guard/README.md, command 14); at most 12 are shown:\n{
      "\n".intercalate (arrows.toList.take 12)}"

/-- #guard_imports root barred: terms of type Lean.Name and List Lean.Name. -/
macro "#guard_imports " r:term:max b:term:max : command =>
  `(run_cmd OnBytes.Guard.checkImports $r $b)

/-- The first parts that no module below the root of verify-on-bytes may have: Lean's library of the
elaborator and the compiler, Lake's, and the nine packages'. -/
def barredOfProgram : List Name := `Lean :: `Lake :: packageRoots

/-- The kind of a constant of whose value no theorem can speak: an axiom, opaque, unsafe or of the
class partial. None for any other. -/
def oddKind (ci : ConstantInfo) : Option String :=
  match ci with
  | .axiomInfo _ => some "an axiom"
  | .opaqueInfo _ => some "opaque"
  | _ => if ci.isUnsafe then some "unsafe" else if ci.isPartial then some "partial" else none

/-- Is the constant let through as one of Lean's helper constants? By its last name part alone, and
only a definition of the class partial. -/
def excused (part : String) (ci : ConstantInfo) : Bool :=
  ci.isPartial && (match ci.name with | .str _ s => s == part | _ => false)

/-- **The check.** Of the modules below "root" that are this library's, or whose name's first part
is in "asOurs": no constant in the module's own list is an axiom, opaque, unsafe or of the class
partial, except a definition of the class partial whose name's last part is "part" (Lean's helper
constants, which command 8 judges). It also refuses if it finds no constant at all. -/
def checkPlain (root : Name) (part : String) (asOurs : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let below ← match modulesBelow env root with
    | .ok b => pure b
    | .error e => throwError "the guard on kinds of constants: {e}"
  let mut mods := 0
  let mut all := 0
  let mut helpers := 0
  let mut bad : Array String := #[]
  for i in below do
    let m := env.header.moduleNames[i]!
    let own := !(coreRoots.contains m.getRoot || packageRoots.contains m.getRoot)
    if own || asOurs.contains m.getRoot then
      mods := mods + 1
      for ci in env.header.moduleData[i]!.constants do
        all := all + 1
        if let some w := oddKind ci then
          if excused part ci then helpers := helpers + 1
          else bad := bad.push ("  " ++ toString ci.name ++ ": " ++ w ++ ", in " ++ toString m)
  logInfo m!"modules below {root} that count as this library's: {mods} (counted so for this call \
    alone, by the first part of their names: {toString asOurs}); constants in their own lists: \
    {all}; of these helper constants by their last part {part}: {helpers}; axioms, opaque, unsafe \
    or partial beside these: {bad.size}"
  if all == 0 then throwError "the guard on kinds of constants refuses: it found no constant of \
    this library below {root}: a check of nothing"
  unless bad.isEmpty do
    throwError "the guard on kinds of constants refuses {bad.size} constants of this library in \
      the modules below {root}: each is an axiom, opaque, unsafe or partial, so no theorem can \
      speak of what it computes (what to do: OnBytes/Guard/README.md, command 15); at most 12 are \
      shown:\n{"\n".intercalate ((bad.qsort (· < ·)).toList.take 12)}"

/-- #guard_plain root part asOurs: terms of type Lean.Name, String and List Lean.Name; the last is
empty except in a test. -/
macro "#guard_plain " r:term:max p:term:max a:term:max : command =>
  `(run_cmd OnBytes.Guard.checkPlain $r $p $a)

/-- The functions that a compiled body calls or takes as closures, each with whether the call stands
in the last place, that is, whether its result is returned at once. A closure that is taken counts
as not in the last place. None if the body is nested deeper than fuel. -/
def placesOf (fuel : Nat) (b : IR.FnBody) (a : Array (Name × Bool)) :
    Option (Array (Name × Bool)) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match b with
    | .vdecl x _ v b => match v with
      | .fap f _ =>
        placesOf fuel b (a.push (f, match b with | .ret (.var y) => x == y | _ => false))
      | .pap f _ => placesOf fuel b (a.push (f, false))
      | _ => placesOf fuel b a
    | .jdecl _ _ v b => (placesOf fuel v a).bind (placesOf fuel b)
    | .case _ _ _ alts => alts.foldlM (fun a alt => placesOf fuel alt.body a) a
    | e => if e.isTerminal then some a else placesOf fuel e.body a

/-- The rings of a graph on the numbers below adj.size, where adj[v] lists the numbers that v points
at: two numbers are in one ring if each can be reached from the other. Returns each number's ring
and each ring's size. Two passes: the order in which a walk in depth leaves the numbers, then a walk
against the arrows in the reverse of that order. -/
def ringsOf (adj : Array (Array Nat)) : Array Nat × Array Nat := Id.run do
  let n := adj.size
  let steps := 2 * (n + adj.foldl (fun k l => k + l.size) 0) + 2
  let mut seen := Array.replicate n false
  let mut order : Array Nat := #[]
  for s in [0:n] do
    unless seen[s]! do
      seen := seen.set! s true
      let mut st : Array (Nat × Nat) := #[(s, 0)]
      for _ in [0:steps] do
        if st.isEmpty then break
        let (v, k) := st.back!
        if k < adj[v]!.size then
          st := st.set! (st.size - 1) (v, k + 1)
          let w := adj[v]![k]!
          if w < n && !seen[w]! then
            seen := seen.set! w true
            st := st.push (w, 0)
        else
          st := st.pop
          order := order.push v
  let mut back : Array (Array Nat) := Array.replicate n #[]
  for v in [0:n] do
    for w in adj[v]! do
      if w < n then back := back.modify w (·.push v)
  let mut ring := Array.replicate n n
  let mut sizes : Array Nat := #[]
  for s in order.reverse do
    if ring[s]! == n then
      let r := sizes.size
      let mut size := 0
      ring := ring.set! s r
      let mut st : Array Nat := #[s]
      for _ in [0:steps] do
        if st.isEmpty then break
        let v := st.back!
        st := st.pop
        size := size + 1
        for w in back[v]! do
          if ring[w]! == n then
            ring := ring.set! w r
            st := st.push w
      sizes := sizes.push size
  return (ring, sizes)

/-- **The check.** Visits every compiled declaration that calls and closures reach from the roots. A
declaration is deep if it calls itself from a place that is not the last, or calls another
declaration of its ring (one from which it can be reached again) from any place. The constants from
which the deep declarations are made ("baseOf") are exactly the names in "allowed", by their printed
form. -/
def checkRings (roots : List Name) (allowed : List String) : CommandElabM Unit := do
  let env ← getEnv
  if roots.isEmpty then throwError "the guard on recursion was given no function to start from"
  let tbl := allCompiled env
  for r in roots do
    unless tbl.contains r do throwError "the guard on recursion: {r} has no compiled code on record"
  let mut idx : Std.HashMap Name Nat := {}
  let mut nodes : Array Name := #[]
  for r in roots do
    unless idx.contains r do
      idx := idx.insert r nodes.size
      nodes := nodes.push r
  let mut adj : Array (Array (Nat × Bool)) := #[]
  for i in [0:100000000] do
    if i ≥ nodes.size then break
    let mut out : Array (Nat × Bool) := #[]
    if let some (.fdecl (body := b) ..) := tbl[nodes[i]!]? then
      let some calls := placesOf 1000000 b #[]
        | throwError "the guard on recursion: the body of {nodes[i]!} is nested too deep to be read"
      for (f, last) in calls do
        let k ← match idx[f]? with
          | some k => pure k
          | none => do
            let k := nodes.size
            idx := idx.insert f k
            nodes := nodes.push f
            pure k
        out := out.push (k, last)
    adj := adj.push out
  unless adj.size == nodes.size do throwError "the guard on recursion: the walk did not end"
  let (ring, sizes) := ringsOf (adj.map fun l => l.map (·.1))
  let mut loops := 0
  let mut deep : Array (String × Name) := #[]
  for v in [0:nodes.size] do
    let inRing := adj[v]!.filter fun (w, _) =>
      ring[w]! == ring[v]! && (sizes[ring[v]!]! > 1 || w == v)
    if inRing.any fun (w, last) => !(last && w == v) then
      deep := deep.push (toString ((baseOf env nodes[v]!).getD nodes[v]!), nodes[v]!)
    else if !inRing.isEmpty then loops := loops + 1
  let found := deep.foldl (fun (a : Array String) x => if a.contains x.1 then a else a.push x.1) #[]
  logInfo m!"compiled code below {roots}: {nodes.size} declarations; that call themselves in the \
    last place alone, and no other of their ring (loops): {loops}; deep, that is with another call \
    into their own ring: {deep.size}, made from {found.size} constants; the closed list has \
    {allowed.length} names\n{lines ((deep.qsort fun a b => a.1 < b.1 || (a.1 == b.1 &&
      a.2.toString < b.2.toString)).map fun x => Name.mkSimple (x.1 ++ ": " ++ toString x.2))}"
  let twice := allowed.filter fun s => allowed.count s > 1
  unless twice.isEmpty do throwError "the guard on recursion: these names stand on the list more \
    than once: {twice.eraseDups}"
  let gone := allowed.filter fun s => !found.contains s
  unless gone.isEmpty do throwError "the guard on recursion: these names are on the list but no \
    deep declaration below the roots is made from them: strike them:\n{"\n".intercalate
      (gone.map ("  " ++ ·))}"
  let new := found.filter fun s => !allowed.contains s
  unless new.isEmpty do throwError "the guard on recursion refuses these constants: compiled code \
    below {roots} that is made from them calls back into its own ring otherwise than by a last \
    call to itself, so its stack can grow with the depth of the recursion, and the closed list \
    does not name them (what to do: OnBytes/Guard/README.md, command 13):\n{"\n".intercalate
      ((new.qsort (· < ·)).toList.map ("  " ++ ·))}"

/-- #guard_rings roots list: terms of type List Lean.Name and List String. -/
macro "#guard_rings " r:term:max a:term:max : command =>
  `(run_cmd OnBytes.Guard.checkRings $r $a)

/-- The functions by which the program judges: the function that the root calls, those that read the
arguments and the files and hand them to a check, those that turn a verdict into the printed line
and the exit code, and the checks themselves. The checks on a model's files are the texts over a
monad of OnBytes/ChecksWithHashAsArgument/M/, taken at the identity monad (OnBytes/Shell/Front.lean, checksAt), with
the two hash functions that are laid into them. That formatHashFastForm and secondHashFunctionTree are in the cone does not show
that they are what is laid in: planLines (OnBytes/Shell/Whole.lean) names formatHashFastForm, and requestItemOf
(OnBytes/ChecksWithHashAsArgument/M/Proof/RequestItem.lean) names secondHashFunctionTree, whatever checksAt is given. No command of
this folder reads the arguments of checksAt in frontChecks; what holds them is the theorem
programFront_eq (OnBytes/Shell/FrontSame.lean), which the guard file does not import. The names, the
places and the first tests are those of modelChecks. Model.Verify.wholeCall, keyCall, leafCall
and planBytes are in main's cone, since checksAt is written as modelChecks with four fields
replaced; they judge nothing and are not listed. Since they stand in the cone, a name on a list that
only they use is not reported as gone.
Written with a single backtick, since no program stands below this file: a name that does not exist
is in no cone, and the command refuses it. -/
def judges : List Name :=
  [`OnBytes.Shell.programFront, `OnBytes.Shell.frontChecks, `OnBytes.Shell.checksAt,
   `OnBytes.Shell.mainIO, `OnBytes.Shell.call, `OnBytes.Shell.kindOf,
   `OnBytes.Shell.Kind.run, `OnBytes.Shell.readOptions, `OnBytes.Shell.partOptions,
   `OnBytes.Shell.whole, `OnBytes.Shell.keyPart, `OnBytes.Shell.leafPart, `OnBytes.Shell.planCall,
   `OnBytes.Shell.judgeFiles, `OnBytes.Shell.earlyEnd, `OnBytes.Shell.partEnd,
   `OnBytes.Shell.finish, `OnBytes.Shell.finishTest, `OnBytes.Shell.finishWork,
   `OnBytes.Shell.before, `OnBytes.Shell.verdict, `OnBytes.Shell.Line.text, `OnBytes.Shell.shown,
   `OnBytes.Shell.num, `OnBytes.Shell.hex64, `OnBytes.Shell.sayAll, `OnBytes.Shell.lastSay,
   `OnBytes.Shell.unwritten, `OnBytes.Shell.faultWith, `OnBytes.Shell.fetch, `OnBytes.Shell.need,
   `OnBytes.Shell.needAll, `OnBytes.Shell.Ending.status, `OnBytes.Shell.Checks.lists,
   `OnBytes.Shell.modelChecks, `OnBytes.Shell.readIO, `OnBytes.Shell.readBody,
   `OnBytes.Shell.readUpTo, `OnBytes.Shell.readOf, `OnBytes.Shell.nameOf, `OnBytes.Shell.codeOf,
   `OnBytes.Shell.Unread.ofCode, `OnBytes.Shell.outIO, `OnBytes.Shell.errIO, `OnBytes.Shell.Ask.run,
   `OnBytes.TwoPort.M.Model.Verify.wholeCall, `OnBytes.TwoPort.M.Model.Verify.keyCall,
   `OnBytes.TwoPort.M.Model.Verify.leafCall, `OnBytes.TwoPort.M.Model.Verify.planBytes,
   `OnBytes.TwoPort.M.Key.check, `OnBytes.TwoPort.M.Entry.check, `OnBytes.TwoPort.M.Proof.check,
   `OnBytes.formatHashFastForm, `OnBytes.secondHashFunctionTree, `OnBytes.Model.Verify.entryNumber,
   `OnBytes.Model.Stages.CallEnd.status, `OnBytes.Shell.product, `OnBytes.Shell.links,
   `OnBytes.Shell.key, `OnBytes.Shell.entry, `OnBytes.Shell.toyProof, `OnBytes.Toy.product,
   `OnBytes.Toy.links, `OnBytes.Key.check, `OnBytes.Entry.check, `OnBytes.Proof.toyCall,
   `OnBytes.Shell.planLines, `OnBytes.Shell.toyKind, `OnBytes.Shell.cutBits,
   `OnBytes.Shell.ownNames, `OnBytes.Shell.badWords, `OnBytes.Shell.closingPart,
   `OnBytes.Shell.closingWhole, `OnBytes.Shell.inList]

/-- Lean core's own constants in the cone of the main of verify-on-bytes whose compiled code is not
made from their definition. A literal list, written here, where no program is imported.
Six reach outside the program, and they alone of the list have a type in IO: IO.FS.Handle.mk,
IO.FS.Handle.read, System.FilePath.metadata, System.FilePath.symlinkMetadata, IO.getStdout,
IO.getStderr. A seventh, System.Platform.getNumBits, asks the machine for its word size.
symlinkMetadata asks for the metadata of a path and follows no link; it reads, and writes nothing.
The program asks it only after the reading of a file has failed with "no such file", to tell a name
that does not exist from a link that leads nowhere (OnBytes/Shell/Ops.lean, nameOf), and uses
nothing of the answer but whether there was one. An eighth acts outside when compiled: panicCore,
for the kernel the default value of its type, prints a message (OnBytes/Guard/README.md, command 5,
limits).
The names under Lean.Name come from default tactics in binder types (of List.merge, List.mergeSort
and a loop over a range); no compiled declaration below main is made from them (seen by asking Lean,
by names, but not of the main that stands on programFront; no command checks it).
lcProof, unsafeCast and the names with Unsafe belong to the fast forms in which Lean's core compiles
loops over arrays and a few other functions. Most of the rest is arithmetic, arrays, byte arrays,
lists and strings. -/
def coreOfProgram : List String :=
  ["Acc.rec", "Array.anyM", "Array.anyMUnsafe", "Array.emptyWithCapacity", "Array.foldlM",
   "Array.foldlMUnsafe", "Array.foldrM", "Array.foldrMUnsafe", "Array.forIn'", "Array.forIn'Unsafe",
   "Array.get!Internal", "Array.getInternal", "Array.instDecidableEq", "Array.mapM",
   "Array.mapMUnsafe", "Array.mk", "Array.mkEmpty", "Array.modifyM", "Array.modifyMUnsafe",
   "Array.pop", "Array.push", "Array.replicate", "Array.set", "Array.set!", "Array.size",
   "Array.swap", "Array.toList", "Array.uget", "Array.uset", "Array.usize", "ByteArray.append",
   "ByteArray.copySlice", "ByteArray.data", "ByteArray.emptyWithCapacity", "ByteArray.get",
   "ByteArray.get!", "ByteArray.mk", "ByteArray.push", "ByteArray.size", "ByteArray.uget",
   "ByteArray.validateUTF8", "Char.ofNatAux", "IO.FS.Handle", "IO.FS.Handle.mk",
   "IO.FS.Handle.read", "IO.RealWorld.nonemptyType", "IO.getStderr", "IO.getStdout", "Int.add",
   "Int.decEq", "Int.decLe", "Int.decLt", "Int.ediv", "Int.emod", "Int.mul", "Int.natAbs",
   "Int.neg", "Int.negSucc", "Int.ofNat", "Int.sub", "Int.tdiv", "Lean.Name.anonymous",
   "Lean.Name.anonymous._override", "Lean.Name.hash", "Lean.Name.hash._override", "Lean.Name.str",
   "Lean.Name.str._override", "List.append", "List.attachWith", "List.dropLast", "List.filter",
   "List.filterMap", "List.flatMap", "List.flatten", "List.foldr", "List.intercalate",
   "List.intersperse", "List.length", "List.map", "List.merge", "List.mergeSort", "List.replicate",
   "List.set", "List.take", "List.takeWhile", "List.zipIdx", "List.zipWith", "Nat.add", "Nat.all",
   "Nat.beq", "Nat.ble", "Nat.decEq", "Nat.decLe", "Nat.decLt", "Nat.div", "Nat.fold", "Nat.land",
   "Nat.log2", "Nat.mod", "Nat.mul", "Nat.pow", "Nat.rec", "Nat.repr", "Nat.shiftLeft",
   "Nat.shiftRight", "Nat.sub", "Nat.xor", "String.Internal.append", "String.Pos.Raw.atEnd",
   "String.Pos.Raw.extract", "String.Pos.Raw.get", "String.Pos.Raw.next",
   "String.Slice.Pattern.Internal.memcmpStr", "String.append", "String.decEq", "String.getUTF8Byte",
   "String.hash", "String.length", "String.ofByteArray", "String.ofList", "String.push",
   "String.toList", "String.toUTF8", "String.utf8ByteSize", "System.FilePath.metadata",
   "System.FilePath.symlinkMetadata", "System.Platform.getNumBits", "UInt32.add", "UInt32.decEq",
   "UInt32.decLe", "UInt32.decLt", "UInt32.ofBitVec", "UInt32.ofNat", "UInt32.sub",
   "UInt32.toBitVec", "UInt32.toNat", "UInt64.add", "UInt64.decEq", "UInt64.decLe", "UInt64.decLt",
   "UInt64.land", "UInt64.lor", "UInt64.mul", "UInt64.ofNat", "UInt64.ofNatLT", "UInt64.shiftLeft",
   "UInt64.shiftRight", "UInt64.sub", "UInt64.toBitVec", "UInt64.toNat", "UInt64.toUInt8",
   "UInt64.toUSize", "UInt64.xor", "UInt8.decEq", "UInt8.decLe", "UInt8.decLt", "UInt8.land",
   "UInt8.ofNat", "UInt8.shiftRight", "UInt8.toBitVec", "UInt8.toNat", "UInt8.toUInt64",
   "USize.add", "USize.decEq", "USize.decLt", "USize.land", "USize.ofNat", "USize.ofNatLT",
   "USize.repr", "USize.sub", "USize.toBitVec", "USize.toNat", "Void.nonemptyType",
   "WellFounded.fix", "WellFounded.fixF", "_private.Init.Data.Array.Basic.0.Array.anyMUnsafe.any",
   "_private.Init.Data.Array.Basic.0.Array.foldlMUnsafe.fold",
   "_private.Init.Data.Array.Basic.0.Array.foldrMUnsafe.fold",
   "_private.Init.Data.Array.Basic.0.Array.forIn'Unsafe.loop",
   "_private.Init.Data.Array.Basic.0.Array.mapMUnsafe.map",
   "_private.Init.Data.Array.Basic.0.Array.modifyMUnsafe._proof_1",
   "_private.Init.Data.List.Attach.0.List.attachWithImpl", "lcProof", "mixHash", "panicCore",
   "unsafeCast", "unsafeCast._proof_1"]

/-- Constants from which deep declarations below the main of verify-on-bytes are made (their
compiled code calls back into its own ring of recursion otherwise than by a last call to itself),
and whose depth at their callers is bounded by a constant of the format or of the program's text
or by a test on a public number that runs before the call, or is the logarithm of a number or of a
length. OnBytes/Guard/README.md has a row for each name. The bounds were read off the code; no
program checks a bound and no command holds it. A literal list, written here, where no program is
imported. -/
def ringsBounded : List String :=
  ["Fmt.drawFN", "Fmt.leNat", "Fmt.rdItems", "Fmt.rdMany", "OnBytes.Lkp.cubesLoop",
   "OnBytes.Lkp.keyTrees", "OnBytes.Lkp.liveLoop", "OnBytes.Lkp.partSteps", "OnBytes.Lkp.tieSteps",
   "OnBytes.Model.Head.callsFrom", "OnBytes.Model.Head.lineSegs", "OnBytes.Model.Layer.layParts",
   "OnBytes.Model.Layer.layTables", "OnBytes.Model.Layer.layTensors",
   "OnBytes.Model.Layer.plansFrom", "OnBytes.Model.Layer.takeCalls",
   "OnBytes.Model.Layer.takeSegments", "OnBytes.Model.Stages.leastWork",
   "OnBytes.Model.Verify.withReply", "OnBytes.Model.WsLay.place", "OnBytes.Model.piecesBelow",
   "OnBytes.Model.piecesOfSize", "OnBytes.Model.t2BLLoop", "OnBytes.Model.wsDigits",
   "OnBytes.Params.ioppStages", "OnBytes.Params.listOfGroups", "OnBytes.Params.reqMoments",
   "OnBytes.Params.solveLater", "OnBytes.Params.stagesOf", "OnBytes.Plan.scanLine",
   "OnBytes.Proof.toyClaimRows", "OnBytes.Psc.hearMany", "OnBytes.Shell.needAll",
   "OnBytes.Shell.sayAll", "OnBytes.Tensor.spreadTo", "OnBytes.Wf.weightsFrom",
   "OnBytes.choicePairs", "OnBytes.denseIndex", "OnBytes.denseNumber", "OnBytes.dotSteps",
   "OnBytes.foldRounds", "OnBytes.productIndex", "OnBytes.recvVectors", "OnBytes.squaresOf",
   "OnBytes.stretchBlocks",
   "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR₂.run",
   "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR₂.run'"]

/-- The other such constants: no bound is known at every caller. The depth of these recursions may
be as great as a file says, or depends on who calls them: functions of Lean's core that many callers
share are here. A file that drives one of them deep enough ends the program with a stack overflow;
it cannot turn a refusal into a yes. -/
def ringsOpen : List String :=
  ["Fmt.Dr.times", "List.foldr", "List.hasDecEq", "List.zipWith", "OnBytes.Psc.hidingWalk",
   "OnBytes.Send.seedsOf", "Std.DHashMap.Internal.AssocList.replace"]

/-- Both lists, for #guard_rings. Joined here and not in the guard file, for the reason given at
"coreOfProgram" in OnBytes/Guard/README.md (command 5). -/
def ringsOfProgram : List String := ringsBounded ++ ringsOpen

end OnBytes.Guard
