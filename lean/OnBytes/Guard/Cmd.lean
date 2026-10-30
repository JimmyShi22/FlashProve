-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Guard/Cmd.lean: the guard commands #guard_pinned and #guard_compiled.

A theorem is about definitions; a program runs compiled code. Lean lets the two differ where a
constant carries a mark: a rule for the compiler (csimp), implemented_by, extern, opaque, unsafe or
partial. Four commands look below main for every such mark that Lean has on record, and compare the
names that the compiler's output calls with the names in the kernel's terms. They do not compare
compiled code with a definition. The guards catch a slip and the plain written forms. They do not
stop someone who runs code at compile time in a file below main. OnBytes/Guard/Program.lean calls
the commands on "main" of verify-on-bytes. If one rejects something, that file does not compile and
the default build fails. This file imports no program, and no program imports it.

 1  #guard_csimp (Csimp.lean): every compiler rule on record is a theorem that depends only on the
    three standard axioms.
 2  #guard_cone (Cone.lean): of the constants that main uses, by the kernel's terms, none whose
    compiled code is not made from its definition belongs to this library.
 3  #guard_pinned (this file): nor does one belong to a package, except those on the command's list,
    which is empty in the guard file.
 4  #guard_compiled (this file): the same for the declarations from which the C files are written;
    and these call no function of this library or of a package that no kernel term below main
    mentions, except for fragments that the compiler has made (known by their names; see the page).
Commands 5 to 15 are in Core.lean.

The tests on listed recursors (checkPinned, with Allow.lean) are for a program that imports Mathlib.
The Lean text verify-on-bytes does not: only the last part of (e) runs. None of them is tested.

What each command checks in full, why it is there, what to do when it rejects, and its limits:
OnBytes/Guard/README.md.
-/
import OnBytes.Guard.Csimp
import OnBytes.Guard.Cone
import OnBytes.Guard.Allow

set_option autoImplicit false

namespace OnBytes.Guard

open Lean Elab Command

/-- Every constant of the cone of the roots: OnBytes.Guard.walk's loop, keeping all that it sees. -/
def coneOf (env : Environment) (roots : List Name) : Except String (Array Name) := do
  let mut seen : NameSet := roots.foldl (fun s n => s.insert n) {}
  let mut stack : Array Name := roots.toArray
  let mut out : Array Name := #[]
  -- a constant goes on the stack once (a root as often as roots names it), so an environment of
  -- fewer than 10^8 constants does not meet the bound; if constants are left when it is met, the
  -- walk fails below. The loop stands in for a while loop
  for _ in [0:100000000] do
    match stack.back? with
    | none => break
    | some c =>
      stack := stack.pop
      out := out.push c
      match env.find? c with
      | none => throw s!"{c} does not exist"
      | some ci =>
        for n in nextOf env c ci do
          unless seen.contains n do
            seen := seen.insert n
            stack := stack.push n
  unless stack.isEmpty do throw "the walk did not end"
  return out

/-- The later of two origins in the order core, packages, own. -/
def later (a b : Origin) : Origin :=
  if a == .own || b == .own then .own
  else if a == .packages || b == .packages then .packages
  else .core

/-- Why c is listed, if it is, and to whom the entry belongs: the latest of the origins of the
constant, of the function that stands in for it, and of the rule that replaces it. -/
def rowOf (env : Environment) (c : Name) : Option (Finding × Origin) :=
  match env.find? c with
  | none => none
  | some ci =>
    let marks := whyListed env c ci
    -- the function that stands in for c without an equation, if any, counts too. (Lean refuses such
    -- a mark on a declaration of an imported module: Lean/Attributes.lean:285, v4.29.1; so this is
    -- a second lock.)
    let o := match Compiler.getImplementedBy? env c with
      | some g => later (originOf env c) (originOf env g)
      | none => originOf env c
    match (Compiler.CSimp.ext.getState env).map.find? c with
    | some e =>
      let proved := match env.find? e.thmName with
        | some (.thmInfo _) => "a theorem"
        | _ => "NOT a theorem: trusted, see OnBytes/Guard/Allow.lean"
      some (⟨c, marks ++ [s!"compiled as {e.toDeclName}, by the rule {e.thmName} \
        ({proved})"]⟩, later o (originOf env e.thmName))
    | none => if marks.isEmpty then none else some (⟨c, marks⟩, o)

/-- The constants that may mention a pinned recursor (one that the list of #guard_pinned names), by
name, in addition to the case-split functions of its own type. One type, three constants (the third
is the function that the rule for List.brecOn.go puts in its place; its name cannot be written, so
"checkPinned" looks it up). The kernel's form of every structural recursion on a list is f ->
List.brecOn -> List.brecOn.go -> List.rec, with the type former List.below next to it. No other type
and no pattern is allowed. This leaves a gap: check (c) cannot tell a direct call of List.brecOn in
this library from a structural recursion (it can for recOn and sizeOf, which mention List.rec
themselves). Check (e) is there for that gap: if List.brecOn is pinned too, only a constant that
Lean's structural-recursion elaborator has on record may mention it. That record is public in Lean,
so code of this library could add to it. OnBytes/Guard/README.md describes (c) and (e). -/
def namersByName : List (Name × List Name) := [(``List.rec, [``List.below, ``List.brecOn.go])]

/-- Constants that check (c) accepts for a pinned recursor without a reason. The list is empty and
should stay empty; the command prints it at every build if it is not. -/
def namersOpen : List (Name × List Name) := []

/-- **The check.** A constant is "listed" if "rowOf" has a row for it, and "pinned" if the argument
pinned names it. Refuses every listed constant of the cone that is not Lean core's, is not pinned,
and is not the function that the rule of a pinned constant puts in its place. Also fails if a pinned
name is not among the listed constants of a package or of this library, or if one of the tests (a),
(b), (c), (e) of OnBytes/Guard/README.md fails. -/
def checkPinned (roots : List Name) (pinned : List Name) : CommandElabM Unit := do
  let env ← getEnv
  if roots.isEmpty then throwError "the pinned guard was given no function to start from"
  match coneOf env roots with
  | .error e => throwError "the pinned guard: {e}"
  | .ok cone =>
    let rows := cone.filterMap (rowOf env)
    let show1 := fun (fs : Array (Finding × Origin)) =>
      MessageData.joinSep
        ((fs.qsort fun a b => Name.lt a.1.name b.1.name).toList.map fun f =>
          m!"  {f.1.name}: {", ".intercalate f.1.why}") "\n"
    let core := rows.filter fun r => r.2 == .core
    let pkgs := rows.filter fun r => r.2 == .packages
    let own := rows.filter fun r => r.2 == .own
    -- the function that a pinned constant's rule puts in its place is pinned with it (Mathlib gives
    -- these functions names that cannot be written down)
    let behind := pinned.filterMap fun n =>
      ((Compiler.CSimp.ext.getState env).map.find? n).map (·.toDeclName)
    let refused := (pkgs ++ own).filter fun r =>
      !pinned.contains r.1.name && !behind.contains r.1.name
    logInfo m!"the cone of {roots}: {cone.size} constants, {rows.size} of them listed; Lean \
      core's own, not shown here: {core.size}\n\
      MATHLIB AND PACKAGES: {pkgs.size}\n{show1 pkgs}\n\
      THIS LIBRARY: {own.size}\n{show1 own}"
    -- a pinned name that this cone does not list is an error: otherwise a name that nothing uses
    -- would stay on the list
    let stale := pinned.filter fun n => !(pkgs ++ own).any fun r => r.1.name == n
    -- every pinned recursor is tested again at every build: (a) it is a recursor declared in Lean's
    -- core; (b) exactly one rule for the compiler is on record for it, the pair of the recursor and
    -- the rule's module is on OnBytes/Guard/Allow.lean's list, and the function on the rule's right
    -- side is declared in the rule's module
    let mut failed : Array MessageData := #[]
    let allRules := (csimpRules env).2
    for n in pinned do
      if let some (.recInfo _) := env.find? n then
        unless originOf env n == .core do failed := failed.push m!"  {n}: (a) it is not declared \
          in Lean's core"
        let mine := allRules.filter fun r => (env.find? r).bind leftOf == some n
        unless mine.size == 1 do failed := failed.push m!"  {n}: (b) {mine.size} rules for the \
          compiler are on record for it, not one: {mine}"
        for r in mine do
          unless mathlibRecursors.contains (n, moduleOf env r) do
            failed := failed.push m!"  {n}: (b) the pair ({n}, {moduleOf env r}) is not on the \
              list of OnBytes/Guard/Allow.lean"
          unless moduleOf env (((env.find? r).bind rightOf).getD .anonymous) == moduleOf env r do
            failed := failed.push m!"  {n}: (b) the right side of its rule {r} is declared in \
              another module than the rule"
    -- (c) who NAMES a pinned recursor in this cone (the walk's own step): only functions that are
    -- casesOn-like by Lean's own test, of the recursor's own type; and, for the recursors in
    -- "namersByName", the constants written there
    -- and the functions that the rules of these constants put in their place
    for n in pinned do
      if let some (.recInfo rv) := env.find? n then
        let ind := rv.getMajorInduct
        let extra := ((namersByName.find? fun p => p.1 == n).map (·.2)).getD [] ++
          ((namersOpen.find? fun p => p.1 == n).map (·.2)).getD []
        let extraBehind := extra.filterMap fun x =>
          ((Compiler.CSimp.ext.getState env).map.find? x).map (·.toDeclName)
        for c in cone do
          let some ci := env.find? c | continue
          unless (nextOf env c ci).contains n do continue
          if extra.contains c || extraBehind.contains c then continue
          let like ← if isCasesOnLike env c then (do
              let info? ← liftCoreM (getCasesInfo? c)
              pure (info?.any fun i => i.indName == ind)) else pure false
          unless like do failed := failed.push m!"  {n}: (c) it is named by {c}, which is neither \
            casesOn-like for {ind} by Lean's own test nor written in namersByName"
    -- (e) the course-of-values recursors: a constant may name a pinned T.brecOn only if Lean's
    -- structural-recursion elaborator made it (its record: Lean.Elab.Structural.eqnInfoExt): such a
    -- function is compiled from its text as written, not from the brecOn term; a direct call is not
    -- on that record.
    -- T.brecOn.go may be named only by T.brecOn and by the function that T.brecOn's rule puts in
    -- its place; a type former written in namersByName (List.below) only by these, by T.brecOn.go
    -- and its stand-in, and by constants on the record. The test on the type former does not look
    -- at the pinned list: it runs even if that list is empty.
    let onRecord := fun (c : Name) => (Lean.Elab.Structural.eqnInfoExt.find? env c).isSome
    let behindOf := fun (x : Name) =>
      (((Compiler.CSimp.ext.getState env).map.find? x).map (·.toDeclName)).toList
    let namersOf := fun (x : Name) => cone.filter fun c =>
      match env.find? c with
      | some ci => (nextOf env c ci).contains x
      | none => false
    for n in pinned do
      if isBRecOnRecursor env n then
        for c in namersOf n do
          unless onRecord c do failed := failed.push m!"  {n}: (e) it is named by {c}, which is \
            not on record as made by Lean's structural-recursion elaborator: an outright call?"
        let go := Name.str n "go"
        for c in namersOf go do
          unless c == n || (behindOf n).contains c do failed := failed.push m!"  {go}: (e) it is \
            named by {c}, which is neither {n} nor the function that its rule puts in its place"
    for (r, xs) in namersByName do
      let .str t _ := r | continue
      let family := [Name.str t "brecOn", Name.str (Name.str t "brecOn") "go"]
      let family := family ++ family.flatMap behindOf
      for x in xs do
        unless x == Name.str t "below" do continue
        for c in namersOf x do
          unless onRecord c || family.contains c do failed := failed.push m!"  {x}: (e) it is \
            named by {c}, which is neither on the structural-recursion record nor one of {family}"
    unless namersOpen.isEmpty do
      logInfo m!"Accepted without a reason: test (c) lets these namers (and the functions \
        that their rules put in their place) stand: {namersOpen}"
    unless stale.isEmpty do
      throwError "the pinned guard: these names are pinned but this cone does not list them: \
        strike them from the list (a pin without a user is an exception that nobody \
        needs):\n{lines stale.toArray}"
    unless failed.isEmpty do
      throwError "the pinned guard: a pinned recursor fails its \
        tests:\n{MessageData.joinSep failed.toList "\n"}"
    unless refused.isEmpty do
      throwError "the pinned guard refuses these constants: they are in the cone of {roots}, \
        their compiled code is not made from their definition, they are not Lean core's, \
        and the list does not name them:\n{show1 refused}"

/-- #guard_pinned roots pinned: both are terms of type List Lean.Name. -/
macro "#guard_pinned " r:term:max p:term:max : command => `(run_cmd OnBytes.Guard.checkPinned $r $p)

/-! ## The fourth command: the compiler's own output -/

/-- the functions that a compiled body calls or takes as closures; `none` if the body is nested
deeper than `fuel`, so that a part of it would go unread -/
def callsOf (fuel : Nat) (b : IR.FnBody) (a : Array Name) : Option (Array Name) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match b with
    | .vdecl _ _ v b => match v with
      | .fap f _ => callsOf fuel b (a.push f)
      | .pap f _ => callsOf fuel b (a.push f)
      | _ => callsOf fuel b a
    | .jdecl _ _ v b => (callsOf fuel v a).bind (callsOf fuel b)
    | .case _ _ _ alts => alts.foldlM (fun a alt => callsOf fuel alt.body a) a
    | e => if e.isTerminal then some a else callsOf fuel e.body a

/-- every compiled declaration on record: those of the imported modules and those of the file that
is being compiled -/
def allCompiled (env : Environment) : Std.HashMap Name IR.Decl := Id.run do
  let mut tbl : Std.HashMap Name IR.Decl := {}
  for i in [0:env.header.moduleNames.size] do
    for d in IR.declMapExt.getModuleEntries env i do tbl := tbl.insert d.name d
    -- where both are there, this one has the body
    for d in IR.declMapExt.getModuleIREntries env i do tbl := tbl.insert d.name d
  for d in IR.getDecls env do tbl := tbl.insert d.name d
  return tbl

/-- for a name with macro scopes (‹name›._@.‹module›._hygCtx._hyg.‹k›): the compiler puts its
suffixes (_redArg, _lam_0 ..) BEFORE the scopes, so the prefixes of ‹name› are tried under the same
scopes -/
def underScopes (env : Environment) (v : MacroScopesView) : Name → Option Name
  | .anonymous => none
  | p@(.str q _) =>
    let c := { v with name := p }.review
    if env.contains c then some c else underScopes env v q
  | p@(.num q _) =>
    let c := { v with name := p }.review
    if env.contains c then some c else underScopes env v q

/-- For a name with macro scopes: the constant it is made from, by "underScopes"; else none. -/
def scoped? (env : Environment) (n : Name) : Option Name :=
  if n.hasMacroScopes then let v := extractMacroScopes n; underScopes env v v.name else none

/-- the constant of the kernel from which a compiled declaration is made: the longest prefix of its
name that is a constant, macro scopes kept -/
def baseOf (env : Environment) : Name → Option Name
  | .anonymous => none
  | n@(.str p _) => if env.contains n then some n else (scoped? env n).orElse fun _ => baseOf env p
  | n@(.num p _) => if env.contains n then some n else (scoped? env n).orElse fun _ => baseOf env p

/-- g ↦ the constants in whose place implemented_by (the stand-in mark, with no equation) puts g -/
def standIns (env : Environment) : NameMap (List Name) := Id.run do
  let mut m : NameMap (List Name) := {}
  for es in (Compiler.implementedByAttr.ext.toEnvExtension.getState env).importedEntries do
    for (c, g) in es do m := m.insert g (c :: (m.find? g).getD [])
  return (Compiler.implementedByAttr.ext.getState env).2.foldl
    (fun m c g => m.insert g (c :: (m.find? g).getD [])) m

/-- g ↦ the rules for the compiler whose right side is g -/
def rightSides (env : Environment) : NameMap (List Compiler.CSimp.Entry) :=
  (Compiler.CSimp.ext.getState env).map.fold
    (fun m _ e => m.insert e.toDeclName (e :: (m.find? e.toDeclName).getD [])) {}

/-- the components that follow the name c in the name d, the last first; none if d does not begin
with c -/
def behindName (c : Name) : Name → Option (List String)
  | .anonymous => if c == .anonymous then some [] else none
  | d@(.str p s) => if d == c then some [] else (behindName c p).map (s :: ·)
  | d@(.num p n) => if d == c then some [] else (behindName c p).map (toString n :: ·)

/-- d has the name of a piece that the compiler lifted out of the code of c (a closed term or an
inner function), not the name of c's own code: a component of d after c begins with "_closed_" or
"_lam_". Only the name is read, not the compiled body. A name that does not begin with c is no
piece; "checkCompiled" then judges it as a function's own code, which is the stricter test. -/
def isPiece (c d : Name) : Bool :=
  match behindName c d with
  | some l => l.any fun s => s.startsWith "_closed_" || s.startsWith "_lam_"
  | none => false

/-- d has the name of a boxed numeral that the compiler lifted out of the code of c: d begins with c
and goes on, and its last part begins with "_boxed_const_". For a name that does not begin with c
the answer is false, which is the stricter side. -/
def isBoxedName (c d : Name) : Bool :=
  match behindName c d with
  | some (s :: _) => s.startsWith "_boxed_const_"
  | _ => false

/-- The compiled declaration has no parameter, and its body does nothing but take one numeral, box
it and return it. -/
def isBoxedNumeral : IR.Decl → Bool
  | .fdecl (xs := xs)
      (body := .vdecl x _ (.lit (.num _)) (.vdecl y _ (.box _ x') (.ret (.var y')))) .. =>
    xs.isEmpty && x == x' && y == y'
  | _ => false

/-- Is the compiled declaration d, under the name of the constant c, let through as a fragment? A
name that ends like a boxed numeral's is judged by the body that is on record for it, and by nothing
else, whatever the other parts of the name are. A name that does not end so and has such a part
further to the left is not let through: the compiler makes none. Every other name is judged by
"isPiece". -/
def isLetThrough (tbl : Std.HashMap Name IR.Decl) (c d : Name) : Bool :=
  if isBoxedName c d then (tbl[d]?).any isBoxedNumeral
  else isPiece c d && !((behindName c d).getD []).any (·.startsWith "_boxed_const_")

/-- One compiled declaration whose code is not made from the definition that the theorems speak of.
-/
structure Row where
  decl : Name
  /-- the kernel's constant from which it is made ("baseOf") -/
  base : Name
  why : List String
  origin : Origin

/-- **The check on compiled code.** Visits every compiled declaration that calls and closures reach
from the roots. A declaration is listed if the constant from which it is made ("baseOf") carries a
mark, or stands in for another by implemented_by or by a rule, or is neither Lean core's nor in the
kernel's cone of the roots (pieces and boxed numerals excepted), or if the declaration has no body
on record. Refuses every listed declaration that is not Lean core's and whose constant "allowed"
does not name. Also fails if a root has no compiled code on record, if a declaration that is called
is not on record or "baseOf" finds no constant for it, or if a body is nested too deep to be read to
its end. -/
def checkCompiled (roots : List Name) (allowed : List Name) : CommandElabM Unit := do
  let env ← getEnv
  if roots.isEmpty then throwError "the guard on compiled code was given no function to start from"
  let tbl := allCompiled env
  for r in roots do
    unless tbl.contains r do throwError "the guard on compiled code: {r} has no compiled code on \
      record"
  let mut seen : NameSet := roots.foldl (fun s n => s.insert n) {}
  let mut queue : Array Name := roots.toArray
  let mut i := 0
  let mut unknown : Array Name := #[]
  -- who was first seen to call whom: for the chains that are printed with a rejection
  let mut par : NameMap Name := {}
  -- a declaration enters the queue once (a root as often as roots names it), so fewer than 10^8
  -- declarations do not meet the bound; if some are left when it is met, the walk fails below. The
  -- loop stands in for a while loop
  for _ in [0:100000000] do
    if i ≥ queue.size then break
    let c := queue[i]!
    i := i + 1
    match tbl[c]? with
    | some (.fdecl (body := b) ..) =>
      let some calls := callsOf 1000000 b #[]
        | throwError "the guard on compiled code: the compiled body of {c} is nested deeper than \
            1000000 steps and was not read to its end"
      for n in calls do
        unless seen.contains n do
          seen := seen.insert n; queue := queue.push n; par := par.insert n c
    | some _ => pure ()
    | none => unknown := unknown.push c
  unless i ≥ queue.size do throwError "the guard on compiled code: the walk did not end"
  let si := standIns env
  let rs := rightSides env
  -- the kernel's cone of the same roots, as command 2 walks it
  let inCone : NameSet ← match coneOf env roots with
    | .error e => throwError "the guard on compiled code: {e}"
    | .ok cone => pure (cone.foldl (fun (s : NameSet) n => s.insert n) {})
  let mut pieces : Array Name := #[]
  let mut rows : Array Row := #[]
  let mut noBase : Array Name := #[]
  for d in queue do
    match baseOf env d with
    | none => noBase := noBase.push d
    | some c =>
      let some ci := env.find? c | continue
      let mut why := whyListed env c ci
      let mut o := originOf env c
      for c' in (si.find? c).getD [] do
        why := why ++ [s!"stands in for {c'} without an equation"]; o := later o (originOf env c')
      for e in (rs.find? c).getD [] do
        let thm := match env.find? e.thmName with | some (.thmInfo _) => "a theorem" | _ => "NOT \
          a theorem"
        why := why ++ [s!"stands in for {e.fromDeclName} by the rule {e.thmName} \
          ({thm})"]; o := later o (originOf env e.thmName)
      -- a stranger: not Lean core's, and no term that the kernel checked below the roots names it
      if originOf env c != .core && !inCone.contains c then
        if isLetThrough tbl c d then pieces := pieces.push d
        else why := why ++ ["A STRANGER: its own code can be called, and the kernel's cone of the \
          roots does not hold it"]
      match tbl[d]? with
      | some (.fdecl ..) => pure ()
      | _ => if why.isEmpty then why := ["no body on record"]
      unless why.isEmpty do rows := rows.push ⟨d, c, why, o⟩
  let show1 := fun (fs : Array Row) =>
    MessageData.joinSep ((fs.qsort fun a b => Name.lt a.decl b.decl).toList.map fun f => m!"  \
      {f.decl}: {", ".intercalate f.why}") "\n"
  let core := rows.filter fun r => r.origin == .core
  let pkgs := rows.filter fun r => r.origin == .packages
  let own := rows.filter fun r => r.origin == .own
  let refused := (pkgs ++ own).filter fun r => !allowed.contains r.base
  logInfo m!"compiled code below {roots}: {queue.size} declarations, {rows.size} of them listed; \
    Lean core's own, not shown here: {core.size}; \
    called but not on record: {unknown.size} {unknown.toList.take 10}; \
    without a constant behind their name: {noBase.size} {noBase.toList.take 10}\n\
    MATHLIB AND PACKAGES: {pkgs.size}\n{show1 pkgs}\n\
    THIS LIBRARY: {own.size}\n{show1 own}\n\
    PIECES LET THROUGH (closed terms, inner functions and boxed numerals under the name of a \
    function outside the kernel's cone, which was compiled first): {pieces.size}\n{lines pieces}"
  unless unknown.isEmpty && noBase.isEmpty do
    throwError "the guard on compiled code cannot judge these declarations (called but not on \
      record, or no constant behind the name): {unknown.toList ++ noBase.toList}"
  unless refused.isEmpty do
    -- one shortest chain of calls (or closures taken) from a root to each refused declaration
    let mut chains : Array MessageData := #[]
    for r in refused do
      let mut chain : List Name := [r.decl]
      let mut c := r.decl
      for _ in [0:100000] do
        match par.find? c with
        | some p => c := p; chain := p :: chain
        | none => break
      chains := chains.push m!"  {" -> ".intercalate (chain.map toString)}"
    throwError "the guard on compiled code refuses these declarations: the program can call them, \
      their code is not made from the definition that the theorems speak of, \
      they are not Lean core's, and the list does not name them:\n{show1 refused}\n\
      How the walk came to them (one shortest chain each):\n\
      {MessageData.joinSep chains.toList "\n"}"

/-- #guard_compiled roots allowed: both are terms of type List Lean.Name. -/
macro "#guard_compiled " r:term:max a:term:max : command =>
  `(run_cmd OnBytes.Guard.checkCompiled $r $a)

end OnBytes.Guard
