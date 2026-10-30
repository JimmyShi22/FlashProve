-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParseThin.lean: the parsers' typed side in a form that can be evaluated at rounds with very many
verifier messages (see 4): the protocol's skeleton in the place of the protocol.

A parser here is a reader of a proof file's bytes followed by the step that makes two of the
compiled verifier's typed inputs from what was read (Run/ParseChain.lean). That second step is the
typed side.

Why. In the library a round carries the list of all its verifier messages as data (`Iop.Round`,
Iop/Shape.lean: the instance `finChal`). Observed elsewhere in this folder (heads of
Run/TwinDefs.lean, Run/ThinDefs.lean): compiled Lean can build that list where a round, a shape, a
protocol or an interface is passed as a value, also as an implicit argument; whether it does depends
on the compiler, function by function. The rule followed here: no function of this file on the path
of an evaluation has a parameter of these types. The parsers of Run/ParseChain.lean,
Run/ParseLax.lean and Run/ParseFull.lean have `{Q : BatchInteractiveOracleProof Y E}`. Here the same functions take
`(P : Run.Twin.PS Y E)`, the skeleton (Run/TwinDefs.lean), explicitly; the protocol `P.up` stands in
types alone. A skeleton has the protocol's fields, with each round's instance behind a function of
`Unit`.

1. What the file contains.  Definitions that can be evaluated.
    `TypingP P`: what a protocol supplies (as `Typing`, Run/ParseChain.lean): saltBytes; plains;
      place; sym. `T.up : Typing P.up`.
    `OpenB.table run paths`: one opening's table: for each listed position (column, typed salt,
      path): made once.
    `toBPrfP P T o`, `toBPrfFullP P T o`: as `toBPrf`, `toBPrfFull`. The tables of all openings are
      built before the function "opens", because the verifier calls that function at each of the
      2^depth places of each tree, and again at each position that is read. The body of that
      function has `T.place p`, two look-ups (the tree's table, then the position) and the symbol's
      typing, nothing else.
    `parseWP`, `parseLaxWP`, `parseFullWP`: the three parsers.

2. What is checked when the file compiles.  Only the types and proofs.

3. Theorems (stated in `Run.Spec`). `parseThin_to`: `toBPrfP P T o = toBPrf T.up o`;
   `parseThin_full`: `toBPrfFullP P T o = toBPrfFull T.up o`; `parseThin_parse`: each parser = its
   namesake at `T.up`.

4. What is not claimed. That no list of verifier messages is built in an evaluation: that is a fact
   about the compiler, no theorem. One trial was made (a skeleton of the small example of
   Run/ParseChain.lean with a trace in every round's instance; the evaluations from another file):
   the three parsers of this file gave the right argument string and built nothing. The trial has no
   positive case: in it `parseLaxW` at `Q := P.up` built nothing either (a control that asks for the
   instance itself did fire the trace). So this form rests on the rule, not on a difference that was
   seen.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.ParseFull
import Run.TwinDefs

set_option autoImplicit false

namespace Run
open Iop Rom Compile Compile.Batch
open _root_.Fmt (Spec ChainOut)

/-- What a protocol supplies (as `Typing`, Run/ParseChain.lean), at its skeleton. -/
structure TypingP {Y : Type} {E : ExtSpec} (P : Twin.PS Y E) where
  saltBytes : Nat
  plains    : Array _root_.Fmt.RoundOut → Option (Plains (Twin.up P.S))
  place     : OPos (Twin.up P.S) → Nat × Nat
  sym       : (p : OPos (Twin.up P.S)) → List UInt64 → Option (OSym (Twin.up P.S) p)

/-- the same as a typing of the protocol -/
def TypingP.up {Y : Type} {E : ExtSpec} {P : Twin.PS Y E} (T : TypingP P) : Typing P.up :=
  ⟨T.saltBytes, T.plains, T.place, T.sym⟩

/-- The argument string, as `mkBPrf` (Run/ParseBS.lean). -/
def mkBPrfP {Y : Type} {E : ExtSpec} (P : Twin.PS Y E) (run : ByteArray) (roots : List ByteArray)
    (plains : Plains (Twin.up P.S))
    (opens : (p : OPos (Twin.up P.S)) → Option (Opening 256 (OSym (Twin.up P.S) p))) :
    OneProtocolProof 256 P.up :=
  ⟨bytesToBits run, roots.map bytesToDig, plains, opens, fun _ => none, fun _ => false, 0, []⟩

/-- what a table holds at a listed position: the column, the typed salt, the path -/
abbrev Row3 : Type := List UInt64 × Bits × List (Dig 256)

/-- One opening's table: a `Row3` for each listed position. -/
def OpenB.table (O : OpenB) (run : ByteArray) (paths : List (List (Dig 256))) : List (Nat × Row3) :=
  O.idx.zip (O.cols.zip ((O.salts.map (leafSalt run)).zip paths))

/-- The opening at a position: a look-up in one opening's table. -/
def atT {σ : Type} (sym : List UInt64 → Option σ) (tab : List (Nat × Row3)) (x : Nat) :
    Option (Opening 256 σ) :=
  match tab.lookup x with
  | none => none
  | some (c, s, p) => (sym c).map fun y => ⟨y, s, p⟩

/-- the look-up in the tables of all trees -/
def atTT {σ : Type} (sym : List UInt64 → Option σ)
    (tabs : List (Nat × List (Nat × Row3))) (t x : Nat) : Option (Opening 256 σ) :=
  match tabs.lookup t with
  | none => none
  | some tab => atT sym tab x

/-- From what was read to two of the verifier's inputs, as `toBPrf` (`parseThin_to`). -/
def toBPrfP {Y : Type} {E : ExtSpec} (P : Twin.PS Y E) (T : TypingP P) (o : ChainOut) :
    Option (List (Dig 256) × OneProtocolProof 256 P.up) :=
  match o.run, T.plains o.rounds with
  | some run, some pl =>
      if (opensB o).all (fun x => x.2.2.ok T.saltBytes x.2.1) then
        let tabs : List (Nat × List (Nat × Row3)) :=
          (opensB o).map fun x => (x.1, x.2.2.table run x.2.2.paths)
        some ([bytesToDig o.pd],
          mkBPrfP P run (rootsB o) pl fun p => atTT (T.sym p) tabs (T.place p).1 (T.place p).2)
      else none
  | _, _ => none

/-- The same with whole paths, as `toBPrfFull` (`parseThin_full`). -/
def toBPrfFullP {Y : Type} {E : ExtSpec} (P : Twin.PS Y E) (T : TypingP P) (o : ChainOut) :
    Option (List (Dig 256) × OneProtocolProof 256 P.up) :=
  match o.run, T.plains o.rounds, opensF o with
  | some run, some pl, some ops =>
      if ops.all (fun x => x.2.2.1.ok T.saltBytes x.2.1) then
        let tabs : List (Nat × List (Nat × Row3)) :=
          ops.map fun x => (x.1, x.2.2.1.table run x.2.2.2)
        some ([bytesToDig o.pd],
          mkBPrfP P run (rootsB o) pl fun p => atTT (T.sym p) tabs (T.place p).1 (T.place p).2)
      else none
  | _, _, _ => none

section
variable {m : Type → Type}
  [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) {Y : Type} {E : ExtSpec}

/-- The parser on the page's own reader (the strict reader `Fmt.wholeChain`). -/
def parseWP (P : Twin.PS Y E) (S : Spec) (T : TypingP P) (file : ByteArray) :
    m (Option (List (Dig 256) × OneProtocolProof 256 P.up)) := do
  let o ← _root_.Fmt.wholeChain h S file
  pure (o.bind (toBPrfP P T))

/-- The lenient parser: on the reader `laxWhole` (Run/ParseLax.lean). -/
def parseLaxWP (P : Twin.PS Y E) (S : Spec) (T : TypingP P) (file : ByteArray) :
    m (Option (List (Dig 256) × OneProtocolProof 256 P.up)) := do
  let o ← laxWhole h S file
  pure (o.bind (toBPrfP P T))

/-- The parser that fills whole paths: on the reader `fullWhole` (Run/ParseFull.lean). -/
def parseFullWP (P : Twin.PS Y E) (S : Spec) (T : TypingP P) (file : ByteArray) :
    m (Option (List (Dig 256) × OneProtocolProof 256 P.up)) := do
  let o ← fullWhole h S file
  pure (o.bind (toBPrfFullP P T))

end

/-! ## The equations with `toBPrf`, `toBPrfFull` and the three parsers at `T.up` -/

theorem lookup_zip3 {α β γ δ : Type} (f : β → γ) (x : Nat) :
    ∀ (l1 : List Nat) (l2 : List α) (l3 : List β) (l4 : List δ),
      (l1.zip (l2.zip ((l3.map f).zip l4))).lookup x =
        ((l1.zip (l2.zip (l3.zip l4))).lookup x).map fun r => (r.1, f r.2.1, r.2.2)
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, [], _ => rfl
  | _ :: _, _ :: _, _ :: _, [] => rfl
  | i :: l1, a :: l2, b :: l3, d :: l4 => by
      simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
      cases x == i
      · exact lookup_zip3 f x l1 l2 l3 l4
      · rfl

theorem atT_table {σ : Type} (sym : List UInt64 → Option σ) (run : ByteArray) (O : OpenB)
    (paths : List (List (Dig 256))) (x : Nat) :
    atT sym (O.table run paths) x = O.atP sym run paths x := by
  unfold atT OpenB.table OpenB.atP
  rw [lookup_zip3]
  cases (O.idx.zip (O.cols.zip (O.salts.zip paths))).lookup x <;> rfl

theorem lookup_map_snd {α β : Type} (g : α → β) (t : Nat) :
    ∀ l : List (Nat × α), (l.map fun x => (x.1, g x.2)).lookup t = (l.lookup t).map g
  | [] => rfl
  | (i, a) :: l => by
      simp only [List.map_cons, List.lookup_cons]
      cases t == i
      · exact lookup_map_snd g t l
      · rfl

def Spec.parseThin_to : Prop :=
  ∀ {Y : Type} {E : ExtSpec} (P : Twin.PS Y E) (T : TypingP P) (o : ChainOut),
    toBPrfP P T o = toBPrf T.up o
def Spec.parseThin_full : Prop :=
  ∀ {Y : Type} {E : ExtSpec} (P : Twin.PS Y E) (T : TypingP P) (o : ChainOut),
    toBPrfFullP P T o = toBPrfFull T.up o
def Spec.parseThin_parse : Prop :=
  ∀ {m : Type → Type} [Monad m]
      (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) {Y : Type} {E : ExtSpec}
      (P : Twin.PS Y E) (S : _root_.Fmt.Spec) (T : TypingP P) (file : ByteArray),
    parseWP h P S T file = parseW h S T.up file ∧
    parseLaxWP h P S T file = parseLaxW h S T.up file ∧
    parseFullWP h P S T file = parseFullW h S T.up file

theorem parseThin_to : Spec.parseThin_to := by
  intro Y E P T o
  unfold toBPrfP toBPrf
  cases hr : o.run with
  | none => rfl
  | some run =>
    cases hp : T.plains o.rounds with
    | none => simp [TypingP.up, hp]
    | some pl =>
      have hp' : T.up.plains o.rounds = some pl := hp
      simp only [hp']
      have e : (fun p =>
          atTT (T.sym p) ((opensB o).map fun x => (x.1, x.2.2.table run x.2.2.paths))
            (T.place p).1 (T.place p).2) =
          (fun p : OPos (Twin.up P.S) => match (opensB o).lookup (T.place p).1 with
            | none => none
            | some x => x.2.at (T.sym p) run (T.place p).2) := by
        funext p
        unfold atTT
        rw [lookup_map_snd (fun y : Nat × OpenB => y.2.table run y.2.paths)]
        cases (opensB o).lookup (T.place p).1 with
        | none => rfl
        | some x => exact atT_table _ _ _ _ _
      show (if _ then some (_, mkBPrfP P run (rootsB o) pl _) else none) = _
      rw [e]
      rfl

theorem parseThin_full : Spec.parseThin_full := by
  intro Y E P T o
  unfold toBPrfFullP toBPrfFull
  cases hr : o.run with
  | none => rfl
  | some run =>
    cases hp : T.plains o.rounds with
    | none => simp [TypingP.up, hp]
    | some pl =>
      have hp' : T.up.plains o.rounds = some pl := hp
      simp only [hp']
      cases ho : opensF o with
      | none => rfl
      | some ops =>
        have e : (fun p =>
            atTT (T.sym p) (ops.map fun x => (x.1, x.2.2.1.table run x.2.2.2))
              (T.place p).1 (T.place p).2) =
            (fun p : OPos (Twin.up P.S) => match ops.lookup (T.place p).1 with
              | none => none
              | some x => x.2.1.atP (T.sym p) run x.2.2 (T.place p).2) := by
          funext p
          unfold atTT
          rw [lookup_map_snd (fun y : Nat × OpenB × List (List (Dig 256)) => y.2.1.table run y.2.2)]
          cases ops.lookup (T.place p).1 with
          | none => rfl
          | some x => exact atT_table _ _ _ _ _
        show (if _ then some (_, mkBPrfP P run (rootsB o) pl _) else none) = _
        rw [e]
        rfl

theorem parseThin_parse : Spec.parseThin_parse := by
  intro m _ h Y E P S T file
  have e1 : toBPrfP P T = toBPrf T.up := funext (parseThin_to P T)
  have e2 : toBPrfFullP P T = toBPrfFull T.up := funext (parseThin_full P T)
  refine ⟨?_, ?_, ?_⟩
  · unfold parseWP parseW; rw [e1]
  · unfold parseLaxWP parseLaxW; rw [e1]
  · unfold parseFullWP parseFullW; rw [e2]

end Run
