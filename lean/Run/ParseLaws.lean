-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParseLaws.lean: equations that say what each field of the parser's argument string is.

Run/ParseChain.lean makes, from what a reader of a proof file returns (`o : Fmt.ChainOut`), two of
the inputs of the compiled verifier (`Compile.Batch.verifyOneProtocol`, the function that the compiler's
verifier runs on each proof string). One of the two is the argument string (`OneProtocolProof`,
Compile/Batch/Verifier.lean): the proof as typed data. Whoever connects a run of that function with
the format page's own verifier needs to know what is in each field. Everything is generic in the
protocol Q and its typing T (`Typing`, Run/ParseChain.lean).

1. What the file contains. Statements (each a `Prop` in `Run.Spec`) and proofs. Many statements of
   this library are written twice: a definition in the namespace `Spec` states a proposition, and a
   theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
    `opensAt T run o`: at a position p, the opening at column `(T.place p).2` of the first opening
      under the tree's number `(T.place p).1`, none if that tree was not opened.
    `opensAtF`: the same for the parser that fills whole paths (Run/ParseFull.lean).

2. What is checked when the file compiles.  Only the types and proofs.

3. Theorems.
    `parseLaws_some`: `toBPrf T o = some x` if and only if there are run, pl with:
      `o.run = some run`; `T.plains o.rounds = some pl`; every opening passes `OpenB.ok`; x = (the
      list with the parameters' digest, `mkBPrf Q run (rootsB o) pl (opensAt T run o)`).
    `parseLaws_someF`: the same for the parser that fills whole paths (`toBPrfFull`, `opensAtF`),
      with one condition more: `opensF o = some ops`, and it is the openings in ops that pass
      `OpenB.ok`.
    `parseLaws_fields`: the fields of `mkBPrf`: salt: the run's value as bits; roots: the roots as
      digests, in the order sent; plains; opens; no external opening; request root: zeros; slot 0;
      empty path.
    `parseLaws_opens`: `(opensB o).lookup (T.place p).1 = some (W, Ob)` gives
      `opensAt T run o p = Ob.at (T.sym p) run (T.place p).2`; = none gives none.
    `parseLaws_at`: `Ob.at sym run x`: if the look-up of x among the listed positions finds (col,
      salt, path), it is some ⟨y, run's value ‖ salt, path⟩ where sym col = some y, and none where
      sym col = none; it is none where the look-up finds nothing.
    `parseLaws_parse`: at the identity monad, `parseW`, `parseLaxW` and `parseFullW` are each its
      reader (`Fmt.wholeChain`, `laxWhole`, `fullWhole`), then `toBPrf` (for the third:
      `toBPrfFull`).

4. What is not claimed. This file claims nothing on what the readers hand out (o itself). Nothing on
   lengths of bit strings.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.ParseFull

set_option autoImplicit false

namespace Run
open Iop Rom Compile Compile.Batch
open _root_.Fmt (ChainOut)

variable {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}

/-- The function "opens" of the argument string that `toBPrf` makes (`parseLaws_some`). -/
def opensAt (T : Typing Q) (run : ByteArray) (o : ChainOut) (p : OPos Q.loc.shape) :
    Option (Opening 256 (OSym Q.loc.shape p)) :=
  match (opensB o).lookup (T.place p).1 with
  | none => none
  | some x => x.2.at (T.sym p) run (T.place p).2

/-- The same with whole paths, for `toBPrfFull` (`parseLaws_someF`). -/
def opensAtF (T : Typing Q) (run : ByteArray)
    (ops : List (Nat × Nat × OpenB × List (List (Dig 256)))) (p : OPos Q.loc.shape) :
    Option (Opening 256 (OSym Q.loc.shape p)) :=
  match ops.lookup (T.place p).1 with
  | none => none
  | some x => x.2.1.atP (T.sym p) run x.2.2 (T.place p).2

def Spec.parseLaws_some : Prop :=
  ∀ {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (T : Typing Q)
      (o : ChainOut) (x : List (Dig 256) × OneProtocolProof 256 Q),
    toBPrf T o = some x ↔
    ∃ run pl,
      o.run = some run ∧
      T.plains o.rounds = some pl ∧
      (opensB o).all (fun y => y.2.2.ok T.saltBytes y.2.1) = true ∧
      x = ([bytesToDig o.pd], mkBPrf Q run (rootsB o) pl (opensAt T run o))

def Spec.parseLaws_someF : Prop :=
  ∀ {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (T : Typing Q)
      (o : ChainOut) (x : List (Dig 256) × OneProtocolProof 256 Q),
    toBPrfFull T o = some x ↔
    ∃ run pl ops,
      o.run = some run ∧
      T.plains o.rounds = some pl ∧
      opensF o = some ops ∧
      ops.all (fun y => y.2.2.1.ok T.saltBytes y.2.1) = true ∧
      x = ([bytesToDig o.pd], mkBPrf Q run (rootsB o) pl (opensAtF T run ops))

def Spec.parseLaws_fields : Prop :=
  ∀ {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (run : ByteArray) (roots : List ByteArray)
      (pl : Plains Q.loc.shape)
      (f : (p : OPos Q.loc.shape) → Option (Opening 256 (OSym Q.loc.shape p))),
    (mkBPrf Q run roots pl f).salt = bytesToBits run ∧
    (mkBPrf Q run roots pl f).roots = roots.map bytesToDig ∧
    (mkBPrf Q run roots pl f).plains = pl ∧
    (mkBPrf Q run roots pl f).opens = f ∧
    (mkBPrf Q run roots pl f).ext = (fun _ => none) ∧
    (mkBPrf Q run roots pl f).rtreq = (fun _ => false) ∧
    (mkBPrf Q run roots pl f).slot = 0 ∧
    (mkBPrf Q run roots pl f).path = []

def Spec.parseLaws_opens : Prop :=
  ∀ {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (T : Typing Q) (run : ByteArray)
      (o : ChainOut) (p : OPos Q.loc.shape),
    (∀ W Ob, (opensB o).lookup (T.place p).1 = some (W, Ob) →
      opensAt T run o p = Ob.at (T.sym p) run (T.place p).2) ∧
    ((opensB o).lookup (T.place p).1 = none → opensAt T run o p = none)

def Spec.parseLaws_at : Prop :=
  ∀ {σ : Type} (sym : List UInt64 → Option σ) (run : ByteArray) (Ob : OpenB) (x : Nat),
    (∀ c s pt, (Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths))).lookup x = some (c, s, pt) →
      Ob.at sym run x = (sym c).map fun y => ⟨y, leafSalt run s, pt⟩) ∧
    ((Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths))).lookup x = none → Ob.at sym run x = none)

def Spec.parseLaws_parse : Prop :=
  ∀ {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
      (h : Nat → Nat → Nat → ByteArray → ByteArray → ByteArray) (S : _root_.Fmt.Spec)
      (T : Typing Q) (file : ByteArray),
    parseW (m := Id) h S T file = (_root_.Fmt.wholeChain (m := Id) h S file).bind (toBPrf T) ∧
    parseLaxW (m := Id) h S T file = (laxWhole (m := Id) h S file).bind (toBPrf T) ∧
    parseFullW (m := Id) h S T file = (fullWhole (m := Id) h S file).bind (toBPrfFull T)

theorem parseLaws_some : Spec.parseLaws_some := by
  intro Y E Q T o x
  unfold toBPrf
  constructor
  · intro hx
    cases hr : o.run with
    | none => simp [hr] at hx
    | some run =>
      cases hp : T.plains o.rounds with
      | none => simp [hr, hp] at hx
      | some pl =>
        simp only [hr, hp] at hx
        by_cases hk : (opensB o).all (fun y => y.2.2.ok T.saltBytes y.2.1) = true
        · rw [if_pos hk] at hx
          exact ⟨run, pl, rfl, rfl, hk, (Option.some.inj hx).symm⟩
        · rw [if_neg hk] at hx
          exact absurd hx (by simp)
  · rintro ⟨run, pl, hr, hp, hk, rfl⟩
    simp only [hr, hp]
    rw [if_pos hk]
    rfl

theorem parseLaws_someF : Spec.parseLaws_someF := by
  intro Y E Q T o x
  unfold toBPrfFull
  constructor
  · intro hx
    cases hr : o.run with
    | none => simp [hr] at hx
    | some run =>
      cases hp : T.plains o.rounds with
      | none => simp [hr, hp] at hx
      | some pl =>
        cases ho : opensF o with
        | none => simp [hr, hp, ho] at hx
        | some ops =>
          simp only [hr, hp, ho] at hx
          by_cases hk : ops.all (fun y => y.2.2.1.ok T.saltBytes y.2.1) = true
          · rw [if_pos hk] at hx
            exact ⟨run, pl, ops, rfl, rfl, rfl, hk, (Option.some.inj hx).symm⟩
          · rw [if_neg hk] at hx
            exact absurd hx (by simp)
  · rintro ⟨run, pl, ops, hr, hp, ho, hk, rfl⟩
    simp only [hr, hp, ho]
    rw [if_pos hk]
    rfl

theorem parseLaws_fields : Spec.parseLaws_fields := fun _ _ _ _ _ =>
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem parseLaws_opens : Spec.parseLaws_opens := by
  intro Y E Q T run o p
  refine ⟨fun W Ob h => ?_, fun h => ?_⟩
  · unfold opensAt; rw [h]
  · unfold opensAt; rw [h]

theorem parseLaws_at : Spec.parseLaws_at := by
  intro σ sym run Ob x
  refine ⟨fun c s pt h => ?_, fun h => ?_⟩
  · unfold OpenB.at OpenB.atP; rw [h]
  · unfold OpenB.at OpenB.atP; rw [h]

theorem parseLaws_parse : Spec.parseLaws_parse := fun _ _ _ _ => ⟨rfl, rfl, rfl⟩

end Run
