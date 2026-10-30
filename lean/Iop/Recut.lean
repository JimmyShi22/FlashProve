-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Recut.lean: the rounds of a protocol are split and merged in one pass.

The file has definitions and one statement, for ordinary interactive oracle proofs (IOPs). The
proofs are in Iop/RecutProofs.lean, the form for protocols with slots in Iop/BatchRecut.lean.
Iop/Split.lean splits a prover message into parts, each in a separate round; Iop/Join.lean makes one
round of two.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

A plan of splits and merges (`XPlan s`) goes through the list of rounds s. It keeps the first round;
or it splits off a first part (`RCut`, Iop/Split.lean) and goes on with the remainder; or it merges
the first round with the second and goes on with the merged round (`msg`, `chal`: cases (J1), (J2)
of Iop/Join.lean). So a remainder can be merged with the next round, a merged round can be split,
and several rounds are merged by repeating the step. `XPlan.OK` has the conditions of the single
steps. `InteractiveOracleProof.recut` is the protocol on the new list of rounds `X.shape`. `Err.recut` gives the new
error counts: 0 for a first part, and e1 · |C2| + |C1| · e2 for a merged round. Round-by-round
soundness is preserved with these errors (`InteractiveOracleProof.Sound.recut`, Iop/RecutProofs.lean).

There is one plan on the original rounds, rather than a split followed by a merge, because the plan
of a second step would be a plan of the list of rounds that the first step makes, which does not
reduce where a part of the list is a variable. A plan is applied before challenges are derived from
hash blocks (Iop/RecutDraws.lean).

Limits: Which pieces of a message go into which part is chosen by the `RCut`, and no condition ties
the choice to the order of the old rounds. Under `XPlan.OK` (at a split: `RCut.OK`, Iop/Split.lean)
the properties do not depend on it. A comparison of a plan with an implementation's hash calls does.
A first part that has been split off is merged with nothing afterwards; to put it under one
challenge with the round before it, merge first and then split (`RCut.unJoin`, Iop/RecutKit.lean).
No plan adds verifier randomness, and none splits a challenge in two. What Iop/Split.lean and
Iop/Join.lean do not say, this file does not say either.
-/
import Iop.Split
import Iop.Join

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Plans -/

/-- A plan of splits and merges for the list of rounds s, the original list. -/
inductive XPlan : Shape → Type 1
  | nil : XPlan []
  | keep (r : Round) {s : Shape} (X : XPlan s) : XPlan (r :: s)
  /-- a first part is split off; the plan goes on with the remainder -/
  | cut {r : Round} {s : Shape} (c : RCut r) (X : XPlan (c.snd :: s)) : XPlan (r :: s)
  /-- (J1): u is a value of the challenge of r1; `XPlan.OK` asks that it is the only one -/
  | msg (r1 r2 : Round) {s : Shape} (u : r1.Chal) (X : XPlan (r1.joinMsg r2 :: s)) : XPlan (r1 :: r2 :: s)
  /-- (J2): r2 has no position -/
  | chal (r1 r2 : Round) {s : Shape} (noPos : r2.Pos → Empty) (X : XPlan (r1.joinChal r2 :: s)) : XPlan (r1 :: r2 :: s)

/-- The new list of rounds. -/
def XPlan.shape : {s : Shape} → XPlan s → Shape
  | _, .nil => []
  | _, .keep r X => r :: X.shape
  | _, .cut c X => c.fst :: X.shape
  | _, .msg _ _ _ X => X.shape
  | _, .chal _ _ _ X => X.shape

/-- The conditions on the single steps. -/
def XPlan.OK : {s : Shape} → XPlan s → Prop
  | _, .nil => True
  | _, .keep _ X => X.OK
  | _, .cut c X => c.OK ∧ X.OK
  | _, .msg _ _ u X => (∀ c, c = u) ∧ X.OK
  | _, .chal _ r2 _ X => (∀ m : r2.Msg, m = r2.dMsg) ∧ X.OK

/-- the number of splits -/
def XPlan.cuts : {s : Shape} → XPlan s → ℕ
  | _, .nil => 0
  | _, .keep _ X => X.cuts
  | _, .cut _ X => X.cuts + 1
  | _, .msg _ _ _ X => X.cuts
  | _, .chal _ _ _ X => X.cuts

/-- the number of merges -/
def XPlan.joins : {s : Shape} → XPlan s → ℕ
  | _, .nil => 0
  | _, .keep _ X => X.joins
  | _, .cut _ X => X.joins
  | _, .msg _ _ _ X => X.joins + 1
  | _, .chal _ _ _ X => X.joins + 1

/-- Change nothing. -/
def XPlan.keepAll : (s : Shape) → XPlan s
  | [] => .nil
  | r :: s => .keep r (XPlan.keepAll s)

/-- The largest number of old rounds whose errors are in a new round, if the first round already
counts for w old rounds. -/
def XPlan.maxRunFrom : {s : Shape} → XPlan s → ℕ → ℕ
  | _, .nil, _ => 0
  | _, .keep _ X, w => max w (X.maxRunFrom 1)
  | _, .cut _ X, w => X.maxRunFrom w
  | _, .msg _ _ _ X, w => X.maxRunFrom (w + 1)
  | _, .chal _ _ _ X, w => X.maxRunFrom (w + 1)

/-- The largest number of old rounds whose errors are in a new round. -/
def XPlan.maxRun {s : Shape} (X : XPlan s) : ℕ := X.maxRunFrom 1


/-! ## 2. From the new list of rounds to the old one -/

/-- The transcript of the old list of rounds. -/
def Tr.old : {s : Shape} → (X : XPlan s) → Tr X.shape → Tr s
  | _, .nil => fun _ => ()
  | _, .keep r X => fun (z : r.Msg × r.Chal × Tr X.shape) => (z.1, z.2.1, Tr.old X z.2.2)
  | _, .cut c X => fun (z : c.fst.Msg × Unit × Tr X.shape) => c.glue z.1 (Tr.old X z.2.2)
  | _, .msg _ _ u X => fun z => Tr.unMsg u (Tr.old X z)
  | _, .chal _ _ _ X => fun z => Tr.unChal (Tr.old X z)

/-- The verifier randomness of the old list: the empty challenges of first parts are dropped, u is
put in at (J1), a pair is taken apart at (J2). -/
def Rho.old : {s : Shape} → (X : XPlan s) → Rho X.shape → Rho s
  | _, .nil => fun _ => ()
  | _, .keep r X => fun (z : r.Chal × Rho X.shape) => (z.1, Rho.old X z.2)
  | _, .cut c X => fun (z : Unit × Rho X.shape) => Rho.old (s := c.snd :: _) X z.2
  | _, .msg r1 r2 (s := s) u X => fun z => (u, (Rho.old X z : Rho (r1.joinMsg r2 :: s)))
  | _, .chal r1 r2 (s := s) _ X => fun z =>
      ((Rho.old X z : Rho (r1.joinChal r2 :: s)).1.1,
        (Rho.old X z : Rho (r1.joinChal r2 :: s)).1.2,
        (Rho.old X z : Rho (r1.joinChal r2 :: s)).2)

/-- The map back: from the verifier randomness of the old list to that of the new one. -/
def Rho.new : {s : Shape} → (X : XPlan s) → Rho s → Rho X.shape
  | _, .nil => fun _ => ()
  | _, .keep r X => fun (z : r.Chal × Rho _) => (z.1, Rho.new X z.2)
  | _, .cut _ X => fun ρ => ((), Rho.new X ρ)
  | _, .msg r1 r2 (s := s) _ X =>
    fun (z : r1.Chal × r2.Chal × Rho s) => Rho.new X (show Rho (r1.joinMsg r2 :: s) from z.2)
  | _, .chal r1 r2 (s := s) _ X =>
    fun (z : r1.Chal × r2.Chal × Rho s) =>
      Rho.new X (show Rho (r1.joinChal r2 :: s) from ((z.1, z.2.1), z.2.2))

/-- The plain parts of the prover messages of the old list. -/
def Plains.old : {s : Shape} → (X : XPlan s) → Plains X.shape → Plains s
  | _, .nil => fun _ => ()
  | _, .keep r X => fun (z : r.Plain × Plains X.shape) => (z.1, Plains.old X z.2)
  | _, .cut c X =>
    fun (z : c.PlainA × Plains X.shape) =>
      (c.plain.symm (z.1, (Plains.old X z.2).1), (Plains.old X z.2).2)
  | _, .msg r1 r2 (s := s) _ X => fun z =>
      ((Plains.old X z : Plains (r1.joinMsg r2 :: s)).1.1,
        (Plains.old X z : Plains (r1.joinMsg r2 :: s)).1.2,
        (Plains.old X z : Plains (r1.joinMsg r2 :: s)).2)
  | _, .chal r1 r2 (s := s) _ X => fun z =>
      ((Plains.old X z : Plains (r1.joinChal r2 :: s)).1,
        r2.dPlain,
        (Plains.old X z : Plains (r1.joinChal r2 :: s)).2)

/-- The map back: from the plain parts of the old list to those of the new one. -/
def Plains.new : {s : Shape} → (X : XPlan s) → Plains s → Plains X.shape
  | _, .nil => fun _ => ()
  | _, .keep r X => fun (z : r.Plain × Plains _) => (z.1, Plains.new X z.2)
  | _, .cut (r := r) c X =>
    fun (z : r.Plain × Plains _) => ((c.plain z.1).1, Plains.new X ((c.plain z.1).2, z.2))
  | _, .msg r1 r2 (s := s) _ X =>
    fun (z : r1.Plain × r2.Plain × Plains s) =>
      Plains.new X (show Plains (r1.joinMsg r2 :: s) from ((z.1, z.2.1), z.2.2))
  | _, .chal r1 r2 (s := s) _ X =>
    fun (z : r1.Plain × r2.Plain × Plains s) =>
      Plains.new X (show Plains (r1.joinChal r2 :: s) from (z.1, z.2.2))

/-- The positions of the new list of rounds are those of the old one. -/
def OPos.oldEquiv : {s : Shape} → (X : XPlan s) → OPos X.shape ≃ OPos s
  | _, .nil => Equiv.refl Empty
  | _, .keep r X => Equiv.sumCongr (Equiv.refl r.Pos) (OPos.oldEquiv X)
  | _, .cut (s := s) c X => (Equiv.sumCongr (Equiv.refl c.PosA) (OPos.oldEquiv X)).trans (c.posAssoc s)
  | _, .msg r1 r2 (s := s) _ X => (OPos.oldEquiv X).trans (OPos.unMsg r1 r2 s)
  | _, .chal r1 r2 (s := s) noPos X => (OPos.oldEquiv X).trans (OPos.unChal r1 r2 s noPos)

/-- The alphabet at a position does not change. -/
def OSym.old :
    {s : Shape} → (X : XPlan s) → (p : OPos X.shape) → OSym X.shape p → OSym s (OPos.oldEquiv X p)
  | _, .nil => fun p => Empty.elim p
  | _, .keep r X => fun (p : r.Pos ⊕ OPos X.shape) => match p with
      | .inl _ => fun a => a
      | .inr q => fun a => OSym.old X q a
  | _, .cut c X => fun (p : c.PosA ⊕ OPos X.shape) => match p with
      | .inl _ => fun a => a
      | .inr q => fun a => c.symUp (OPos.oldEquiv X q) (OSym.old X q a)
  | _, .msg _ _ _ X => fun p a => OSym.unMsg (OPos.oldEquiv X p) (OSym.old X p a)
  | _, .chal _ _ noPos X => fun p a => OSym.unChal noPos (OPos.oldEquiv X p) (OSym.old X p a)

/-- The map back from `OSym.old`. -/
def OSym.new :
    {s : Shape} → (X : XPlan s) → (p : OPos X.shape) → OSym s (OPos.oldEquiv X p) → OSym X.shape p
  | _, .nil => fun p => Empty.elim p
  | _, .keep r X => fun (p : r.Pos ⊕ OPos X.shape) => match p with
      | .inl _ => fun a => a
      | .inr q => fun a => OSym.new X q a
  | _, .cut c X => fun (p : c.PosA ⊕ OPos X.shape) => match p with
      | .inl _ => fun a => a
      | .inr q => fun a => OSym.new X q (c.symDown (OPos.oldEquiv X q) a)
  | _, .msg _ _ _ X => fun p a => OSym.new X p (OSym.reMsg (OPos.oldEquiv X p) a)
  | _, .chal _ _ noPos X => fun p a => OSym.new X p (OSym.reChal noPos (OPos.oldEquiv X p) a)

/-! ## 3. From the old list of rounds to the new one -/

/-- A strategy of the old list as one of the new list: it sends a message that is split part by
part; at (J1) its second message is the one that it sends after u; at (J2) its second message is
dropped. -/
def Strat.recut : {s : Shape} → {β : Type} → (X : XPlan s) → Strat s β → Strat X.shape β
  | _, _, .nil => fun b => b
  | _, β, .keep r X =>
    fun (z : r.Msg × (r.Chal → Strat _ β)) => (z.1, fun c => Strat.recut X (z.2 c))
  | _, β, .cut (r := r) c X =>
    fun (z : r.Msg × (r.Chal → Strat _ β)) =>
      (c.left z.1, fun _ => Strat.recut X (c.right z.1, z.2))
  | _, β, .msg r1 r2 (s := s) u X => fun (z : r1.Msg × (r1.Chal → r2.Msg × (r2.Chal → Strat s β))) =>
      Strat.recut X
        (show Strat (r1.joinMsg r2 :: s) β from (Round.msgPair z.1 (z.2 u).1, (z.2 u).2))
  | _, β, .chal r1 r2 (s := s) _ X => fun (z : r1.Msg × (r1.Chal → r2.Msg × (r2.Chal → Strat s β))) =>
      Strat.recut X (show Strat (r1.joinChal r2 :: s) β from (z.1, fun c => (z.2 c.1).2 c.2))

/-- The errors: a first part has the error 0; a merged round has e1 * card C2 + card C1 * e2, for
the two rounds' errors e1, e2 and sets of challenges C1, C2. -/
def Err.recut : {s : Shape} → (X : XPlan s) → Err s → Err X.shape
  | _, .nil => fun _ => ()
  | _, .keep _ X => fun (z : ℕ × Err _) => (z.1, Err.recut X z.2)
  | _, .cut _ X => fun ε => (0, Err.recut X ε)
  | _, .msg r1 r2 (s := s) _ X => fun (z : ℕ × ℕ × Err s) =>
      Err.recut X
        (show Err (r1.joinMsg r2 :: s)
          from (z.1 * Fintype.card r2.Chal + Fintype.card r1.Chal * z.2.1, z.2.2))
  | _, .chal r1 r2 (s := s) _ X => fun (z : ℕ × ℕ × Err s) =>
      Err.recut X
        (show Err (r1.joinChal r2 :: s)
          from (z.1 * Fintype.card r2.Chal + Fintype.card r1.Chal * z.2.1, z.2.2))

variable {X : Type} {E : ExtSpec}

/-- The protocol with its rounds split and merged. The verifier reads the same positions and decides
as before, on the transcript of the old list of rounds. -/
def InteractiveOracleProof.recut (Q : InteractiveOracleProof X E) (P : XPlan Q.shape) : InteractiveOracleProof X E where
  shape    := P.shape
  blinded  := fun p => Q.blinded (OPos.oldEquiv P p)
  extReads := fun x ρ => Q.extReads x (Rho.old P ρ)
  reads    := fun x ρ pl =>
    (Q.reads x (Rho.old P ρ) (Plains.old P pl)).map (OPos.oldEquiv P).symm.toEmbedding
  accept   := fun x y τ => Q.accept x y (Tr.old P τ)

/-- The honest prover: the same coins and the same external string; a value of the verifier
randomness is in the abort set if the old one is. -/
def Honest.recut {Q : InteractiveOracleProof X E} {Wt : Type} (H : Honest Q Wt) (P : XPlan Q.shape) :
    Honest (Q.recut P) Wt where
  Coin  := H.Coin
  ext   := H.ext
  strat := fun w x c => Strat.recut P (H.strat w x c)
  Bad   := {ρ | Rho.old P ρ ∈ H.Bad}
  Hid   := fun w x => {ρ | Rho.old P ρ ∈ H.Hid w x}

/-! ## 4. The statement (its theorem: `recutLength`, Iop/RecutProofs.lean) -/

namespace Spec

/-- One round more for each split, one less for each merge. -/
def recutLength : Prop := ∀ (s : Shape) (P : XPlan s), P.shape.length + P.joins = s.length + P.cuts






end Spec

end Iop
