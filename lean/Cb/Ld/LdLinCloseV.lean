-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseV.lean: whole tests on groups in a batch: the honest side.

Definitions, and statements (each statement a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdLinCloseVProofs.lean (that of `Spec.ldRunV_given`: Cb/Ld/LdLinCloseVRun.lean). (Plans of
such tests for a batch, with their honest side: Cb/Ld/LdLinCloseVPlan.lean.)
The tests, their links, extractors and errors are those of one instance (Cb/Ld/LdLinCloseRun.lean,
Cb/Ld/LdLinCloseChain.lean), unchanged; their annotations for a batch are those of
Cb/Ld/LdBatchBlocks.lean (`D.linkLo`: the test in every slot; `D.linkSh`: once, by the shared part).
Here each link gets the honest side of a batch (Ior/LinkV.lean), in the form in which it is carried
along a chain (Cb/Ld/LdLinChainV.lean: `JV`, `LinkV`, `PV`).

Main names:
What a whole test leaves does not depend on its transcript (`Spec.ldRunV_run`):
  `D.outX`, `D.outY`, `D.outW`, what the test leaves: the rows of the test are dropped; samples,
    words and pairs of the oracle messages that are not kept are dropped.
  `Spec.ldRunV_congr`: what the honest prover sends is a function of the acting part: the rows that
    the test takes in, with targets and states (`D.G.claims`: the sample rows of all members
    included), and the members' pairs (`D.G.wit`); of its coins and of the verifier's messages.
  `Spec.ldRunV_given`: what the simulator is given lies in the members' words: every position that
    the test's verifier reads, or to which a position of the test's oracles is tied, is a position
    of a member of the group.
The two links. VA: what the honest side of a batch adds at the joint before the test (shared
witness, tie, demand on families of positions).
  `D.loV`, the test in every slot: each slot runs the one-instance prover on its own witness; the
    shared witness is handed on.
  `D.shV`, the test once, by the shared part alone: "rep" reads a statement and a witness off the
    shared witness; the shared part runs the one-instance prover on them; the slots are silent;
    "nx": the next shared witness.
  `Spec.ldRunV_local`: `D.loV` is a piece (`PV`: `PieceV`, Ior/LinkVBears.lean) if: `D.OK`; the tie
    is carried to what the test leaves; the link bears what follows (each slot's budget); `qB.Her`.
  `Spec.ldRunV_shared`: `D.shV` is a piece if: `D.OK`; on tied statements the acting part is that of
    rep: same rows, same pairs of the members, same words of the members as sent ("yrep"); the tie
    is carried; the link bears what follows (at the union); `qB.Her`; a value of `E₀.Str`.

Limits: no plan is given; the demands on families of positions ("bears what follows") are hypotheses
here. This file says nothing on splitting. It says nothing on soundness (Cb/Ld/LdBatchBlocks*.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBatchBlocksPlan
import Cb.Ld.LdLinBHonTop
import Ior.LinkVPiece
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) {St₀ Wp : Type} {E₀ : ExtSpec}

/-- What the test leaves: of the explicit part, of the oracles, of the witness. -/
def LdRunD.outX (x : (((D.B → E) × (∀ b, D.Sb b)) × St₀) × S.Smp) : St₀ × (S.sub D.kp).Smp :=
  (x.1.2, S.res (T := OMsg.Smp) D.kp x.2)
def LdRunD.outY (y : (E₀.prod S.ext).Str) : (E₀.prod (S.sub D.kp).ext).Str :=
  (y.1, fun a => y.2 a.1)
def LdRunD.outW (w : S.Wit × Wp) : (S.sub D.kp).Wit × Wp := (S.res (T := OMsg.Wit) D.kp w.1, w.2)

variable (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp))
  (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) (N : ℕ) (VA : JV N (S.jointCf (D.pre A₀)))

/-- The test in every slot. -/
def LdRunD.loV
    (tieB : VA.W0 → St₀ × (S.sub D.kp).Smp → (E₀.prod (S.sub D.kp).ext).Str →
      (S.sub D.kp).Wit × Wp → Prop)
    (qB : QFam (E₀.prod (S.sub D.kp).ext) N) :
    LinkV Unit N VA (⟨VA.W0, tieB, qB⟩ : JV N ((S.sub D.kp).jointCf A₀)) :=
  ⟨D.linkLo A₀ d d',
    (D.link A₀ d d').H.localV VA.W0,
    budEach (D.link A₀ d d').R N (D.link A₀ d d').P.bud⟩

/-- the shared part's strategy: the one-instance prover on what rep reads off the shared witness -/
def LdRunD.s0 {W0' : Type}
    (rep : VA.W0 → ((((D.B → E) × (∀ b, D.Sb b)) × St₀) × S.Smp) × (S.Wit × Wp)) (nx : VA.W0 → W0')
    (w0 : VA.W0) (c : (D.link A₀ d d').H.Coin) :
    Strat (D.link A₀ d d').R.shape W0' :=
  Strat.map (fun _ => nx w0) ((D.link A₀ d d').H.strat (rep w0).2 (rep w0).1 c)

/-- The test once, by the shared part alone. -/
def LdRunD.shV (W0' : Type)
    (tieB : W0' → St₀ × (S.sub D.kp).Smp → (E₀.prod (S.sub D.kp).ext).Str →
      (S.sub D.kp).Wit × Wp → Prop)
    (qB : QFam (E₀.prod (S.sub D.kp).ext) N)
    (rep : VA.W0 → ((((D.B → E) × (∀ b, D.Sb b)) × St₀) × S.Smp) × (S.Wit × Wp))
    (nx : VA.W0 → W0') :
    LinkV Unit N VA (⟨W0', tieB, qB⟩ : JV N ((S.sub D.kp).jointCf A₀)) :=
  ⟨D.linkSh A₀ d d',
    (D.link A₀ d d').H.sharedV (D.s0 A₀ d d' N VA rep nx),
    budUnion (D.link A₀ d d').R N (D.link A₀ d d').P.bud⟩

end

namespace Spec

/-- What the test leaves does not depend on its transcript. -/
def ldRunV_run : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp),
    (∀ w x c ρ, (((D.link A₀ d d').H.strat w x c).run ρ).2 = (D.outX x, D.outW w)) ∧
    ∀ y τ, (D.link A₀ d d').R.imp y τ = D.outY y

/-- What the honest prover sends is a function of the acting part, of its coins and of the
verifier's messages. -/
def ldRunV_congr : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
      (x x' : (((D.B → E) × (∀ b, D.Sb b)) × St₀) × S.Smp) (w w' : S.Wit × Wp) c ρ,
    D.G.claims x.1.1 x.2 = D.G.claims x'.1.1 x'.2 → D.G.wit w.1 = D.G.wit w'.1 →
    (((D.link A₀ d d').H.strat w x c).run ρ).1 = (((D.link A₀ d d').H.strat w' x' c).run ρ).1

/-- What the simulator is given (`IOR.given`, Ior/Honest.lean) lies in the members' words. -/
def ldRunV_given : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp)
      (d' : LdBrW D.G D.kp Wp) ρ T (p : (E₀.prod S.ext).Pos),
    p ∈ (D.link A₀ d d').R.given ρ T → ∃ (a : D.G.A) (x : (S.om a.1).P), p = Sum.inr ⟨a.1, x⟩

/-- States, under the hypotheses below: the test in every slot is a piece. -/
def ldRunV_local : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
      (N : ℕ) (VA : JV N (S.jointCf (D.pre A₀)))
      (tieB : VA.W0 → St₀ × (S.sub D.kp).Smp → (E₀.prod (S.sub D.kp).ext).Str →
        (S.sub D.kp).Wit × Wp → Prop)
      (qB : QFam (E₀.prod (S.sub D.kp).ext) N),
    D.OK → (∀ x y w, VA.rel x y w → tieB w.1 (D.outX x) (D.outY y) (D.outW w.2)) →
    (D.link A₀ d d').R.BearsV (RoundSplits.allLocal _)
      (budEach (D.link A₀ d d').R N (D.link A₀ d d').P.bud) VA.q qB →
    qB.Her → (D.loV A₀ d d' N VA tieB qB).PV

/-- States, under the hypotheses below: the test once, by the shared part alone, is a piece. -/
def ldRunV_shared : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
      (N : ℕ) (VA : JV N (S.jointCf (D.pre A₀))) (W0' : Type)
      (tieB : W0' → St₀ × (S.sub D.kp).Smp → (E₀.prod (S.sub D.kp).ext).Str →
        (S.sub D.kp).Wit × Wp → Prop)
      (qB : QFam (E₀.prod (S.sub D.kp).ext) N)
      (rep : VA.W0 → ((((D.B → E) × (∀ b, D.Sb b)) × St₀) × S.Smp) × (S.Wit × Wp))
      (yrep : VA.W0 → S.ext.Str) (nx : VA.W0 → W0') (_ : E₀.Str),
    D.OK → (∀ x y w, VA.rel x y w →
      D.G.claims x.1.1 x.2 = D.G.claims (rep w.1).1.1.1 (rep w.1).1.2 ∧
      D.G.wit w.2.1 = D.G.wit (rep w.1).2.1 ∧
      ∀ a : D.G.A, y.2 a.1 = yrep w.1 a.1) →
    (∀ x y w, VA.rel x y w → tieB (nx w.1) (D.outX x) (D.outY y) (D.outW w.2)) →
    (D.link A₀ d d').R.BearsV (RoundSplits.const (RAnn.ofShared .sh) _)
      (budUnion (D.link A₀ d d').R N (D.link A₀ d d').P.bud) VA.q qB →
    qB.Her → (D.shV A₀ d d' N VA W0' tieB qB rep nx).PV

end Spec
end Cb
