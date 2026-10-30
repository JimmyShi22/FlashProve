-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefBelow.lean: every round-by-round error of the body of the reference segment, as a
probability, is at most one number, if those of its named blocks are.

Book-keeping on soundness errors: a bound κ on each round's error, as a probability, passes from
the sub-protocols of a segment's body to the body.
Statements and proofs. Rules of the framework only; nothing of a text is rendered here.
Cb/Req1/LdReqBelow.lean: `p.Below κ`: in every round of every move, the count of bad verifier
messages is at most κ times the number of verifier messages. No sum of errors is formed. These
errors are numbers that a link lists (the data fields `Link.P.err`, `Nums.err`): that a link is
sound at the numbers that it lists is no statement of this file. Steps without rounds ask nothing.

Main names:
  `Spec.ldSegRef_rr_below`: read, then the range check. `D.prog.Below κ` from: the two sendings'
    numbers, each at most κ times the number of its seeds; p.err ≤ κ · (the number of verifier
    messages (`Fintype.card p.Chal`)).
  `Spec.ldSegRef_dg_below`: `(Q.prog ..).Below κ` from: the shift: 2^(1+d) ≤ κ · |E|; the digits'
    lookup's chain (`lk.ErrBelow κ`).
  `Spec.ldSegRef_tn_below`: the batching. `(X.prog ..).Below κ` from `Err.Below` at κ of its own
    list of errors (the evader's number; 1; the degree for each column variable).
  `Spec.ldSegRef_body_below`: `(Y.body z tensor).Below κ` from `Below κ` of the front, of the two
    lists above (read and range check; digits) and of `tensor`.
  `Spec.ldSegRefAll_below`: the closed body: `(A.body ..).Below κ` from `A.Nums κ`.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegBelowRef
import Cb.Req1.LdSegRefAllProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR IOR.Chain
open scoped ENNReal

/-- The numbers of the closed body's named blocks, as probabilities, are at most κ (`Err.Below`,
Iop/InteractiveOracleProof.lean). -/
structure LdRefD.Nums {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E}
    (A : LdRefD E Kc I) (κ : ℝ≥0∞) : Prop where
  front : A.V.prog.Below κ
  send1 : (ldSendFamErr A.Xa.Q.D.N A.Xa.Q.D.Sd A.Xa.Q.D.L : ℝ≥0∞) ≤
    κ * (Fintype.card A.Xa.Q.D.Sd.D : ℝ≥0∞)
  draw  : (A.Xa.Q.D.p.err : ℝ≥0∞) ≤ κ * (Fintype.card A.Xa.Q.D.p.Chal : ℝ≥0∞)
  send3 : (ldSendFamErr A.Xa.Q.D.N' A.Xa.Q.D.Sd' A.Xa.Q.D.L' : ℝ≥0∞) ≤
    κ * (Fintype.card A.Xa.Q.D.Sd'.D : ℝ≥0∞)
  shift : ((2 ^ (1 + A.Xa.Q.d) : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card E : ℝ≥0∞)
  lk    : Err.Below
    (A.Xa.A.baseN A.Xa.ι I.C.E0 A.Xa.Q.T.Msg (I.C.PIdx × (A.W₁ × A.Gh)) Kc A.Xa.Q.T.ents).P.err κ
  batt  : Err.Below (A.X.bt.nums I.C.E0 Kc).err κ

namespace Spec

def ldSegRef_rr_below : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E]
      (D : LdRrD E Kc E₀ Wp) (κ : ℝ≥0∞),
    (ldSendFamErr D.N D.Sd D.L : ℝ≥0∞) ≤ κ * (Fintype.card D.Sd.D : ℝ≥0∞) →
    (D.p.err : ℝ≥0∞) ≤ κ * (Fintype.card D.p.Chal : ℝ≥0∞) →
    (ldSendFamErr D.N' D.Sd' D.L' : ℝ≥0∞) ≤ κ * (Fintype.card D.Sd'.D : ℝ≥0∞) → D.prog.Below κ

def ldSegRef_dg_below : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (Q : LdDgP E Kc E₀ Wp)
      (mult : Q.X₄ × E → Ms Q.T E₀ → Prop) (ent : Ms Q.T E₀ → Q.Nn → E) (n : ℕ)
      (lk : Chain Kc (Q.lkS mult).J (Q.lkT ent n).J) (κ : ℝ≥0∞),
    ((2 ^ (1 + Q.d) : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card E : ℝ≥0∞) →
    lk.ErrBelow κ → (Q.prog mult ent n lk).Below κ

def ldSegRef_tn_below : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc) (St₁ : Type) (fz : X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))) (κ : ℝ≥0∞),
    Err.Below (X.bt.nums X.C.E0 Kc).err κ → (X.prog St₁ fz Az).Below κ

def ldSegRef_body_below : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (Y : LdBodyD E Kc E₀ Wp)
      (z : LdStage E Kc) (tensor : LdProg Y.tgt z) (κ : ℝ≥0∞),
    Y.front.Below κ → Y.G.Q.D.prog.Below κ → (Y.G.Q.prog Y.mult Y.G.ent Y.G.n Y.lk).Below κ →
    tensor.Below κ → (Y.body z tensor).Below κ

/-- The closed body. -/
def ldSegRefAll_below : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (A : LdRefD E Kc I) (St₁ : Type)
      (fz : A.X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ I.C.E0 (A.Xa.Q.T.Msg × (I.C.PIdx × (A.W₁ × A.Gh)))) (κ : ℝ≥0∞),
    A.Nums κ → (A.body St₁ fz Az).Below κ

end Spec

theorem ldSegRef_rr_below : Spec.ldSegRef_rr_below := by
  intro E Kc E₀ Wp _ _ D κ h1 h2 h3
  obtain ⟨hs, _, _, _, _, hp⟩ := ldSeg_below_named E Kc κ
  have c2 : (LdMv.send D.s1 D.d1).chain = .one D.d1.link := by rw [LdMv.chain]
  have c3 : (LdMv.sub D.s2 D.s3 (.one D.draw)).chain = .one D.draw := by rw [LdMv.chain]
  have c4 : (LdMv.send D.s3v D.d3).chain = .one D.d3.link := by rw [LdMv.chain]
  unfold LdRrD.prog LdRrD.derive
  rw [LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc,
    c2, c3, c4, errBelow_one, errBelow_one, errBelow_one]
  exact ⟨⟨⟨⟨⟨LdProg.below_nil _ κ, hp _ _ _ _ _ _⟩, (hs D.s1 D.d1).2 h1⟩, ⟨h2, trivial⟩⟩,
      hp _ _ _ _ _ _⟩,
    (hs D.s3v D.d3).2 h3⟩

theorem ldSegRef_dg_below : Spec.ldSegRef_dg_below := by
  intro E Kc E₀ Wp _ _ Q mult ent n lk κ h1 h2
  obtain ⟨_, _, _, _, _, hp⟩ := ldSeg_below_named E Kc κ
  have c2 : (LdMv.sub Q.u0 Q.u1 (.one Q.shift)).chain = .one Q.shift := by rw [LdMv.chain]
  have c4 : (LdMv.sub (Q.lkS mult) (Q.lkT ent n) lk).chain = lk := by rw [LdMv.chain]
  unfold LdDgP.prog LdDgP.pre LdDgP.stepA LdDgP.stepB
  rw [LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc,
    LdProg.below_snoc, c2, c4, errBelow_one]
  exact ⟨⟨⟨⟨LdProg.below_nil _ κ, hp _ _ _ _ _ _⟩, ⟨h1, trivial⟩⟩, hp _ _ _ _ _ _⟩, h2⟩

theorem ldSegRef_tn_below : Spec.ldSegRef_tn_below := by
  intro E Kc _ _ X St₁ fz Az κ h
  obtain ⟨_, _, _, _, _, hp⟩ := ldSeg_below_named E Kc κ
  have c2 : (LdMv.sub X.m0 X.m1 (.one X.link)).chain = .one X.link := by rw [LdMv.chain]
  unfold LdTenD.prog LdTenD.stepIn LdTenD.stepOut
  rw [LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc, c2, errBelow_one]
  exact ⟨⟨⟨LdProg.below_nil _ κ, hp _ _ _ _ _ _⟩, h⟩, hp _ _ _ _ _ _⟩

theorem ldSegRef_body_below : Spec.ldSegRef_body_below := by
  intro E Kc E₀ Wp _ _ Y z tensor κ hf hr hd ht
  obtain ⟨_, _, _, _, _, hp⟩ := ldSeg_below_named E Kc κ
  unfold LdBodyD.body
  refine LdProg.below_app _ _ κ
    ((LdProg.below_snoc _ _ _).2 ⟨LdProg.below_app _ _ κ (LdProg.below_app _ _ κ hf hr) hd, ?_⟩) ht
  unfold LdBodyD.step LdGaP.step
  exact hp _ _ _ _ _ _

theorem ldSegRefAll_below : Spec.ldSegRefAll_below := fun E Kc _ _ _ A St₁ fz Az κ h =>
  ldSegRef_body_below E Kc _ _ A.Y (A.X.tgt St₁ Az) (A.X.prog St₁ fz Az) κ h.front
    (ldSegRef_rr_below E Kc _ _ A.Xa.Q.D κ h.send1 h.draw h.send3)
    (ldSegRef_dg_below E Kc _ _ A.Xa.Q A.Xa.mult A.Xa.ent A.Xa.A.nRows A.Xa.lk κ
      h.shift ((errBelow_one A.Xa.link κ).2 h.lk))
    (ldSegRef_tn_below E Kc A.X St₁ fz Az κ h.batt)

end Cb
