-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegBelowRef.lean: in every round the error at most one number κ times the number of
verifier messages: the front, and a segment with one group, in terms of the blocks' own error lists.

Statements (in `Cb.Spec`) and proofs. Framework only.
Cb/Req1/LdReqBelow.lean carries "every round's error is at most κ times the number of verifier
messages" (`Err.Below`, Iop/InteractiveOracleProof.lean) through chains and lists, and says what it means for the
named moves. Here the same for the blocks of the front and for the closed terms.
A list of errors is below c (`Err.Below`) if each number is at most c times the number of all values
of its round's verifier message. These errors are numbers that a link lists (the data field
`Link.P.err`; in the statements, among them: `T.par.err`, `Z.ev.err`, `D.Z.err`, `l.P.err`,
`ldSendFamErr ..`): that a link is sound at the numbers that it lists is no statement of this file.

Main names:
  `Spec.ldSegBelowRef_psc`: the sumcheck alone: its list of moves has `Below κ` iff the sumcheck's
    own list of errors (`T.par.err`) has `Err.Below .. κ`.
  `Spec.ldSegBelowRef_in`: claims joined, then the sumcheck: iff the evader's number (`Z.ev.err`) is
    at most κ times the number of its seeds, and the sumcheck's list has `Err.Below .. κ`.
  `Spec.ldSegBelowRef_front`: the front in the table's order: `B.prog.Below κ` follows from pre's,
    the first block's, and each further sumcheck's. Steps have no round.
  `Spec.ldSegBelowRef_one`: a segment with one group (`segOne`; its body has sendings, sub-protocols
    and steps only): from the body's; the batching's evader; the link l, bridge to fold; the one
    sending (the sum over the members of multiplicity times (L choose 2) times the sample map's
    number, against the number of joint seeds); the locations ((|P| - e - 1)^t against |P|^t).

Limits: no sum of errors is formed. This file says nothing on the value of any number. It says
nothing on proof of work.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegFrontRef
import Cb.Req1.LdReqRefZk

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain
open scoped ENNReal

namespace Spec

def ldSegBelowRef_psc : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
      (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) (κ : ℝ≥0∞),
    (frPsc Kc T S E₀ Wp A0 msg).Below κ ↔ Err.Below (T.par.err E₀) κ

def ldSegBelowRef_in : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (Z : PscIn E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
      (R0 : Rels Kc Z.St0 E₀ (S.Msg × Wp)) (msg : S.Msg → Z.T.J → E) (κ : ℝ≥0∞),
    (frIn Kc Z S E₀ Wp R0 msg).Below κ ↔
    (Z.ev.err : ℝ≥0∞) ≤ κ * (Fintype.card Z.ev.D : ℝ≥0∞) ∧ Err.Below (Z.T.par.err E₀) κ

def ldSegBelowRef_front : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (z : LdStage E Kc) (B : LdFrontTab E Kc z) (κ : ℝ≥0∞),
    B.pre.Below κ → (B.Z.ev.err : ℝ≥0∞) ≤ κ * (Fintype.card B.Z.ev.D : ℝ≥0∞) →
    Err.Below (B.Z.T.par.err z.E₀) κ →
    (∀ i ≤ B.m, Err.Below ((B.T i).par.err z.E₀) κ) → B.prog.Below κ

def ldSegBelowRef_one : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc) (D : LdCl1 E Kc)
      (body : LdProg a D.bat.src) (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step)
      (l : Link Kc D.fold.src.J D.fold.mid) (Q : LdCloseD D.fold) (κ : ℝ≥0∞),
    body.Below κ → (D.Z.err : ℝ≥0∞) ≤ κ * (Fintype.card D.Z.D : ℝ≥0∞) → Err.Below l.P.err κ →
    (ldSendFamErr Q.N Q.Sd Q.L : ℝ≥0∞) ≤ κ * (Fintype.card Q.Sd.D : ℝ≥0∞) →
    (((Fintype.card D.Pf - D.e - 1) ^ Q.t : ℕ) : ℝ≥0∞) ≤
      κ * (Fintype.card (Fin Q.t → D.Pf) : ℝ≥0∞) →
    (segOne D body hT l Q).Below κ

end Spec

section
variable {E Kc : Type} [Field E] [Fintype E]

theorem ldStepF_below (S : Sig E) {St St' Wp : Type} {E₀ : ExtSpec} (A : Rels Kc St E₀ (S.Msg × Wp))
    (A' : Rels Kc St' E₀ (S.Msg × Wp)) (f : St → St') (κ : ℝ≥0∞) :
    (ldStepF S A A' f).chain.ErrBelow κ :=
  (errBelow_one _ κ).2 trivial

end

theorem ldSegBelowRef_psc : Spec.ldSegBelowRef_psc := by
  intro E Kc _ _ T S E₀ Wp A0 msg κ
  unfold frPsc
  rw [LdProg.below_snoc]
  exact ⟨fun h => (errBelow_one _ κ).1 h.2, fun h => ⟨LdProg.below_nil _ κ, (errBelow_one _ κ).2 h⟩⟩

theorem ldSegBelowRef_in : Spec.ldSegBelowRef_in := by
  intro E Kc _ _ Z S E₀ Wp R0 msg κ
  unfold frIn
  rw [LdProg.below_snoc, LdProg.below_snoc]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨((errBelow_one _ κ).1 h1).1, (errBelow_one _ κ).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨LdProg.below_nil _ κ, (errBelow_one _ κ).2 ⟨h1, trivial⟩⟩, (errBelow_one _ κ).2 h2⟩

section
variable {E Kc : Type} [Field E] [Fintype E] {z : LdStage E Kc}

theorem LdFrontTab.tw_below (B : LdFrontTab E Kc z) (κ : ℝ≥0∞)
    (h : ∀ i ≤ B.m, Err.Below ((B.T i).par.err z.E₀) κ) : ∀ k ≤ B.m, (B.tw k).Below κ
  | 0, hk => (ldSegBelowRef_psc E Kc _ _ _ _ _ _ κ).2 (h 0 hk)
  | k + 1, hk => by
      rw [LdFrontTab.tw_succ]
      exact LdProg.below_app _ _ κ
        ((LdProg.below_snoc _ _ _).2
          ⟨tw_below B κ h k (Nat.le_of_succ_le hk), ldStepF_below _ _ _ _ κ⟩)
        ((ldSegBelowRef_psc E Kc _ _ _ _ _ _ κ).2 (h (k + 1) hk))

end

theorem ldSegBelowRef_front : Spec.ldSegBelowRef_front := by
  intro E Kc _ _ z B κ hp h1 h2 h3
  unfold LdFrontTab.prog LdFrontTab.head
  exact (LdProg.below_snoc _ _ _).2
    ⟨LdProg.below_app _ _ κ
        ((LdProg.below_snoc _ _ _).2
          ⟨LdProg.below_app _ _ κ hp ((ldSegBelowRef_in E Kc _ _ _ _ _ _ κ).2 ⟨h1, h2⟩),
            ldStepF_below _ _ _ _ κ⟩)
        (B.tw_below κ h3 B.m le_rfl),
      ldStepF_below _ _ _ _ κ⟩

theorem ldSegBelowRef_one : Spec.ldSegBelowRef_one := by
  intro E Kc _ _ a D body hT l Q κ hb hZ hl hs hc
  obtain ⟨n1, n2, -, n4, n5, -⟩ := ldSeg_below_named E Kc κ
  refine ⟨hb, ?_, ?_, (n1 D.fold.tgt Q.snd).2 hs, ?_⟩
  · show D.batP.Below κ
    unfold LdCl1.batP
    exact (LdProg.below_snoc _ _ _).2
      ⟨(LdProg.below_snoc _ _ _).2 ⟨LdProg.below_nil _ κ, (errBelow_one _ κ).2 ((n2 D.bat).2 hZ)⟩,
        ldStepF_below _ _ _ _ κ⟩
  · show (Q.foldP l).Below κ
    unfold LdCloseD.foldP
    exact (LdProg.below_snoc _ _ _).2
      ⟨LdProg.below_nil _ κ, (errBelow_one _ κ).2 ((n5 D.fold l).2 hl)⟩
  · show Q.locP.Below κ
    unfold LdCloseD.locP
    exact (LdProg.below_snoc _ _ _).2 ⟨LdProg.below_nil _ κ, (errBelow_one _ κ).2 ((n4 Q.loc).2 hc)⟩

end Cb
