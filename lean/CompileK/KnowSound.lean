-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowSound.lean: BCS with shared rounds, many proofs, with a witness: the proof of
`Compile.Batch.Spec.bcsSoundBatchK` (CompileK/KnowSoundSpec.lean).

This file is about soundness of an interactive oracle proof compiled with Merkle trees and
Fiat-Shamir queries (BCS), with a witness. The three protocols are those of the interface: Test
(`L.offline`), Link (`L.link`) and Batch (`L.onlineBatch`). A lane (`Lane`, Compile/Batch/Rooted.lean;
`laneOf`, Compile/Batch/Sound.lean) is one of them as the analysis takes it, with its state
function.

Main names:
  `SndBK.laws`: (Snd-B) with a witness (`SndBK`, Ior/Batch.lean, which is defined as (Snd-B) in the
    late form of the guarded protocol (`BatchInteractiveOracleProof.guard`, Ior/Batch.lean) for the empty language)
    gives laws of a state function of the protocol itself: every statement starts in state 0 of its
    early part (`early x`); a prover message keeps 0; the switch of the round "late" keeps 0; state
    0 at a full transcript that V accepts: the witness read off its oracles is valid; the law on
    verifier messages, unchanged.
  `bcsSoundBatchK`: Bad = E_M (`EM`) or E_F (`EF`) or the state event (`StepEvent`, `stepS`) of one
    of the three protocols: the same term as in `Compile.Batch.bcsSoundBatchG`
    (Compile/Batch/Sound.lean), with the state function of `SndBK` in the lane of Batch (`laneB`).
    Its probability is bounded by the same lines, because the lanes ask of a state function only the
    law on verifier messages.
  `BcsAtK.toBcsAt`: a check on the definition: `BcsAtK` gives `BcsAt`
    (Compile/Batch/SpecSoundG.lean) for the language "there is a witness", same event, same bound.

Limits: what the head of CompileK/KnowSoundSpec.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowStar
import CompileK.KnowSoundSpec

set_option autoImplicit false

namespace Iop.BatchInteractiveOracleProof
variable {X Wn : Type} {E : ExtSpec}

/-- What `SndBK` gives, written out, in the late form. -/
theorem SndBK.laws {Q : BatchInteractiveOracleProof X E} {N : ℕ} {early : X → X} {late : Option ℕ}
    {R : X → E.Str → Wn → Prop} {wit : X → Orcs Q.loc.shape → Wn}
    {ε : Err Q.loc.shape} (h : Q.SndBK N early late R wit ε) :
    (∀ n, late = some n → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann) ∧
    ∃ State : E.Str → X → PTr Q.loc.shape → Bool,
      (∀ y x, State y (early x) (PTr.empty Q.loc.shape) = false) ∧
      (∀ y x (τ : AtP Q.loc.shape) (m : τ.round.Msg),
        State y x (.atP τ) = false → State y x (.atV (τ.snoc m)) = false) ∧
      (∀ y x (τ : AtP Q.loc.shape),
        late = some τ.idx → State y (early x) (.atP τ) = false → State y x (.atP τ) = false) ∧
      (∀ y x (τ : Tr Q.loc.shape), State y (if late.isSome then x else early x) (.full τ) = false →
        Q.loc.accept x y τ = true → R x y (wit x τ.read)) ∧
      (∀ y (x : Fin N → Option X),
        JointLaw N Q.loc.shape Q.ann ε fun j => (x j).map (State y)) := by
  obtain ⟨h0, State, h1, h2, h3, h4, h5⟩ := h
  refine ⟨h0, State, fun y x => h1 y x id, h2, fun y x τ => h3 y x τ id, fun y x τ hs ha => ?_, h5⟩
  have h6 : (Q.guard R wit).loc.accept x y τ = false := h4 y x τ id hs
  simp only [guard] at h6
  rcases (Bool.and_eq_false_iff).1 h6 with h7 | h7
  · rw [ha] at h7
    cases h7
  · simpa using h7

end Iop.BatchInteractiveOracleProof

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open scoped ENNReal

/-- BCS with shared rounds, many proofs, with the named witness. -/
theorem bcsSoundBatchK : Spec.bcsSoundBatchK := by
  intro I X Wn lam L W Rno wit εs hS hlT hlL hlB hco hW
  obtain ⟨εT, hbT, hsT⟩ := hS.sndT
  obtain ⟨εL, hbL, hsL⟩ := hS.sndL
  obtain ⟨εB, hbB, hK⟩ := hS.sndB
  obtain ⟨hB0, State, hB1, hB2, hBs, hB3, hB4⟩ := hK.laws
  have oT : (laneT W εT).OK L.maxBatchSize := laneOf_ok hW.T.sh (stOf_joint L.offline εT L.maxBatchSize)
  have oL : (laneL W εL).OK L.maxBatchSize := laneOf_ok hW.Lk.sh (stOf_joint L.link εL L.maxBatchSize)
  have oB : (laneB W εB State).OK L.maxBatchSize := laneOf_ok hW.B.sh hB4
  refine ⟨fun tr =>
      (EM tr ∨ EF tr) ∨ StepEvent (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) tr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro β A t hA
    have h := pr_stepEvent_le (S := spec lam W.K L)
      (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) (fun _ => εs)
      (fun pre e he hs =>
        hs.elim (fun h1 => h1.1 he) fun h1 => h1.elim (fun h2 => h2.1 he) fun h2 => h2.1 he)
      (fun pre o q _ => pr_stepS_le rfl rfl rfl hW.slots oT oL oB hbT hbL hbB pre o q) A t hA
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    calc
      pr A.withTrace.law
            {o | (EM o.2 ∨ EF o.2) ∨
              StepEvent (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) o.2} ≤
          pr A.withTrace.law {o | EM o.2 ∨ EF o.2} +
            pr A.withTrace.law
              {o | StepEvent (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) o.2} :=
        pr_union_le _ _ _
      _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
      _ ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
          rw [add_comm]
          gcongr
          exact Nat.le_succ t
  · rintro tr tr' ((h | h) | h)
    · exact Or.inl (Or.inl (h.append tr'))
    · exact Or.inl (Or.inr (h.append tr'))
    · exact Or.inr (StepEvent.append h tr')
  · intro tr cm π hB hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    exact mem_of_accepted Tag.test (BatchInteractiveOracleProof.ofProto L.offline) W.T _ id (fun _ => none)
      (fun s => some (.inl s)) hW.T hlT
      (Iop.BatchOne.BAnn.allLocal_coherent _) (Lg := fun _ y => L.decodeIndex y ≠ none) (stOf L.offline εT)
      (prjSym Tag.test) (fun p a => prjSym_emb Tag.test p a) some (fun _ => rfl) (fun _ => some ())
      (fun tr cms => extEnc W tr (cms.getD 0 default)) εT hM (fun h => hB (Or.inl (Or.inr h)))
      (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inl h2⟩)) [cm] () π
      (fun _ => ()) (fun _ => rfl) (fun _ _ h => absurd rfl h) (fun y hL => stOf_start hsT y () hL)
      (fun y τ m _ h => stOf_prover y () τ m h) (fun y τ _ h => stOf_full y () τ h) hrun
      (fun pre q a post htr hocc => extEnc_before htr hM (hocc _ (by simp)))
      (fun p a sl h => by
        rw [hW.extDepth.1, (hW.extT p).1, (hW.extT p).2] at h
        exact extEnc_apply hW h)
  · intro tr cm cm' π hB hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    exact mem_of_accepted Tag.link (BatchInteractiveOracleProof.ofProto L.link) W.Lk _ id (fun _ => none)
      (fun s => some (.inl s)) hW.Lk hlL
      (Iop.BatchOne.BAnn.allLocal_coherent _)
      (Lg := fun _ y => L.decodeIndex y.1 = none ∨ L.decodeIndex y.2 = L.decodeIndex y.1) (stOf L.link εL)
      (prjSym Tag.link) (fun p a => prjSym_emb Tag.link p a) some (fun _ => rfl) (fun _ => some ())
      (fun tr cms => (extEnc W tr (cms.getD 0 default), extEnc W tr (cms.getD 1 default)))
      εL hM (fun h => hB (Or.inl (Or.inr h)))
      (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inr (Or.inl h2)⟩))
      [cm, cm'] () π
      (fun _ => ()) (fun _ => rfl) (fun _ _ h => absurd rfl h) (fun y hL => stOf_start hsL y () hL)
      (fun y τ m _ h => stOf_prover y () τ m h) (fun y τ _ h => stOf_full y () τ h) hrun
      (fun pre q a post htr hocc =>
        Prod.ext (extEnc_before htr hM (hocc _ (by simp)))
          (extEnc_before htr hM (hocc _ (by simp))))
      (fun p a sl h => by
        rw [hW.extDepth.2.1] at h
        cases p with
        | inl p =>
          rw [(hW.extL.1 p).1, (hW.extL.1 p).2] at h
          exact extEnc_apply hW h
        | inr p =>
          rw [(hW.extL.2 p).1, (hW.extL.2 p).2] at h
          exact extEnc_apply hW h)
  · intro tr cm x π hB hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    obtain ⟨ρ, rts, ph, hch, hst, hacc⟩ := star_of_accepted
      Tag.onl L.onlineBatch W.B _ id some (fun s => some (.inl s)) hW.B hlB hco State
      (prjSym Tag.onl) (fun p a => prjSym_emb Tag.onl p a) some (fun _ => rfl) id
      (fun tr cms => extEnc W tr (cms.getD 0 default)) εB hM (fun h => hB (Or.inl (Or.inr h)))
      (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inr (Or.inr h2)⟩)) [cm] x π
      (instB L x) (instX_some L x) (fun n hn _ => hB0 n hn)
      (by rw [instB_zero hB0]; exact hB1 _ x)
      (fun τ m h => by
        rcases instB_step hB0 x τ.idx with h1 | ⟨h1, h2, h3⟩
        · rw [h1] at h; exact hB2 _ _ τ m h
        · rw [h2] at h; rw [h3]; exact hB2 _ x τ m (hBs _ x τ h1 h)) hrun
      (fun pre q a post htr hocc => extEnc_before htr hM (hocc _ (by simp)))
      (fun p a sl h => by
        rw [hW.extDepth.2.2, (hW.extB p).1, (hW.extB p).2] at h
        exact extEnc_apply hW h)
    -- the end law of the state function, at τ∗ (`trStar`, Compile/Batch/Runs.lean)
    have hw := hB3 _ x _ (by rw [← instB_last hB0]; exact hst) hacc
    -- the oracles of τ∗ are what the named extractor reads
    rw [readB_of_chainQB hch]
    exact hw
  · intro tr tr' cm hB hann
    exact extEnc_stable (fun h => hB (Or.inl (Or.inl h)))
      (List.prefix_append _ _) (occursIn_of_announced hann)
  · intro tr tr' π hB hocc
    exact readStar_congr _ _ _ _ _ _ fun c hc d j =>
      extLeaf_stable (fun h => hB (Or.inl (Or.inl h))) (List.prefix_append _ _) (hocc c hc) d j

/-- A check on the definition: the form with a witness gives the form for the language "there is a
witness", with the same event and the same bound. -/
theorem BcsAtK.toBcsAt {I X Wn : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L}
    {Rno : I → X → Wn → Prop} {wit : X → Orcs L.onlineBatch.loc.shape → Wn} {εs : ℝ≥0∞}
    (h : BcsAtK W Rno wit εs) :
    BcsAt W (fun i x => ∃ w, Rno i x w) εs := by
  obtain ⟨Bad, h1, h2, h3, h4, h5, h6, -⟩ := h
  exact ⟨Bad, h1, h2, h3, h4,
    fun tr cm x π hB hr => (h5 tr cm x π hB hr).imp id fun ⟨i, hi, hw⟩ => ⟨i, hi, _, hw⟩, h6⟩

end Compile.Batch
