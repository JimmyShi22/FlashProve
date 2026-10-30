-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowSoundT.lean: BCS with shared rounds, many proofs, with a witness map that reads the
whole local transcript.

This file is about soundness of an interactive oracle proof compiled with Merkle trees and
Fiat-Shamir queries (BCS): under the hypotheses of `Spec.bcsSoundBatchKT`, outside an event Bad on
lists of queries, a proof that the compiled verifier of a slot of Batch accepts, with all its
queries in the list, yields a transcript off which a witness is read, unless the encoded index does
not decode.
A definition, a statement and its proof. The analogue of CompileK/KnowSoundSpec.lean and
CompileK/KnowSound.lean for a wide witness map, which reads the instance, the encoded index and the
slot's whole local transcript (Hiop/KnowWide.lean).

Main names:
  `trStar_congr`: the extracted transcript depends on the trace only through what stands under the
    roots of the rounds.
  `BcsAtKT W Rno wit εs`: `BcsAtK` (CompileK/KnowSoundSpec.lean) with these changes. The clause for
    a slot: outside Bad, if the compiled verifier of a slot accepts (x, π) and all its queries are
    in the trace, then its chain runs within the trace to verifier messages ρ, and the encoded index
    under the root does not decode, or it decodes to i and wit x y τ∗ is a witness of (i, x): y the
    extracted encoded index, τ∗ = starB W tr π ρ the extracted local transcript with ρ. Stability,
    outside Bad: τ∗ at given ρ does not change when the trace goes on, once all roots of π occur;
    new: the same for an encoded index under a root that occurs.
  `Spec.bcsSoundBatchKT`: the wide knowledge soundness of the interface (`BatchProtocol.SoundKT`,
    Hiop/KnowWide.lean), locality, coherence and the wire's laws (`W.OKG`) give `BcsAtKT`. The event
    Bad and its bound are those of CompileK/KnowSound.lean, with the state function of `SndBKT` in
    the lane of Batch (`laneB`).

The proof: `star_of_accepted` (CompileK/KnowStar.lean), which carries it, already speaks of the full
τ∗.

Limits: it speaks of a trace that holds the verifier's queries. In the experiment of the binding
definition the extractor is not handed these: CompileK/KnowBindingT.lean.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowSound
import CompileK.KnowExtT

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open scoped ENNReal

section Congr
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- The extracted transcript depends on the trace only through what stands under the roots of the
rounds. -/
theorem trStar_congr {tr tr' : Trace (spec lam K L)} :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (prjS : (p : OPos s) → Body L → Option (OSym s p)) (rts : RootsOfChain lam s)
        (pls : Plains s) (ρ : Rho s),
      (∀ c ∈ RootsOfChain.list s rts, ∀ d j, extLeaf tr d c j = extLeaf tr' d c j) →
      trStar tr s A ws prjS rts pls ρ = trStar tr' s A ws prjS rts pls ρ
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (w, ws), prjS, (rt, rts), (pl, pls), (c, ρ), h => by
      show (msgStar tr w (fun p => prjS (.inl p)) rt pl,
          c,
          trStar tr s A ws (fun p => prjS (.inr p)) rts pls ρ) =
        (msgStar tr' w (fun p => prjS (.inl p)) rt pl,
          c,
          trStar tr' s A ws (fun p => prjS (.inr p)) rts pls ρ)
      rw [msgStar_congr w (fun p => prjS (.inl p)) pl fun c hc => h c (by
            rcases hc with hc | hc <;> simp [RootsOfChain.list, hc]),
        trStar_congr s A ws (fun p => prjS (.inr p)) rts pls ρ fun c hc => h c (by
          simp only [RootsOfChain.list, List.mem_append]; exact Or.inr hc)]

end Congr

variable {I X Wn : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The conclusion of BCS with shared rounds, with the value of a wide witness map, for one wire. -/
def BcsAtKT (W : QueryLayout lam L) (Rno : I → X → Wn → Prop)
    (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ), A.QueryBound t →
      pr A.withTrace.law {o | Bad o.2} ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    (∀ tr cm π, ¬ Bad tr → RunsIn tr (vT W cm π) true → L.decodeIndex (extEnc W tr cm) ≠ none) ∧
    (∀ tr cm cm' π, ¬ Bad tr → RunsIn tr (vL W cm cm' π) true →
      L.decodeIndex (extEnc W tr cm) = none ∨ L.decodeIndex (extEnc W tr cm') = L.decodeIndex (extEnc W tr cm)) ∧
    (∀ tr cm x π, ¬ Bad tr → RunsIn tr (vB W cm x π) true →
      ∃ ρ rts ph,
        RunsIn tr (chainS W cm x π) (some (ρ, rts, ph)) ∧
        (L.decodeIndex (extEnc W tr cm) = none ∨
          ∃ i,
            L.decodeIndex (extEnc W tr cm) = some i ∧ Rno i x (wit x (extEnc W tr cm) (starB W tr π ρ)))) ∧
    (∀ tr tr' cm,
      ¬ Bad (tr ++ tr') → Announced W tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm) ∧
    (∀ tr tr' π ρ, ¬ Bad (tr ++ tr') →
      (∀ c ∈ RootsOfChain.list L.onlineBatch.loc.shape (rtsB W π), (evM lam W.K L).OccursIn tr c) →
      starB W tr π ρ = starB W (tr ++ tr') π ρ) ∧
    (∀ tr tr' cm,
      ¬ Bad (tr ++ tr') → (evM lam W.K L).OccursIn tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm)

/-- BCS with shared rounds, many proofs, wide witness map, for a wire whose rounds may have proof of
work. -/
def Spec.bcsSoundBatchKT : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞),
    L.SoundKT Rno wit εs → L.offline.IsLocal → L.link.IsLocal → L.onlineBatch.loc.IsLocal →
    L.onlineBatch.ann.Coherent → W.OKG → BcsAtKT W Rno wit εs

/-- BCS with shared rounds, many proofs, with the value of a wide witness map at the extracted
transcript. -/
theorem bcsSoundBatchKT : Spec.bcsSoundBatchKT := by
  intro I X Wn lam L W Rno wit εs hS hlT hlL hlB hco hW
  obtain ⟨εT, hbT, hsT⟩ := hS.sndT
  obtain ⟨εL, hbL, hsL⟩ := hS.sndL
  obtain ⟨εB, hbB, hK⟩ := hS.sndB
  obtain ⟨hB0, State, hB1, hB2, hBs, hB3, hB4⟩ :=
    (sndBKT_laws X Wn _ L.onlineBatch L.maxBatchSize L.early L.late (L.relB Rno) wit εB).1 hK
  have oT : (laneT W εT).OK L.maxBatchSize := laneOf_ok hW.T.sh (stOf_joint L.offline εT L.maxBatchSize)
  have oL : (laneL W εL).OK L.maxBatchSize := laneOf_ok hW.Lk.sh (stOf_joint L.link εL L.maxBatchSize)
  have oB : (laneB W εB State).OK L.maxBatchSize := laneOf_ok hW.B.sh hB4
  refine ⟨fun tr =>
      (EM tr ∨ EF tr) ∨ StepEvent (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) tr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    -- the end law of the state function, at τ∗
    have hw := hB3 _ x _ (by rw [← instB_last hB0]; exact hst) hacc
    refine ⟨ρ, rts, ph, hch, ?_⟩
    unfold starB
    rw [rtsB_of_chainQB hch]
    exact hw
  · intro tr tr' cm hB hann
    exact extEnc_stable (fun h => hB (Or.inl (Or.inl h)))
      (List.prefix_append _ _) (occursIn_of_announced hann)
  · intro tr tr' π ρ hB hocc
    exact trStar_congr _ _ _ _ _ _ _ fun c hc d j =>
      extLeaf_stable (fun h => hB (Or.inl (Or.inl h))) (List.prefix_append _ _) (hocc c hc) d j
  · intro tr tr' cm hB hocc
    exact extEnc_stable (fun h => hB (Or.inl (Or.inl h))) (List.prefix_append _ _) hocc

/-- A check on the definition: the wide form gives the form for the language "there is a witness",
with the same event and the same bound. -/
theorem BcsAtKT.toBcsAt {I X Wn : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L}
    {Rno : I → X → Wn → Prop} {wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn}
    {εs : ℝ≥0∞} (h : BcsAtKT W Rno wit εs) :
    BcsAt W (fun i x => ∃ w, Rno i x w) εs := by
  obtain ⟨Bad, h1, h2, h3, h4, h5, h6, -, -⟩ := h
  exact ⟨Bad, h1, h2, h3, h4, fun tr cm x π hB hr => by
    obtain ⟨_, _, _, _, hw⟩ := h5 tr cm x π hB hr
    exact hw.imp id fun ⟨i, hi, hw⟩ => ⟨i, hi, _, hw⟩, h6⟩

end Compile.Batch
