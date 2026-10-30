-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/GlueBinding.lean: from a bad event on traces to index binding of the compiled scheme
(words of this library: lean/GLOSSARY.md).

`Spec.bcsSoundBatchG` (Compile/Batch/SpecSoundG.lean) is about an event Bad on traces. This file
joins the cheating committer, the cheating prover and the verifier into one algorithm (`joinedB`).
After the committer it adds a query to `ann` at the root cm in ivk: the query announces cm, and by
the last clause of `BcsAt` what is extracted under an announced root does not change later outside
Bad. For `W.OKG` and an event Bad as in `BcsAt` the file shows: whenever the experiment of index
binding (ZKCP/Gen.lean) ends in its bad event, the trace of the joined algorithm is Bad. The terms
`extractorB`, `tVB`, `epsB` are in Compile/Batch/SpecBinding.lean.
  `bindingBatchAt`      index binding from R_yes ⊆ R_no, the event Bad of one wire record (`BcsAt`,
                        Compile/Batch/SpecSoundG.lean) and `W.OKG`
  `bindingBatchS`       index binding from `Spec.bcsSoundBatchG`, R_yes ⊆ R_no, soundness and
                        locality of the three protocols, a coherent annotation and `W.OKG`; the
                        rounds may have proof-of-work bits
The experiment has one request and one proof, whatever the number of slots: a proof holds the proof
string of one slot.
The general tools: Compile/GlueBinding.lean.
-/
import Compile.Batch.SpecBinding
import Compile.Batch.SpecSoundG
import Compile.Batch.GlueTools
import Compile.Batch.ForestSound
import Compile.Batch.Local

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## The extractor -/

/-- If leaf and node answers are one hash block, the extractor reads entries at one-block oracles
only (`LocalTo`). -/
theorem extractorB_local (W : QueryLayout lam L) (m : OracleCoding (spec lam W.K L) lam)
    (hl : m.blocks OracleName.leaf = 1) (hn : m.blocks OracleName.node = 1) : LocalTo (extractorB W) m :=
  localTo_of_extEnc W m hl hn (extractorB W) (fun v => v.cm) (fun _ y => L.decodeIndex y)
    (fun _ _ => rfl) fun _ _ _ _ _ _ _ => rfl

/-! ## The verifier -/

theorem detBound_V (W : QueryLayout lam L) (p : Params) (v : IVK lam L) (x : X) (π : Prf lam L) :
    DetBound (V W p v x π) (tVB W) := by
  unfold V tVB
  split
  · split_ifs
    · simp only [bind_eq]
      refine ((detBound_vTS W _ _ _ _).bind
        (t := tVQB W.Lk W.depthReq + (tVQB W.B W.depthReq + 0)) fun a =>
          (detBound_vLS W _ _ _ _ _).bind (t := tVQB W.B W.depthReq + 0) fun b =>
            (detBound_vBS W _ _ _ _ _).bind (t := 0) fun c => detBound_pure _ _).mono ?_
      omega
    · exact detBound_pure _ _
  · exact detBound_pure _ _

/-! ## The core -/

/-- The deterministic part of index binding: from `hT`, `hL`, `hO` (Test, Link, Batch), x is in R_no
at the index to which Y₀ decodes. -/
theorem pathLemmaB {Rno : I → X → Prop} {x : X} {Y₀ Y₁ : Fin L.wordLength → L.Symbol} (hT : L.decodeIndex Y₀ ≠ none)
    (hL : L.decodeIndex Y₀ = none ∨ L.decodeIndex Y₁ = L.decodeIndex Y₀)
    (hO : L.decodeIndex Y₁ = none ∨ ∃ i, L.decodeIndex Y₁ = some i ∧ Rno i x) :
    ∃ i, L.decodeIndex Y₀ = some i ∧ Rno i x := by
  rcases hL with h | h
  · exact absurd h hT
  · rcases hO with h' | ⟨i, hi, hr⟩
    · exact absurd (h ▸ h') hT
    · exact ⟨i, h ▸ hi, hr⟩

/-- Under the hypotheses below: outside Bad, the request of an accepted proof is in R_no at the
index that the committer's trace determines. -/
theorem coreB (W : QueryLayout lam L) (hW : W.OKG) (p : Params) {Rno : I → X → Prop} {Bad : Tc W → Prop}
    (hT : ∀ tr cm π, ¬ Bad tr → RunsIn tr (vT W cm π) true → L.decodeIndex (extEnc W tr cm) ≠ none)
    (hL : ∀ tr cm cm' π, ¬ Bad tr → RunsIn tr (vL W cm cm' π) true →
      L.decodeIndex (extEnc W tr cm) = none ∨ L.decodeIndex (extEnc W tr cm') = L.decodeIndex (extEnc W tr cm))
    (hO : ∀ tr cm x π, ¬ Bad tr → RunsIn tr (vB W cm x π) true →
      L.decodeIndex (extEnc W tr cm) = none ∨ ∃ i, L.decodeIndex (extEnc W tr cm) = some i ∧ Rno i x)
    (hE : ∀ tr tr' cm,
      ¬ Bad (tr ++ tr') → Announced W tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm)
    (v : IVK lam L) (x : X) (π : Prf lam L) (trC rest trV : Tc W) (u : Unit) (hsub : trV ⊆ rest)
    (hrun : RunsIn trV (V W p v x π) true) (hnb : ¬ Bad ((trC ++ [annE W v.cm u]) ++ rest)) :
    ∃ i, L.decodeIndex (extEnc W trC v.cm) = some i ∧ Rno i x := by
  set tr : Tc W := (trC ++ [annE W v.cm u]) ++ rest with htr
  have hrun' : RunsIn tr (V W p v x π) true :=
    hrun.mono fun e he => List.mem_append_right _ (hsub he)
  have hann : Announced W (trC ++ [annE W v.cm u]) v.cm := by
    cases u
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  have hext : extEnc W trC v.cm = extEnc W tr v.cm := by
    rw [← extEnc_ann trC v.cm u v.cm]
    exact hE _ rest v.cm hnb hann
  rw [hext]
  unfold V at hrun'
  split at hrun'
  · rename_i πT πL πB _ _ _
    split_ifs at hrun'
    · simp only [bind_eq, pure_eq, runsIn_bind_iff, runsIn_pure_iff] at hrun'
      obtain ⟨a, ha, b, hb, c, hc, habc⟩ := hrun'
      simp only [Bool.and_eq_true] at habc
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := habc
      obtain ⟨_, _, ha'⟩ := runsIn_verifyB_of_strict hW.T ha
      obtain ⟨_, _, hb'⟩ := runsIn_verifyB_of_strict hW.Lk hb
      obtain ⟨_, _, hc'⟩ := runsIn_verifyB_of_strict hW.B hc
      exact pathLemmaB (hT tr v.cm _ hnb ha') (hL tr v.cm π.cm _ hnb hb') (hO tr π.cm x _ hnb hc')
    · exact absurd (runsIn_pure_iff.1 hrun') (by simp)
  · exact absurd (runsIn_pure_iff.1 hrun') (by simp)

/-! ## The theorem -/

/-- the cheating committer, the added query at the root cm in ivk, the cheating prover and V, as one
algorithm -/
def joinedB (W : QueryLayout lam L) (p : Params) {St : Type} (Ct : TypedOracleComputation lam W.K L (IVK lam L × St))
    (Pt : St → TypedOracleComputation lam W.K L (X × Prf lam L)) :
    TypedOracleComputation lam W.K L Unit :=
  Ct.bind fun a => (OComp.ask (S := spec lam W.K L) OracleName.ann a.1.cm).bind fun _ =>
    (Pt a.2).bind fun xp => (V W p a.1 xp.1 xp.2).bind fun _ => OComp.pure ()

theorem joinedB_queryBound (W : QueryLayout lam L) (p : Params) {St : Type}
    {Ct : TypedOracleComputation lam W.K L (IVK lam L × St)} {Pt : St → TypedOracleComputation lam W.K L (X × Prf lam L)} {tC tP : ℕ}
    (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    (joinedB W p Ct Pt).QueryBound (tC + tP + tVB W + 1) := by
  have h : (joinedB W p Ct Pt).QueryBound (tC + (1 + (tP + (tVB W + 0)))) := by
    unfold joinedB
    exact hC.bind fun a =>
        (detBound_ask (S := spec lam W.K L) OracleName.ann a.1.cm).queryBound.bind fun _ =>
      (hP a.2).bind fun xp => (detBound_V W p a.1 xp.1 xp.2).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- Index binding of the compiled scheme from R_yes ⊆ R_no, the event Bad of this wire record
(`BcsAt W Rno N.εs`) and a well-formed wire record (`W.OKG`; its rounds may have proof-of-work
bits). -/
theorem bindingBatchAt (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Ryes Rno : I → X → Prop)
    (N : LH.Nums) (hsub : ∀ i x, Ryes i x → Rno i x) (hB : BcsAt W Rno N.εs) (hW : W.OKG) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair Ryes Rno hsub) (argB W WP p) (extractorB W) (epsB W N) := by
  intro tC tP St Ct Pt hC hP
  obtain ⟨Bad, hrare, -, hT, hL, hO, hE⟩ := hB
  have hpt : ∀ f : Fam (spec lam W.K L),
      PrCoins f (ZKCP.Gen.bindingExp (argB W WP p) (extractorB W) Ct Pt)
          (ZKCP.Gen.bindingBad (relPair Ryes Rno hsub)) ≤
        PrCoins f (joinedB W p Ct Pt).withTrace {o | Bad o.2} := by
    intro f
    unfold PrCoins
    simp only [ZKCP.Gen.bindingExp, bind_eq, pure_eq, joinedB, withTrace_bind, OComp.bind_assoc,
      OComp.ask, OComp.withTrace, OComp.bind, OComp.runEager_bind, OComp.runEager]
    refine pr_bind_le_bind _ _ _ _ _ fun a _ => pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
    have e1 : ((argB W WP p).V a.1.1 b.1.1 b.1.2).runEager f =
        ((V W p a.1.1 b.1.1 b.1.2).withTrace.runEager f).map Prod.fst :=
      (runEager_withTrace_fst f _).symm
    rw [e1, PMF.bind_map]
    refine pr_bind_le_bind _ _ _ _ _ fun c hc => pr_pure_le_pure ?_
    rintro ⟨hacc, hbad⟩
    by_contra hnb
    have hrun : RunsIn c.2 (V W p a.1.1 b.1.1 b.1.2) true := by
      have := runsIn_of_mem_support (detBound_V W p a.1.1 b.1.1 b.1.2) f c hc
      have hc1 : c.1 = true := hacc
      rwa [hc1] at this
    have hnb' : ¬ Bad ((a.2 ++ [annE W a.1.1.cm (f OracleName.ann a.1.1.cm)]) ++ (b.2 ++ (c.2 ++ []))) := by
      simpa [annE] using hnb
    obtain ⟨i, hi, hr⟩ := coreB W hW p hT hL hO hE a.1.1 b.1.1 b.1.2 a.2 (b.2 ++ (c.2 ++ [])) c.2 _
      (fun e he => List.mem_append_right _ (List.mem_append_left _ he)) hrun hnb'
    have hi' : (extractorB W).Ei a.1.1 a.2 = some i := hi
    simp only [hi'] at hbad
    rcases hbad with hb | hb
    · exact hb ⟨(), hr⟩
    · exact hb hr
  calc
    Rom.Pr (ZKCP.Gen.bindingExp (argB W WP p) (extractorB W) Ct Pt)
          (fun _ => ZKCP.Gen.bindingBad (relPair Ryes Rno hsub)) ≤
        Rom.Pr (joinedB W p Ct Pt).withTrace (fun _ => {o | Bad o.2}) :=
      MeasureTheory.lintegral_mono hpt
    _ = pr (joinedB W p Ct Pt).withTrace.law {o | Bad o.2} := Pr_eq_law _ _
    _ ≤ ((tC + tP + tVB W + 1 : ℕ) : ℝ≥0∞) * N.εs +
          2 * ((tC + tP + tVB W + 1 + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
        hrare Unit (joinedB W p Ct Pt) _ (joinedB_queryBound W p hC hP)
    _ = epsB W N tC tP := rfl

/-- Index binding from exactly what the proof uses: `Spec.bcsSoundBatchG` (a hypothesis here;
Compile/Batch/Sound.lean proves it), R_yes ⊆ R_no, the three soundness properties, locality, a
coherent annotation, `W.OKG`; not the whole bundle `L.Props`. So for a concrete protocol it can be
proved before hiding and completeness. -/
theorem bindingBatchS (hS : Spec.bcsSoundBatchG) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (Ryes Rno : I → X → Prop) (N : LH.Nums) (hsub : ∀ i x, Ryes i x → Rno i x)
    (hsound : L.Sound Rno N.εs) (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal)
    (hlB : L.onlineBatch.loc.IsLocal) (hcoh : L.onlineBatch.ann.Coherent) (hW : W.OKG) :
    ZKCP.Gen.HasIndexBindingWith (relPair Ryes Rno hsub) (argB W WP p) (extractorB W) (epsB W N) :=
  bindingBatchAt W WP p Ryes Rno N hsub (hS I X lam L W Rno N.εs hsound hlT hlL hlB hcoh hW) hW

end Compile.Batch
