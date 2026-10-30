-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/RelTrue.lean: guards on the true request (`TrueAt` of Cm/RelBase.lean), the sentence in which the
language of the relation pair of Cm/TargetPRel.lean ends, at a lawful table and a prime p with
2^61 - 1 ≤ p; and the index type reaches every well-formed choice of weight tensors.

In standard terms: sanity checks on a definition: theorems, most at made-up weights, which show
that the predicate `TrueAt` is neither empty nor everything and reads every covered position, a
layer's weights and earlier tokens.

Facts on that sentence alone: no cells, no code, no protocol, no chance. For the pair of
Cm/TargetPRel.lean `Spec.target_p_guards` (Cm/TargetPLangs.lean) carries four of them to "has a
witness": `true_zero`, `false_zero`, `true_layer`, `true_earlier`; `false_form` has its like in
`head3_of_rno` (Cm/TargetPRelProofs.lean). No theorem carries `true_pos`, `true_unique` or
`true_next` to that pair. For the pair with the cost ledger: Policy/Rel/LedgerGuards.lean,
Policy/Rel/PosGuards.lean. Further guards (the router, the
routed experts, a filler behind the covered stretch, an index with no true request):
Cm/RelTrueExp.lean. The sentence against the text's, written out after it: Cm/RelTruePaper.lean.

Main names:
  `Idx.ofIndex`, `index_ofIndex`, `index_onto`: every well-formed choice of weight tensors
    (`Index ppref`) is held by a digit matrix: `matrixRef` of Inst/Model/MatrixOf.lean, cut to the
    shape.
  `trueAt_ofIndex`: at the matrix of given tensors `TrueAt` is the relation "exact match" (`RinfS`,
    Inst/Model/ProgramR.lean) at these tensors.
  `true_zero`: not empty, with many covered positions: at every lawful table (`Lawful pp`,
    Inst/Model/Scales.lean: another predicate than `Scales.Lawful` of Cm/Rel2.lean), at the matrix
    of the all-zero weights, for every r < e ≤ 1,024 the request with all tokens 0 is true.
  `false_zero`: not everything: there, a request with one covered position whose checked token is
    not 0 is not true.
  `false_form`: a request without its form (e ≤ r, or e < 1,024 with y ≠ 0) is not true, at any
    words and index.
  `true_pos`: that position's token against that position's logits: under `hσ`, `hτ`, at the
    reference scales and the made-up weights "token t is embedded in channel σ t, channel j votes
    for token τ j": a request is true if and only if it has its form and at every covered position
    t the checked token is τ (σ x_t).
  `true_unique`: at any words and index: two true requests with the same r and e and the same
    tokens 0 .. r have the same tokens up to number e (token number 1,024 is y): the reply is a
    function of what stands before it.
  `true_next`: see its doc comment.
  `true_layer`: it reads the weights of a layer, at the reference scales: two indices with the same
    embedding, output matrix and layers 1 .. 47, and one request that is true at the one and not at
    the other.
  `true_earlier`: it reads earlier tokens, at the reference scales: one index, two prompts with the
    same last token; one reply is true of the one and not of the other.

Limits: all indices here are made up for these proofs: their weights are made up; where a theorem
stands at fixed scales, these are the library's reference scales (`ppRef`, Inst/Model/Scales.lean;
where their numbers come from: lean/CREDITS.md, section 8). No theorem shows a true request at
weights of interest; the guard on a layer has one layer that computes, on "the next token".
This file says nothing on how often the program runs on real weights (where a range test fails at
any of the 1,024 positions no request is true). That the map from digit matrices to tensors is not
one to one is by reading of the layout; no theorem here.
These guards import more files of Inst/Model/ than Cm/Rel.lean does, through the file that holds the
all-zero index; the statements speak of `TrueAt` alone.
`true_layer` and `true_earlier` use the made-up weights and prompts of Inst/Model/SanityAtt.lean.

Terms: lean/GLOSSARY.md.
-/
import Cm.RelBase
import Inst.Model.RequestGuards2
import Inst.Model.IndexM
import Inst.Model.SanityAtt

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All Inst.Model.ScalesSanity Inst.Model.ProgramRGuards
  Inst.Model.SanityRef Inst.Model.SanityAtt Finset
open Inst.Model.Layout (kRef hRef)

/-! ## 1. Every well-formed choice of tensors is held by a digit matrix -/

theorem ext_cut_ref (j : Index ppref) : ext (cut (Layout.matrixRef j)) = Layout.matrixRef j :=
  ext_cut fun y c h => IndexM.matrixRef_zero j y c h

/-- the digit matrix that holds the tensors j, with 0 wherever no byte of a weight lies -/
def Idx.ofIndex (j : Index ppref) : Idx :=
  ⟨cut (Layout.matrixRef j), by rw [ext_cut_ref]; exact Layout.wfw_matrixRef j⟩

theorem mat_ofIndex (j : Index ppref) : (Idx.ofIndex j).mat = Layout.matrixRef j := ext_cut_ref j

theorem weights_ofIndex (j : Index ppref) : (Idx.ofIndex j).weights = j.val := by
  unfold Idx.weights
  rw [mat_ofIndex]
  exact congrArg Subtype.val (Layout.indexOf_matrixRef j)

theorem index_ofIndex (j : Index ppref) : (Idx.ofIndex j).index = j :=
  Subtype.ext (weights_ofIndex j)

theorem index_onto : Function.Surjective Idx.index := fun j => ⟨_, index_ofIndex j⟩

theorem trueAt_ofIndex (κ : ℕ → LayerScale) (nf : NormPar) (j : Index ppref) (x : Instance ppref) :
    TrueAt κ nf (Idx.ofIndex j) x ↔ RinfS ppref κ nf (fun _ => tbRef) j x := by
  rw [trueAt_iff, weights_ofIndex, RinfS_iff]
  exact Iff.rfl

/-! ## 2. Not empty, not everything -/

theorem true_zero {pp : ScalesAndPolicy} (h : Lawful pp) (rF eF : Fin (ppref.T + 1)) (hre : rF.val < eF.val) :
    TrueAt pp.kap pp.nf (Idx.ofIndex iZero) (RequestGuards2.xz rF eF) :=
  (trueAt_ofIndex _ _ iZero _).2
    (zero_true_of h _ ⟨hre, Nat.lt_succ_iff.1 eF.isLt, fun _ => rfl⟩ fun t _ _ =>
      RequestGuards2.xz_w rF eF t)

theorem false_zero (κ : ℕ → LayerScale) (nf : NormPar) (x : Instance ppref) {t : ℕ} (hr : x.r ≤ t)
    (he : t < x.e) (hw : x.w t ≠ 0) :
    ¬ TrueAt κ nf (Idx.ofIndex iZero) x := fun hT => by
  have hS := ((trueAt_ofIndex κ nf iZero x).1 hT).2.2 t hr he
  rw [gap_zero' (lg_zero _ _ _ _ t) (x.w_lt t), if_neg hw] at hS
  exact absurd hS one_ne_zero

theorem false_form (κ : ℕ → LayerScale) (nf : NormPar) (i : Idx) (x : Instance ppref)
    (h : x.e ≤ x.r ∨ (x.e < ppref.T ∧ x.y.val ≠ 0)) : ¬ TrueAt κ nf i x := by
  rintro ⟨⟨a, _, c⟩, _⟩
  rcases h with h | ⟨h1, h2⟩
  · omega
  · exact h2 (c h1)

/-! ## 3. That position's token against that position's logits -/

section Pos
variable (σ τ : ℕ → ℕ) (prompt : Fin ppref.T → Fin ppref.V)

/-- Under `hσ`: the logits of wts σ τ at every position: 2,047 for the token for which the channel
of that position's token votes, 0 for every other -/
theorem lg_pos (hσ : ∀ t, σ t < 5120) (pos : ℕ) (hpos : pos < ppref.T) {ι : ℕ} (hι : ι < 202048) :
    lg ppref tbRef (wts σ τ) prompt pos ι = if ι = τ (σ (prompt ⟨pos, hpos⟩)) then 2047 else 0 := by
  have e : X ppref tbRef (wts σ τ) prompt (2 * ppref.layers) pos =
      row (σ (prompt ⟨pos, hpos⟩)) := by
    rw [show X ppref tbRef (wts σ τ) prompt (2 * ppref.layers) = X ppref tbRef (wts σ τ) prompt 0
        from X_zero ppref tbRef (embOf σ) (headOf τ) prompt shifts_ref _]
    exact X0_wts σ τ prompt hσ pos hpos
  unfold lg nrm dot
  rw [e]
  show ∑ j ∈ range 5120, NORM.out npR 5120 (row (σ (prompt ⟨pos, hpos⟩))) j * headOf τ j ι = _
  rw [sum_eq_single (σ (prompt ⟨pos, hpos⟩))
        (fun j _ hj => by rw [out_row (hσ _), if_neg hj, zero_mul])
        (fun h => absurd (mem_range.2 (hσ _)) h),
    out_row (hσ _), if_pos rfl]
  unfold headOf
  rw [if_pos ⟨hσ _, hι⟩]
  split_ifs <;> norm_num

theorem lgK_ref (w : Weights) (p : Fin ppref.T → Fin ppref.V) :
    lgK ppref (fun _ => ppref.scale) ppref.nf (fun _ => tbRef) w p = lg ppref tbRef w p := by
  funext pos ι
  unfold lgK lg nrmK nrm
  rw [Inst.Model.XK_const]

theorem runsK_ref (w : Weights) (p : Fin ppref.T → Fin ppref.V) (h : Runs ppref tbRef w p) :
    RunsK ppref (fun _ => ppref.scale) ppref.nf (fun _ => tbRef) w p := by
  unfold RunsK
  rw [Inst.Model.XK_const]
  exact h

theorem true_pos (hσ : ∀ t, σ t < 5120) (hτ : ∀ j, τ j < 202048) (x : Instance ppref) :
    TrueAt ppRef.kap ppRef.nf (Idx.ofIndex ⟨wts σ τ, wts_wf σ τ⟩) x ↔
    Head3 x ∧ ∀ t (ht : t < ppref.T), x.r ≤ t → t < x.e → x.w t = τ (σ (x.prompt ⟨t, ht⟩)) := by
  rw [trueAt_iff, weights_ofIndex]
  refine and_congr_right fun _ => ?_
  show (RunsK ppref ppRef.kap ppref.nf (fun _ => tbRef) (wts σ τ) x.prompt ∧
      ∀ t, x.r ≤ t → t < x.e →
        gapOf ppref.V (lgK ppref ppRef.kap ppref.nf (fun _ => tbRef) (wts σ τ) x.prompt t) (x.w t) =
          0) ↔
    _
  rw [kap_ref, lgK_ref]
  have hw : ∀ t, x.w t < 202048 := fun t => x.w_lt t
  constructor
  · rintro ⟨-, hg⟩ t ht hr he
    have h1 :=
      ((gapOf_eq_zero_iff _ _ (x.w_lt t)).1 (hg t hr he)).1 (τ (σ (x.prompt ⟨t, ht⟩))) (hτ _)
    rw [lg_pos σ τ x.prompt hσ t ht (hτ _), if_pos rfl, lg_pos σ τ x.prompt hσ t ht (hw t)] at h1
    by_contra hne
    rw [if_neg hne] at h1
    norm_num at h1
  · intro h
    refine ⟨runsK_ref _ _ (runs_wts σ τ x.prompt hσ), fun t hr he => ?_⟩
    have ht : t < ppref.T := lt_of_lt_of_le he x.e_le
    rw [gapOf_eq_zero_iff _ _ (x.w_lt t)]
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [lg_pos σ τ x.prompt hσ t ht hv, lg_pos σ τ x.prompt hσ t ht (hw t), if_pos (h t ht hr he)]
      split_ifs <;> norm_num
    · rw [lg_pos σ τ x.prompt hσ t ht (lt_trans hv (hw t)), lg_pos σ τ x.prompt hσ t ht (hw t),
        if_pos (h t ht hr he), if_neg (by rw [← h t ht hr he]; exact Nat.ne_of_lt hv)]
      norm_num

end Pos

/-! ## 4. The reply is a function of what stands before it -/

theorem true_unique (κ : ℕ → LayerScale) (nf : NormPar) (i : Idx)
    (x x' : Instance ppref) (hr : x.r = x'.r) (he : x.e = x'.e) (hx : TrueAt κ nf i x)
    (hx' : TrueAt κ nf i x') (h0 : ∀ t ≤ x.r, x.tok t = x'.tok t) : ∀ t ≤ x.e, x.tok t = x'.tok t :=
  RequestGuards2.reply_unique ppref κ nf (fun _ => tbRef) i.index x x' hr he
    ((trueAt_iff κ nf i x).1 hx).2 ((trueAt_iff κ nf i x').1 hx').2 h0

/-! ## 5. It reads a layer's weights, and earlier tokens -/

/-- at `Idx.ofIndex j`, on "the next token after these 1,024 tokens", at the reference scales, a
true request is: Model_i(prompt) = y (`ModelIs`, Inst/Model/Program.lean) -/
theorem true_next (j : Index ppref) (p : Fin ppref.T → Fin ppref.V) (y : Fin ppref.V) :
    TrueAt ppRef.kap ppRef.nf (Idx.ofIndex j) (Instance.nextOf p y) ↔
    ModelIs ppref tbRef j.val p y.val := by
  rw [trueAt_ofIndex, RinfS_iff]
  have h1 : RinfS0 ppref ppRef.kap ppRef.nf (fun _ => tbRef) j (Instance.nextOf p y) ↔
      ModelIsK ppref ppRef.kap ppRef.nf (fun _ => tbRef) j.val p y.val :=
    ModelS_nextOf ppref (by decide) _ _ _ j.val p y
  have h2 : ModelIsK ppref ppRef.kap ppRef.nf (fun _ => tbRef) j.val p y.val ↔
      ModelIs ppref tbRef j.val p y.val := by
    rw [kap_ref]
    exact iff_of_eq (congrFun (congrFun (RinfK_const ppref tbRef) j) (Instance.nextOf p y))
  exact ⟨fun h => h2.1 (h1.1 h.2), fun h => ⟨head3_nextOf (by decide) p y, h1.2 (h2.2 h)⟩⟩

theorem true_layer :
    ∃ (i i' : Idx) (x : Instance ppref),
      i.weights.Emb = i'.weights.Emb ∧
      i.weights.H = i'.weights.H ∧
      (∀ L, L ≠ 0 → i.weights.layer L = i'.weights.layer L) ∧
      TrueAt ppRef.kap ppRef.nf i x ∧
      ¬ TrueAt ppRef.kap ppRef.nf i' x := by
  refine ⟨Idx.ofIndex ⟨wA, wA_wf⟩, Idx.ofIndex ⟨wZ, wZ_wf⟩,
    Instance.nextOf pA ⟨7, by decide⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [weights_ofIndex, weights_ofIndex]; rfl
  · rw [weights_ofIndex, weights_ofIndex]; rfl
  · intro L hL
    rw [weights_ofIndex, weights_ofIndex]
    exact if_neg hL
  · exact (true_next ⟨wA, wA_wf⟩ pA ⟨7, by decide⟩).2 model_wA_pA
  · intro h
    have h7 := (true_next ⟨wZ, wZ_wf⟩ pA ⟨7, by decide⟩).1 h
    exact absurd (modelIs_unique _ _ _ _ h7 model_wZ_pA) (by decide)

theorem true_earlier :
    ∃ (i : Idx) (p p' : Fin ppref.T → Fin ppref.V) (y : Fin ppref.V),
      p ⟨1023, by decide⟩ = p' ⟨1023, by decide⟩ ∧
      TrueAt ppRef.kap ppRef.nf i (Instance.nextOf p y) ∧
      ¬ TrueAt ppRef.kap ppRef.nf i (Instance.nextOf p' y) := by
  refine ⟨Idx.ofIndex ⟨wA, wA_wf⟩, pA, pB, ⟨7, by decide⟩, rfl, ?_, ?_⟩
  · exact (true_next ⟨wA, wA_wf⟩ pA ⟨7, by decide⟩).2 model_wA_pA
  · intro h
    have h7 := (true_next ⟨wA, wA_wf⟩ pB ⟨7, by decide⟩).1 h
    exact absurd (modelIs_unique _ _ _ _ h7 model_wA_pB) (by decide)

end Cm
