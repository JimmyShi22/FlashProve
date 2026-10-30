-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetPartBite2.lean: a guard for "the proofs hide the index": there is something to hide
between. At every lawful table of scales, for every range r < e ≤ 1,024, one request is true at
8,192^48 indices with pairwise different weights; at the reference scales two indices share a true
request and are told apart by another.

Definitions, statements (`Cm.Spec.target_bite2_many`, `target_bite2_two`, `target_bite2_same`,
`target_bite2_ref`) and proofs. Nothing assumed beyond the hypotheses of the statements and whatever
the arguments hold as proofs. No cells, no code, no protocol, no chance.
"True" is `PaperTrue` (Cm/RelTruePaper.lean): r < e ≤ 1,024; the integer program runs on the
prompt; at every position t of the range below 1,023 the next token of the prompt is the greedy
token of the logits at t; the reply is the greedy token at position 1,023 if e = 1,024, and 0
otherwise. By `paper_iff` there it is `TrueAt` (Cm/RelBase.lean).

Why: it may be objected: "some
request is true" is shown at the all-zero weights alone, and "the index matters" as true-at-one,
false-at-the-other. If at some lawful table one index alone had true requests, a simulator that
holds that index would serve, and a sentence on the hiding of proofs would have nothing to hide
between.

Main names:
  `biteVs a`: made-up indices: see its docstring (`iW`: Inst/Model/ScalesSanity.lean).
  `Spec.target_bite2_many`: the request is the one with all tokens 0 and that range
    (`RequestGuards2.xz`).
  `Spec.target_bite2_same`: an admission as a theorem: at every lawful s, for every a and every
    request x: x is true at `biteVs a` exactly if x has its form (r < e ≤ 1,024; reply 0 if
    e < 1,024) and every checked token of its range is 0: a condition in which a does not occur.

Limits: the first two (`target_bite2_many`, `target_bite2_two`) close that hole and no more. The
indices of the first two are made up and all behave alike: their embedding is 0, so the stream is 0
at every position and layer, all logits are 0, and the entries in which they differ are multiplied
by 0: they have one language (`target_bite2_same`). They differ as indices and as weights, which is
what a key commits to; they do not differ as models. The weight lies on the last,
`target_bite2_ref`, which stands at the reference scales (`sRef`) alone: there the two indices are
different models (another request tells them apart) that answer one request alike.
This file does not say the last at every lawful table (it would ask weights whose stream is not 0,
so the range tests and roundings of all normalisations at all lawful parameters). It holds there,
with other made-up indices: Cm/TargetPartBite2K.lean: `target_bite2_all`. This file does not say
anything on real weights. It does not say anything on a protocol: that a scheme's proofs hide
anything is the matter of other files.
Terms: lean/GLOSSARY.md.
-/
import Cm.Rel2Guards
import Cm.RelTruePaper

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All Inst.Model.ScalesSanity
  Inst.Model.ProgramRGuards Inst.Model.SanityRef

/-- the value a L - 4,096 in layer L < 48; 0 beyond -/
def biteV (a : Fin 48 → Fin 8192) : ℕ → ℤ := fun L =>
  if h : L < 48 then ((a ⟨L, h⟩).val : ℤ) - 4096 else 0

theorem biteV_box (a : Fin 48 → Fin 8192) (L : ℕ) : -4096 ≤ biteV a L ∧ biteV a L ≤ 4095 := by
  unfold biteV
  split
  · rename_i h
    have := (a ⟨L, h⟩).isLt
    omega
  · norm_num

theorem biteV_far (a : Fin 48 → Fin 8192) (L : ℕ) (h : 48 ≤ L) : biteV a L = 0 := by
  unfold biteV
  rw [dif_neg (by omega)]

/-- made-up indices: the entry [0][0] of the value matrix of layer L is a L - 4,096; every other
weight is 0 -/
def biteVs (a : Fin 48 → Fin 8192) : Idx :=
  Idx.ofIndex ⟨iW (biteV a) fun _ _ => 0,
    iW_wf (biteV_box a) (biteV_far a) fun t j => by split_ifs <;> norm_num⟩

namespace Spec

/-- one request, true at 8,192^48 indices with pairwise different weights: at every lawful table,
for every range -/
def target_bite2_many : Prop :=
  Function.Injective (fun a => (biteVs a).weights) ∧
  ∀ s : Scales, s.Lawful →
    ∀ rF eF : Fin (ppref.T + 1),
      rF.val < eF.val → ∀ a, PaperTrue s.kap s.nf (biteVs a) (RequestGuards2.xz rF eF)

/-- two indices with different weights and a common true request: the same two for all tables. (not
all hypotheses are named here: see the statement below) -/
def target_bite2_two : Prop :=
  ∃ i i' : Idx,
    i.weights ≠ i'.weights ∧
    ∀ s : Scales, s.Lawful →
      ∀ rF eF : Fin (ppref.T + 1), rF.val < eF.val →
        ∃ x : Instance ppref,
          x.rF = rF ∧ x.eF = eF ∧ PaperTrue s.kap s.nf i x ∧ PaperTrue s.kap s.nf i' x

/-- At every lawful table: these made-up indices all have one language: the condition on the right
does not name a -/
def target_bite2_same : Prop :=
  ∀ s : Scales, s.Lawful →
    ∀ (a : Fin 48 → Fin 8192) (x : Instance ppref),
      PaperTrue s.kap s.nf (biteVs a) x ↔ Head3 x ∧ ∀ t, x.r ≤ t → t < x.e → x.w t = 0

/-- at the reference scales: two different models that answer one request alike -/
def target_bite2_ref : Prop :=
  ∃ (i i' : Idx) (x x' : Instance ppref),
    PaperTrue sRef.kap sRef.nf i x ∧
    PaperTrue sRef.kap sRef.nf i' x ∧
    PaperTrue sRef.kap sRef.nf i x' ∧
    ¬ PaperTrue sRef.kap sRef.nf i' x'

end Spec

theorem normOut_zero {np : NormPar} (h : np.OK) (d j : ℕ) : NORM.out np d (fun _ => 0) j = 0 := by
  unfold NORM.out NORM.yw
  rw [zero_mul, rhu_zero (by have := h.2.2.2.2.1; omega)]
  decide

/-- the program runs at these weights, on every prompt, at every lawful table -/
theorem runs_vs {pp : ScalesAndPolicy} (h : Lawful pp) (vs : ℕ → ℤ) (prompt : Fin ppref.T → Fin ppref.V) :
    RunsK ppref pp.kap pp.nf (fun _ => tbRef) (iW vs fun _ _ => 0) prompt := by
  refine (runsW pp.nf _ _ _ prompt (fun L hL => shifts1 h hL)).2 ?_
  have e : x0 pp.kap (fun _ => tbRef) vs (fun _ _ => 0) prompt = fun _ _ => 0 := by
    funext pos j
    show (if hh : pos < ppref.T then (0 : ℤ) else 0) = 0
    split <;> rfl
  rw [e]
  refine ⟨fun L hL pos _ => ⟨normOK_zero (normsOK h hL).1 _, ?_, normOK_zero (normsOK h hL).2 _⟩,
    fun pos _ => normOK_zero h.nf _⟩
  have hv : 1 ≤ (pp.kap L).kv := (shifts1 h hL).2.2.1
  show Fits16 (rhu (NORM.out (pp.kap L).n1 5120 (fun _ => 0) 0 * vs L) (pp.kap L).kv)
  rw [normOut_zero (normsOK h hL).1, zero_mul, rhu_zero hv]
  exact fits16_zero

theorem lg_vs (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (vs : ℕ → ℤ) (Emb : Mat)
    (prompt : Fin ppref.T → Fin ppref.V) (pos v : ℕ) :
    lgK ppref κ nf tbs (iW vs Emb) prompt pos v = 0 := by
  simp [lgK, iW, dot_zero]

theorem true_vs {pp : ScalesAndPolicy} (h : Lawful pp) (a : Fin 48 → Fin 8192)
    (rF eF : Fin (ppref.T + 1)) (hre : rF.val < eF.val) :
    TrueAt pp.kap pp.nf (biteVs a) (RequestGuards2.xz rF eF) :=
  (trueAt_ofIndex _ _ _ _).2 ⟨runs_vs h _ _, ⟨hre, Nat.lt_succ_iff.1 eF.isLt, fun _ => rfl⟩, fun t _ _ => by
    rw [gap_zero' (lg_vs _ _ _ _ _ _ t) ((RequestGuards2.xz rF eF).w_lt t),
      if_pos (RequestGuards2.xz_w rF eF t)]⟩

theorem biteVs_inj : Function.Injective (fun a => (biteVs a).weights) := by
  intro a b hab
  have h1 : iW (biteV a) (fun _ _ => 0) = iW (biteV b) fun _ _ => 0 := by
    have := hab
    simp only [biteVs, weights_ofIndex] at this
    exact this
  funext L
  have h2 : ((iW (biteV a) fun _ _ => 0).layer L.val).Wv 0 0 =
      ((iW (biteV b) fun _ _ => 0).layer L.val).Wv 0 0 := by rw [h1]
  have h3 : biteV a L.val = biteV b L.val := by simpa [iW, layW] using h2
  unfold biteV at h3
  rw [dif_pos L.isLt, dif_pos L.isLt, Fin.eta] at h3
  exact Fin.ext (by omega)

theorem target_bite2_many : Spec.target_bite2_many :=
  ⟨biteVs_inj, fun s hs rF eF hre a => (paper_iff s.kap s.nf _ _).1 (true_vs hs.toPP a rF eF hre)⟩

theorem target_bite2_two : Spec.target_bite2_two :=
  ⟨biteVs fun _ => 0, biteVs fun _ => 1,
    fun h => absurd (congrFun (target_bite2_many.1 h) 0) (by decide),
    fun s hs rF eF hre =>
      ⟨_, rfl, rfl, target_bite2_many.2 s hs rF eF hre _, target_bite2_many.2 s hs rF eF hre _⟩⟩

theorem target_bite2_same : Spec.target_bite2_same := fun s hs a x =>
  (paper_iff s.kap s.nf _ x).symm.trans ((trueAt_ofIndex _ _ _ x).trans
    ⟨fun ⟨_, h3, hg⟩ => ⟨h3, fun t hr he => by
      have h := hg t hr he
      rw [gap_zero' (lg_vs _ _ _ _ _ _ t) (x.w_lt t)] at h
      by_contra hne
      rw [if_neg hne] at h
      exact one_ne_zero h⟩,
     fun ⟨h3, hx⟩ =>
       ⟨runs_vs hs.toPP _ _,
         h3,
         fun t hr he => by rw [gap_zero' (lg_vs _ _ _ _ _ _ t) (x.w_lt t), if_pos (hx t hr he)]⟩⟩)

/-- token 1 is embedded in channel 1, every other token in channel 0 -/
def biteS : ℕ → ℕ := fun t => if t = 1 then 1 else 0
/-- channel 1 votes for token 1, every other channel for token 0 -/
def biteT : ℕ → ℕ := fun j => if j = 1 then 1 else 0
/-- the request: token 1, then 1,023 tokens 0; reply 0; all positions covered -/
def biteX : Instance ppref :=
  ⟨fun k => if k.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩, ⟨0, by decide⟩, 0, Fin.last _⟩

theorem biteX_w (t : ℕ) : biteX.w t = 0 := by
  unfold Instance.w Instance.tok biteX
  split
  · simp
  · rfl

theorem target_bite2_ref : Spec.target_bite2_ref := by
  have hS : ∀ t, biteS t < 5120 := fun t => by unfold biteS; split <;> norm_num
  have hT : ∀ j, biteT j < 202048 := fun j => by unfold biteT; split <;> norm_num
  have h3 : ∀ x : Instance ppref, x.rF = 0 → x.eF = Fin.last _ → Head3 x := fun x h1 h2 => by
    have e1 : x.r = 0 := by show x.rF.val = 0; rw [h1]; rfl
    have e2 : x.e = ppref.T := by show x.eF.val = ppref.T; rw [h2]; rfl
    exact ⟨by rw [e1, e2]; decide, le_of_eq e2, fun h => absurd h (by rw [e2]; exact lt_irrefl _)⟩
  refine ⟨Idx.ofIndex ⟨wts biteS fun _ => 0, wts_wf _ _⟩, Idx.ofIndex ⟨wts biteS biteT, wts_wf _ _⟩,
    RequestGuards2.xz 0 (Fin.last _), biteX, ?_, ?_, ?_, ?_⟩
  · exact (paper_iff _ _ _ _).1
      ((true_pos biteS (fun _ => 0) hS (fun _ => by norm_num) _).2
        ⟨h3 _ rfl rfl, fun t _ _ _ => RequestGuards2.xz_w _ _ t⟩)
  · exact (paper_iff _ _ _ _).1
      ((true_pos biteS biteT hS hT _).2
        ⟨h3 _ rfl rfl,
          fun t _ _ _ =>
            (RequestGuards2.xz_w _ _ t).trans (by simp [RequestGuards2.xz, biteS, biteT])⟩)
  · exact (paper_iff _ _ _ _).1
      ((true_pos biteS (fun _ => 0) hS (fun _ => by norm_num) _).2
        ⟨h3 _ rfl rfl, fun t _ _ _ => biteX_w t⟩)
  · intro h
    have := ((true_pos biteS biteT hS hT _).1 ((paper_iff _ _ _ _).2 h)).2
      0 (by decide) (Nat.zero_le _) (by show 0 < (Fin.last ppref.T).val; decide)
    rw [biteX_w] at this
    simp [biteX, biteS, biteT] at this

end Cm
