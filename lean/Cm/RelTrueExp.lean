-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/RelTrueExp.lean: further guards on the true request (`TrueAt` of Cm/RelBase.lean), beside
Cm/RelTrue.lean: a token far behind the covered stretch can take a true reply out of the relation;
a well-formed index can have no true request at all.

In standard terms: more sanity checks on the predicate `TrueAt`, at made-up weights: it depends on
the router's and the routed experts' weights of one mixture-of-experts layer, and the integer
program's range tests at all positions are part of it.

Facts on that sentence alone, all at the reference scales: no cells, no code, no protocol, no
chance. In the larger library guards carry them to "has a witness" in the second relation pair, at
the reference scales; the guards' file is not in this library.

Main names:
  `true_router`, `true_expert`: see their doc comments.
  `filler`: the range tests of all 1,024 positions are part of the sentence: one index, two
    requests with the same r = 0, e = 1, y = 0 and the same tokens 0 .. 1,022; they differ in token
    1,023 alone, 1,022 places behind the covered stretch; the first is true, the second is not (a
    query channel at position 1,023 fails its 16-bit test).
  `empty_language`: a well-formed index can have no true request at all.
Which weights a theorem shows to be read, with Cm/RelTrue.lean: embedding and output matrix
(`true_pos`); W_v, W_o of layer 0 (`true_layer`); W_r and the routed experts' three matrices of
layer 1 (here).

Limits: still without a guard: W_q, W_k and the rotation tables as far as the reply goes (every
guard has all scores 0; `filler` and `empty_language` read W_q through a range test only); every
row of the table Exp but Exp[0]; the dense and the shared W_g, W_u, W_d; the second normalisation's
parameters; every layer above layer 1.
All indices here are made up for these proofs: their weights are made up; the four theorems stand at
the library's reference scales (`ppRef`, Inst/Model/Scales.lean; where their numbers come from:
lean/CREDITS.md, section 8). These theorems say nothing on the weights of a trained model.
The four theorems use the made-up weights of Inst/Model/SanityExp.lean, Inst/Model/SanityPart.lean,
Inst/Model/SanityRef.lean and Inst/Model/SanityAtt.lean.

Terms: lean/GLOSSARY.md.
-/
import Cm.RelTrue
import Inst.Model.SanityExp
import Inst.Model.SanityPart

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

/-! ## 1. The router and the routed experts -/

section Exp
open Inst.Model Inst.Model.All Inst.Model.SanityRef Inst.Model.SanityAtt Inst.Model.SanityExp

/-- It reads the router: two indices that differ in W_r of layer 1 only; one request true at the
one, not at the other -/
theorem true_router :
    ∃ (i i' : Idx) (x : Instance ppref),
      i.weights.Emb = i'.weights.Emb ∧
      i.weights.H = i'.weights.H ∧
      (∀ L, L ≠ 1 → i.weights.layer L = i'.weights.layer L) ∧
      { i.weights.layer 1 with Wr := (i'.weights.layer 1).Wr } = i'.weights.layer 1 ∧
      TrueAt ppRef.kap ppRef.nf i x ∧
      ¬ TrueAt ppRef.kap ppRef.nf i' x := by
  refine ⟨Idx.ofIndex ⟨wE 5 5, wE_wf 5 5 (by norm_num) (by norm_num)⟩,
    Idx.ofIndex ⟨wE 6 5, wE_wf 6 5 (by norm_num) (by norm_num)⟩,
    Instance.nextOf pC ⟨7, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [weights_ofIndex, weights_ofIndex]; rfl
  · rw [weights_ofIndex, weights_ofIndex]; rfl
  · intro L hL
    rw [weights_ofIndex, weights_ofIndex]
    show (if L = 1 then _ else _) = (if L = 1 then _ else _)
    rw [if_neg hL, if_neg hL]
  · rw [weights_ofIndex, weights_ofIndex]; rfl
  · exact (true_next ⟨wE 5 5, _⟩ pC ⟨7, by decide⟩).2 (model_on 5 (by norm_num))
  · intro h
    have h7 := (true_next ⟨wE 6 5, _⟩ pC ⟨7, by decide⟩).1 h
    exact absurd (modelIs_unique _ _ _ _ h7 (model_off 6 5 (by norm_num) (by norm_num))) (by decide)

/-- It reads the routed experts: the same for the matrices of the routed experts of layer 1 -/
theorem true_expert :
    ∃ (i i' : Idx) (x : Instance ppref),
      i.weights.Emb = i'.weights.Emb ∧
      i.weights.H = i'.weights.H ∧
      (∀ L, L ≠ 1 → i.weights.layer L = i'.weights.layer L) ∧
      { i.weights.layer 1 with
        Eg := (i'.weights.layer 1).Eg, Eu := (i'.weights.layer 1).Eu,
        Ed := (i'.weights.layer 1).Ed } =
        i'.weights.layer 1 ∧
      TrueAt ppRef.kap ppRef.nf i x ∧
      ¬ TrueAt ppRef.kap ppRef.nf i' x := by
  refine ⟨Idx.ofIndex ⟨wE 5 5, wE_wf 5 5 (by norm_num) (by norm_num)⟩,
    Idx.ofIndex ⟨wE 5 6, wE_wf 5 6 (by norm_num) (by norm_num)⟩,
    Instance.nextOf pC ⟨7, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [weights_ofIndex, weights_ofIndex]; rfl
  · rw [weights_ofIndex, weights_ofIndex]; rfl
  · intro L hL
    rw [weights_ofIndex, weights_ofIndex]
    show (if L = 1 then _ else _) = (if L = 1 then _ else _)
    rw [if_neg hL, if_neg hL]
  · rw [weights_ofIndex, weights_ofIndex]; rfl
  · exact (true_next ⟨wE 5 5, _⟩ pC ⟨7, by decide⟩).2 (model_on 5 (by norm_num))
  · intro h
    have h7 := (true_next ⟨wE 5 6, _⟩ pC ⟨7, by decide⟩).1 h
    exact absurd (modelIs_unique _ _ _ _ h7 (model_off 5 6 (by norm_num) (by norm_num))) (by decide)

end Exp

/-! ## 2. A filler; an index without a true request -/

section Part
open Finset Inst.Model Inst.Model.All Inst.Model.SanityRef
  Inst.Model.SanityAtt Inst.Model.SanityPart

theorem Aq_cst (x : ℕ → Vec) (i : ℕ) (hX : x i = cst) (c : ℕ) (hc : c < 5120) :
    Att.Aq ppref bigQ x i c = 4801305600 := by
  unfold Att.Aq Att.a dot
  rw [hX]
  show ∑ j ∈ range 5120, NORM.out npR 5120 cst j * (if j < 5120 ∧ c < 5120 then (4095 : ℤ) else 0) =
    _
  rw [sum_congr rfl fun j hj => show NORM.out npR 5120 cst j * (if j < 5120 ∧ c < 5120 then (4095 : ℤ) else 0) = 937755 by
    rw [out_cst (mem_range.1 hj), if_pos ⟨mem_range.1 hj, hc⟩]; norm_num]
  simp

theorem qkw_last (x : ℕ → Vec) (hX : x 1023 = cst) :
    Att.qkw ppref tbRef bigQ 0 x 1023 0 =
      rhu (tbRef.C 0 1023 0 * 4801305600 - tbRef.S 0 1023 0 * 4801305600) 29 := by
  have hAY0 : Att.AY ppref bigQ x 1023 0 = 4801305600 := by
    unfold Att.AY
    rw [if_pos (by decide), Aq_cst x 1023 hX 0 (by norm_num)]
  have hAY1 : Att.AY ppref bigQ x 1023 1 = 4801305600 := by
    unfold Att.AY
    rw [if_pos (by decide), Aq_cst x 1023 hX 1 (by norm_num)]
  have hY : Att.Y' ppref tbRef bigQ 0 x 1023 0 =
      tbRef.C 0 1023 0 * 4801305600 - tbRef.S 0 1023 0 * 4801305600 := by
    unfold Att.Y'
    have h1 : 0 % ppref.ch = 0 := Nat.zero_mod _
    simp only [h1, Nat.zero_div, Nat.zero_mod, if_true, zero_add, hAY0, hAY1]
  unfold Att.qkw
  rw [hY, if_pos (by decide)]
  rfl

theorem not_fits :
    ¬ Fits16 (rhu (tbRef.C 0 1023 0 * 4801305600 - tbRef.S 0 1023 0 * 4801305600) 29) := by
  unfold Fits16
  decide +kernel

def iP : Idx := Idx.ofIndex ⟨wP, wP_wf⟩
/-- all 1,024 tokens are 0; position 0 alone is covered; y = 0 -/
def xT : Instance ppref := ⟨SanityPart.pC, t0, ⟨0, by decide⟩, ⟨1, by decide⟩⟩
/-- the same, but the last token, a filler 1,022 places behind the covered stretch, is 1 -/
def xF : Instance ppref := ⟨pA, t0, ⟨0, by decide⟩, ⟨1, by decide⟩⟩

theorem kap_pp : ppRef.kap = fun _ => ppref.scale := kap_ref

/-- A filler takes a true reply out of the relation: one index, two requests with the same r = 0, e
= 1, y and the same tokens 0 .. 1,022; the one is true, the other is not -/
theorem filler :
    TrueAt ppRef.kap ppRef.nf iP xT ∧ ¬ TrueAt ppRef.kap ppRef.nf iP xF ∧ xT.r = xF.r ∧
    xT.e = xF.e ∧ xT.y = xF.y ∧ ∀ t ≤ 1022, xT.tok t = xF.tok t := by
  refine ⟨⟨⟨show 0 < 1 by norm_num, show 1 ≤ 1024 by norm_num, fun _ => rfl⟩,
      ?_, fun t h1 h2 => ?_⟩,
    ?_, rfl, rfl, rfl, ?_⟩
  · unfold iP
    rw [weights_ofIndex, kap_pp]
    exact runsK_ref _ _ model_pC.1
  · have hl : ∀ t v, logitsAt ppRef.kap ppRef.nf iP xT t v = 0 := fun t v => by
      show lgK ppref ppRef.kap ppRef.nf (fun _ => tbRef) iP.weights xT.prompt t v = 0
      unfold iP
      rw [weights_ofIndex]
      exact dot_zero _ _
    have ht : t = 0 := by
      have : t < 1 := h2
      omega
    subst ht
    have hw : xT.w 0 = 0 := by
      unfold Instance.w Instance.tok
      rw [dif_pos (by decide)]
      rfl
    refine ⟨fun v _ => by rw [hl, hl], fun v hv => ?_⟩
    rw [hw] at hv
    exact absurd hv (Nat.not_lt_zero _)
  · rintro ⟨-, hr, -⟩
    unfold iP at hr
    rw [weights_ofIndex, kap_pp] at hr
    unfold RunsK at hr
    rw [Inst.Model.XK_const] at hr
    have h := ((hr.1 0 (by decide)).1 1023 (by decide)).2.1 0 (by decide)
    have hX : X ppref tbRef wP pA (2 * 0) 1023 = cst := by
      funext j
      show (if h : 1023 < ppref.T then embP (pA ⟨1023, h⟩) j else 0) = _
      rw [dif_pos (by decide)]
      simp [embP, pA, t1, cst]
    have h' : Fits16 (Att.qkw ppref tbRef bigQ 0 (X ppref tbRef wP pA (2 * 0)) 1023 0) := h
    rw [qkw_last _ hX] at h'
    exact not_fits h'
  · intro t ht
    have h : t < ppref.T := by
      show t < 1024
      omega
    unfold Instance.tok
    rw [dif_pos h, dif_pos h]
    show (SanityPart.pC ⟨t, h⟩).val = (pA ⟨t, h⟩).val
    unfold SanityPart.pC pA
    rw [if_pos (show t < 1023 by omega)]

/-- at the reference scales there is a well-formed index whose language is empty: no request at all
is true -/
theorem empty_language (x : Instance ppref) :
    ¬ TrueAt ppRef.kap ppRef.nf (Idx.ofIndex ⟨haltW, haltW_wf⟩) x := by
  rintro ⟨-, hr, -⟩
  rw [weights_ofIndex] at hr
  rw [kap_pp] at hr
  unfold RunsK at hr
  rw [Inst.Model.XK_const] at hr
  have h := ((hr.1 0 (by decide)).1 0 (by decide)).2.1 0 (by decide)
  have e : Att.qkw ppref tbRef (haltW.layer 0) 0 (X ppref tbRef haltW x.prompt (2 * 0)) 0 0 =
      36631 :=
    qkw_haltW x.prompt
  have h2 : Att.qkw ppref tbRef (haltW.layer 0) 0 (X ppref tbRef haltW x.prompt (2 * 0)) 0 0 <
      2 ^ 15 := h.2
  rw [e] at h2
  exact absurd h2 (by norm_num)

end Part

end Cm
