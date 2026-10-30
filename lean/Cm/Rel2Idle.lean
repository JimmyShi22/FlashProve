-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/Rel2Idle.lean: what "every lawful table of scales" admits: two lawful tables at which a statement
over every lawful table says little of the weights.

In standard terms: two degenerate choices of the quantization scales that meet the hypothesis
"lawful". At one of them a theorem gives weights at which every logit is 0 whatever the output
matrix is.

Definitions, statements and proofs. Beside Cm/Rel2.lean (`Scales.Lawful`) and Cm/Rel2Guards.lean
(`sRef`, `lawful_sRef`).

"Lawful" (Cm/Rel2.lean) asks ranges, and equations and inequalities between numbers of the table,
only. It shuts out the tables at which a normalisation puts out 0 whatever its input; it does not
shut out tables at which it puts out 0 for every input of interest.

Main names:
  `sIdle`, `lawful_idle`: the table with exponent = shift = 24 and constant 1 in all 97
    normalisations and the largest shifts for values, gates, up projections and router is lawful. By
    hand, no theorem here: there a normalised row has entries in {-2, .., 2}, all but a few of them
    0, every product with a column of 13-bit weights is below 2^23, so values and up projections are
    0 and no block adds anything to the stream. (The library from which the model's files are copied
    proves a statement of this kind, in a file that is not copied.)
  `sFlat`, `lawful_flat`: the table with the reference words in all 48 layers and only the final
    normalisation changed to (24, 24, 1) is lawful.
  `logits_flat`: at `sFlat` and the weights "every token is embedded as (1000, .., 1000); zero
    layers; any output matrix H": every logit is 0, at every position, whatever H is. The general
    remark, by hand: with the final normalisation's exponent at most 5 above its shift, a last
    stream whose 5,120 channels are of like size has |z| / root about 1/72, so the normalised row
    is 0: all logits are 0 and token 0 is the first choice at every position whatever H is.

Limits: advice to whoever quotes the theorems (no rule of this library): quote a statement "for
every lawful table" at the reference table `sRef`, or add that the table is a public parameter which
the reader must inspect. That `sRef` is not such a table is shown by the guards (Cm/RelTrue.lean,
Cm/RelTrueExp.lean). How far the guards reach: Limits, in the head of
Cm/RelTrueExp.lean.
This file says nothing on any fitted table or real weights.

Terms: lean/GLOSSARY.md.
-/
import Cm.Rel2Guards

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm
open Finset Inst.Model Inst.Model.All Inst.Model.SanityRef

/-! ## 1. Exponent = shift in all normalisations -/

def wIdle : Words := ⟨16, 16, 24, 19, 24, 24, 19, 24, 24, 24, ⟨24, 24, 1⟩, ⟨24, 24, 1⟩, 8⟩
def sIdle : Scales := ⟨fun _ => wIdle, ⟨24, 24, 1⟩⟩
theorem sh_idle (L : ℕ) : (sIdle.kap L).sh = 8 := by
  unfold Scales.kap
  split <;> rfl
theorem lawful_idle : sIdle.Lawful :=
  ⟨fun _ => (by decide : FFSeg.Ranges wIdle.scale),
    fun _ => (by decide : 4 ≤ wIdle.sh ∧ wIdle.sh ≤ 12),
    fun _ _ => by rw [sh_idle, sh_idle],
    (by unfold NormPar.OK; decide),
    ⟨fun _ => (by decide : wIdle.n1.K ≤ wIdle.n1.M ∧ wIdle.n2.K ≤ wIdle.n2.M),
      (by decide : (24 : ℕ) ≤ 24)⟩⟩

/-! ## 2. The reference words, and a final normalisation that flattens -/

/-- the reference words in all 48 layers; only the final normalisation is changed, to (M, K, ϵ) =
(24, 24, 1) -/
def sFlat : Scales := ⟨sRef.w, ⟨24, 24, 1⟩⟩
theorem kap_flat : sFlat.kap = sRef.kap := rfl
theorem lawful_flat : sFlat.Lawful :=
  ⟨lawful_sRef.ff, lawful_sRef.sh, lawful_sRef.one, (by unfold NormPar.OK; decide),
    ⟨lawful_sRef.km.1, (by decide : (24 : ℕ) ≤ 24)⟩⟩

theorem out_flat {j : ℕ} (hj : j < 5120) : NORM.out ⟨24, 24, 1⟩ 5120 cst j = 0 := by
  unfold NORM.out NORM.yw NORM.R NORM.sig
  rw [V_cst, show cst j = 1000 from if_pos hj]
  decide +kernel

/-- every token is embedded as (1000, .., 1000) -/
def embC : Mat := fun t j => if t < 202048 ∧ j < 5120 then 1000 else 0

/-- at the lawful table `sFlat`, whatever the output matrix H is, every logit is 0 (zero layers,
flat rows) -/
theorem logits_flat (H : Mat) (p : Fin ppref.T → Fin ppref.V) (pos : ℕ)
    (hpos : pos < ppref.T) (v : ℕ) :
    lgK ppref sFlat.kap sFlat.nf (fun _ => tbRef) ⟨fun _ => zeroLayer, embC, H⟩ p pos v = 0 := by
  have hk : sFlat.kap = fun _ => ppref.scale := kap_ref
  rw [hk]
  unfold lgK nrmK
  rw [Inst.Model.XK_const, X_zero ppref tbRef embC H p shifts_ref _]
  have e : X ppref tbRef ⟨fun _ => zeroLayer, embC, H⟩ p 0 pos = cst := by
    funext j
    show (if h : pos < ppref.T then embC (p ⟨pos, h⟩) j else 0) = _
    rw [dif_pos hpos]
    have hv : (p ⟨pos, hpos⟩).val < 202048 := (p ⟨pos, hpos⟩).isLt
    simp [embC, cst, hv]
  rw [e]
  unfold dot
  exact sum_eq_zero fun j hj => by
    show NORM.out ⟨24, 24, 1⟩ 5120 cst j * _ = 0
    rw [out_flat (mem_range.1 hj), zero_mul]

end Cm
