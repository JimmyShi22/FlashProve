-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CsSim.lean: the claim after a code switch, and that the format's code switch computes
it.

The library's code switch (Cb/Ld/LdSwitch.lean) hands on a target and a linear form with a state.
With the parameters of OnBytes/Slice/CsData.lean this file writes the form as a vector on the new
tables (`csNext`) and gives target and vector in the field, entry by entry:
 `csNext_fst`  the target: the old target, the answer under θ, and for the draw number i the three
               coordinates of the long symbol at the drawn position under θ^(2 + 3 i), θ^(3 + 3 i),
               θ^(4 + 3 i);
 `csNext_snd`  the vector at an entry of the layout: the old vector (0 on tails and free room), the
               sample's weight under θ, and under the same powers the weights of the entry in the
               three coordinates of the long symbol (`midRow`, OnBytes/Slice/CsRow.lean).
`cs_sim` says that this is the row that the format's own function computes (`csStep`,
Fmt/M1Cs.lean), if the claim before the switch is what a fold hands on, the word is made of the old
tree's columns, and seed, answer, element and positions are those that the format's decision reads.

Main definition: `csNext`. Main theorems: `csNext_fst`, `csNext_snd`, `cs_sim`.
Not claimed. Nothing on a protocol: the block is in OnBytes/Slice/BlockCs.lean.
-/
import OnBytes.Slice.CsOut
import OnBytes.Slice.CsRow
import OnBytes.Slice.CsSmp
import OnBytes.Slice.CsVals
import OnBytes.Slice.CsAt
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

variable {s s' : Sg}

/-- The claim after a switch, as a target and a vector on the new tables. τ₀, v, y: the target,
the vector and the word before the switch. ρo: the seed of the sample. ans: the answer. c: the drawn
positions and the drawn element. -/
def csNext (hf : CsFit s s') (τ₀ : GE) (v : s.cMid.J → GE) (y : s.cMid.Word)
    (ρo : (Fin s'.st.na → GE) × GEˣ) (ans : GE) (c : (Fin s.t → s.Ps) × GE) :
    GE × (s'.cIn.J → GE) :=
  ((csSw hf).W.tgt' τ₀ (fun _ => ans) (s.cMid.T y) c,
    (csSw hf).sl' ((csSw hf).stOf v ρo c.1, c.2))

/-- The new target, written out. -/
theorem csNext_fst (hf : CsFit s s') (τ₀ : GE) (v : s.cMid.J → GE) (y : s.cMid.Word)
    (ρo : (Fin s'.st.na → GE) × GEˣ) (ans : GE) (c : (Fin s.t → s.Ps) × GE) :
    (csNext hf τ₀ v y ρo ans c).1
      = τ₀ + c.2 * ans + ∑ i : Fin s.t, c.2 ^ (2 + 3 * i.val) *
          (s.cMid.T y (c.1 i) (.inl ()) + c.2 * s.cMid.T y (c.1 i) (.inr (.inl ()))
            + c.2 ^ 2 * s.cMid.T y (c.1 i) (.inr (.inr ()))) :=
  tgt_out hf τ₀ (fun _ => ans) (s.cMid.T y) c.1 c.2

/-- The new vector at an entry of the layout, written out. -/
theorem csNext_snd (hf : CsFit s s') (τ₀ : GE) (v : s.cMid.J → GE) (y : s.cMid.Word)
    (ρo : (Fin s'.st.na → GE) × GEˣ) (ans : GE) (c : (Fin s.t → s.Ps) × GE)
    (n : CsK s ⊕ CsFree hf) :
    (csNext hf τ₀ v y ρo ans c).2 (csPlace hf n)
      = ldPad (ldPad v) n + c.2 * (csSample hf).mat ρo () n
        + ∑ i : Fin s.t, c.2 ^ (2 + 3 * i.val) *
          (ldPad (midRow s (c.1 i).val (.inl ())) n
            + c.2 * ldPad (midRow s (c.1 i).val (.inr (.inl ()))) n
            + c.2 ^ 2 * ldPad (midRow s (c.1 i).val (.inr (.inr ()))) n) := by
  have hrow : ∀ (i : Fin s.t) (α : s.cMid.Aa), s.cMid.row (c.1 i) α = midRow s (c.1 i).val α :=
    fun i α => funext fun k => row_mid s (c.1 i) α k
  refine (ldSwitch_form GE s.Ps s'.Ps (s.cMid.J → GE) (csSw hf) v ρo c n).trans ?_
  refine (form_out hf (ldPad v) ρo c.1 c.2 n).trans ?_
  simp only [hrow]

/-- The claim after the switch is the format's new row. R: what a fold hands on. col: the old
tree's columns. z, beta: the seed as the format's decision reads it. alpha: the answer. theta, xs:
the drawn element and the drawn positions. -/
theorem cs_sim (hf : CsFit s s') (R : Fmt.M1.SRow) (hg : R.g.length = s.h + s.g)
    (col : ℕ → Fmt.M1.Col) (cols : ℕ → Option Fmt.M1.Col)
    (hcols : ∀ x c, cols x = some c → c = col x)
    (z : List Fmt.M1.E) (beta alpha theta : Fmt.M1.E) (xs : List ℕ) (hz : z.length = s'.st.na)
    (hx : xs.length = s.t) (β : GEˣ) (hβ : β.val = toE beta) (Qs : Fin s.t → s.Ps)
    (hQ : ∀ i, (Qs i).val = xs.getD i.val 0) (G' : Fmt.M1.GRow)
    (h : Fmt.M1.csStep .two s.st s'.st R
      (Fmt.M1.sampleRow .two s'.st.Am s'.st.Az z beta alpha) xs theta cols = some G') :
    csNext hf (toE R.t) (vecMid s R) (wordMid s col (ptL _ R.g)) (ptL _ z, β) (toE alpha)
      (Qs, toE theta) = stmIn s' G' := by
  obtain rfl := cs_cols s.st s'.st R _ xs theta col cols hcols G' h
  refine Prod.ext ?_ (funext fun j => ?_)
  · show _ = toE (Fmt.M1.sumRows .two theta (allRows .two s.st s'.st R _ xs col)).t
    rw [csNext_fst, toE_cs_t, hx, Finset.sum_range]
    refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
    show toE theta ^ (2 + 3 * i.val) * (s.cMid.T _ (Qs i) _ + toE theta * s.cMid.T _ (Qs i) _
      + toE theta ^ 2 * s.cMid.T _ (Qs i) _) = _
    rw [mid_main s R hg col (Qs i), mid_mask s R hg col (Qs i),
      mid_fresh s R hg col (Qs i), hQ]
    rfl
  · obtain ⟨n, rfl⟩ := (csPlace hf).surjective j
    show _ = vecIn s' _ (csPlace hf n)
    rw [csNext_snd, vecIn_eq, cs_at hf R _ xs theta col n, smp_mat hf z beta alpha hz β hβ n, hx,
      Finset.sum_range]
    simp only [hQ]

end OnBytes.Slice

#print axioms OnBytes.Slice.csNext_fst
#print axioms OnBytes.Slice.csNext_snd
#print axioms OnBytes.Slice.cs_sim
