-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPlaneRead.lean.
The three claims of the byte-level verifier that read the planes of the counts, in the words of the
flat function.

`Forest.planeClaims` (OnBytes/Model/Look.lean) closes the leaves' sumcheck and makes two more
claims. This file reads a run that returns: for every reading ρ of the byte-level field in a
commutative ring K, in every later state of the sub-proof, for every mask row and all entries of
virtual rows.

Main names:
  `planeClaims_rows`: the context is as before; the state is a later one, with as many slots taken;
    and the three forms are worth, in this order:
    the residue of the flat function's row `TwV.rowU` of the leaves' sumcheck, plus eps times the
    factor `leavesA` times the planes' value `planesK` at the leaves' point;
    what stands under the slot of the value that the bits' sumcheck has shown, less the planes'
    value at the bits' point;
    `countK`: minus the number of keys that are not padding, plus the columns' sums.
    The values of the caller's forms stand in the statement as letters.

Under: the caller's routines are quiet (`Quiet`); the leaves' sumcheck is in the state `Ran`, its
start is read by `FormIs` in an earlier state, its places are the ledger's (`LedAt`); the state's
arrays have their sizes (`Sized`); a key's number has fewer than 64 bits.

Limits: the second form has the opposite sign to the flat function's row `TwV.rowBitE`. What the
values of the caller's forms are is the caller's to state. Not claimed: anything on soundness,
completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneClaims
import OnBytes.Tie.Pv.Lookup.Forest.FoPscForm

set_option autoImplicit false

namespace Cb.Fo.PlaneClaims
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

theorem planeClaims_rows (g : Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F0 F G : Fork) (c c' : Ctx) (rows : Array Aff)
    (h : planeClaims g lm bit pin F c = .ok ((rows, G), c'))
    {first : ℕ} {mu eps : E} {zd : List (E × ℕ)} {rs : List (List E × E)}
    (hR : Ran g.leaves first mu eps zd rs) {tg : K} {inc : List (Pl × K)}
    (hC : FormIs ρ F0 g.leaves.start tg inc) (ht : ρ.val g.leaves.target = tg)
    (h0 : Later F0 F) (hF : Sized F) {L : Led Pl} {n : ℕ} (hL : LedAt L first (dgOf zd) n)
    (hv : g.shape.v < 64) (vals : List K) :
    (planeCols g.shape lm).toBool = true ∧ c' = c ∧ Later F G ∧ Sized G ∧ G.next = F.next ∧
      ∃ r0 r1 r2, rows = #[r0, r1, r2] ∧
        ∀ H, Later G H → ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K),
          r0.value ρ (H.worldOf ρ mask entry) =
              rowRes (muOf mask) (rowU L (dgOf zd)
                ⟨ρ.val g.leaves.eps, g.leaves.r.toList.map ρ.val, ρ.val g.leaves.claim, vals⟩
                inc 1) +
              ρ.val eps * (ρ.val g.leavesA * planesK g.shape lm (rdL ρ g.zb0) fun col =>
                (got (bit 0 col) F c).value ρ (H.worldOf ρ mask entry)) ∧
          r1.value ρ (H.worldOf ρ mask entry) =
              (H.worldOf ρ mask entry).slot g.sBit - planesK g.shape lm (rdL ρ g.zb1) (fun col =>
                (got (bit 1 col) F c).value ρ (H.worldOf ρ mask entry)) ∧
          r2.value ρ (H.worldOf ρ mask entry) =
              Pin.countK g.shape lm fun col =>
                (got (pin col) F c).value ρ (H.worldOf ρ mask entry) := by
  obtain ⟨hm, row, p', h5, hr⟩ := planeClaims_run g lm bit pin hb hp F G c c' rows h
  obtain ⟨a1, a2, a3, a4, _, a6⟩ := row_form ρ hR h5 hC ht h0 hF hL vals
  refine ⟨hm, a1, a2, a3, a4, row, _, _, hr, fun H hH mask entry => ⟨?_, ?_, ?_⟩⟩
  · rw [a6 H hH mask entry, Aff.value_scale, planesAff_value, ρ.one]
    rfl
  · rw [Aff.value_sub, Aff.value_slot, planesAff_value]
    rfl
  · exact countAff_value ρ _ g lm _ hv

end
end Cb.Fo.PlaneClaims
