-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoR5Bit.lean.
The test on bits in the byte-level lookup routine: the claim that its sumcheck leaves is the flat
function's row.

The byte-level routine of a sub-proof's lookup (OnBytes.Model.Forest.pad) ends with a sumcheck that
tests that the planes hold bits. OnBytes/Tie/Pv/Lookup/Forest/FoR5Run.lean writes out the state of
that sumcheck for every run
that returns (`R5D.bits2`), and OnBytes/Tie/Pv/Lookup/Forest/FoR5Flat.lean shows that the flat step
reads the same factor,
challenges, last claim and shown value off the rounds. Here the claim on mask entries that the
routine makes of that state (`Psc.rowForm` at the summand v * v - v) is compared with the flat
function's row `TwV.rowBitU`, in the words of OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean: in every
later state and for every mask
row the two have one value.

 * `bits2_ran`: the state is one of a sumcheck under equality weights (`Ran`,
 OnBytes/Tie/Pv/Psc/PscWhole.lean),
   with the further variable as the last.
 * `zdB'_degs`: its degrees: 2 in each coordinate of the fresh point, 2 in the further variable.
 * `bits_rowU`: the claim is the row `rowU L dg s [] (v * (v - 1))`, for every record L of places
   that puts the hiding polynomial's coefficients under the slots from the sumcheck's first on, in
   the order of the verifier's walk (`LedAt`, OnBytes/Tie/Pv/Lookup/Forest/FoLedAt.lean). By
     `row_is` (OnBytes/Tie/Pv/Lookup/Forest/FoFork.lean).
 * `shown_bit`: the value that the routine reads back under the slot of the shown value is the one
   that was sent.
 * `bits_rowBitU`: at the public numbers of a forest (`numsF`): the claim is `rowBitU`. Premises:
   the fresh point has 5 + d coordinates; the sumcheck's first slot is the ledger's; the trace's
   record of this sumcheck is the one that the flat step reads (`r5_bits`).
Beside these, `bits2_ran`, `bits_rowU` and `bits_rowBitU` ask, each as far as it needs them, the
run's own facts, as `leavesBits_ok` (OnBytes/Tie/Pv/Lookup/Forest/FoR5Run.lean) hands them out:
the rounds fit (`FitsA`), the further variable's round sends 2 scalars, one value is shown, the
state before is `Sized`, and the steps on the state (`hideRun` twice, `shown` once) return.

Not claimed here: that a run meets the three premises named at `bits_rowBitU` (they are shown where
the stretches of the routine are put together); the claim on the planes' value at the point.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoR5Flat
import OnBytes.Tie.Pv.Lookup.Forest.FoFork
import OnBytes.Tie.Pv.Lookup.Forest.FoLedAt

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

section
variable (D : R5D) (m d : ℕ) (rho : Array E) (first : ℕ)

/-- The bits' state is one of a sumcheck under equality weights. -/
theorem bits2_ran (hB : FitsA (zdB D.ptZ) D.rsB) (hY : D.sentY.size = 2) :
    Ran (D.bits2 m d rho first) (firstB m d rho first) D.muB D.epsB D.zdB' D.rsB' := by
  have e : eqW D.zdB' = eqW (zdB D.ptZ) ++ [OnBytes.Psc.Weight.atZero 3] := by
    unfold R5D.zdB' eqW
    rw [List.map_append]
    rfl
  have hc : OnBytes.Psc.claimAfter (eqW D.zdB') D.rsB' (addE D.muB (mulE D.epsB zeroE)) =
      (D.bits2 m d rho first).claim := _root_.Fo.claimAfter_snoc _ _ _ _ _ (fits_of _ _ hB)
  have hf : Fits D.zdB' D.rsB' :=
    _root_.Fo.fits_snoc _ _ _ _ (fits_of _ _ hB) (by
      show D.sentY.toList.length + 1 = 3
      rw [Array.length_toList, hY])
  have hv : (D.bits2 m d rho first).vars.toList = eqW D.zdB' := by
    rw [e]
    simp [R5D.bits2, R5D.bits1, after]
  have hr : (D.bits2 m d rho first).r.toList = D.rsB'.map (·.2) := by
    simp [R5D.bits2, R5D.bits1, after, R5D.rsB', lsOf, Function.comp_def]
  exact ⟨rfl, rfl, hv, hr, hc.symm, hf⟩

/-- The degrees by round. -/
theorem zdB'_degs : D.zdB'.map (·.2 - 1) = List.replicate D.ptZ.size 2 ++ [2] := by
  unfold R5D.zdB' zdB zdOf
  simp only [List.map_append, List.map_map]
  show (D.ptZ.reverse.toList.map fun _ => 2) ++ [2] = _
  rw [List.map_const']
  simp

theorem rsB_length (hB : FitsA (zdB D.ptZ) D.rsB) : D.rsB.length = D.ptZ.size := by
  have h := (fits_of _ _ hB).length
  simp only [zdB, zdOf, lsOf, List.length_map, Array.length_toList, Array.size_reverse] at h
  exact h.symm

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The challenges by round, the further variable's last, read. -/
def R5D.xsB : List K := (D.rsB.map fun r => ρ.val r.2) ++ [ρ.val D.beta]

/-- The claim of the bits' sumcheck is the flat function's row on the hiding coefficients. -/
theorem bits_rowU (hB : FitsA (zdB D.ptZ) D.rsB) (hY : D.sentY.size = 2) {F6 F8 : Fork}
    (hF : Sized F6)
    (h8 : F6.hideRun (D.bits2 m d rho first).first
      (Array.replicate (D.bits2 m d rho first).walk.1.length zeroE) (subE zeroE oneE) = some F8)
    (vBit : E) (L : Led Pl) (n : ℕ)
    (hL : LedAt L (firstB m d rho first) (List.replicate D.ptZ.size 2 ++ [2]) n) (vals : List K) :
    RowIs ρ F8 ((D.bits2 m d rho first).rowForm (subE (mulE vBit vBit) vBit) {})
      (rowU L (List.replicate D.ptZ.size 2 ++ [2])
        ⟨ρ.val D.epsB, D.xsB ρ, ρ.val (D.bits2 m d rho first).claim, vals⟩ []
        (ρ.val vBit * (ρ.val vBit - 1))) := by
  intro G hG mask entry
  have hR := bits2_ran D m d rho first hB hY
  have hr : (D.bits2 m d rho first).r.toList.map ρ.val = D.xsB ρ := by
    rw [hR.r_eq]
    simp [R5D.rsB', R5D.xsB, lsOf, Function.comp_def]
  have hl : (D.xsB ρ).length = (List.replicate D.ptZ.size 2 ++ [2]).length := by
    simp [R5D.xsB, rsB_length D hB]
  have e := row_is ρ hR (zero_formIs ρ F6) ρ.zero (Later.refl F6) hF h8
    (subE (mulE vBit vBit) vBit) {} L
    (by rw [zdB'_degs, hr]; exact fun mask => hL.hide K (D.xsB ρ) mask hl) vals G hG mask entry
  rw [zdB'_degs, hr] at e
  have hk : ({} : Aff).value ρ (G.worldOf ρ mask entry) = 0 := by simp [Aff.value, ρ.zero]
  rw [e, hk, mul_zero, add_zero, ρ.sub, ρ.mul,
    show ρ.val vBit * ρ.val vBit - ρ.val vBit = ρ.val vBit * (ρ.val vBit - 1) by ring]
  rfl

omit [CommRing K] in
/-- What the routine reads back under the slot of the shown value is what was sent. -/
theorem shown_bit {T F6 : Fork} (hT : Sized T) (sBit : ℕ) (hv : D.v.size = 1)
    (h6 : T.hideRun sBit D.v D.beta = some F6) (vBit : E) (hs : F6.shown sBit = some vBit) :
    Sized F6 ∧ vBit = D.v.getD 0 zeroE := by
  obtain ⟨_, hS, hnew, _⟩ := hideRun_ok T F6 sBit D.v D.beta hT h6
  refine ⟨hS, ?_⟩
  unfold Fork.shown at hs
  split_ifs at hs
  exact (Option.some.inj hs).symm.trans (hnew 0 (by omega)).2.2.2.1

/-- At the public numbers of a forest: the claim of the bits' sumcheck is the flat function's. -/
theorem bits_rowBitU (h : FoNums.Sh) (lm jLK : ℕ) (θ : K) (t : Trace K)
    (hB : FitsA (zdB D.ptZ) D.rsB) (hY : D.sentY.size = 2) (hv : D.v.size = 1)
    (hk : D.ptZ.size = 5 + h.d) (hf : firstB m d rho first = jLK + (FoNums.S h).fBit)
    (ht : t.bits = ⟨ρ.val D.epsB, D.xsB ρ, ρ.val (D.bits2 m d rho first).claim, rdA ρ D.v⟩)
    {T F6 F8 : Fork} (hT : Sized T) (sBit : ℕ) (h6 : T.hideRun sBit D.v D.beta = some F6)
    (vBit : E) (hs : F6.shown sBit = some vBit)
    (h8 : F6.hideRun (D.bits2 m d rho first).first
      (Array.replicate (D.bits2 m d rho first).walk.1.length zeroE) (subE zeroE oneE) = some F8) :
    RowIs ρ F8 ((D.bits2 m d rho first).rowForm (subE (mulE vBit vBit) vBit) {})
      (rowBitU (numsF h lm jLK θ) t) := by
  obtain ⟨hS, hv0⟩ := shown_bit D hT sBit hv h6 vBit hs
  have hval : t.bits.v 0 = ρ.val vBit := by
    obtain ⟨x, hx⟩ : ∃ x, D.v.toList = [x] :=
      List.length_eq_one_iff.1 (by rw [Array.length_toList]; exact hv)
    have e1 : D.v.toList.getD 0 zeroE = D.v.getD 0 zeroE := by
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    rw [ht, hv0, ← e1]
    show ((D.v.toList.map ρ.val).getD 0 0) = _
    rw [hx]
    rfl
  have key := bits_rowU D m d rho first ρ hB hY hS h8 vBit (ledF jLK (FoNums.S h).pBitC) 1
    (by rw [hk, hf]; exact ledAt_bit h jLK) (rdA ρ D.v)
  show RowIs ρ F8 _ (rowU (ledF jLK (FoNums.S h).pBitC) (List.replicate (5 + h.d) 2 ++ [2]) t.bits
    [] (t.bits.v 0 * (t.bits.v 0 - 1)))
  rw [hval, ht, ← hk]
  exact key

end
end Fo

#print axioms Fo.bits2_ran
#print axioms Fo.bits_rowU
#print axioms Fo.shown_bit
#print axioms Fo.bits_rowBitU
