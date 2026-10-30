-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoR5At.lean.
The layer of the table's leaves and the test on bits, at the public numbers of a forest of calls.

`r5` (OnBytes/Tie/Pv/Lookup/Forest/FoR5.lean) is stated for any record of the flat function's public
numbers whose two last
orders are the byte-level routine's. Here the record is the one of a forest h (`Fo.numsF h lm jLK
θ`), the number of variables is 5 + h.d, and the lookup's first slot is jLK.

`r5_at`: from the eight lines of the routine, each as a run that returns, and from the fact that the
leaves' sumcheck begins at its slot of the ledger (`F.next = jLK + fEnd`), under the further
premises of `r5` (the state fits; the table's point; the fresh point's 5 + d coordinates):
 * all of `R5Is` at these numbers;
 * for every trace whose last sumcheck is the one that the run's rounds give: the claim of the bits'
   sumcheck that the routine returns is, by its value in every later state and for every row of
   masks, the flat function's row `TwV.rowBitU`;
 * the slot of the shown value is the place of that value's mask in the flat function's ledger;
 * behind the stretch the next free slot is jLK + the number of the lookup's slots;
 * the hidden value under the slot of the shown value: what was shown reads as the bits' shown
   value, and the factor of its mask entry as the further variable's challenge;
 * the numbers of coefficients of the leaves' rounds are the flat function's degrees plus one;
 * how many elements each round sends and draws: the last three pieces of the flat function's
   list of rounds.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoR5
import OnBytes.Tie.Pv.Lookup.Forest.FoR5Bit
import OnBytes.Tie.Pv.Lookup.Forest.FoTieKit

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- At a forest's numbers. -/
theorem r5_at (h : FoNums.Sh) (lm jLK : ℕ) (θ : K) (rho : Array E) (C : Aff) (pt : List K)
    (hpt : rdA ρ rho = pt.reverse) (hs : rho.size = 5 + h.d)
    (F F1 F2 F3 F4 F5 F6 F7 F8 : Fork) (c c1 c2 c3 c4 c5 c6 c7 c8 : Ctx)
    (lv0 lv b0 b1 b2 b3 : Psc) (zb0 zb1 z : Array E) (sBit : ℕ) (vBit : E) (row : Aff)
    (hF : Sized F) (hz : z.size = 5 + h.d) (hN : F.next = jLK + (FoNums.S h).fEnd)
    (h1 : pscBegin C F c = .ok ((lv0, F1), c1))
    (h2 : roundsIn .eq lv0
      ((List.range (5 + h.d)).map fun j => (rho.getD j zeroE, if j < h.d then 2 else 1)) F1 c1 =
        .ok (((zb0, lv), F2), c2))
    (h3 : SubM.point .zero (5 + h.d) F2 c2 = .ok ((z, F3), c3))
    (h4 : pscBegin (Aff.ofConst zeroE) F3 c3 = .ok ((b0, F4), c4))
    (h5 : roundsIn .eq2 b0 (z.reverse.toList.map fun z => (z, 0)) F4 c4 =
      .ok (((zb1, b1), F5), c5))
    (h6 : pscEnds b1 2 1 F5 c5 = .ok (((sBit, b2), F6), c6))
    (h7 : SubM.shown sBit F6 c6 = .ok ((vBit, F7), c7))
    (h8 : pscRow b2 (subE (mulE vBit vBit) vBit) {} F7 c7 = .ok (((row, b3), F8), c8)) :
    ∃ D : R5D, D.ptZ = z ∧
      R5Is ρ (numsF h lm jLK θ) (5 + h.d) h.d rho C pt F F8 c c8 lv zb0 zb1 sBit row D ∧
      (∀ t : Trace K, t.bits = D.bitsSc ρ (5 + h.d) h.d rho F.next →
        RowIs ρ F8 row (rowBitU (numsF h lm jLK θ) t)) ∧
      sBit = slotNo ((numsF h lm jLK θ).ledB.sh 0) ∧
      F8.next = jLK + Forest.elems h ∧
      FormIs ρ F8 (Aff.slot sBit) ((D.bitsSc ρ (5 + h.d) h.d rho F.next).v 0)
        [(Pl.mask sBit, (D.bitsSc ρ (5 + h.d) h.d rho F.next).be)] ∧
      ((zdL (5 + h.d) h.d rho).map fun p => p.2) = (dgE (numsF h lm jLK θ)).map (· + 1) ∧
      (flEv ρ (D.evs (5 + h.d) h.d rho)).map (fun r => (r.1.length, r.2.length)) =
        scRounds (FoNums.S h).scEnd ++ [(0, FoNums.w + h.d)] ++ scRounds (FoNums.S h).scBit := by
  obtain ⟨D, hD, R⟩ := r5 ρ (numsF h lm jLK θ) (5 + h.d) h.d rho C pt rfl rfl hpt hs (by omega)
    F F1 F2 F3 F4 F5 F6 F7 F8 c c1 c2 c3 c4 c5 c6 c7 c8 lv0 lv b0 b1 b2 b3 zb0 zb1 z sBit vBit row
    hF hz h1 h2 h3 h4 h5 h6 h7 h8
  clear h1 h2 h3 h4 h5 h6 h7 h8
  have hb := Cb.Fo.Walk.first_bit h
  have hall := Cb.Fo.Walk.first_all h
  have hfB : firstB (5 + h.d) h.d rho F.next = jLK + (FoNums.S h).fBit := by
    rw [firstB_eq _ _ _ _ (by omega), hN, hb]
    omega
  have hDg : ((zdL (5 + h.d) h.d rho).map fun p => p.2) =
      (dgE (numsF h lm jLK θ)).map (· + 1) := by
    show _ = ((FoNums.ordE h).map fun c => if c < FoNums.w then 1 else 2).map (· + 1)
    simp only [zdL, zdOf, FoNums.ordE, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < 5 + h.d := List.mem_range.1 hj
    simp only [Function.comp, roundValues, FoNums.placeOf, FoNums.w]
    by_cases c : j < h.d
    · rw [if_pos c, if_neg (by omega)]
    · rw [if_neg c, if_pos (by omega)]
  refine ⟨D, hD, R, fun t ht => ?_, ?_, ?_, ?_, hDg, ?_⟩
  · obtain ⟨G6, g1, g2, g3⟩ := R.fill
    rw [R.rowIs]
    refine bits_rowBitU D (5 + h.d) h.d rho F.next ρ h lm jLK θ t R.fitsB R.sizeY R.sizeV R.sizeZ
      hfB ht (took_sized _ hF) sBit g1 _ g2 ?_
    rw [show (D.bits2 (5 + h.d) h.d rho F.next).first = F.next + (1 + (5 + h.d + h.d)) from
      firstB_eq _ _ _ _ (by omega)]
    exact g3
  · rw [show (numsF h lm jLK θ).ledB.sh 0 = _ from (ledAt_bit h jLK).sh 0 (by omega)]
    show sBit = jLK + (FoNums.S h).fBit + 1 + (List.replicate (5 + h.d) 2 ++ [2]).sum + 0
    rw [R.sBitIs, hN, hb]
    simp
    omega
  · rw [R.next, hN, ← hall, hb]
    simp [sumcheckSlots, roundValues]
    omega
  · have hv : (D.bitsSc ρ (5 + h.d) h.d rho F.next).v 0 = ρ.val (F8.vp.getD sBit zeroE) := by
      obtain ⟨x, hx⟩ : ∃ x, D.v.toList = [x] :=
        List.length_eq_one_iff.1 (by rw [Array.length_toList]; exact R.sizeV)
      have e1 : D.v.toList.getD 0 zeroE = D.v.getD 0 zeroE := by
        simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
      rw [R.under.2.1, ← e1]
      show ((D.v.toList.map ρ.val).getD 0 0) = _
      rw [hx]
      rfl
    have hbe : (D.bitsSc ρ (5 + h.d) h.d rho F.next).be = ρ.val (F8.mf.getD sBit zeroE) := by
      rw [R.under.2.2]
      simp [Sc.be, R5D.bitsSc]
    rw [hv, hbe]
    exact slot_formIs ρ R.under.1
  · have e1 : ((zdL (5 + h.d) h.d rho).map fun p => (p.2 - 1, 1)) =
        (FoNums.S h).scEnd.degs.map fun n => (n, 1) := by
      have a : ((zdL (5 + h.d) h.d rho).map fun p => (p.2 - 1, 1)) =
          ((zdL (5 + h.d) h.d rho).map fun p => p.2).map fun x => (x - 1, 1) := by
        rw [List.map_map]
        rfl
      rw [a, hDg, (nums_led h jLK lm θ).2.2.2.2.2.2, List.map_map]
      rfl
    have e2 : ((zdB D.ptZ).map fun p => (p.2 - 1, 1)) = List.replicate (5 + h.d) (2, 1) := by
      have a : ((zdB D.ptZ).map fun p => (p.2 - 1, 1)) =
          ((zdB D.ptZ).map fun p => p.2).map fun x => (x - 1, 1) := by
        rw [List.map_map]
        rfl
      rw [a, zdB_snd, R.sizeZ, List.map_replicate]
    rw [R.sizes, e1, e2]
    show _ = ((1, 1) :: (FoNums.S h).scEnd.degs.map (fun n => (n, 1)) ++ []) ++ [(0, 5 + h.d)] ++
      ((1, 1) :: (List.replicate (5 + h.d) 2 ++ [2]).map (fun n => (n, 1)) ++ [(1, 0)])
    simp

end
end Fo
