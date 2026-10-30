-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoTieEnd.lean.
The tie of a sub-proof's lookup: what the byte-level verifier's Forest.tie returns, read into a
commutative ring, is what the flat function computes from the same rounds.

States, for every reading ρ of the byte-level field:
  tie_is: if Forest.tie returns, then a list of calls leads from the run's first context to its
    last (Evs); it is a row of rounds: those of 31 steps, then a point; on them the flat function
    takes its 31 steps; the state left is a later one, in which the tie's own slots, and no others,
    are newly filled and nothing else is turned; the 31 claims are the flat function's rows; the
    slot of the key side's root holds the flat function's claim on the keys' product; the point is
    the drawn point reversed; and, if five elements were drawn, the start form of the table side's
    top level is the flat function's.
Premises: the state fits (Sized), and its first free slot is base; the public factor reads as the
flat function's; the flat function has 32 planes in 2^5 places; its places of each step's masks lie
from the step's first slot on.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTieAll
import OnBytes.Tie.Pv.Lookup.Port.FoTwins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The last member of a list of m + 1. -/
theorem last_of {α : Type} (l : List α) (m : ℕ) (d : α) (h : l.length = m + 1) :
    ∃ q, q.length = m ∧ l = q ++ [l.getD m d] := by
  rcases List.eq_nil_or_concat' l with rfl | ⟨q, z, rfl⟩
  · exact absurd h (by simp)
  · have hq : q.length = m := by simpa using h
    refine ⟨q, hq, ?_⟩
    rw [snoc_getD, if_neg (by omega), if_pos hq.symm]

variable (N : Nums Pl K) (lam : K) (base : ℕ)

/-- The trace in which the tie alone is played. -/
def tieTrace (scs : List (Sc K)) (join : List K) : Trace K :=
  ⟨lam, scs, join, [], 0, [], Sc.zero, [], Sc.zero⟩

/-- What Forest.tie returns. -/
theorem tie_is (a : E) (ha : ρ.val a = fac N lam) (hn : N.n = 30) (hw : N.w = 5)
    (hLed : ∀ j, j < 31 → LedAt (N.ledTie j) (base + tieOff j) [3] (if j = 0 then 3 else 2))
    (F0 G : Fork) (c0 c' : Ctx) (hF0 : Sized F0) (hb : F0.next = base) (T : Forest.Tie)
    (h : Forest.tie a F0 c0 = .ok ((T, G), c')) :
    ∃ l scs c1 pt, Evs l c0 c1 ∧ Rds l ∧ Evs [.point .lkpPlanes 5 pt] c1 c' ∧
      (∀ rest, tieGo 31 0 0 (flEv ρ (l ++ [.point .lkpPlanes 5 pt]) ++ rest) =
        (scs, ([], rdA ρ pt) :: rest)) ∧
      Later F0 G ∧ Sized G ∧ Same (took F0 (tieOff 31)) G ∧
      (∀ j, Filled G j ↔ Filled F0 j ∨ (base ≤ j ∧ j < base + tieOff 31)) ∧
      T.rows.size = 31 ∧
      (∀ i, i < 31 → RowIs ρ G (T.rows.getD i {})
        ((tieRowsR N lam scs.reverse).reverse.getD i ⟨[], 0⟩)) ∧
      T.sZ = base + 4 ∧
      FormIs ρ G (Aff.slot T.sZ) (tK (tieTrace lam scs (rdA ρ pt)))
        (fK N (tieTrace lam scs (rdA ρ pt))) ∧
      rdA ρ T.rhoT = (rdA ρ pt).reverse ∧
      (pt.size = 5 → FormIs ρ G T.cT (tgT0 N (tieTrace lam scs (rdA ρ pt)))
        (incT0 N (tieTrace lam scs (rdA ρ pt)))) ∧
      Stretch F0 G (tieOff 31) ∧
      (flEv ρ l).map (fun r => (r.1.length, r.2.length)) = (List.range 31).flatMap tieSizes := by
  obtain ⟨s, c1, pt, h1, hev, rfl⟩ := tie_ok a F0 G c0 c' T h
  obtain ⟨l, scs, i1, i2, i3, i4, i5, i6, inv, i7, i8⟩ :=
    tieLoop_is ρ N lam base a ha hLed F0 c0 hF0 hb 31 (le_refl _) s G c1 h1
  obtain ⟨z1, z2⟩ := inv.sZ (by norm_num)
  refine ⟨l, scs, c1, pt, i1, i2, hev, fun rest => ?_, i4, inv.sized, i5, i6, inv.rowsN, inv.rows,
    z1, z2, ?_, fun hpt => ?_, i7, i8⟩
  · rw [flEv_app ρ (i2.closed ρ), List.append_assoc, i3]
    rfl
  · show (pt.reverse.toList.map ρ.val) = (pt.toList.map ρ.val).reverse
    rw [Array.toList_reverse, List.map_reverse]
  · obtain ⟨q, hq, hl⟩ := last_of scs 30 Sc.zero inv.len
    have hsP := inv.sP
    rw [if_neg (by norm_num)] at hsP
    have e1 : tgEnd 0 0 scs = (scs.getD 30 Sc.zero).v (nxAt 30) := by
      unfold tgEnd
      rw [inv.len]
      conv_lhs => rw [hl]
      rw [List.getLast?_append]
      rfl
    have e2 : tieInc N scs.reverse =
        [((N.ledTie 30).sh (nxAt 30), (scs.getD 30 Sc.zero).be)] := by
      conv_lhs => rw [hl]
      rw [List.reverse_append]
      show [((N.ledTie q.reverse.length).sh (nxAt q.reverse.length), (scs.getD 30 Sc.zero).be)] = _
      rw [List.length_reverse, hq]
    rw [e1, e2] at hsP
    have hslot : ∀ j, j < 32 → FormIs ρ G (Aff.slot ((s.sG.push s.sP).getD j 0))
        (tgtT N (tieTrace lam scs (rdA ρ pt)) j) (formT N (tieTrace lam scs (rdA ρ pt)) j) := by
      intro j hj
      rw [push_getD, inv.sGN]
      unfold tgtT formT
      rw [hn]
      by_cases h31 : j < 31
      · rw [if_pos h31, if_pos h31, if_pos h31]
        exact inv.sG j h31
      · have e : j = 31 := by omega
        rw [if_neg h31, if_neg h31, if_neg h31, if_pos e, if_pos e, if_pos e]
        exact hsP
    have hej : ∀ j, j < 32 → ρ.val ((eqTab pt.reverse).getD j zeroE) = eqN (rdA ρ pt) j := by
      intro j hj
      rw [rdL_getD, eqTab_val, eqTabK_get, rdL_length, Array.size_reverse, hpt,
        if_pos (show j < 2 ^ 5 from hj)]
      congr 1
      show (pt.reverse.toList.map ρ.val).reverse = pt.toList.map ρ.val
      rw [Array.toList_reverse, List.map_reverse, List.reverse_reverse]
    refine formIs_value ρ fun H hH mask entry => ?_
    rw [tieCT_value]
    unfold tgT0 incT0
    rw [evalL_flatMap, hw, lsum, lsum, lsum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < 32 := Finset.mem_range.mp hj
    have hv := (hslot j hj' H hH).2 mask entry
    rw [Aff.value_slot] at hv
    rw [hv, hej j hj', evalL_scale]
    show _ = eqN (rdA ρ pt) j * _ - eqN (rdA ρ pt) j * _
    ring

end
end Fo
