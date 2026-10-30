-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoTieEnd.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoTieEnd.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  tie_is
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  Filled, FormIs, Later, LedAt, RowIs, Same, Sized, Stretch, eqTab_val, evalL_flatMap,
  evalL_scale, flEv, flEv_app, formIs_value, last_of, push_getD, rdL_getD, rdL_length, rhoT,
  tgEnd, tieCT_value, tieOff, tieSizes, tieTrace, took
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTieEnd
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.PscRounds
import Johnson.Top.H.FlPort.FoTieAll
import Johnson.Top.H.FlPort.FoTieInv

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.PscRun

section
variable {K : Type} [CommRing K] (ρ : Reading K)

variable (N : Nums Pl K) (lam : K) (base : ℕ)

/-- What lkTie returns. -/
theorem tie_is (a : E) (ha : ρ.val a = fac N lam) (hn : N.n = 30) (hw : N.w = 5)
    (hLed : ∀ j, j < 31 → LedAt (N.ledTie j) (base + tieOff j) [3] (if j = 0 then 3 else 2))
    (F0 G : Fork) (c0 c' : Tape) (hF0 : Sized F0) (hb : F0.next = base) (T : Forest.Tie)
    (h : lkTie a F0 c0 = .ok ((T, G), c')) :
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

end Fo.Tp
