-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/DotIn.lean: the row (Dot), as K14's second part of the last chain lays it,
has passed the plain ground's tests on a new open row: stated in the library's form
`OnBytes.Means.RowIn` (Johnson/Desc/Means/Says.lean), at the statement and the own group behind the
block. Theorems.

Why. `addRowP_inv` (Johnson/Desc/Third/Law/Later.lean) keeps, of the ground's eight clauses on a new
row, "no test has begun" and "no sample row". A table of this chain's joints promises behind the
block that every open row of the own group lies on tables that the group's members have.

Main names.
  `addRowP_rowIn`: addRowP's yes gives `Means.RowIn` of the row, at the statement and the group in
    front of the adding: four of the ground's clauses ("the terms | the single entries | the runs |
    the forms fit their places").
  `dotIn_k14Second`: the block's yes gives the border, the own group in front and the row (Dot) (as
    `Says` names them) with `Means.RowIn` of (Dot) at the statement behind and the own group behind.

The plain ground asks these clauses by the description's own `Own.placeFits`, `Own.formFits`,
`Own.tensorInOrder` and `Own.coeffsInside`. The proof carries them back to the program's
`Blk.placeOk`, `Form.fits`, `Tensor.ok` and `Coeffs.ok` by the laws of agreement
(Johnson/Desc/Own/RowsAgree.lean, Johnson/Desc/Own/ShapesAgree.lean).

Limits. `t.v.ok` of the terms, `w.coeffs.ok` of the runs and "no coefficient on a pad", which the
ground asks too, are not carried. Of the form "a yes gives": met by a block that never says yes.
Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.Law.Says
import Johnson.Desc.Means.Keeps
import Johnson.Desc.Own.RowsAgree
import Johnson.Desc.Own.ShapesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open Desc.Plain (DState)
open VerifiableInference.Desc.Later
open VerifiableInference.Desc.Ground (addRowP)

namespace VerifiableInference.Desc.Third.Law

/-- addRowP's yes: the row lies on tables that the group's members have. -/
theorem addRowP_rowIn {L : Type} (d d' : DState L) (g : Nat) (row : OnBytes.Row) (G : OnBytes.Group)
    (h : addRowP d g row = some d') (hG : d.st.groups[g]? = some G) : Means.RowIn d.st G row := by
  unfold addRowP at h
  split at h
  · rename_i hok
    have t4 := ok_mem hok _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have t5 := ok_mem hok _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    have t6 := ok_mem hok _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _))))))
    have t7 := ok_mem hok _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))))
    rw [hG] at t4 t5 t6 t7
    -- The four clauses are found by their places in the ground's list. The four lines `have u4` to
    -- `have u7` beneath are the guard: if a clause more comes into the list, they fail.
    -- The ground asks these clauses in the description's own text of the four tests.
    -- Under `try` a lemma that has been renamed fails in silence: the red then comes at `have u4`.
    try simp only [← Own.placeFits_agrees, ← Own.formFits_agrees, ← Own.tensorInOrder_agrees,
      ← Own.coeffsInside_agrees] at t4 t5 t6 t7
    have u4 : (row.terms.all fun t => t.v.ok && Blk.placeOk d.st G t.oracle t.part t.v.vars 0) =
        true := t4
    have u5 : (row.units.all fun u =>
        Blk.placeOk d.st G u.oracle u.part (d.st.tableBits u.oracle u.part) u.index) = true := t5
    have u6 : (row.runs.all fun w =>
        w.coeffs.ok && decide (0 < w.coeffs.size) && decide (1 ≤ w.step) &&
          Blk.placeOk d.st G w.oracle w.part (d.st.tableBits w.oracle w.part)
            (w.first + w.step * (w.coeffs.size - 1))) = true := t6
    have u7 : (row.forms.all fun f =>
        Blk.placeOk d.st G f.oracle .main (d.st.tableBits f.oracle .main) 0 &&
          f.c.fits (d.st.tableBits f.oracle .main)) = true := t7
    simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, decide_eq_true_eq] at u4 u5 u6 u7
    exact ⟨fun t ht => (u4 t (Array.mem_toList_iff.1 ht)).2,
      fun u hu => u5 u (Array.mem_toList_iff.1 hu),
      fun w hw => ⟨(u6 w (Array.mem_toList_iff.1 hw)).1.1.2, (u6 w (Array.mem_toList_iff.1 hw)).1.2,
        (u6 w (Array.mem_toList_iff.1 hw)).2⟩,
      fun f hf => u7 f (Array.mem_toList_iff.1 hf)⟩
  · cases h

/-- **(Dot) lies on tables that the own group's members behind the block have.** -/
theorem dotIn_k14Second {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') :
    ∃ (x : Border) (G : OnBytes.Group) (dot : OnBytes.Row), s.loc.border = some x ∧
      s.st.groups[s.loc.own]? = some G ∧
      linDotRow p.S x.g x.shared.psi s.st.oracles.size (linLayOmega s.st.codes p.S) s.loc.w
        (linLayW s.st.codes p.S) = some dot ∧
      Means.RowIn s'.st { G with
      members := G.members.insertIdxIfInBounds (G.members.filter (· < s.st.oracles.size)).size
        s.st.oracles.size
      kept := G.kept.insertIdxIfInBounds (G.members.filter (· < s.st.oracles.size)).size false
      rows := G.rows.push dot } dot := by
  obtain ⟨x, a, dot, b, hx, ha, hd, hb, e⟩ := k14Second_inv p s s' rs gs h
  subst e
  obtain ⟨y, G, hm, _, _, _, _, hG0, _, g2, _, _, _⟩ := takeOver_says _ _ _ _ _ ha
  have hm' : a.1 = s.st.oracles.size := hm
  have hc : a.2.st.codes = s.st.codes := (carries_takeOver _ _ _ _ _ ha).1.1.codes
  obtain ⟨_, _, eb⟩ := addRowP_inv _ _ _ _ hb
  rw [hc, hm'] at hd
  refine ⟨x, G, dot, hx, hG0, hd, ?_⟩
  show Means.RowIn b.st _ dot
  rw [eb]
  have hr := addRowP_rowIn _ _ _ _ _ hb g2
  refine Means.RowIn.extends (Means.extends_withRow _ _ _) ?_ hr
  exact fun _ hh => hh

end VerifiableInference.Desc.Third.Law
