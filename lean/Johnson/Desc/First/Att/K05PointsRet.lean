-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PointsRet.lean: pointsOf (Att/Points.lean) returns where its guards'
numbers are right.

Main names:
  `guard_ret`: a guard on a true condition returns.
  `points_ret`: as many remainder messages, units and rows as the place has; each unit's inner point
    of its length; the three single units there,
    with NP pieces and inner points of their lengths: then pointsOf returns.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PointsRows
import Johnson.Desc.First.Att.K05LeftRet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part

theorem guard_ret {p : Prop} [Decidable p] (h : p) : (guard p : Option Unit) = some () := by
  simp [guard, h]

/-- **pointsOf returns.** -/
theorem points_ret {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left}
    (n1 : (g.units .kr [.rm, .rd]).length = h.remainders.size)
    (n2 : g.scores.length = h.scores.size) (n3 : g.scores.length = L.scores.size)
    (hu : ∀ u ∈ g.scores, (inner u (zk.getD u.call #[])).size =
      (if u.below then g.lgk + (g.lnT - 1) + g.lnT else g.lgk + g.lnT) + 2 * g.lB)
    {uW uX uH : UnitG} (sW : g.single .wl = some uW) (sX : g.single .ix = some uX) (sH : g.single .wh = some uH)
    (pW : (piecesOf uW (zk.getD uW.call #[])).size = g.NP) (pX : (piecesOf uX (zk.getD uX.call #[])).size = g.NP)
    (pH : (piecesOf uH (zk.getD uH.call #[])).size = g.NP)
    (zW : (inner uW (zk.getD uW.call #[])).size = 1 + g.lgk + g.lt + g.ldh)
    (zX : (inner uX (zk.getD uX.call #[])).size = g.lgk + g.lt)
    (zH : (inner uH (zk.getD uH.call #[])).size = g.lgk + g.lt + g.ldh) :
    ∃ p, pointsOf g zk h L = some p := by
  cases hp : pointsOf g zk h L with
  | some p => exact ⟨p, rfl⟩
  | none =>
    exfalso
    unfold pointsOf at hp
    simp only [Option.bind_eq_bind, Option.bind_eq_none_iff, Option.pure_def] at hp
    have k1 := hp () (guard_ret (by simp [n1])) () (guard_ret (by simp [n2, ← n3]))
    rw [← Array.foldlM_toList] at k1
    refine Exists.elim (foldlM_some _ _ ?_ _) fun acc hacc => Option.some_ne_none _
      (k1 acc hacc uW sW uX sX uH sH ()
        (guard_ret (by simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨⟨pW, pX⟩, pH⟩)) ()
        (guard_ret (by simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨⟨zW, zX⟩, zH⟩)))
    intro x hx acc
    have hxu : x.1.1 ∈ g.scores := by
      have h1 := (List.of_mem_zip (by simpa using hx)).1
      have h2 := (List.of_mem_zip (by simpa using h1)).1
      simpa using h2
    exact ⟨_, by rw [guard_ret (beq_iff_eq.2 (hu _ hxu))]; rfl⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.points_ret
