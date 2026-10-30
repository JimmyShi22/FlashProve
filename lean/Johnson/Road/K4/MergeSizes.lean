-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MergeSizes.lean: THREE SIZES OF WHAT THE MERGE OF THE WEIGHT CLAIMS LEAVES, behind
K4's hearing: as many records as the plan counts claims, at least one, and as many challenges as the
layout has column bits. Statements and proofs, off the text of `flatForkEnd` and `Fl.wsForkMerge`
(OnBytes/K/Kc/QuietLink.lean) and the hearing's chain of calls (`hear_parts`,
OnBytes/Desc/First/K4/MergeClaims.lean).

Why. The pending row's function `pendingRowO` (Johnson/Desc/First/Pend/Row.lean) has, behind a test
on the layout's rows, three tests on what the merge left: the list of records is not empty; it has
as many members as the caller counts claims; there are lay.lk challenges. These are the facts on
K4's side of the three.

  `rounds_size`: n rounds append n challenges.
  `merge_sizes`: where `flatForkEnd lay cl sv` returns wo: cl is not empty; wo.recs has cl.size
    members; wo.rm has lay.lk.
  **`wo_sizes`**: where `hear` at the plain engine returns o: o.wo.recs is not empty and has hp.NCL
    members; o.wo.rm has P.wsLay.lk.

Limits. ONE DIRECTION, FROM A RETURN. THAT THE CALLER's COUNT OF CLAIMS IS hp.NCL, AND ITS LAYOUT
P.wsLay, IS NOT SAID HERE. Nothing on the further tests of `pendingRowO`. Nothing on what the
records hold. Nothing on soundness.
-/
import OnBytes.Desc.First.K4.MergeClaims
import Johnson.Road.K4.Reads.HearStarts
import OnBytes.Desc.First.P1.BatchPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.Desc.First.K4 (engFl hear hear_parts)
open OnBytes.Desc.First.K4.Reads (Ret)
open OnBytes.Desc.First.P1 (must_some pure_some batch_spec powers_size)

/-- n rounds append n challenges. -/
theorem rounds_size : ∀ (n : ℕ) (rm : Array E) (p : Psc),
    Ret (Fl.wsForkRounds n rm p) fun x => x.1.size = rm.size + n
  | 0, rm, p => by
    unfold Fl.wsForkRounds
    exact Ret.pure rfl
  | n + 1, rm, p => by
    unfold Fl.wsForkRounds
    refine Ret.skip fun x => ?_
    obtain ⟨r, p'⟩ := x
    intro F t a G u e
    have h := rounds_size n (rm.push r) p' F t a G u e
    rw [Array.size_push] at h
    omega

/-- **What the merge leaves has these sizes.** -/
theorem merge_sizes {lay : WsLay} {cl : Array WsClaim} {sv : Array ℕ} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (h : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    cl.size ≠ 0 ∧ wo.recs.length = cl.size ∧ wo.rm.size = lay.lk := by
  unfold flatForkEnd at h
  obtain ⟨_, A1, a1, c1, k1⟩ := OnBytes.Desc.First.P1.bind_some.mp h
  obtain ⟨m1, rfl, rfl⟩ := must_some.mp c1
  obtain ⟨_, A2, a2, c2, k2⟩ := OnBytes.Desc.First.P1.bind_some.mp k1
  obtain ⟨_, rfl, rfl⟩ := must_some.mp c2
  obtain ⟨_, A3, a3, c3, k3⟩ := OnBytes.Desc.First.P1.bind_some.mp k2
  obtain ⟨_, rfl, rfl⟩ := must_some.mp c3
  obtain ⟨x, G4, u4, c4, k4⟩ := OnBytes.Desc.First.P1.bind_some.mp k3
  obtain ⟨o, rho⟩ := x
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k4
  unfold Fl.wsForkMerge at c4
  obtain ⟨rho', B1, b1, d1, l1⟩ := OnBytes.Desc.First.P1.bind_some.mp c4
  obtain ⟨_, rfl, y, _, rfl⟩ := batch_spec d1
  obtain ⟨p, B2, b2, _, l2⟩ := OnBytes.Desc.First.P1.bind_some.mp l1
  obtain ⟨x2, B3, b3, d3, l3⟩ := OnBytes.Desc.First.P1.bind_some.mp l2
  obtain ⟨rm, p1⟩ := x2
  obtain ⟨x3, B4, b4, _, l4⟩ := OnBytes.Desc.First.P1.bind_some.mp l3
  obtain ⟨sFv, p2⟩ := x3
  obtain ⟨fvp, B5, b5, _, l5⟩ := OnBytes.Desc.First.P1.bind_some.mp l4
  obtain ⟨e, _, _⟩ := pure_some.mp l5
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hr : rm.size = 0 + lay.lk := rounds_size _ _ _ _ _ _ _ _ d3
  have hs : sv.size = cl.size := by
    simp only [Bool.and_eq_true, beq_iff_eq] at m1
    exact m1.2
  refine ⟨fun z => ?_, ?_, ?_⟩
  · obtain rfl := Array.eq_empty_of_size_eq_zero z
    simp at m1
  · simp [powers_size, hs]
  · show rm.size = lay.lk
    omega

/-- **Behind K4's hearing.** -/
theorem wo_sizes {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork}
    {t u : Tape} (h : hear engFl P hp g fo F t = some (o, G, u)) :
    o.wo.recs.isEmpty = false ∧ o.wo.recs.length = hp.NCL ∧ o.wo.rm.size = P.wsLay.lk := by
  obtain ⟨_, _, _, _, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, _, _, _, _, _, _, _, hs,
    hE⟩ := hear_parts h
  obtain ⟨h0, h1, h2⟩ := merge_sizes hE
  refine ⟨?_, by rw [h1, hs], h2⟩
  cases e : o.wo.recs with
  | nil =>
    rw [e] at h1
    exact absurd h1.symm h0
  | cons _ _ => rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.merge_sizes
#print axioms OnBytes.Road.K4.wo_sizes
