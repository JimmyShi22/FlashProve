-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Cut/CutPad.lean: **wherever the lookup's hearing `K3.messages`
(Johnson/Desc/First/Look/K3Lookup.lean) returns, the library's flat copy `lkPad`
(OnBytes/K/Kc/FlatHear.lean) returns the same value, the same ledger and the same tape.** Theorems
with their proofs.

Main names:

  `draws_ok`: the two draws give `lkDraws`, where there are several calls.
  `keyOrders_ok`: every order of the key side has mu members, all below mu, if 10 ≤ dT.
  `messages_cut`: the tie, from the premises one by one.
  `messages_lkPad`: the tie, from `Fo.ShapeOf calls pub lid h` and 1 < h.NC.

The premises, and who pays each.

  Fo.ShapeOf calls pub lid h (OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean): h is what `Forest.shape`
    makes of the calls, with the padding numbers pub, which pass `Forest.pubAsk`. `lkPad` asks
    both tests itself; `messages` is handed h. Paid by whoever makes the place's shape
    (`P.shape`).
  1 < h.NC: `messages` always hears the shift; `lkPad` only where there are several calls. Paid by
    `K3.hear`, which asks it.
  What `Fl.levelIn` asks of the orders and the points, and `level` does not, is no premise: 10 ≤
    dT follows from the shape's yes (`OnBytes.Ends.shape_adm`, a lemma on the pure function
    `Forest.shape`); the points' sizes go along the runs. `K3.planOk` is not used.

Limits. It is a tie between two texts, an equation on what they return: it has no error term. One
way alone: `lkPad`'s yes is not shown to give `messages`' yes. It does not say that `messages`
returns anywhere: that is a matter of runs. No routine in a context of the verifier program's
channel is named.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Cut.CutLevel
import Johnson.Top.H.Cut.CutTie
import OnBytes.Tie.Pv.Lookup.Port.FoHeard
import OnBytes.Tie.Pv.Lookup.Ends.ShapePrem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3Cut
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundForm Call orderDefault)
open OnBytes.Model.Forest (Shape Heard shape pubAsk)

/-- The shift and alpha, where there are several calls. -/
theorem draws_ok {h : Shape} (hN : 1 < h.NC) {F1 F2 F3 : Fork} {t1 t2 t3 : Tape} {theta alpha : E}
    (k5 : Fl.answer .lkpShift F1 t1 = some (theta, F2, t2))
    (k6 : Fl.answer .lkp F2 t2 = some (alpha, F3, t3)) :
    lkDraws h F1 t1 = some ((theta, alpha, K3.paddingFactor h theta alpha), F3, t3) := by
  have hN' : h.NC > 1 := hN
  unfold lkDraws
  rw [if_pos hN']
  exact bindM k5 (bindM k6 rfl)

/-- Every order of the key side has mu members, all below mu. -/
theorem keyOrders_ok {h : Shape} (hd : 10 ≤ h.dT) (mu : Nat) :
    (K3.keyOrders h mu).length = mu ∧ ∀ v ∈ K3.keyOrders h mu, v < mu := by
  unfold K3.keyOrders
  split
  · rename_i e
    have e' : mu + 1 = h.dT + h.rK := e
    exact orderForest_ok (by omega)
  · exact orderDefault_ok mu

/-- **The tie, from the premises one by one.** -/
theorem messages_cut {calls : Array Call} {pub : Array Nat} {lid : Nat} {h0 : Shape}
    (hs : shape calls lid = .ok h0) (hp : (pubAsk h0 pub).toBool = true)
    (hN : 1 < h0.NC) (hd : 10 ≤ h0.dT) {F : Fork} {t : Tape} {x : Heard × Fork × Tape}
    (hm : K3.messages { h0 with pub := pub } F t = some x) :
    lkPad calls pub lid F t = some x := by
  unfold K3.messages at hm
  obtain ⟨slot0, A1, a1, k1, hm⟩ := bindS hm
  obtain ⟨o1, A2, a2, k2, hm⟩ := bindS hm
  obtain ⟨o2, A3, a3, k3, hm⟩ := bindS hm
  obtain ⟨o3, A4, a4, k4, hm⟩ := bindS hm
  obtain ⟨theta, A5, a5, k5, hm⟩ := bindS hm
  obtain ⟨alpha, A6, a6, k6, hm⟩ := bindS hm
  obtain ⟨⟨rows, sZ, sG⟩, A7, a7, k7, hm⟩ := bindS hm
  obtain ⟨y, A8, a8, k8, hm⟩ := bindS hm
  obtain ⟨keys, A9, a9, k9, hm⟩ := bindS hm
  obtain ⟨table, A10, a10, k10, hm⟩ := bindS hm
  obtain ⟨_, A11, a11, k11, hm⟩ := bindS hm
  obtain ⟨leaves, A12, a12, k12, hm⟩ := bindS hm
  obtain ⟨⟨zb0, leaves1⟩, A13, a13, k13, hm⟩ := bindS hm
  obtain ⟨y5, A14, a14, k14, hm⟩ := bindS hm
  obtain ⟨bits, A15, a15, k15, hm⟩ := bindS hm
  obtain ⟨s1, A16, a16, k16, hm⟩ := bindS hm
  obtain ⟨_, A17, a17, k17, hm⟩ := bindS hm
  obtain ⟨_, A18, a18, k18, hm⟩ := bindS hm
  obtain ⟨_, A19, a19, k19, hm⟩ := bindS hm
  -- the pieces
  have kd := draws_ok (h := { h0 with pub := pub }) hN k5 k6
  have kt := tie_lkTie k7 k8
  have kk := run_fold (m0 := 0) (orders := K3.keyOrders { h0 with pub := pub })
    (fun i _ => keyOrders_ok (h := { h0 with pub := pub }) hd (0 + i)) (by rfl) k9
  simp only [Nat.zero_add] at kk
  have ky : y.reverse.size = 5 := by
    rw [Array.size_reverse]
    exact point_size k8
  have kb := run_fold (m0 := 5) (orders := orderDefault) (fun i _ => orderDefault_ok (5 + i)) ky k10
  have k5' : y5.reverse.toList.length = 5 + (({ h0 with pub := pub } : Shape)).d := by
    rw [Array.length_toList, Array.size_reverse]
    exact point_size k14
  obtain ⟨b0, B0, c0, b1, B1, c1, b2, B2, c2, vBit, b3, j0, j1, j2, j3, j4⟩ := whole_bits k5' k15
  -- the flat text, line by line
  unfold lkPad
  refine bindM (a := h0) (F1 := F) (t1 := t) (by rw [hs]; rfl) ?_
  refine bindM (mustM hp _ _) ?_
  refine bindM k1 ?_
  refine bindM k2 ?_
  refine bindM k3 ?_
  refine bindM k4 ?_
  refine bindM kd ?_
  refine bindM kt ?_
  refine bindM kk.1 ?_
  refine bindM kb.1 ?_
  refine bindM k11 ?_
  refine bindM k12 ?_
  refine bindM k13 ?_
  refine bindM k14 ?_
  refine bindM j0 ?_
  refine bindM j1 ?_
  refine bindM j2 ?_
  refine bindM j3 ?_
  refine bindM j4 ?_
  refine bindM k16 ?_
  refine bindM k17 ?_
  refine bindM k18 ?_
  refine bindM k19 ?_
  exact hm

/-- **messages' yes gives lkPad's yes: the same value, the same ledger, the same tape.** -/
theorem messages_lkPad {calls : Array Call} {pub : Array Nat} {lid : Nat} {h : Shape}
    (hS : Fo.ShapeOf calls pub lid h) (hN : 1 < h.NC) {F : Fork} {t : Tape}
    {x : Heard × Fork × Tape} (hm : K3.messages h F t = some x) :
    lkPad calls pub lid F t = some x := by
  obtain ⟨h0, hs, hp, rfl⟩ := hS
  exact messages_cut hs (by rw [hp]; rfl) hN (OnBytes.Ends.shape_adm hs).2.2.1 hm

end VerifiableInference.Desc.K3Cut

#print axioms VerifiableInference.Desc.K3Cut.messages_lkPad
#print axioms VerifiableInference.Desc.K3Cut.tie_lkTie
#print axioms VerifiableInference.Desc.K3Cut.run_fold
#print axioms VerifiableInference.Desc.K3Cut.whole_bits
