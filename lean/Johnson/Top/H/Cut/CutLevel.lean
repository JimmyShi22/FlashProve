-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Cut/CutLevel.lean: the grand product (Johnson/Desc/First/Prod/Level.lean: `level`,
`turn`, `run`) gives the library's flat level (`Fl.levelIn`, OnBytes/K/Kc/Flat.lean; `lkLevel`,
OnBytes/K/Kc/FlatHear.lean). Theorems with their proofs, each from the part's yes, with the value,
the ledger behind and the tape left spelled out.

The three differences between the two texts, and how each is met:

  (i) `level` makes its row in front of the round LINE, `Fl.levelIn` behind it: the row's making
    leaves the tape and goes the same way on any tape; the draw leaves the ledger and goes the
    same way on any ledger (Johnson/Top/H/Cut/CutKit.lean).
  (ii) `Fl.levelIn` asks that the order has mu members, each below mu, and that the point has the
    coordinates that are read; `level` does not. See Limits.
  (iii) `level` lays r back from the list of challenges, `Fl.levelIn` sets it round by round:
    `rounds_level` (Johnson/Top/H/Cut/CutWhole.lean).

Main names: `cut_levelIn` (from `WholeCut` and the draw of LINE), `level_levelIn`, `turn_lkLevel`,
`run_fold`; `orderDefault_ok`, `orderForest_ok`.

Limits. Premises: order.length = m; every member is below m; the point has m coordinates. Who
pays: the orders' two are paid by `orderDefault_ok` (nothing is asked) and `orderForest_ok` (rK +
9 ≤ mu); the point's size goes along a run by induction (`run_fold`), from the first point's size,
which the caller pays. One way alone: the flat level's yes is not shown to give `level`'s. These
are ties between texts, equations on what they return: they have no error term. No routine in a
context of the verifier program's channel is named.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Cut.CutWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3Cut
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundForm orderDefault)
open OnBytes.Model.Forest (Descent orderForestRange)
open First.Prod (wholeStandIn Whole LevelOut Carried layBack level turn run stepDown)

/-- Setting coordinates keeps the number of coordinates. -/
theorem setAll_size (m : Nat) : ∀ (l : List (Nat × E)) (r : Array E),
    (l.foldl (fun (r : Array E) x => r.set! (m - 1 - x.1) x.2) r).size = r.size
  | [], _ => rfl
  | x :: l, r => by
    rw [List.foldl_cons, setAll_size m l]
    exact Array.size_setIfInBounds

/-- **One level, from the course of its masked sumcheck and the draw of LINE behind it.** -/
theorem cut_levelIn {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F Fw G : Fork}
    {t tw u : Tape} {w : Whole} {xi : E} (hlen : order.length = m)
    (hlt : ∀ v ∈ order, v < m ∧ m - 1 - v < z.size)
    (hw : WholeCut C (order.map fun b => z.getD (m - 1 - b) zeroE) 2 2
      (fun v => mulE (v.getD 0 zeroE) (v.getD 1 zeroE)) F t w Fw tw)
    (hxi : Fl.answer .line Fw tw = some (xi, G, u)) :
    Fl.levelIn m z C order F t =
      some ({ r := layBack m order (w.challenges.take m), sL := w.sEnd, sR := w.sEnd + 1, tau := xi,
              row := w.row }, G, u) := by
  obtain ⟨p0, F0, t0, p1, F1, t1, p2, F2, t2, ends, p3, h0, h1, h2, hs, h4, hc⟩ := hw
  obtain ⟨cs, hl, hcs, hL⟩ :=
    rounds_level m z order (Array.replicate m zeroE) p0 F0 t0 p1 F1 t1 hlt h1
  obtain ⟨beta, hb⟩ := ends_r h2
  obtain ⟨e4, hrow⟩ := pscRow_anyTape h4
  subst e4
  obtain ⟨e5, hans⟩ := answer_anyLedger hxi
  subst e5
  have hch : w.challenges.take m = cs := by
    have k : (([] : List E) ++ cs ++ [beta]).take m = cs := by
      rw [List.nil_append, ← hlen, ← hl]
      exact List.take_left' rfl
    rw [hc, hb, Array.toList_push, hcs, begin_r h0]
    exact k
  unfold Fl.levelIn
  refine bindM (mustM (by simp [hlen]) _ _) ?_
  refine bindM h0 ?_
  refine bindM hL ?_
  refine bindM h2 ?_
  refine bindM (hans _) ?_
  refine bindM (shownM (hs 0 (by omega)) _) ?_
  refine bindM (shownM (hs 1 (by omega)) _) ?_
  refine bindM (hrow _) ?_
  rw [hch]
  rfl

/-- The point that is laid back has m coordinates. -/
theorem layBack_size (m : Nat) (order : List Nat) (cs : List E) :
    (layBack m order cs).size = m := by
  unfold First.Prod.layBack
  rw [setAll_size]
  simp

/-- **One level.** -/
theorem level_levelIn {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {t u : Tape} {o : LevelOut} (hlen : order.length = m)
    (hlt : ∀ v ∈ order, v < m ∧ m - 1 - v < z.size)
    (h : level m z order C F t = some (o, G, u)) :
    Fl.levelIn m z C order F t =
        some ({ r := o.r, sL := o.sL, sR := o.sR, tau := o.xi, row := o.row }, G, u) ∧
      o.r.size = m := by
  unfold First.Prod.level at h
  obtain ⟨w, Fw, tw, hw, g1⟩ := bindS h
  obtain ⟨xi, Fx, tx, hxi, g2⟩ := bindS g1
  obtain ⟨e1, e2, e3⟩ := pureS g2
  subst e1 e2 e3
  exact ⟨cut_levelIn hlen hlt (whole_ok hw) hxi, layBack_size _ _ _⟩

/-- **One turn of a run**: the level, its row pushed, the step down. -/
theorem turn_lkLevel {order : List Nat} {s s' : Carried} {m : Nat} {F G : Fork} {t u : Tape}
    (hlen : order.length = m) (hlt : ∀ v ∈ order, v < m) (hsz : s.point.size = m)
    (h : turn order s m F t = some (s', G, u)) :
    lkLevel ⟨s.rows, s.point, s.form⟩ m order F t = some (⟨s'.rows, s'.point, s'.form⟩, G, u) ∧
      s'.point.size = m + 1 := by
  unfold First.Prod.turn at h
  obtain ⟨o, F1, t1, h1, h⟩ := bindS h
  obtain ⟨e1, e2, e3⟩ := pureS h
  subst e1 e2 e3
  obtain ⟨hL, hr⟩ :=
    level_levelIn hlen (fun v hv => ⟨hlt v hv, by have := hlt v hv; omega⟩) h1
  refine ⟨?_, ?_⟩
  · unfold lkLevel
    exact bindM hL rfl
  · show (#[o.xi] ++ o.r).size = m + 1
    rw [Array.size_append, hr]
    have k : (#[o.xi] : Array E).size = 1 := rfl
    omega

/-- **A run of n levels** gives the fold of the flat levels, and the point grows by one coordinate a
level. -/
theorem run_fold {m0 n : Nat} {orders : Nat → List Nat} {s s' : Carried} {F G : Fork} {t u : Tape}
    (ho : ∀ i, i < n → (orders (m0 + i)).length = m0 + i ∧ ∀ v ∈ orders (m0 + i), v < m0 + i)
    (hs : s.point.size = m0) (h : run m0 n orders s F t = some (s', G, u)) :
    (List.range n).foldlM (fun (d : Descent) i => lkLevel d (m0 + i) (orders (m0 + i)))
        ⟨s.rows, s.point, s.form⟩ F t = some (⟨s'.rows, s'.point, s'.form⟩, G, u) ∧
      s'.point.size = m0 + n := by
  unfold First.Prod.run at h
  rw [List.range_eq_range'] at h ⊢
  have K : Gives (fun (a : Carried) (b : Descent) =>
        b = ⟨a.rows, a.point, a.form⟩ ∧ a.point.size = m0 + n)
      ((List.range' 0 n).foldlM (fun (s : Carried) i => turn (orders (m0 + i)) s (m0 + i)) s)
      ((List.range' 0 n).foldlM (fun (d : Descent) i => lkLevel d (m0 + i) (orders (m0 + i)))
        ⟨s.rows, s.point, s.form⟩) := by
    refine Gives.foldRange _ _ n
      (fun i (a : Carried) (b : Descent) => b = ⟨a.rows, a.point, a.form⟩ ∧ a.point.size = m0 + i)
      0 0 s ⟨s.rows, s.point, s.form⟩ ?_ ⟨rfl, hs⟩
    intro i a b hi hab F1 t1 a' G1 u1 e
    obtain ⟨hb, ha⟩ := hab
    subst hb
    rw [Nat.zero_add] at e ⊢
    obtain ⟨k1, k2⟩ := turn_lkLevel (ho i hi).1 (ho i hi).2 ha e
    exact ⟨_, k1, rfl, k2⟩
  obtain ⟨b, hb, e, hsz⟩ := K F t s' G u h
  subst e
  exact ⟨hb, hsz⟩

/-! ## The orders -/

/-- The default order of mu variables has mu members, all below mu. -/
theorem orderDefault_ok (mu : Nat) :
    (orderDefault mu).length = mu ∧ ∀ v ∈ orderDefault mu, v < mu := by
  unfold OnBytes.Model.orderDefault
  refine ⟨by simp, fun v hv => ?_⟩
  simpa using hv

/-- The order of the last key level has mu members, all below mu, if mu - rK is at least 9. -/
theorem orderForest_ok {mu rK : Nat} (h : rK + 9 ≤ mu) :
    (orderForestRange mu rK).length = mu ∧ ∀ v ∈ orderForestRange mu rK, v < mu := by
  unfold OnBytes.Model.Forest.orderForestRange
  refine ⟨?_, fun v hv => ?_⟩
  · simp only [List.length_append, List.length_map, List.length_reverse, List.length_range,
      List.length_cons, List.length_nil]
    omega
  · simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_range] at hv
    rcases hv with (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩) | hv
    · have k : c ≤ 8 := by
        simp at hc
        omega
      omega
    · omega
    · omega

end VerifiableInference.Desc.K3Cut
