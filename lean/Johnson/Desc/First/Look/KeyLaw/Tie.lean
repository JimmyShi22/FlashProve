-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Tie.lean: the first two stretches of the lookup: the tie of the two
sides' roots (tieG against the course's cHead behind its draw) and the parts' steps (partsG against
cParts).

Main names:
  headTail D s: the course's first stretch behind the draw of alpha; cHead_eq.
  tieLoop, tie_sim; parts_loop, parts_sim.

Limits. One world W of mask entries; where the flat functions return.

-/
import Johnson.Desc.First.Look.KeyLaw.Step
import Johnson.Desc.First.Look.K3LookupGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm Reading World)
open OnBytes.PscRun (took Later Sized Filled Ran)
open First.Prod (wholeStandIn Whole)
open Lk6.PortSim (noClaim onValue sTie sTie1 sProd)
open Lk6.Mid (Dt Cs RowF pscC heardF slots eqPairsF cTie cHead cPart cParts)

theorem own_add (a b : ℕ) : own (a + b) = own a ++ own b :=
  List.replicate_add a b false

theorem flat_succ {α : Type} (n : ℕ) (L : List α) :
    ((List.range (n + 1)).flatMap fun _ => L) = L ++ (List.range n).flatMap fun _ => L := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

theorem getD_push_lt (a : Array ℕ) (v i : ℕ) (h : i < a.size) : (a.push v).getD i 0 = a.getD i 0 :=
    by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt h]

theorem getD_push_eq (a : Array ℕ) (v : ℕ) : (a.push v).getD a.size 0 = v := by
  simp [Array.getD_eq_getD_getElem?]

variable {W : PscF.World} {home : ℕ → Slot} {D : Dt}

/-- The later steps of the tie. -/
theorem tieLoop (l : List ℕ) : ∀ (x x' : Array Aff × ℕ × Array ℕ) (F G : Fork) (t u : Tape) (s : Cs)
    (j : ℕ) (pat : List Bool),
    (l.foldlM (m := Fl) (fun (s : Array Aff × ℕ × Array ℕ) _ => do
      let y ← wholeStandIn (Aff.slot s.2.1) [] 3 2 fun v =>
        mulE (mulE (v.getD 0 zeroE) (v.getD 0 zeroE)) (v.getD 1 zeroE)
      pure (s.1.push y.row, y.sEnd, s.2.2.push (y.sEnd + 1))) x) F t = some (x', G, u) →
    St W home D F t s (own (6 * l.length) ++ pat) x.1.toList →
    RC W home F (Aff.slot x.2.1) s.pow → x.2.2.size = j + 1 →
    (∀ i ≤ j, RC W home F (Aff.slot (x.2.2.getD i 0)) (s.planes i)) →
    St W home D G u (cTie D l.length j s) pat x'.1.toList ∧
      RC W home G (Aff.slot x'.2.1) (cTie D l.length j s).pow ∧
      x'.2.2.size = j + 1 + l.length ∧
      (∀ i ≤ j + l.length, RC W home G (Aff.slot (x'.2.2.getD i 0))
        ((cTie D l.length j s).planes i)) ∧
      (cTie D l.length j s).rest = s.rest ∧ (cTie D l.length j s).alpha = s.alpha ∧ Later F G ∧
      Shp t u ((List.range l.length).flatMap fun _ => pscShape [] (some (3, 2))) := by
  induction l with
  | nil =>
    intro x x' F G t u s j pat h hst hp hz hpl
    cases pure_some h
    exact ⟨hst, hp, hz, hpl, rfl, rfl, Later.refl _, Shp.refl _⟩
  | cons a l ih =>
    intro x x' F G t u s j pat h hst hp hz hpl
    rw [List.foldlM_cons] at h
    replace h := bind_some h
    obtain ⟨x1, G1, u1, h1, h⟩ := h
    replace h1 := bind_some h1
    obtain ⟨y, G2, u2, h2, h1⟩ := h1
    cases pure_some h1
    have hst' : St W home D F t s ((if false = true then own (1 + 2 * ([] : List E).length + 3 + 2 -
        2)
        ++ [true, true] else own (1 + 2 * ([] : List E).length + 3 + 2)) ++
        (own (6 * l.length) ++ pat)) x.1.toList := by
      have e : own (6 * (a :: l).length) ++ pat = own 6 ++ (own (6 * l.length) ++ pat) := by
        rw [List.length_cons, show 6 * (l.length + 1) = 6 + 6 * l.length by omega, own_add,
          List.append_assoc]
      rw [e] at hst
      exact hst
    obtain ⟨s1, -, -, s4, s5, s6⟩ := step (c := onValue s.pow) (S := sTie) (place := id) h2 hst' rfl
        hp
      rfl rfl (by decide) (fun pt y => by
        show (y.map readE).getD 0 0 * (y.map readE).getD 0 0 * (y.map readE).getD 1 0 = _
        rw [readE_mul, readE_mul, read_getD, read_getD])
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := ih _ x' _ G _ u
      { (pscC D (onValue s.pow) sTie false 0 id s).2 with
        pow := (pscC D (onValue s.pow) sTie false 0 id s).1.ends.getD 0 noClaim
        planes := Function.update (pscC D (onValue s.pow) sTie false 0 id s).2.planes (j + 1)
          ((pscC D (onValue s.pow) sTie false 0 id s).1.ends.getD 1 noClaim) }
      (j + 1) pat h
      (by
        have := s1.congr (s' := { (pscC D (onValue s.pow) sTie false 0 id s).2 with
          pow := (pscC D (onValue s.pow) sTie false 0 id s).1.ends.getD 0 noClaim
          planes := Function.update (pscC D (onValue s.pow) sTie false 0 id s).2.planes (j + 1)
            ((pscC D (onValue s.pow) sTie false 0 id s).1.ends.getD 1 noClaim) }) rfl rfl rfl rfl
        simpa using this)
      (s4 0 (by decide)).2
      (by simp [hz])
      (fun i hi => by
        rcases Nat.lt_or_ge i (j + 1) with hlt | hge
        · show RC W home _ (Aff.slot ((x.2.2.push (y.sEnd + 1)).getD i 0))
            (Function.update s.planes (j + 1) _ i)
          rw [getD_push_lt _ _ _ (by omega), Function.update_of_ne (by omega)]
          exact (hpl i (by omega)).later s5
        · obtain rfl : i = j + 1 := by omega
          show RC W home _ (Aff.slot ((x.2.2.push (y.sEnd + 1)).getD (j + 1) 0))
            (Function.update s.planes (j + 1) _ (j + 1))
          rw [← hz, getD_push_eq, Function.update_self]
          exact (s4 1 (by decide)).2)
    refine ⟨r1, r2, ?_, fun i hi => r4 i ?_, r5, r6, s5.trans r7, ?_⟩
    · rw [r3, List.length_cons]; omega
    · rw [List.length_cons] at hi; omega
    · rw [List.length_cons, flat_succ]
      exact s6.trans r8

/-- The course's first stretch behind the draw of alpha. -/
def headTail (D : Dt) (s1 : Cs) : Cs :=
  let r := pscC D ⟨[], [], 0⟩ (sTie1 (D.fac s1.alpha)) false 0 id s1
  let s := cTie D (D.S.pl - 2) 0
    { r.2 with
      rest := r.1.ends.getD 0 noClaim
      pow := r.1.ends.getD 1 noClaim
      planes := Function.update r.2.planes 0 (r.1.ends.getD 2 noClaim) }
  { s with planes := Function.update s.planes (D.S.pl - 1) s.pow }

theorem cHead_eq (D : Dt) (f : List (Lk6.Flat.RV GE)) (own idx : ℕ) :
    cHead D f own idx = headTail D
      { (⟨f, own, idx, [], 0, noClaim, noClaim, noClaim, noClaim, fun _ => noClaim,
          fun _ => noClaim, fun _ => noClaim, []⟩ : Cs).next with
        alpha := (⟨f, own, idx, [], 0, noClaim, noClaim, noClaim, noClaim, fun _ => noClaim,
          fun _ => noClaim, fun _ => noClaim, []⟩ : Cs).draw } := rfl

/-- **The tie.** -/
theorem tie_sim {wn : ℕ} {a : E} {F G : Fork} {t u : Tape} {res : Array Aff × ℕ × Array ℕ} {s1 : Cs}
    {pat : List Bool} (h : tieG wn a F t = some (res, G, u)) (hw : 2 ≤ wn) (hpl : D.S.pl = wn)
    (hst : St W home D F t s1 (own (7 + 6 * (wn - 2)) ++ pat) [])
    (ha : readE a = D.fac s1.alpha) :
    St W home D G u (headTail D s1) pat res.1.toList ∧
      RC W home G (Aff.slot res.2.1) (headTail D s1).rest ∧ (headTail D s1).rest.point = [] ∧
      (∀ j < wn, RC W home G (Aff.slot (res.2.2.getD j 0)) ((headTail D s1).planes j)) ∧
      (headTail D s1).alpha = s1.alpha ∧ Later F G ∧
      Shp t u (pscShape [] (some (3, 3)) ++
        (List.range (wn - 2)).flatMap fun _ => pscShape [] (some (3, 2))) := by
  unfold tieG at h
  replace h := bind_some h
  obtain ⟨x, G1, u1, h1, h⟩ := h
  replace h := bind_some h
  obtain ⟨y, G2, u2, h2, h⟩ := h
  cases pure_some h
  have hst' : St W home D F t s1 ((if false = true then own (1 + 2 * ([] : List E).length + 3 + 3 -
      2)
      ++ [true, true] else own (1 + 2 * ([] : List E).length + 3 + 3)) ++
      (own (6 * (List.range (wn - 2)).length) ++ pat)) [] := by
    rw [own_add, List.append_assoc] at hst
    rw [List.length_range]
    exact hst
  obtain ⟨s1', p1, -, s4, s5, s6⟩ := step (c := ⟨[], [], 0⟩) (S := sTie1 (D.fac s1.alpha)) (place :=
      id)
    h1 hst' rfl ((Reads.const F zeroE).congr rfl readE_zero.symm) rfl rfl (by decide)
    (fun pt y => by
      show (y.map readE).getD 0 0 - D.fac s1.alpha * (y.map readE).getD 1 0 *
        (y.map readE).getD 1 0 * (y.map readE).getD 2 0 = _
      rw [readE_sub, readE_mul, readE_mul, readE_mul, read_getD, read_getD, read_getD, ha]
      ring)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := tieLoop (List.range (wn - 2)) _ y _ _ _ _
    { (pscC D ⟨[], [], 0⟩ (sTie1 (D.fac s1.alpha)) false 0 id s1).2 with
      rest := (pscC D ⟨[], [], 0⟩ (sTie1 (D.fac s1.alpha)) false 0 id s1).1.ends.getD 0 noClaim
      pow := (pscC D ⟨[], [], 0⟩ (sTie1 (D.fac s1.alpha)) false 0 id s1).1.ends.getD 1 noClaim
      planes := Function.update (pscC D ⟨[], [], 0⟩ (sTie1 (D.fac s1.alpha)) false 0 id s1).2.planes
        0 ((pscC D ⟨[], [], 0⟩ (sTie1 (D.fac s1.alpha)) false 0 id s1).1.ends.getD 2 noClaim) }
    0 pat h2 (s1'.congr rfl rfl rfl rfl) (s4 1 (by decide)).2 rfl
    (fun i hi => by
      obtain rfl : i = 0 := by omega
      show RC W home _ (Aff.slot (x.sEnd + 2)) (Function.update
        (pscC D ⟨[], [], 0⟩ (sTie1 (D.fac s1.alpha)) false 0 id s1).2.planes 0 _ 0)
      rw [Function.update_self]
      exact (s4 2 (by decide)).2)
  rw [List.length_range] at r1 r2 r3 r4 r5 r6 r8
  rw [← hpl] at r1 r2 r3 r4 r5 r6 r8 hw ⊢
  refine ⟨r1.congr rfl rfl rfl rfl, ?_,
    (congrArg (·.point) r5).trans ((s4 0 (by decide)).1.trans p1), fun j hj => ?_, r6,
    s5.trans r7, s6.trans r8⟩
  · show RC W home _ _ (cTie D (D.S.pl - 2) 0 _).rest
    rw [r5]
    exact (s4 0 (by decide)).2.later r7
  · show RC W home _ (Aff.slot ((y.2.2.push y.2.1).getD j 0))
      (Function.update (cTie D (D.S.pl - 2) 0 _).planes (D.S.pl - 1) (cTie D (D.S.pl - 2) 0 _).pow
          j)
    rcases Nat.lt_or_ge j (D.S.pl - 1) with hlt | hge
    · rw [getD_push_lt _ _ _ (by omega), Function.update_of_ne (by omega)]
      exact r4 j (by omega)
    · obtain rfl : j = D.S.pl - 1 := by omega
      have e : D.S.pl - 1 = y.2.2.size := by omega
      rw [Function.update_self]
      conv => enter [4, 1]; rw [e]
      rw [getD_push_eq]
      exact r2

/-- The parts' steps. -/
theorem parts_loop : ∀ (n : ℕ) (rows : Array Aff) (C : Aff) (F G : Fork) (t u : Tape)
    (res : Array Aff × List Aff) (s : Cs) (j : ℕ) (pat : List Bool),
    partsG n rows C F t = some (res, G, u) →
    St W home D F t s (own (5 * n) ++ pat) rows.toList → RC W home F C s.rest →
    s.rest.point = [] →
    St W home D G u (cPart D n j s) pat res.1.toList ∧ res.2.length = n + 1 ∧
      (∀ i < n, RC W home G (res.2.getD i {}) ((cPart D n j s).roots (j + i)) ∧
        ((cPart D n j s).roots (j + i)).point = []) ∧
      (RC W home G (res.2.getD n {}) (cPart D n j s).rest ∧ (cPart D n j s).rest.point = []) ∧
      (∀ i < j, (cPart D n j s).roots i = s.roots i) ∧
      (cPart D n j s).planes = s.planes ∧ (cPart D n j s).alpha = s.alpha ∧ Later F G ∧
      Shp t u ((List.range n).flatMap fun _ => pscShape [] (some (2, 2)))
  | 0, rows, C, F, G, t, u, res, s, j, pat, h, hst, hC, hP => by
    cases pure_some h
    exact ⟨hst, rfl, fun i hi => (by omega), ⟨hC, hP⟩, fun _ _ => rfl, rfl, rfl, Later.refl _,
      Shp.refl _⟩
  | n + 1, rows, C, F, G, t, u, res, s, j, pat, h, hst, hC, hP => by
    unfold partsG at h
    replace h := bind_some h
    obtain ⟨w, G1, u1, h1, h⟩ := h
    replace h := bind_some h
    obtain ⟨x, G2, u2, h2, h⟩ := h
    cases pure_some h
    have hst' : St W home D F t s ((if false = true then own (1 + 2 * ([] : List E).length + 2 + 2 -
        2)
        ++ [true, true] else own (1 + 2 * ([] : List E).length + 2 + 2)) ++
        (own (5 * n) ++ pat)) rows.toList := by
      rw [show 5 * (n + 1) = 5 + 5 * n by omega, own_add, List.append_assoc] at hst
      exact hst
    obtain ⟨s1, p1, -, s4, s5, s6⟩ := step (c := onValue s.rest) (S := sProd) (place := id) h1 hst'
        rfl
      hC rfl rfl (by decide) (fun pt y => by
        show (y.map readE).getD 0 0 * (y.map readE).getD 1 0 = _
        rw [readE_mul, read_getD, read_getD])
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := parts_loop n _ _ _ _ _ _ x
      { (pscC D (onValue s.rest) sProd false 0 id s).2 with
        roots := Function.update (pscC D (onValue s.rest) sProd false 0 id s).2.roots j
          ((pscC D (onValue s.rest) sProd false 0 id s).1.ends.getD 0 noClaim)
        rest := (pscC D (onValue s.rest) sProd false 0 id s).1.ends.getD 1 noClaim }
      (j + 1) pat h2
      (by
        have := s1.congr (s' := { (pscC D (onValue s.rest) sProd false 0 id s).2 with
          roots := Function.update (pscC D (onValue s.rest) sProd false 0 id s).2.roots j
            ((pscC D (onValue s.rest) sProd false 0 id s).1.ends.getD 0 noClaim)
          rest := (pscC D (onValue s.rest) sProd false 0 id s).1.ends.getD 1 noClaim })
          rfl rfl rfl rfl
        simpa using this)
      (s4 1 (by decide)).2 ((s4 1 (by decide)).1.trans p1)
    refine ⟨r1, by simp [r2], fun i hi => ?_, r4, fun i hi => ?_, r6, r7, s5.trans r8, ?_⟩
    · cases i with
      | zero =>
        have e : (cPart D (n + 1) j s).roots (j + 0) =
            (pscC D (onValue s.rest) sProd false 0 id s).1.ends.getD 0 noClaim :=
          (r5 j (by omega)).trans (Function.update_self ..)
        rw [e]
        exact ⟨(s4 0 (by decide)).2.later r8, (s4 0 (by decide)).1.trans p1⟩
      | succ i =>
        have := r3 i (by omega)
        rw [show j + 1 + i = j + (i + 1) by omega] at this
        exact this
    · exact (r5 i (by omega)).trans (Function.update_of_ne (by omega) _ _)
    · rw [flat_succ]
      exact s6.trans r9

/-- **The parts.** -/
theorem parts_sim {m : ℕ} {rows : Array Aff} {C : Aff} {F G : Fork} {t u : Tape}
    {res : Array Aff × List Aff} {s : Cs} {pat : List Bool} (hm : D.S.m = m) (h1 : 1 ≤ m)
    (h : partsG (m - 1) rows C F t = some (res, G, u))
    (hst : St W home D F t s (own (5 * (m - 1)) ++ pat) rows.toList) (hC : RC W home F C s.rest)
    (hP : s.rest.point = []) :
    St W home D G u (cParts D s) pat res.1.toList ∧ res.2.length = m ∧
      (∀ i < m, RC W home G (res.2.getD i {}) ((cParts D s).roots i) ∧
        ((cParts D s).roots i).point = []) ∧
      (cParts D s).planes = s.planes ∧ (cParts D s).alpha = s.alpha ∧ Later F G ∧
      Shp t u ((List.range (m - 1)).flatMap fun _ => pscShape [] (some (2, 2))) := by
  obtain ⟨r1, r2, r3, r4, -, r6, r7, r8, r9⟩ := parts_loop (m - 1) rows C F G t u res s 0 pat h hst
      hC hP
  subst hm
  refine ⟨r1.congr rfl rfl rfl rfl, by omega, fun i hi => ?_, r6, r7, r8, r9⟩
  show RC W home _ _ (Function.update (cPart D (D.S.m - 1) 0 s).roots (D.S.m - 1)
    (cPart D (D.S.m - 1) 0 s).rest i) ∧ (Function.update (cPart D (D.S.m - 1) 0 s).roots (D.S.m - 1)
    (cPart D (D.S.m - 1) 0 s).rest i).point = []
  rcases Nat.lt_or_ge i (D.S.m - 1) with hlt | hge
  · rw [Function.update_of_ne (by omega)]
    have := r3 i hlt
    rwa [Nat.zero_add] at this
  · obtain rfl : i = D.S.m - 1 := by omega
    rw [Function.update_self]
    exact r4

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.tie_sim
#print axioms VerifiableInference.Desc.K3.KeyLaw.parts_sim
