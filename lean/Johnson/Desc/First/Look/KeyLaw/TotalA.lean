-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/TotalA.lean: the stretches of the lookup's hearing RETURN, on a tape
of their shapes, from a ledger with their slots free ahead: the tie, the parts, a run of levels.

Main names:
  Go T F t pat L: the ledger has as many free slots ahead as the pattern pat has members, up to the
    slot T; the tape has the shapes L.
  go_whole: one masked sumcheck.
  tie_ok, parts_ok, levels_ok: the stretches; each says the sizes of what it returns and that the
    forms it returns name filled slots alone.

Limits. Nothing on what the values are.

-/
import Johnson.Desc.First.Look.KeyLaw.WholeOk
import Johnson.Desc.First.Look.KeyLaw.Mid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm)
open OnBytes.PscRun (took Later Sized Filled Ran)
open First.Prod (wholeStandIn Whole Carried turn level stepDown layBack)

/-- Free slots ahead for the pattern, up to the slot T; a tape of the shapes L. -/
structure Go (T : ℕ) (F : Fork) (t : Tape) (pat : List Bool) (L : List Shape) : Prop where
  fr : Fr F pat.length
  tot : F.next + pat.length = T
  sh : t.map shapeOf = L

theorem allShown_empty (F : Fork) : AllShown F {} := fun x hx => by simp at hx

theorem allShown_const (F : Fork) (c : E) : AllShown F (Aff.ofConst c) :=
  fun x hx => by simp [Aff.ofConst] at hx

theorem AllShown.scale {F : Fork} {a : Aff} (h : AllShown F a) (k : E) : AllShown F (Aff.scale a k)
    :=
  (allShown_empty F).addMul h k

theorem AllShown.add {F : Fork} {a b : Aff} (ha : AllShown F a) (hb : AllShown F b) :
    AllShown F (a + b) := ha.addMul hb oneE

variable {T : ℕ}

/-- One masked sumcheck. -/
theorem go_whole {C : Aff} {zs : List E} {dY n : ℕ} {endTerm : List E → E} {F : Fork} {t : Tape}
    {p1 pat : List Bool} {L : List Shape} (hp1 : p1.length = 1 + 2 * zs.length + dY + n)
    (h : Go T F t (p1 ++ pat) (pscShape (List.replicate zs.length 2) (some (dY, n)) ++ L))
    (hC : AllShown F C) (hdY : 1 ≤ dY) (hn : 1 ≤ n) :
    ∃ w G u, wholeStandIn C zs dY n endTerm F t = some (w, G, u) ∧ Go T G u pat L ∧ Later F G ∧
      (∀ i < n, AllShown G (Aff.slot (w.sEnd + i))) ∧
      (∀ j < F.next, (Filled G j ↔ Filled F j)) ∧ w.challenges.length = zs.length + 1 := by
  have hfr := h.fr
  have htot := h.tot
  rw [List.length_append, hp1] at hfr htot
  obtain ⟨w, G, u, e, a1, a2, a3, a4, a5, a6, a7⟩ := whole_ok (endTerm := endTerm) hfr hC hdY hn
      h.sh
  exact ⟨w, G, u, e, ⟨a2, by rw [a3]; omega, a1⟩, a4, a5, a6, a7⟩

/-- A round in which nothing is sent and one element is drawn. -/
theorem go_answer {r : RoundName} {F : Fork} {t : Tape} {pat : List Bool} {L : List Shape}
    (hr : r.name ≠ "") (h : Go T F t pat ([(r.name, 0, 1, 0)] ++ L)) :
    ∃ x u, Fl.answer r F t = some (x, F, u) ∧ Go T F u pat L := by
  obtain ⟨x, u, e, hu⟩ := answer_ok (F := F) hr h.sh
  exact ⟨x, u, e, ⟨h.fr, h.tot, hu⟩⟩

theorem go_point {r : RoundName} {n : ℕ} {F : Fork} {t : Tape} {pat : List Bool} {L : List Shape}
    (hr : r.name ≠ "") (h : Go T F t pat ([(r.name, 0, n, 0)] ++ L)) :
    ∃ x u, Fl.point r n F t = some (x, F, u) ∧ Go T F u pat L := by
  obtain ⟨x, u, e, hu⟩ := point_ok (F := F) hr h.sh
  exact ⟨x, u, e, ⟨h.fr, h.tot, hu⟩⟩

/-! ## The tie -/

theorem tieLoop_ok (l : List ℕ) : ∀ (x : Array Aff × ℕ × Array ℕ) (F : Fork) (t : Tape)
    (pat : List Bool) (L : List Shape),
    Go T F t (own (6 * l.length) ++ pat)
      (((List.range l.length).flatMap fun _ => pscShape [] (some (3, 2))) ++ L) →
    AllShown F (Aff.slot x.2.1) → (∀ j < x.2.2.size, AllShown F (Aff.slot (x.2.2.getD j 0))) →
    ∃ x' G u, (l.foldlM (m := Fl) (fun (s : Array Aff × ℕ × Array ℕ) _ => do
        let y ← wholeStandIn (Aff.slot s.2.1) [] 3 2 fun v =>
          mulE (mulE (v.getD 0 zeroE) (v.getD 0 zeroE)) (v.getD 1 zeroE)
        pure (s.1.push y.row, y.sEnd, s.2.2.push (y.sEnd + 1))) x) F t = some (x', G, u) ∧
      Go T G u pat L ∧ Later F G ∧ x'.1.size = x.1.size + l.length ∧
      AllShown G (Aff.slot x'.2.1) ∧ x'.2.2.size = x.2.2.size + l.length ∧
      (∀ j < x'.2.2.size, AllShown G (Aff.slot (x'.2.2.getD j 0))) := by
  induction l with
  | nil =>
    intro x F t pat L h h1 h2
    exact ⟨x, F, t, rfl, h, Later.refl _, rfl, h1, rfl, h2⟩
  | cons a l ih =>
    intro x F t pat L h h1 h2
    have h' : Go T F t (own 6 ++ (own (6 * l.length) ++ pat))
        (pscShape (List.replicate ([] : List E).length 2) (some (3, 2)) ++
          (((List.range l.length).flatMap fun _ => pscShape [] (some (3, 2))) ++ L)) := by
      have e1 : own (6 * (a :: l).length) ++ pat = own 6 ++ (own (6 * l.length) ++ pat) := by
        rw [List.length_cons, show 6 * (l.length + 1) = 6 + 6 * l.length by omega, own_add,
          List.append_assoc]
      rw [e1, List.length_cons, flat_succ, List.append_assoc] at h
      exact h
    obtain ⟨y, G1, u1, e, g1, g2, g3, -, -⟩ := go_whole (endTerm := fun v =>
      mulE (mulE (v.getD 0 zeroE) (v.getD 0 zeroE)) (v.getD 1 zeroE)) (own_length 6) h' h1
      (by decide) (by decide)
    obtain ⟨x', G, u, e', r1, r2, r3, r4, r5, r6⟩ := ih
      (x.1.push y.row, y.sEnd, x.2.2.push (y.sEnd + 1)) G1 u1 pat L g1 (g3 0 (by decide))
      (fun j hj => by
        rw [Array.size_push] at hj
        rcases Nat.lt_or_ge j x.2.2.size with hlt | hge
        · show AllShown G1 (Aff.slot ((x.2.2.push (y.sEnd + 1)).getD j 0))
          rw [getD_push_lt _ _ _ hlt]
          exact (h2 j hlt).later g2
        · obtain rfl : j = x.2.2.size := by omega
          show AllShown G1 (Aff.slot ((x.2.2.push (y.sEnd + 1)).getD x.2.2.size 0))
          rw [getD_push_eq]
          exact g3 1 (by decide))
    refine ⟨x', G, u, ?_, r1, g2.trans r2, ?_, r4, ?_, r6⟩
    · rw [List.foldlM_cons, bind_eq (bind_eq e)]
      exact e'
    · rw [r3, List.length_cons]
      show (x.1.push y.row).size + l.length = _
      rw [Array.size_push]; omega
    · rw [r5, List.length_cons]
      show (x.2.2.push (y.sEnd + 1)).size + l.length = _
      rw [Array.size_push]; omega

theorem tie_ok {wn : ℕ} {a : E} {F : Fork} {t : Tape} {pat : List Bool} {L : List Shape}
    (hw : 2 ≤ wn)
    (h : Go T F t (own (7 + 6 * (wn - 2)) ++ pat) ((pscShape [] (some (3, 3)) ++
      (List.range (wn - 2)).flatMap fun _ => pscShape [] (some (3, 2))) ++ L)) :
    ∃ res G u, tieG wn a F t = some (res, G, u) ∧ Go T G u pat L ∧ Later F G ∧
      res.1.size = wn - 1 ∧ AllShown G (Aff.slot res.2.1) ∧
      (∀ j < wn, AllShown G (Aff.slot (res.2.2.getD j 0))) := by
  have h' : Go T F t (own 7 ++ (own (6 * (List.range (wn - 2)).length) ++ pat))
      (pscShape (List.replicate ([] : List E).length 2) (some (3, 3)) ++
        (((List.range (List.range (wn - 2)).length).flatMap fun _ => pscShape [] (some (3, 2))) ++
          L)) := by
    rw [own_add, List.append_assoc, List.append_assoc] at h
    rw [List.length_range]
    exact h
  obtain ⟨x, G1, u1, e, g1, g2, g3, -, -⟩ := go_whole (endTerm := fun v =>
    subE (v.getD 0 zeroE) (mulE a (mulE (mulE (v.getD 1 zeroE) (v.getD 1 zeroE)) (v.getD 2 zeroE))))
    (own_length 7) h' (allShown_const F zeroE) (by decide) (by decide)
  obtain ⟨y, G, u, e', r1, r2, r3, r4, r5, r6⟩ := tieLoop_ok (List.range (wn - 2))
    (#[x.row], x.sEnd + 1, #[x.sEnd + 2]) G1 u1 pat L g1 (g3 1 (by decide))
    (fun j hj => by
      obtain rfl : j = 0 := by
        have : j < 1 := hj
        omega
      exact g3 2 (by decide))
  rw [List.length_range] at r3 r5
  have r5' : y.2.2.size = wn - 1 := by
    rw [r5]
    show 1 + (wn - 2) = _
    omega
  refine ⟨(y.1, x.sEnd, y.2.2.push y.2.1), G, u, ?_, r1, g2.trans r2, ?_, (g3 0 (by decide)).later
      r2,
    fun j hj => ?_⟩
  · unfold tieG
    dsimp only
    rw [bind_eq e, bind_eq e']
    rfl
  · rw [r3]
    show 1 + (wn - 2) = _
    omega
  · show AllShown G (Aff.slot ((y.2.2.push y.2.1).getD j 0))
    rcases Nat.lt_or_ge j y.2.2.size with hlt | hge
    · rw [getD_push_lt _ _ _ hlt]
      exact r6 j hlt
    · obtain rfl : j = y.2.2.size := by omega
      rw [getD_push_eq]
      exact r4

/-! ## The parts -/

theorem parts_ok : ∀ (n : ℕ) (rows : Array Aff) (C : Aff) (F : Fork) (t : Tape) (pat : List Bool)
    (L : List Shape),
    Go T F t (own (5 * n) ++ pat) (((List.range n).flatMap fun _ => pscShape [] (some (2, 2))) ++ L)
        →
    AllShown F C →
    ∃ res G u, partsG n rows C F t = some (res, G, u) ∧ Go T G u pat L ∧ Later F G ∧
      res.1.size = rows.size + n ∧ res.2.length = n + 1 ∧ (∀ c ∈ res.2, AllShown G c)
  | 0, rows, C, F, t, pat, L, h, hC =>
    ⟨(rows, [C]), F, t, rfl, h, Later.refl _, rfl, rfl, fun c hc => by
      obtain rfl : c = C := by simpa using hc
      exact hC⟩
  | n + 1, rows, C, F, t, pat, L, h, hC => by
    have h' : Go T F t (own 5 ++ (own (5 * n) ++ pat))
        (pscShape (List.replicate ([] : List E).length 2) (some (2, 2)) ++
          (((List.range n).flatMap fun _ => pscShape [] (some (2, 2))) ++ L)) := by
      rw [show 5 * (n + 1) = 5 + 5 * n by omega, own_add, List.append_assoc, flat_succ,
        List.append_assoc] at h
      exact h
    obtain ⟨w, G1, u1, e, g1, g2, g3, -, -⟩ := go_whole (endTerm := fun v =>
      mulE (v.getD 0 zeroE) (v.getD 1 zeroE)) (own_length 5) h' hC (by decide) (by decide)
    obtain ⟨x, G, u, e', r1, r2, r3, r4, r5⟩ := parts_ok n (rows.push w.row)
      (Aff.slot (w.sEnd + 1)) G1 u1 pat L g1 (g3 1 (by decide))
    refine ⟨(x.1, Aff.slot w.sEnd :: x.2), G, u, ?_, r1, g2.trans r2, ?_, by simp [r4],
      fun c hc => ?_⟩
    · unfold partsG
      rw [bind_eq e, bind_eq e']
      rfl
    · rw [r3, Array.size_push]; omega
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact (g3 0 (by decide)).later r2
      · exact r5 c hc

/-! ## A run of levels -/

theorem levelsPat_head (keys : Bool) (n N : ℕ) (hN : 2 ≤ N) :
    (if (keys && n == 0) = true then own (N - 2) ++ [true, true] else own N).length = N := by
  split
  · rw [List.length_append, own_length]
    show N - 2 + 2 = N
    omega
  · exact own_length N

theorem levels_ok (keys : Bool) (more : ℕ) (orders : ℕ → List ℕ) : ∀ (n l : ℕ) (cf : Carried)
    (F : Fork) (t : Tape) (pat : List Bool) (L : List Shape),
    Go T F t (levelsPat keys more n l ++ pat) (levelsShape more n l ++ L) → AllShown F cf.form →
    (∀ i, l ≤ i → i < l + n → (orders (more + i)).length = more + i) →
    cf.point.size = more + l →
    ∃ cf' G u, ((List.range' l n).foldlM (m := Fl)
        (fun s i => turn (orders (more + i)) s (more + i)) cf) F t = some (cf', G, u) ∧
      Go T G u pat L ∧ Later F G ∧ AllShown G cf'.form ∧ cf'.rows.size = cf.rows.size + n ∧
      cf'.point.size = more + l + n := by
  intro n
  induction n with
  | zero =>
    intro l cf F t pat L h hC _ hz
    exact ⟨cf, F, t, rfl, h, Later.refl _, hC, rfl, hz⟩
  | succ n ih =>
    intro l cf F t pat L h hC ho hz
    have hol := ho l (Nat.le_refl l) (by omega)
    have hzl : ((orders (more + l)).map fun b => cf.point.getD (more + l - 1 - b) zeroE).length =
        more + l := by rw [List.length_map, hol]
    have h' : Go T F t
        ((if (keys && n == 0) = true then own (1 + 2 * (more + l) + 2 + 2 - 2) ++ [true, true]
          else own (1 + 2 * (more + l) + 2 + 2)) ++ (levelsPat keys more n (l + 1) ++ pat))
        (pscShape (List.replicate ((orders (more + l)).map fun b =>
            cf.point.getD (more + l - 1 - b) zeroE).length 2) (some (2, 2)) ++
          ([(RoundName.line.name, 0, 1, 0)] ++ (levelsShape more n (l + 1) ++ L))) := by
      rw [hzl, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
      exact h
    obtain ⟨w, G1, u1, e, g1, g2, g3, -, -⟩ := go_whole (endTerm := fun v =>
      mulE (v.getD 0 zeroE) (v.getD 1 zeroE))
      (by rw [hzl]; exact levelsPat_head keys n _ (by omega)) h' hC (by decide) (by decide)
    obtain ⟨xi, u2, e2, g4⟩ := go_answer (by decide) g1
    obtain ⟨cf', G, u, e', r1, r2, r3, r4, r5⟩ := ih (l + 1)
      { rows := cf.rows.push w.row
        point := #[xi] ++ layBack (more + l) (orders (more + l)) (w.challenges.take (more + l))
        form := Aff.scale (Aff.slot w.sEnd) (subE oneE xi) + Aff.scale (Aff.slot (w.sEnd + 1)) xi }
      G1 u2 pat L g4 (((g3 0 (by decide)).scale _).add ((g3 1 (by decide)).scale _))
      (fun i h1 h2 => ho i (by omega) (by omega))
      (by
        show (#[xi] ++ layBack (more + l) (orders (more + l)) (w.challenges.take (more + l))).size =
            _
        rw [Array.size_append, layBack_size]
        show 1 + (more + l) = _
        omega)
    refine ⟨cf', G, u, ?_, r1, g2.trans r2, r3, ?_, by rw [r5]; omega⟩
    · rw [List.range'_succ, List.foldlM_cons]
      have et : turn (orders (more + l)) cf (more + l) F t = some (
          { rows := cf.rows.push w.row
            point := #[xi] ++
              layBack (more + l) (orders (more + l)) (w.challenges.take (more + l))
            form := Aff.scale (Aff.slot w.sEnd) (subE oneE xi) +
              Aff.scale (Aff.slot (w.sEnd + 1)) xi }, G1, u2) := by
        have el : level (more + l) cf.point (orders (more + l)) cf.form F t = some (
            { r := layBack (more + l) (orders (more + l)) (w.challenges.take (more + l))
              sL := w.sEnd, sR := w.sEnd + 1, xi := xi, row := w.row }, G1, u2) := by
          unfold level
          rw [bind_eq e, bind_eq e2]
          rfl
        unfold turn
        rw [bind_eq el]
        rfl
      rw [bind_eq et]
      exact e'
    · rw [r4]
      show (cf.rows.push w.row).size + n = _
      rw [Array.size_push]; omega

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.tie_ok
#print axioms VerifiableInference.Desc.K3.KeyLaw.parts_ok
#print axioms VerifiableInference.Desc.K3.KeyLaw.levels_ok
