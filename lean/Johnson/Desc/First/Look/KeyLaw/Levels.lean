-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Levels.lean: a run of levels of a product tree (First.Prod.run,
Johnson/Desc/First/Prod/Level.lean) against the course's levels (cLevels, Mid/Course.lean).

Main names:
  Frame s s': the two stands have the same claims in hand, alpha and zero point.
  answer_st, point_st: a round in which nothing is sent.
  rev_getD, layBack_loop, layBack_byVar: a point laid back by variable: the kind has the highest
    variable first, the course the lowest.
  levelsPat: the pattern of a run's hidden values. levelsShape: its rounds' shapes.
  levels_sim: THE RUN.

Limits. One world W of mask entries; where the flat functions return.

-/
import Johnson.Desc.First.Look.KeyLaw.Tie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm Reading World)
open OnBytes.PscRun (took Later Sized Filled Ran)
open First.Prod (wholeStandIn Whole Carried turn level stepDown layBack)
open Lk6.PortSim (noClaim sProd lineF byVarF)
open Lk6.Mid (Dt Cs RowF pscC heardF slots eqPairsF cLevels ordFirst ordDown)

/-- The same claims in hand, alpha and zero point. -/
structure Frame (s s' : Cs) : Prop where
  alpha : s'.alpha = s.alpha
  rest : s'.rest = s.rest
  pow : s'.pow = s.pow
  top : s'.top = s.top
  bit : s'.bit = s.bit
  planes : s'.planes = s.planes
  roots : s'.roots = s.roots
  leaves : s'.leaves = s.leaves
  zt : s'.zt = s.zt

theorem Frame.refl (s : Cs) : Frame s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.trans {a b c : Cs} (h : Frame a b) (h' : Frame b c) : Frame a c :=
  ⟨h'.alpha.trans h.alpha, h'.rest.trans h.rest, h'.pow.trans h.pow, h'.top.trans h.top,
    h'.bit.trans h.bit, h'.planes.trans h.planes, h'.roots.trans h.roots,
    h'.leaves.trans h.leaves, h'.zt.trans h.zt⟩

variable {W : PscF.World} {home : ℕ → Slot} {D : Dt}

/-- A round in which nothing is sent and one element is drawn. -/
theorem answer_st {r : RoundName} {F G : Fork} {t u : Tape} {x : E} {s : Cs} {pat : List Bool}
    {rows : List Aff} (h : Fl.answer r F t = some (x, G, u)) (hst : St W home D F t s pat rows) :
    G = F ∧ St W home D F u s.next pat rows ∧ s.draw = readE x ∧ Shp t u [(r.name, 0, 1, 0)] := by
  obtain ⟨w, rfl, rfl⟩ := answer_fl h
  have hr : s.rounds = ([], [readE x]) :: flatK (u.map key) := hst.base.rounds
  refine ⟨rfl, ⟨⟨hst.base.sized, ?_⟩, hst.al, hst.rows⟩, ?_, ⟨[kr r 0 [] [x]], rfl, rfl⟩⟩
  · show s.rounds.tail = _
    rw [hr]; rfl
  · show (s.rounds.headD ([], [])).2.headD 0 = _
    rw [hr]; rfl

/-- A round in which nothing is sent and n elements are drawn. -/
theorem point_st {r : RoundName} {n : ℕ} {F G : Fork} {t u : Tape} {x : Array E} {s : Cs}
    {pat : List Bool} {rows : List Aff} (h : Fl.point r n F t = some (x, G, u))
    (hst : St W home D F t s pat rows) :
    G = F ∧ St W home D F u s.next pat rows ∧ s.draws = x.toList.map readE ∧ x.size = n ∧
      Shp t u [(r.name, 0, n, 0)] := by
  obtain ⟨w, rfl, hn, rfl⟩ := point_fl h
  have hr : s.rounds = ([], x.toList.map readE) :: flatK (u.map key) := hst.base.rounds
  refine ⟨rfl, ⟨⟨hst.base.sized, ?_⟩, hst.al, hst.rows⟩, ?_, hn, ⟨[kr r 0 [] x.toList], rfl, ?_⟩⟩
  · show s.rounds.tail = _
    rw [hr]; rfl
  · show (s.rounds.headD ([], [])).2 = _
    rw [hr]; rfl
  · show [(r.name, 0, x.toList.length, 0)] = _
    rw [Array.length_toList, hn]

/-! ## Points -/

theorem rev_getD {α : Type} (l : List α) (b : ℕ) (d : α) (h : b < l.length) :
    l.reverse.getD b d = l.getD (l.length - 1 - b) d := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by omega),
    List.getElem_reverse]

/-- What the loop of layBack leaves at the place of variable t. -/
theorem layBack_loop (m t : ℕ) (ht : t < m) : ∀ (l : List (ℕ × E)) (r : Array E), r.size = m →
    (l.map (·.1)).Nodup → (∀ x ∈ l, x.1 < m) →
    (l.foldl (fun (r : Array E) x => r.set! (m - 1 - x.1) x.2) r).getD (m - 1 - t) zeroE =
      (l.lookup t).getD (r.getD (m - 1 - t) zeroE)
  | [], r, _, _, _ => rfl
  | (b, x) :: l, r, hr, hn, hb => by
    rw [List.foldl_cons, layBack_loop m t ht l _ (by simpa using hr) (List.nodup_cons.1 hn).2
      fun y hy => hb y (List.mem_cons_of_mem _ hy), List.lookup_cons]
    have hbm : b < m := hb (b, x) List.mem_cons_self
    by_cases e : t = b
    · subst e
      have hnone : l.lookup t = none := by
        rw [List.lookup_eq_none_iff]
        intro p hp
        rw [bne_iff_ne]
        intro he
        exact (List.nodup_cons.1 hn).1 (List.mem_map.2 ⟨p, hp, he.symm⟩)
      rw [hnone, beq_self_eq_true]
      show (r.set! (m - 1 - t) x).getD (m - 1 - t) zeroE = x
      exact PscRun.getD_set_self r _ x zeroE (by omega)
    · have : (t == b) = false := by simpa using e
      rw [this]
      show (l.lookup t).getD ((r.set! (m - 1 - b) x).getD (m - 1 - t) zeroE) = _
      rw [PscRun.getD_set_other r _ _ x zeroE (by omega)]

theorem layBack_size (m : ℕ) (order : List ℕ) (cs : List E) : (layBack m order cs).size = m := by
  unfold layBack
  generalize order.zip cs = l
  have : ∀ (l : List (ℕ × E)) (r : Array E), r.size = m →
      (l.foldl (fun (r : Array E) x => r.set! (m - 1 - x.1) x.2) r).size = m := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons x l ih => exact fun r h => ih _ (by simpa using h)
  exact this l _ (by simp)

theorem orderOk_spec {m : ℕ} {order : List ℕ} (h : First.Prod.orderOk m order = true) :
    order.length = m ∧ (∀ b ∈ order, b < m) ∧ order.Nodup := by
  unfold First.Prod.orderOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, List.nodup_iff_count_le_one.2 fun a => ?_⟩
  by_cases ha : a ∈ order
  · exact le_of_eq (h3 a (h2 a ha))
  · rw [List.count_eq_zero_of_not_mem ha]; omega

/-- **A point laid back**: the kind's array, turned and read, is the course's list by variable. -/
theorem layBack_byVar {m : ℕ} {order : List ℕ} (h : First.Prod.orderOk m order = true) (cs : List E)
    (hc : cs.length = m) :
    (layBack m order cs).toList.reverse.map readE = byVarF (cs.map readE) order := by
  obtain ⟨h1, h2, h3⟩ := orderOk_spec h
  have hs := layBack_size m order cs
  apply List.ext_getElem
  · simp [byVarF, hs, hc]
  · intro t ht1 ht2
    have ht : t < m := by simpa [hs] using ht1
    have e1 : ((layBack m order cs).toList.reverse.map readE)[t] =
        readE ((layBack m order cs).getD (m - 1 - t) zeroE) := by
      rw [List.getElem_map, ← List.getD_eq_getElem _ zeroE, rev_getD _ _ _ (by simpa [hs] using ht),
        Array.length_toList, hs]
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    rw [e1]
    unfold layBack byVarF
    rw [layBack_loop m t ht _ _ (by simp) (by
        rw [List.map_fst_zip (by omega)]; exact h3)
      (fun x hx => h2 _ (List.of_mem_zip hx).1)]
    rw [List.getElem_map, List.getElem_range, zip_read_right, Lk6.PortSim.lookup_read, read_optD]
    congr 2
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl


/-! ## The run -/

theorem frame_pscC (D : Dt) (c : PscF.Claim) (S : PscF.Summand) (keys : Bool) (kept : ℕ)
    (place : List GE → List GE) (s : Cs) : Frame s (pscC D c S keys kept place s).2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem frame_next (s : Cs) : Frame s s.next := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The pattern of the hidden values of n levels from level l on. -/
def levelsPat (keys : Bool) (more : ℕ) : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, l =>
    (if (keys && n == 0) = true then own (1 + 2 * (more + l) + 2 + 2 - 2) ++ [true, true]
      else own (1 + 2 * (more + l) + 2 + 2)) ++ levelsPat keys more n (l + 1)

/-- The shapes of their rounds. -/
def levelsShape (more : ℕ) : ℕ → ℕ → List Shape
  | 0, _ => []
  | n + 1, l =>
    (pscShape (List.replicate (more + l) 2) (some (2, 2)) ++ [(RoundName.line.name, 0, 1, 0)]) ++
      levelsShape more n (l + 1)

/-- The kind's orders are the course's, and each is a list of its level's variables, each once. -/
def OrdIs (D : Dt) (keys : Bool) (more : ℕ) (orders : ℕ → List ℕ) : ℕ → ℕ → Prop
  | 0, _ => True
  | n + 1, l =>
    (if (keys && n == 0) = true then ordFirst D.S.order (more + l) else ordDown (more + l)) =
        orders (more + l) ∧
      First.Prod.orderOk (more + l) (orders (more + l)) = true ∧ OrdIs D keys more orders n (l + 1)

theorem cLevels_succ (D : Dt) (keys : Bool) (more n l : ℕ) (c : PscF.PointClaim) (s : Cs) :
    cLevels D keys more (n + 1) l c s =
      cLevels D keys more n (l + 1)
        (lineF (pscC D ⟨(if (keys && n == 0) = true then ordFirst D.S.order (more + l)
              else ordDown (more + l)).map fun t => PscF.Weight.equality (c.point.getD t 0) 3,
            c.masks, c.value⟩ sProd (keys && n == 0) 0
            (byVarF · (if (keys && n == 0) = true then ordFirst D.S.order (more + l)
              else ordDown (more + l))) s).2.draw
          ((pscC D ⟨(if (keys && n == 0) = true then ordFirst D.S.order (more + l)
              else ordDown (more + l)).map fun t => PscF.Weight.equality (c.point.getD t 0) 3,
            c.masks, c.value⟩ sProd (keys && n == 0) 0
            (byVarF · (if (keys && n == 0) = true then ordFirst D.S.order (more + l)
              else ordDown (more + l))) s).1.ends.getD 0 noClaim)
          ((pscC D ⟨(if (keys && n == 0) = true then ordFirst D.S.order (more + l)
              else ordDown (more + l)).map fun t => PscF.Weight.equality (c.point.getD t 0) 3,
            c.masks, c.value⟩ sProd (keys && n == 0) 0
            (byVarF · (if (keys && n == 0) = true then ordFirst D.S.order (more + l)
              else ordDown (more + l))) s).1.ends.getD 1 noClaim))
        (pscC D ⟨(if (keys && n == 0) = true then ordFirst D.S.order (more + l)
              else ordDown (more + l)).map fun t => PscF.Weight.equality (c.point.getD t 0) 3,
            c.masks, c.value⟩ sProd (keys && n == 0) 0
            (byVarF · (if (keys && n == 0) = true then ordFirst D.S.order (more + l)
              else ordDown (more + l))) s).2.next := rfl

theorem arr_getD (a : Array E) (i : ℕ) : a.toList.getD i zeroE = a.getD i zeroE := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- **A run of levels.** -/
theorem levels_sim (keys : Bool) (more : ℕ) (orders : ℕ → List ℕ) : ∀ (n l : ℕ)
    (cf cf' : Carried) (F G : Fork) (t u : Tape) (c : PscF.PointClaim) (s : Cs) (pat : List Bool),
    ((List.range' l n).foldlM (m := Fl) (fun s i => turn (orders (more + i)) s (more + i)) cf) F t =
      some (cf', G, u) →
    OrdIs D keys more orders n l →
    St W home D F t s (levelsPat keys more n l ++ pat) cf.rows.toList →
    RC W home F cf.form c → c.point = cf.point.toList.reverse.map readE →
    cf.point.size = more + l →
    St W home D G u (cLevels D keys more n l c s).2 pat cf'.rows.toList ∧
      RC W home G cf'.form (cLevels D keys more n l c s).1 ∧
      (cLevels D keys more n l c s).1.point = cf'.point.toList.reverse.map readE ∧
      cf'.point.size = more + l + n ∧ Frame s (cLevels D keys more n l c s).2 ∧ Later F G ∧
      Shp t u (levelsShape more n l) := by
  intro n
  induction n with
  | zero =>
    intro l cf cf' F G t u c s pat h _ hst hC hp hz
    cases pure_some h
    exact ⟨hst, hC, hp, hz, Frame.refl _, Later.refl _, Shp.refl _⟩
  | succ n ih =>
    intro l cf cf' F G t u c s pat h hord hst hC hp hz
    obtain ⟨ho, hok, hrest⟩ := hord
    obtain ⟨ol, ob, -⟩ := orderOk_spec hok
    rw [List.range'_succ, List.foldlM_cons] at h
    replace h := bind_some h
    obtain ⟨cf1, G1, u1, h1, h⟩ := h
    unfold turn at h1
    replace h1 := bind_some h1
    obtain ⟨o, G2, u2, h2, h1⟩ := h1
    cases pure_some h1
    unfold level at h2
    replace h2 := bind_some h2
    obtain ⟨w, G3, u3, h3, h2⟩ := h2
    replace h2 := bind_some h2
    obtain ⟨xi, G4, u4, h4, h2⟩ := h2
    cases pure_some h2
    rw [cLevels_succ, ho]
    have hzl : ((orders (more + l)).map fun b => cf.point.getD (more + l - 1 - b) zeroE).length =
        more + l := by rw [List.length_map, ol]
    have hst' : St W home D F t s
        ((if (keys && n == 0) = true then own (1 + 2 * ((orders (more + l)).map fun b =>
            cf.point.getD (more + l - 1 - b) zeroE).length + 2 + 2 - 2) ++ [true, true]
          else own (1 + 2 * ((orders (more + l)).map fun b =>
            cf.point.getD (more + l - 1 - b) zeroE).length + 2 + 2)) ++
          (levelsPat keys more n (l + 1) ++ pat)) cf.rows.toList := by
      rw [hzl, ← List.append_assoc]
      exact hst
    obtain ⟨s1, p1, p2, s4, s5, s6⟩ := step
      (c := ⟨(orders (more + l)).map fun t => PscF.Weight.equality (c.point.getD t 0) 3,
        c.masks, c.value⟩) (S := sProd) (place := (byVarF · (orders (more + l)))) h3 hst'
      (by
        show (orders (more + l)).map (fun t => PscF.Weight.equality (c.point.getD t 0) 3) = _
        rw [List.map_map]
        refine List.map_congr_left fun b hb => ?_
        show PscF.Weight.equality (c.point.getD b 0) 3 =
          PscF.Weight.equality (readE (cf.point.getD (more + l - 1 - b) zeroE)) 3
        rw [hp, read_getD, rev_getD _ _ _ (by rw [Array.length_toList, hz]; exact ob b hb),
          Array.length_toList, hz, arr_getD])
      hC rfl rfl (by decide) (fun pt y => by
        show (y.map readE).getD 0 0 * (y.map readE).getD 1 0 = _
        rw [readE_mul, read_getD, read_getD])
    have fr := frame_pscC D ⟨(orders (more + l)).map fun t =>
      PscF.Weight.equality (c.point.getD t 0) 3, c.masks, c.value⟩ sProd (keys && n == 0) 0
      (byVarF · (orders (more + l))) s
    rw [hzl] at p1 p2 s6
    generalize pscC D ⟨(orders (more + l)).map fun t =>
      PscF.Weight.equality (c.point.getD t 0) 3, c.masks, c.value⟩ sProd (keys && n == 0) 0
      (byVarF · (orders (more + l))) s = r at s1 p1 s4 fr ⊢
    obtain ⟨rfl, a1, a2, a3⟩ := answer_st h4 s1
    obtain ⟨e0p, e0⟩ := s4 0 (by decide)
    obtain ⟨e1p, e1⟩ := s4 1 (by decide)
    obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := ih (l + 1) _ cf' _ G _ u
      (lineF r.2.draw (r.1.ends.getD 0 noClaim) (r.1.ends.getD 1 noClaim)) r.2.next pat h hrest
      (by simpa using a1)
      (by
        have := (Reads.scale e0 (subE oneE xi)).add (Reads.scale e1 xi)
        rw [readE_sub, readE_one, ← a2] at this
        exact this)
      (by
        show (r.1.ends.getD 0 noClaim).point ++ [r.2.draw] = _
        rw [e0p, p1, a2, ← layBack_byVar hok _ (by
          rw [List.length_take, p2]; omega)]
        simp [stepDown])
      (by
        show (#[xi] ++ layBack (more + l) (orders (more + l)) (w.challenges.take (more + l))).size =
            _
        rw [Array.size_append, layBack_size]
        show 1 + (more + l) = _
        omega)
    refine ⟨r1, r2, r3, ?_, (fr.trans (frame_next _)).trans r5, s5.trans r6, ?_⟩
    · rw [r4]; omega
    · exact (s6.trans a3).trans r7

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.levels_sim
#print axioms VerifiableInference.Desc.K3.KeyLaw.layBack_byVar
