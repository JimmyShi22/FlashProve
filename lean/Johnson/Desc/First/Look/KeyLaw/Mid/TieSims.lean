-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/TieSims.lean: along the lookup's head (the first draw and the
tie) the course over the field of Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean (a text of the
program's lookup written anew over the field; that the program's run, read in the field, is this
course is shown in files that are not in this library) goes with the plain function of the flat
rounds of Cb/Pv/KeyLookup/TieRun.lean: the first of the eight conditions `Sims` of
Johnson/Desc/First/Look/KeyLaw/Mid/Seams.lean, at the relation `Sim` of
Johnson/Desc/First/Look/KeyLaw/Mid/Relation.lean.

The course is made of `PscF.outOf`, a text over the field of the program's sumcheck. One step each
is OnBytes/Tie/Pv/KeyLookup/TieSim.lean; this file joins the steps.

Main names:
  `Places A sl L D own`: where the tie's record of places `L` stands among the mask entries that the
  course takes from number own on: step 0 takes seven (four that bear the first polynomial's
  coefficients, the constant's first; then those of the three ends), each later step six.
  `fits3`: three rounds that fit a step's formats are what was heard, written out.
  `stepC`, `cTie_snoc`: the course's later steps, taken from the end.
  `first`, `first_at`, `stepC_at`: the course's first step and a later step at rounds written out.
  `Rel`: the relation between the course's stand and the flat state after the steps 0, .., n.
  `tie_goes`: the relation holds after the steps 0, .., n, on all rounds that fit.
  `head_sim`: the condition `Sims.head`. `head_field`: the same, in that condition's very words at
  `A.runD P` (Cb/Pv/KeyLookup/LamRun.lean).
Limits: the conditions of `head_sim` are: the course's number of planes is the record's; 2 ≤ pl; the
course's public factor is the record's at the caller's state; `Places`. Nothing on the program's
blocks on machine words, nothing on soundness.

-/
import OnBytes.Tie.Pv.KeyLookup.TieSim
import Johnson.Desc.First.Look.KeyLaw.Mid.Relation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid.TieSim
open Lk6.PortSim Lk6.TieSim

open OnBytes OnBytes.Slice Lk6.PortSim Flat Cb Cb.LdLkp

/-! ### lists of a given length -/

theorem len0 {α : Type} : ∀ l : List α, l.length = 0 → l = []
  | [], _ => rfl
  | _ :: _, h => absurd h (by simp)

theorem len1 {α : Type} : ∀ l : List α, l.length = 1 → ∃ a, l = [a]
  | [], h => absurd h (by simp)
  | [a], _ => ⟨a, rfl⟩
  | _ :: _ :: _, h => absurd h (by simp)

theorem len2 {α : Type} : ∀ l : List α, l.length = 2 → ∃ a b, l = [a, b]
  | [], h => absurd h (by simp)
  | [_], h => absurd h (by simp)
  | [a, b], _ => ⟨a, b, rfl⟩
  | _ :: _ :: _ :: _, h => absurd h (by simp)

theorem len3 {α : Type} : ∀ l : List α, l.length = 3 → ∃ a b c, l = [a, b, c]
  | [], h => absurd h (by simp)
  | [_], h => absurd h (by simp)
  | [_, _], h => absurd h (by simp)
  | [a, b, c], _ => ⟨a, b, c, rfl⟩
  | _ :: _ :: _ :: _ :: _, h => absurd h (by simp)

/-- Three rounds that fit a step's formats are what was heard, written out. -/
theorem fits3 (k : ℕ) (g : List (RV GE))
    (h : fitsAll [⟨1, 1, false⟩, ⟨3, 1, true⟩, ⟨k, 0, false⟩] g = true) :
    ∃ mu eps q1 q2 q3 be vals, vals.length = k ∧
      g = flatY ⟨mu, eps, [([q1, q2, q3], be)], vals⟩ := by
  rcases g with _ | ⟨r0, _ | ⟨r1, _ | ⟨r2, _ | ⟨r3, t⟩⟩⟩⟩
  · exact absurd h (by simp [fitsAll])
  · exact absurd h (by simp [fitsAll])
  · exact absurd h (by simp [fitsAll])
  · have h' : Fm.fits ⟨1, 1, false⟩ r0 = true ∧ Fm.fits ⟨3, 1, true⟩ r1 = true ∧
        Fm.fits ⟨k, 0, false⟩ r2 = true := by simpa [fitsAll, and_assoc] using h
    obtain ⟨a0, a1, a2⟩ := h'
    obtain ⟨b0, c0, _⟩ := (Fm.fits_iff _ _).1 a0
    obtain ⟨b1, c1, _⟩ := (Fm.fits_iff _ _).1 a1
    obtain ⟨b2, c2, _⟩ := (Fm.fits_iff _ _).1 a2
    obtain ⟨x0, y0⟩ := r0
    obtain ⟨x1, y1⟩ := r1
    obtain ⟨x2, y2⟩ := r2
    obtain ⟨mu, rfl⟩ := len1 x0 b0
    obtain ⟨eps, rfl⟩ := len1 y0 c0
    obtain ⟨q1, q2, q3, rfl⟩ := len3 x1 b1
    obtain ⟨be, rfl⟩ := len1 y1 c1
    obtain rfl := len0 y2 c2
    exact ⟨mu, eps, q1, q2, q3, be, x2, b2, rfl⟩
  · exact absurd h (by simp [fitsAll])

/-! ### the course's steps -/

/-- A later step of the course: step j hands on the next power and plane j + 1's root. -/
def stepC (D : Dt) (j : ℕ) (s : Cs) : Cs :=
  { (pscC D (onValue s.pow) sTie false 0 id s).2 with
    pow := (pscC D (onValue s.pow) sTie false 0 id s).1.ends.getD 0 noClaim
    planes := Function.update (pscC D (onValue s.pow) sTie false 0 id s).2.planes (j + 1)
      ((pscC D (onValue s.pow) sTie false 0 id s).1.ends.getD 1 noClaim) }

theorem cTie_cons (D : Dt) (n j : ℕ) (s : Cs) :
    cTie D (n + 1) j s = cTie D n (j + 1) (stepC D j s) := rfl

/-- The later steps, taken from the end. -/
theorem cTie_snoc (D : Dt) : ∀ (n j : ℕ) (s : Cs),
    cTie D (n + 1) j s = stepC D (j + n) (cTie D n j s)
  | 0, _, _ => rfl
  | n + 1, j, s => by
    rw [cTie_cons D (n + 1) j s, cTie_snoc D n (j + 1) (stepC D j s), cTie_cons D n j s]
    have e : j + 1 + n = j + (n + 1) := by omega
    rw [e]

/-- A later step at rounds written out. -/
theorem stepC_at (D : Dt) (j : ℕ) (s : Cs) (mu eps q1 q2 q3 be v0 v1 : GE)
    (rest : List (RV GE))
    (hr : s.rounds = flatY ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1]⟩ ++ rest) :
    stepC D j s =
      { s with
        rounds := rest
        own := s.own + 6
        rows := s.rows ++ [⟨(PscF.outOf (onValue s.pow) sTie
            [D.ms (s.own + 0), D.ms (s.own + 1), D.ms (s.own + 2), D.ms (s.own + 3),
              D.ms (s.own + 4), D.ms (s.own + 5)]
            ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1]⟩).rowMasks, [],
          (PscF.outOf (onValue s.pow) sTie
            [D.ms (s.own + 0), D.ms (s.own + 1), D.ms (s.own + 2), D.ms (s.own + 3),
              D.ms (s.own + 4), D.ms (s.own + 5)]
            ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1]⟩).rowTarget⟩]
        pow := ⟨[], [(D.ms (s.own + 4), be)], v0⟩
        planes := Function.update s.planes (j + 1) ⟨[], [(D.ms (s.own + 5), be)], v1⟩ } := by
  obtain ⟨rounds, own, idx, rows, alpha, rs, pow, top, bit, planes, roots, leaves, zt⟩ := s
  obtain rfl : rounds = _ := hr
  rfl

/-- The course's stand behind the first step of the tie; g: the rounds behind the first draw. -/
def first (D : Dt) (al : GE) (own idx : ℕ) (g : List (RV GE)) : Cs :=
  { (pscC D ⟨[], [], 0⟩ (sTie1 (D.fac al)) false 0 id
      ⟨g, own, idx, [], al, noClaim, noClaim, noClaim, noClaim, fun _ => noClaim,
        fun _ => noClaim, fun _ => noClaim, []⟩).2 with
    rest := (pscC D ⟨[], [], 0⟩ (sTie1 (D.fac al)) false 0 id
      ⟨g, own, idx, [], al, noClaim, noClaim, noClaim, noClaim, fun _ => noClaim,
        fun _ => noClaim, fun _ => noClaim, []⟩).1.ends.getD 0 noClaim
    pow := (pscC D ⟨[], [], 0⟩ (sTie1 (D.fac al)) false 0 id
      ⟨g, own, idx, [], al, noClaim, noClaim, noClaim, noClaim, fun _ => noClaim,
        fun _ => noClaim, fun _ => noClaim, []⟩).1.ends.getD 1 noClaim
    planes := Function.update (fun _ => noClaim) 0
      ((pscC D ⟨[], [], 0⟩ (sTie1 (D.fac al)) false 0 id
        ⟨g, own, idx, [], al, noClaim, noClaim, noClaim, noClaim, fun _ => noClaim,
          fun _ => noClaim, fun _ => noClaim, []⟩).1.ends.getD 2 noClaim) }

/-- The head's course: the draw, the first step, the later steps, the last plane. -/
theorem cHead_eq (D : Dt) (r : RV GE) (g : List (RV GE)) (own idx : ℕ) :
    cHead D (r :: g) own idx =
      { cTie D (D.S.pl - 2) 0 (first D (r.2.headD 0) own idx g) with
        planes := Function.update (cTie D (D.S.pl - 2) 0 (first D (r.2.headD 0) own idx g)).planes
          (D.S.pl - 1) (cTie D (D.S.pl - 2) 0 (first D (r.2.headD 0) own idx g)).pow } := rfl

/-- The first step at rounds written out. -/
theorem first_at (D : Dt) (al : GE) (own idx : ℕ) (mu eps q1 q2 q3 be v0 v1 v2 : GE)
    (rest : List (RV GE)) :
    first D al own idx (flatY ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1, v2]⟩ ++ rest) =
      ⟨rest, own + 7, idx, [⟨(PscF.outOf (onValue noClaim) (sTie1 (D.fac al))
            [D.ms (own + 0), D.ms (own + 1), D.ms (own + 2), D.ms (own + 3), D.ms (own + 4),
              D.ms (own + 5), D.ms (own + 6)]
            ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1, v2]⟩).rowMasks, [],
          (PscF.outOf (onValue noClaim) (sTie1 (D.fac al))
            [D.ms (own + 0), D.ms (own + 1), D.ms (own + 2), D.ms (own + 3), D.ms (own + 4),
              D.ms (own + 5), D.ms (own + 6)]
            ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1, v2]⟩).rowTarget⟩], al,
        ⟨[], [(D.ms (own + 4), be)], v0⟩, ⟨[], [(D.ms (own + 5), be)], v1⟩, noClaim, noClaim,
        Function.update (fun _ => noClaim) 0 ⟨[], [(D.ms (own + 6), be)], v2⟩,
        fun _ => noClaim, fun _ => noClaim, []⟩ := rfl

/-! ### the relation along the tie -/

section
variable (A : Dat GE) (sl : Slot → A.J) (L : TiePl GE A.J) (D : Dt) (own : ℕ)

/-- Where the tie's record of places stands among the mask entries that the course takes. -/
structure Places : Prop where
  w00 : L.wAt 0 (Sum.inr () : Fin 3 ⊕ Unit) = sl (D.ms (own + 0))
  w01 : L.wAt 0 (Sum.inl 0 : Fin 3 ⊕ Unit) = sl (D.ms (own + 1))
  w02 : L.wAt 0 (Sum.inl 1 : Fin 3 ⊕ Unit) = sl (D.ms (own + 2))
  w03 : L.wAt 0 (Sum.inl 2 : Fin 3 ⊕ Unit) = sl (D.ms (own + 3))
  cZ : L.cZ = sl (D.ms (own + 4))
  c0f : L.cAt 0 false = sl (D.ms (own + 5))
  c0t : L.cAt 0 true = sl (D.ms (own + 6))
  w0 : ∀ l, L.wAt (l + 1) (Sum.inr () : Fin 3 ⊕ Unit) = sl (D.ms (own + (7 + 6 * l) + 0))
  w1 : ∀ l, L.wAt (l + 1) (Sum.inl 0 : Fin 3 ⊕ Unit) = sl (D.ms (own + (7 + 6 * l) + 1))
  w2 : ∀ l, L.wAt (l + 1) (Sum.inl 1 : Fin 3 ⊕ Unit) = sl (D.ms (own + (7 + 6 * l) + 2))
  w3 : ∀ l, L.wAt (l + 1) (Sum.inl 2 : Fin 3 ⊕ Unit) = sl (D.ms (own + (7 + 6 * l) + 3))
  cf : ∀ l, L.cAt (l + 1) false = sl (D.ms (own + (7 + 6 * l) + 4))
  ct : ∀ l, L.cAt (l + 1) true = sl (D.ms (own + (7 + 6 * l) + 5))

/-- The course's stand and the flat state after the steps 0, .., n. -/
structure Rel (al : GE) (idx n : ℕ) (s : Cs) (a : TieR.TAcc GE A.J) : Prop where
  mf : a.mf = rdMF sl s.pow.masks
  tg : a.tg = s.pow.value
  all : a.all = rdS A sl s.rest
  planes : ∀ j ≤ n, a.planes j = rdS A sl (s.planes j)
  rows : a.rows = s.rows.map (rdRow A sl)
  own : s.own = own + (7 + 6 * n)
  idx : s.idx = idx
  al : s.alpha = al

/-- A row that names no kept map, read. -/
theorem rdRow_nil (m : PscF.MaskForm) (t : GE) : rdRow A sl ⟨m, [], t⟩ = ⟨rdMF sl m, t⟩ := by
  unfold rdRow
  congr 1
  funext j
  show rdMF sl m j + 0 = rdMF sl m j
  rw [add_zero]

variable {A sl L D own}

/-- A later step keeps the relation. -/
theorem step_goes (hP : Places A sl L D own) (al : GE) (idx n : ℕ) (s : Cs)
    (x : TieR.TAcc GE A.J) (hR : Rel A sl own al idx n s x)
    (hf : fitsAll TieR.fmN (s.rounds.take TieR.fmN.length) = true) :
    Rel A sl own al idx (n + 1) (stepC D n s)
        (TieR.stepN (L.wAt (n + 1)) (L.cAt (n + 1) false) (L.cAt (n + 1) true) (n + 1) x
          (s.rounds.take TieR.fmN.length)) ∧
      (stepC D n s).rounds = s.rounds.drop TieR.fmN.length := by
  obtain ⟨mu, eps, q1, q2, q3, be, vals, hv, hg⟩ := fits3 2 _ hf
  obtain ⟨v0, v1, rfl⟩ := len2 vals hv
  have hr : s.rounds = flatY ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1]⟩ ++
      s.rounds.drop TieR.fmN.length := by
    rw [← hg]
    exact (List.take_append_drop _ _).symm
  have hs := tieN_step sl s.pow (L.wAt (n + 1)) (D.ms (s.own + 0)) (D.ms (s.own + 1))
    (D.ms (s.own + 2)) (D.ms (s.own + 3)) (D.ms (s.own + 4)) (D.ms (s.own + 5))
    (by rw [hR.own]; exact hP.w0 n) (by rw [hR.own]; exact hP.w1 n)
    (by rw [hR.own]; exact hP.w2 n) (by rw [hR.own]; exact hP.w3 n)
    mu eps q1 q2 q3 be v0 v1 (n + 1) x hR.mf hR.tg
  have ecf : L.cAt (n + 1) false = sl (D.ms (s.own + 4)) := by rw [hR.own]; exact hP.cf n
  have ect : L.cAt (n + 1) true = sl (D.ms (s.own + 5)) := by rw [hR.own]; exact hP.ct n
  rw [hg, ecf, ect, hs, stepC_at D n s mu eps q1 q2 q3 be v0 v1 _ hr]
  refine ⟨⟨rfl, rfl, hR.all, fun j hj => ?_, ?_, ?_, hR.idx, hR.al⟩, rfl⟩
  · by_cases h : j = n + 1
    · subst h
      show (if n + 1 = n + 1 then _ else _) = rdS A sl (Function.update s.planes (n + 1) _ (n + 1))
      rw [if_pos rfl, Function.update_self]
      rfl
    · show (if j = n + 1 then _ else _) = rdS A sl (Function.update s.planes (n + 1) _ j)
      rw [if_neg h, Function.update_of_ne h]
      exact hR.planes j (by omega)
  · show x.rows ++ [_] = (s.rows ++ [_]).map (rdRow A sl)
    rw [List.map_append, ← hR.rows, List.map_singleton, rdRow_nil]
  · show s.own + 6 = own + (7 + 6 * (n + 1))
    rw [hR.own]
    omega

/-- The first step sets the relation up. -/
theorem first_goes (hP : Places A sl L D own) (al : GE) (idx : ℕ) (a0 : TieR.TAcc GE A.J)
    (hm : a0.mf = rdMF sl []) (ht : a0.tg = 0) (hrw : a0.rows = []) (g : List (RV GE))
    (hf : fitsAll (TieR.fmT 0) (g.take (TieR.fmT 0).length) = true) :
    Rel A sl own al idx 0 (first D al own idx g)
        (TieR.accT (D.fac al) L.wAt L.cZ L.cAt 0 a0 (g.take (TieR.fmT 0).length)) ∧
      (first D al own idx g).rounds = g.drop (TieR.fmT 0).length := by
  obtain ⟨mu, eps, q1, q2, q3, be, vals, hv, hg⟩ := fits3 3 _ hf
  obtain ⟨v0, v1, v2, rfl⟩ := len3 vals hv
  have hr : g = flatY ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1, v2]⟩ ++
      g.drop (TieR.fmT 0).length := by
    rw [← hg]
    exact (List.take_append_drop _ _).symm
  have hs := tie1_step sl (D.fac al) (L.wAt 0) (D.ms (own + 0)) (D.ms (own + 1)) (D.ms (own + 2))
    (D.ms (own + 3)) (D.ms (own + 4)) (D.ms (own + 5)) (D.ms (own + 6)) hP.w00 hP.w01 hP.w02 hP.w03
    mu eps q1 q2 q3 be v0 v1 v2 a0 hm ht
  have e1 : first D al own idx g = first D al own idx
      (flatY ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1, v2]⟩ ++ g.drop (TieR.fmT 0).length) :=
    congrArg _ hr
  show Rel A sl own al idx 0 (first D al own idx g)
      (TieR.step0 (D.fac al) (L.wAt 0) L.cZ (L.cAt 0 false) (L.cAt 0 true) a0
        (g.take (TieR.fmT 0).length)) ∧ _
  rw [hg, hP.cZ, hP.c0f, hP.c0t, hs, e1, first_at]
  refine ⟨⟨rfl, rfl, rfl, fun j hj => ?_, ?_, rfl, rfl, rfl⟩, rfl⟩
  · obtain rfl : j = 0 := by omega
    show (if (0 : ℕ) = 0 then _ else a0.planes 0) =
      rdS A sl (Function.update (fun _ : ℕ => noClaim) 0 _ 0)
    rw [if_pos rfl, Function.update_self]
    rfl
  · show a0.rows ++ [_] = [_].map (rdRow A sl)
    rw [hrw, List.nil_append, List.map_singleton, rdRow_nil]

/-- **The relation holds after the steps 0, .., n, on all rounds that fit.** -/
theorem tie_goes (hP : Places A sl L D own) (al : GE) (idx : ℕ) (a0 : TieR.TAcc GE A.J)
    (hm : a0.mf = rdMF sl []) (ht : a0.tg = 0) (hrw : a0.rows = []) :
    ∀ (n : ℕ) (g : List (RV GE)), fitsAll (TieR.fmT n) (g.take (TieR.fmT n).length) = true →
      Rel A sl own al idx n (cTie D n 0 (first D al own idx g))
          (TieR.accT (D.fac al) L.wAt L.cZ L.cAt n a0 (g.take (TieR.fmT n).length)) ∧
        (cTie D n 0 (first D al own idx g)).rounds = g.drop (TieR.fmT n).length
  | 0, g, hf => first_goes hP al idx a0 hm ht hrw g hf
  | n + 1, g, hf => by
    have h := glue (Rel A sl own al idx n) (Rel A sl own al idx (n + 1))
      (fun g => cTie D n 0 (first D al own idx g)) (TieR.accT (D.fac al) L.wAt L.cZ L.cAt n) a0
      (stepC D n)
      (TieR.stepN (L.wAt (n + 1)) (L.cAt (n + 1) false) (L.cAt (n + 1) true) (n + 1))
      (TieR.fmT n) TieR.fmN (tie_goes hP al idx a0 hm ht hrw n)
      (fun s x hR hf' => step_goes hP al idx n s x hR hf') g hf
    rw [cTie_snoc, Nat.zero_add]
    exact h

/-- **The head's condition.** -/
theorem head_sim (st : A.St) (idx : ℕ) (hS : D.S.pl = A.pl) (hpl : 2 ≤ A.pl)
    (hfac : ∀ al, D.fac al = A.fac st al) (hP : Places A sl L D own) (f : List (RV GE))
    (hf : fitsAll (⟨0, 1, false⟩ :: TieR.fmT (A.pl - 2))
      (f.take (⟨0, 1, false⟩ :: TieR.fmT (A.pl - 2) : List Fm).length) = true) :
    Sim A sl st own idx 1 (cHead D f own idx)
        (A.headRun L (A.pl - 2) st
          (f.take (⟨0, 1, false⟩ :: TieR.fmT (A.pl - 2) : List Fm).length)) ∧
      (cHead D f own idx).rounds =
        f.drop (⟨0, 1, false⟩ :: TieR.fmT (A.pl - 2) : List Fm).length := by
  rcases f with _ | ⟨r, g⟩
  · exact absurd hf (by simp [fitsAll])
  have hf' : Fm.fits ⟨0, 1, false⟩ r = true ∧
      fitsAll (TieR.fmT (A.pl - 2)) (g.take (TieR.fmT (A.pl - 2)).length) = true := by
    simpa [fitsAll] using hf
  obtain ⟨hR, hrd⟩ := tie_goes (D := D) hP (r.2.headD 0) idx
    ⟨fun _ => 0, 0, (A.ini st (r.2.headD 0)).all, (A.ini st (r.2.headD 0)).planes,
      (A.ini st (r.2.headD 0)).rows⟩ rfl rfl rfl (A.pl - 2) g hf'.2
  rw [cHead_eq, hS]
  rw [hfac] at hR
  generalize cTie D (A.pl - 2) 0 (first D (r.2.headD 0) own idx g) = s at hR hrd ⊢
  have eo : ownAt A.toPub 1 = 7 + 6 * (A.pl - 2) := by simp [ownAt]
  refine ⟨⟨rfl, hR.al.symm, hR.rows, ?_, ?_, fun _ => hR.all, fun _ j hj => ?_,
    fun h => absurd h (by omega), fun h => absurd h (by omega), fun h => absurd h (by omega),
    fun h => absurd h (by omega)⟩, hrd⟩
  · rw [eo]
    exact hR.own
  · show _ = idx + 0
    exact hR.idx
  · by_cases h : j < A.pl - 2 + 1
    · refine (if_pos h).trans ?_
      show _ = rdS A sl (Function.update s.planes (A.pl - 1) s.pow j)
      rw [Function.update_of_ne (by omega)]
      exact hR.planes j (by omega)
    · obtain rfl : j = A.pl - 1 := by omega
      refine (if_neg h).trans ?_
      show _ = rdS A sl (Function.update s.planes (A.pl - 1) s.pow (A.pl - 1))
      rw [Function.update_self]
      exact congrArg₂ SCl.mk hR.mf hR.tg

/-- The same, in the very words of `Sims.head` at `A.runD P`. -/
theorem head_field (P : Pl A) (st : A.St) (idx : ℕ) (hS : D.S.pl = A.pl) (hpl : 2 ≤ A.pl)
    (hfac : ∀ al, D.fac al = A.fac st al) (hP : Places A sl P.tie D own) :
    ∀ f, fitsAll (A.runD P).fHead (f.take (A.runD P).fHead.length) = true →
      Sim A sl st own idx 1 (cHead D f own idx)
          ((A.runD P).rHead st (f.take (A.runD P).fHead.length)) ∧
        (cHead D f own idx).rounds = f.drop (A.runD P).fHead.length :=
  fun f hf => head_sim st idx hS hpl hfac hP f hf

end

end Lk6.Mid.TieSim

#print axioms Lk6.Mid.TieSim.tie_goes
#print axioms Lk6.Mid.TieSim.head_sim
#print axioms Lk6.Mid.TieSim.head_field
