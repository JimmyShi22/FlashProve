-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/LevSimC.lean: one level of the course over the field (`cLevels`,
Course.lean) goes with one level of the plain function of LevRunC.lean. The course is our text of
the program's lookup, over the field. That the program's run, read in the field, is this course is
not shown here.

Main names:
  `cLev` one level of the course: the sumcheck, the join on a line.
  `cLevels_succ`, `cLevels_snoc` the levels, split at the first; at the last: only the last level of
    a key tree is special.
  `Same s s'` the two stands have the same alpha and claims in hand.
  `freshOf` the fresh mask entries of a level.
  `stepLev` one level of the plain function, on what is read off a level's state.
  `lev_goes` from a claim and a state that go together, on rounds that fit: the next claim and state
    go together; the course has taken just these rounds and entries and filed one row, which read is
    the row that the plain function appends.
Limits: the order's list is that of a permutation σ; the places are those of the fresh entries.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.LevSimB
import Johnson.Desc.First.Look.KeyLaw.Mid.Relation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim
open OnBytes OnBytes.Slice Flat Lev

/-- One level of the course. -/
def cLev (D : Dt) (last : Bool) (k : ℕ) (c : PscF.PointClaim) (s : Cs) : PscF.PointClaim × Cs :=
  ((lineF
      (pscC D ⟨(if last then ordFirst D.S.order k else ordDown k).map fun t =>
        PscF.Weight.equality (c.point.getD t 0) 3, c.masks, c.value⟩ sProd last 0
        (byVarF · (if last then ordFirst D.S.order k else ordDown k)) s).2.draw
      ((pscC D ⟨(if last then ordFirst D.S.order k else ordDown k).map fun t =>
        PscF.Weight.equality (c.point.getD t 0) 3, c.masks, c.value⟩ sProd last 0
        (byVarF · (if last then ordFirst D.S.order k else ordDown k)) s).1.ends.getD 0 noClaim)
      ((pscC D ⟨(if last then ordFirst D.S.order k else ordDown k).map fun t =>
        PscF.Weight.equality (c.point.getD t 0) 3, c.masks, c.value⟩ sProd last 0
        (byVarF · (if last then ordFirst D.S.order k else ordDown k)) s).1.ends.getD 1 noClaim)),
    (pscC D ⟨(if last then ordFirst D.S.order k else ordDown k).map fun t =>
        PscF.Weight.equality (c.point.getD t 0) 3, c.masks, c.value⟩ sProd last 0
        (byVarF · (if last then ordFirst D.S.order k else ordDown k)) s).2.next)

theorem cLevels_succ (D : Dt) (keys : Bool) (more n l : ℕ) (c : PscF.PointClaim) (s : Cs) :
    cLevels D keys more (n + 1) l c s =
      cLevels D keys more n (l + 1) (cLev D (keys && n == 0) (more + l) c s).1
        (cLev D (keys && n == 0) (more + l) c s).2 := rfl

/-- Only the last level of a key tree is special. -/
theorem cLevels_snoc (D : Dt) (keys : Bool) (more : ℕ) : ∀ (n l : ℕ) (c : PscF.PointClaim) (s : Cs),
    cLevels D keys more (n + 1) l c s =
      cLev D keys (more + (l + n)) (cLevels D false more n l c s).1 (cLevels D false more n l c s).2
  | 0, l, c, s => by
    rw [cLevels_succ]
    show cLev D (keys && (0 == 0)) (more + l) c s = cLev D keys (more + (l + 0)) c s
    have e : (keys && ((0 : ℕ) == 0)) = keys := by simp
    rw [e]
    rfl
  | n + 1, l, c, s => by
    rw [cLevels_succ, cLevels_snoc D keys more n (l + 1), cLevels_succ D false]
    have e : (keys && (n + 1 == 0)) = false := by simp
    have e' : (false && (n == 0)) = false := rfl
    have ea : l + 1 + n = l + (n + 1) := by omega
    rw [e, e', ea]

/-- The two stands have the same alpha and claims in hand. -/
structure Same (s s' : Cs) : Prop where
  alpha : s'.alpha = s.alpha
  rest : s'.rest = s.rest
  pow : s'.pow = s.pow
  top : s'.top = s.top
  bit : s'.bit = s.bit
  planes : s'.planes = s.planes
  roots : s'.roots = s.roots
  leaves : s'.leaves = s.leaves
  zt : s'.zt = s.zt

theorem Same.refl (s : Cs) : Same s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Same.trans {s s' s'' : Cs} (h : Same s s') (h' : Same s' s'') : Same s s'' :=
  ⟨h'.alpha.trans h.alpha, h'.rest.trans h.rest, h'.pow.trans h.pow, h'.top.trans h.top,
    h'.bit.trans h.bit, h'.planes.trans h.planes, h'.roots.trans h.roots,
    h'.leaves.trans h.leaves, h'.zt.trans h.zt⟩

/-- the fresh mask entries of a level of k variables -/
def freshOf (D : Dt) (last : Bool) (k : ℕ) (s : Cs) : List Slot :=
  if last then slots D.ms s.own (2 * k + 5 - 2) ++ slots D.ix s.idx 2
  else slots D.ms s.own (2 * k + 5)

theorem freshOf_len (D : Dt) (last : Bool) (k : ℕ) (s : Cs) :
    (freshOf D last k s).length = 2 * k + 5 := by
  unfold freshOf slots
  cases last <;> simp

theorem ws_sum : ∀ (k : ℕ) (z : Fin k → GE), ((wsOf z).map fun w => w.d - 1).sum = 2 * k + 2
  | 0, z => by
    rw [wsOf_zero]
    rfl
  | k + 1, z => by
    rw [wsOf_succ, List.map_cons, List.sum_cons, ws_sum k]
    show 3 - 1 + (2 * k + 2) = _
    omega

theorem masks_clOf {k : ℕ} (σ : Equiv.Perm (Fin k)) (c : PscF.PointClaim) :
    PscF.masksOf (clOf σ c) sProd = 2 * k + 5 := by
  show 1 + ((PscF.varsOf (clOf σ c) sProd).map fun w => w.d - 1).sum + 2 = _
  rw [vars_clOf, ws_sum]
  omega

/-- The sumcheck of a level in the course, written out. -/
theorem pscC_lev (D : Dt) (last : Bool) {k : ℕ} (σ : Equiv.Perm (Fin k)) (c : PscF.PointClaim)
    (place : List GE → List GE) (s : Cs) :
    pscC D (clOf σ c) sProd last 0 place s =
      ({ PscF.outOf (clOf σ c) sProd (freshOf D last k s) (heardF k true s.rounds) with
          point := place
            (PscF.outOf (clOf σ c) sProd (freshOf D last k s) (heardF k true s.rounds)).point
          ends := (PscF.outOf (clOf σ c) sProd (freshOf D last k s)
            (heardF k true s.rounds)).ends.map fun e => { e with point := place e.point } },
        { s with
          rounds := s.rounds.drop (k + 3)
          own := s.own + (if last then 2 * k + 5 - 2 else 2 * k + 5)
          idx := s.idx + (if last then 2 else 0)
          rows := s.rows ++
            [⟨(PscF.outOf (clOf σ c) sProd (freshOf D last k s) (heardF k true s.rounds)).rowMasks,
              [], (PscF.outOf (clOf σ c) sProd (freshOf D last k s)
                (heardF k true s.rounds)).rowTarget⟩] }) := by
  unfold pscC freshOf
  simp only [clOf_len, masks_clOf]
  rfl

variable {J : Type} [DecidableEq J] (sl : Slot → J)

/-- One level of the plain function, on what is read off a level's state. -/
def stepLev (k : ℕ) (σ : Equiv.Perm (Fin k)) (wv : ℕ → Fin 2 → J) (wc c0 c1 : J) (a : Acc GE J)
    (f : List (RV GE)) : Acc GE J :=
  stepLine c0 c1 (stepSum k σ wv wc a (f.take (fmSum k).length)) (f.drop (fmSum k).length)

theorem fmLev_len (k : ℕ) : (fmLev k).length = k + 4 := by
  show (fmSum k ++ [_]).length = _
  rw [List.length_append, fmSum_len]
  rfl

/-- What a level leaves behind, beside the next claim. -/
structure LevOut (s s' : Cs) (last : Bool) (k : ℕ) (a a' : Acc GE J) : Prop where
  rounds : s'.rounds = s.rounds.drop (k + 4)
  own : s'.own = s.own + (if last then 2 * k + 5 - 2 else 2 * k + 5)
  idx : s'.idx = s.idx + (if last then 2 else 0)
  rows : ∃ m t, s'.rows = s.rows ++ [⟨m, [], t⟩] ∧ a'.rows = a.rows ++ [⟨rdMF sl m, t⟩]
  same : Same s s'

theorem cLev_of (D : Dt) (last : Bool) (k : ℕ) (σ : Equiv.Perm (Fin k))
    (hσ : (if last then ordFirst D.S.order k else ordDown k) = List.ofFn fun j => (σ j).val)
    (c : PscF.PointClaim) (s : Cs) :
    cLev D last k c s =
      (lineF (pscC D (clOf σ c) sProd last 0 (byVarF · (List.ofFn fun j => (σ j).val)) s).2.draw
        ((pscC D (clOf σ c) sProd last 0
          (byVarF · (List.ofFn fun j => (σ j).val)) s).1.ends.getD 0 noClaim)
        ((pscC D (clOf σ c) sProd last 0
          (byVarF · (List.ofFn fun j => (σ j).val)) s).1.ends.getD 1 noClaim),
        (pscC D (clOf σ c) sProd last 0 (byVarF · (List.ofFn fun j => (σ j).val)) s).2.next) := by
  unfold cLev
  rw [hσ]
  rfl

/-- **One level.** -/
theorem lev_goes (D : Dt) (last : Bool) (k : ℕ) (σ : Equiv.Perm (Fin k))
    (hσ : (if last then ordFirst D.S.order k else ordDown k) = List.ofFn fun j => (σ j).val)
    (c : PscF.PointClaim) (a : Acc GE J) (hrel : RelC sl c a) (s : Cs)
    (hf : fitsAll (fmLev k) (s.rounds.take (k + 4)) = true) :
    RelC sl (cLev D last k c s).1
        (stepLev k σ (wvF sl k (freshOf D last k s)) (wcF sl k (freshOf D last k s))
          (sl ((freshOf D last k s).getD (2 * k + 3) ⟨0, 0⟩))
          (sl ((freshOf D last k s).getD (2 * k + 4) ⟨0, 0⟩)) a (s.rounds.take (k + 4))) ∧
      (cLev D last k c s).1.point.length = k + 1 ∧
      LevOut sl s (cLev D last k c s).2 last k a
        (stepLev k σ (wvF sl k (freshOf D last k s)) (wcF sl k (freshOf D last k s))
          (sl ((freshOf D last k s).getD (2 * k + 3) ⟨0, 0⟩))
          (sl ((freshOf D last k s).getD (2 * k + 4) ⟨0, 0⟩)) a (s.rounds.take (k + 4))) := by
  have e3 : (s.rounds.take (k + 4)).take (k + 3) = s.rounds.take (k + 3) :=
    take_take_add (k + 3) 1 s.rounds
  have e4 : (s.rounds.take (k + 4)).drop (k + 3) = (s.rounds.drop (k + 3)).take 1 :=
    drop_take_add (k + 3) 1 s.rounds
  have h1 : fitsAll (fmSum k) (s.rounds.take (k + 3)) = true := by
    have h0 := (fitsAll_app (fmSum k) [⟨0, 1, false⟩] _ hf).1
    rw [fmSum_len, e3] at h0
    exact h0
  obtain ⟨v0, G, hF, hGl, hG2⟩ := fits_sum k _ h1
  have hh : heardF k true s.rounds = hdOf k v0 G := by
    rw [heard_take, hF]
    rfl
  have hG1 : k + 1 ≤ G.length := by omega
  have hfr := freshOf_len D last k s
  have hP := pscC_lev D last σ c (byVarF · (List.ofFn fun j => (σ j).val)) s
  rw [hh] at hP
  have hc := cLev_of D last k σ hσ c s
  rw [hP] at hc
  have hE := out_ends σ c (freshOf D last k s) v0 G hG1 hfr (hG2 (k + 1) (Nat.le_refl _))
  have hS := sum_sim sl σ c a hrel (freshOf D last k s) hfr v0 G hG1
    (fun j hj => hG2 j (Nat.le_succ_of_le hj))
  have hpt := out_point σ c (freshOf D last k s) v0 G hG1
  generalize PscF.outOf (clOf σ c) sProd (freshOf D last k s) (hdOf k v0 G) = o at hc hE hS hpt
  have hA : stepLev k σ (wvF sl k (freshOf D last k s)) (wcF sl k (freshOf D last k s))
      (sl ((freshOf D last k s).getD (2 * k + 3) ⟨0, 0⟩))
      (sl ((freshOf D last k s).getD (2 * k + 4) ⟨0, 0⟩)) a (s.rounds.take (k + 4)) =
      stepLine (sl ((freshOf D last k s).getD (2 * k + 3) ⟨0, 0⟩))
        (sl ((freshOf D last k s).getD (2 * k + 4) ⟨0, 0⟩))
        ⟨byVarF ((List.range k).map (chC G)) (List.ofFn fun j => (σ j).val), chC G k,
          snt G (k + 1) 0, snt G (k + 1) 1, a.rows ++ [⟨rdMF sl o.rowMasks, o.rowTarget⟩]⟩
        ((s.rounds.drop (k + 3)).take 1) := by
    unfold stepLev
    rw [fmSum_len, e3, e4, hF, hS, hpt]
  have hr : chC ((s.rounds.drop (k + 3)).take 1) 0 =
      ((s.rounds.drop (k + 3)).headD ([], [])).2.headD 0 := by
    cases s.rounds.drop (k + 3) <;> rfl
  rw [hE] at hc
  rw [hc, hA]
  refine ⟨?_, ?_, ?_⟩
  · exact line_sim sl _ _ _ _ _ _ _ _ _ hr
  · show (byVarF ((List.range k).map (chC G)) (List.ofFn fun j => (σ j).val) ++ [_]).length = k + 1
    rw [List.length_append]
    unfold byVarF
    simp
  · refine ⟨?_, rfl, rfl, ⟨_, _, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    show (s.rounds.drop (k + 3)).tail = s.rounds.drop (k + 4)
    rw [List.tail_drop]

end Lk6.Mid

#print axioms Lk6.Mid.cLevels_snoc
#print axioms Lk6.Mid.pscC_lev
#print axioms Lk6.Mid.lev_goes
