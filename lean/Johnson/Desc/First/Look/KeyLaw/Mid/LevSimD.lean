-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/LevSimD.lean: the levels of a product tree in the course over the
field (`cLevels`, Course.lean) go with `Lev.treeStep` (LevRunC.lean). The course is our text of the
program's lookup, over the field. That the program's run, read in the field, is this course is not
shown here.

Main names:
  `rd0` a row without terms on the table of bits, read.
  `Outs` what some levels leave behind: the rounds and mask entries taken, the rows filed, which
    read are the rows that the plain function appends; alpha and the claims in hand are untouched.
  `fmN`, `stepsN`, `ownN` n levels: formats, plain function, number of mask entries.
  `frAt`, `PlAt` the fresh mask entries of a level; «the order and the places of level l are the
    program's».
  `levels_goes` n levels none of which is special. `tree_goes`: n + 1 levels, the last of which may
    be a key tree's last.
  `treeStep_eq`, `fmT_eq` `Lev.treeStep P n` is `stepsN P (n + 1)`; the formats likewise.
Limits: `PlAt` at each level is a premise; the rounds fit.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.LevSimC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim
open OnBytes OnBytes.Slice Flat Lev

variable {J : Type} [DecidableEq J] (sl : Slot → J)

/-- A row without terms on the table of bits, read. -/
def rd0 (r : RowF) : Cb.LdLkp.Row GE J := ⟨rdMF sl r.masks, r.target⟩

/-- What some levels leave behind. -/
structure Outs (s s' : Cs) (nr own idx : ℕ) (a a' : Acc GE J) : Prop where
  rounds : s'.rounds = s.rounds.drop nr
  own : s'.own = s.own + own
  idx : s'.idx = s.idx + idx
  rows : ∃ new : List RowF, (∀ r ∈ new, r.maps = []) ∧ s'.rows = s.rows ++ new ∧
    a'.rows = a.rows ++ new.map (rd0 sl)
  same : Same s s'

theorem Outs.refl (s : Cs) (a : Acc GE J) : Outs sl s s 0 0 0 a a :=
  ⟨rfl, rfl, rfl, ⟨[], fun _ h => absurd h List.not_mem_nil, (List.append_nil _).symm,
    (List.append_nil _).symm⟩, Same.refl s⟩

theorem Outs.step {s s' s'' : Cs} {nr own idx k : ℕ} {last : Bool} {a a' a'' : Acc GE J}
    (h : Outs sl s s' nr own idx a a') (h' : LevOut sl s' s'' last k a' a'') :
    Outs sl s s'' (nr + (k + 4)) (own + (if last then 2 * k + 5 - 2 else 2 * k + 5))
      (idx + (if last then 2 else 0)) a a'' where
  rounds := by rw [h'.rounds, h.rounds, List.drop_drop]
  own := by rw [h'.own, h.own, Nat.add_assoc]
  idx := by rw [h'.idx, h.idx, Nat.add_assoc]
  rows := by
    obtain ⟨new, hn, e1, e2⟩ := h.rows
    obtain ⟨m, t, e3, e4⟩ := h'.rows
    refine ⟨new ++ [⟨m, [], t⟩], fun r hr => ?_, ?_, ?_⟩
    · rcases List.mem_append.1 hr with hr | hr
      · exact hn r hr
      · rw [List.mem_singleton.1 hr]
    · rw [e3, e1, List.append_assoc]
    · rw [e4, e2, List.map_append, List.append_assoc]
      rfl
  same := h.same.trans h'.same

/-- n levels: formats, number of mask entries -/
def fmN (g : ℕ) : ℕ → List Fm
  | 0 => []
  | n + 1 => fmN g n ++ fmLev (g + n)
def ownN (g : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ownN g n + (2 * (g + n) + 5)

/-- n levels of the plain function, on what is read off a level's state -/
def stepsN {g : ℕ} (P : TreeD J g) : ℕ → Acc GE J → List (RV GE) → Acc GE J
  | 0 => fun a _ => a
  | n + 1 => seqRun (fmN g n).length (stepsN P n)
      (stepLev (g + n) (P.sg n) (P.wv n) (P.wc n) (P.c n false) (P.c n true))

/-- the fresh mask entries of a level of k variables, from the numbers of those taken -/
def frAt (D : Dt) (last : Bool) (k own idx : ℕ) : List Slot :=
  if last then slots D.ms own (2 * k + 5 - 2) ++ slots D.ix idx 2 else slots D.ms own (2 * k + 5)

/-- The order and the places of level l are the course's. -/
structure PlAt {g : ℕ} (D : Dt) (P : TreeD J g) (last : Bool) (l own idx : ℕ) : Prop where
  ord : (if last then ordFirst D.S.order (g + l) else ordDown (g + l)) =
    List.ofFn fun j => (P.sg l j).val
  wv : P.wv l = wvF sl (g + l) (frAt D last (g + l) own idx)
  wc : P.wc l = wcF sl (g + l) (frAt D last (g + l) own idx)
  c0 : P.c l false = sl ((frAt D last (g + l) own idx).getD (2 * (g + l) + 3) ⟨0, 0⟩)
  c1 : P.c l true = sl ((frAt D last (g + l) own idx).getD (2 * (g + l) + 4) ⟨0, 0⟩)

section
variable {g : ℕ} (D : Dt) (P : TreeD J g) (c : PscF.PointClaim) (a : Acc GE J) (s : Cs)

/-- One level more behind n levels none of which is special. -/
theorem snoc_step (keys : Bool) (n : ℕ)
    (ih : RelC sl (cLevels D false g n 0 c s).1 (stepsN P n a (s.rounds.take (fmN g n).length)) ∧
      Outs sl s (cLevels D false g n 0 c s).2 (fmN g n).length (ownN g n) 0 a
        (stepsN P n a (s.rounds.take (fmN g n).length)))
    (hp : PlAt sl D P keys n (s.own + ownN g n) s.idx)
    (hf : fitsAll (fmN g (n + 1)) (s.rounds.take (fmN g (n + 1)).length) = true) :
    RelC sl (cLevels D keys g (n + 1) 0 c s).1
        (stepsN P (n + 1) a (s.rounds.take (fmN g (n + 1)).length)) ∧
      (cLevels D keys g (n + 1) 0 c s).1.point.length = g + n + 1 ∧
      Outs sl s (cLevels D keys g (n + 1) 0 c s).2 (fmN g (n + 1)).length
        (ownN g n + (if keys then 2 * (g + n) + 5 - 2 else 2 * (g + n) + 5))
        (0 + (if keys then 2 else 0)) a
        (stepsN P (n + 1) a (s.rounds.take (fmN g (n + 1)).length)) := by
  have hl : (fmN g (n + 1)).length = (fmN g n).length + (g + n + 4) := by
    show (fmN g n ++ fmLev (g + n)).length = _
    rw [List.length_append, fmLev_len]
  rw [hl] at hf ⊢
  have e1 : (s.rounds.take ((fmN g n).length + (g + n + 4))).take (fmN g n).length =
      s.rounds.take (fmN g n).length := take_take_add _ _ _
  have e2 : (s.rounds.take ((fmN g n).length + (g + n + 4))).drop (fmN g n).length =
      (cLevels D false g n 0 c s).2.rounds.take (g + n + 4) := by
    rw [drop_take_add, ih.2.rounds]
  have h2 : fitsAll (fmLev (g + n)) ((cLevels D false g n 0 c s).2.rounds.take (g + n + 4)) =
      true := by
    have h0 := (fitsAll_app (fmN g n) (fmLev (g + n)) _ hf).2
    rw [e2] at h0
    exact h0
  have eS : stepsN P (n + 1) a (s.rounds.take ((fmN g n).length + (g + n + 4))) =
      stepLev (g + n) (P.sg n) (P.wv n) (P.wc n) (P.c n false) (P.c n true)
        (stepsN P n a (s.rounds.take (fmN g n).length))
        ((cLevels D false g n 0 c s).2.rounds.take (g + n + 4)) := by
    show stepLev (g + n) (P.sg n) (P.wv n) (P.wc n) (P.c n false) (P.c n true)
      (stepsN P n a ((s.rounds.take ((fmN g n).length + (g + n + 4))).take (fmN g n).length))
      ((s.rounds.take ((fmN g n).length + (g + n + 4))).drop (fmN g n).length) = _
    rw [e1, e2]
  have eF : frAt D keys (g + n) (s.own + ownN g n) s.idx =
      freshOf D keys (g + n) (cLevels D false g n 0 c s).2 := by
    unfold frAt freshOf
    rw [ih.2.own, ih.2.idx]
    rfl
  have hg := lev_goes sl D keys (g + n) (P.sg n) hp.ord (cLevels D false g n 0 c s).1
    (stepsN P n a (s.rounds.take (fmN g n).length)) ih.1 (cLevels D false g n 0 c s).2 h2
  rw [← eF, ← hp.wv, ← hp.wc, ← hp.c0, ← hp.c1, ← eS] at hg
  have eC : cLevels D keys g (n + 1) 0 c s =
      cLev D keys (g + n) (cLevels D false g n 0 c s).1 (cLevels D false g n 0 c s).2 := by
    rw [cLevels_snoc, Nat.zero_add]
  rw [eC]
  exact ⟨hg.1, hg.2.1, ih.2.step sl hg.2.2⟩

/-- n levels none of which is special. -/
theorem levels_goes (hrel : RelC sl c a) : ∀ n : ℕ,
    (∀ l < n, PlAt sl D P false l (s.own + ownN g l) s.idx) →
    fitsAll (fmN g n) (s.rounds.take (fmN g n).length) = true →
    RelC sl (cLevels D false g n 0 c s).1 (stepsN P n a (s.rounds.take (fmN g n).length)) ∧
      Outs sl s (cLevels D false g n 0 c s).2 (fmN g n).length (ownN g n) 0 a
        (stepsN P n a (s.rounds.take (fmN g n).length))
  | 0, _, _ => ⟨hrel, Outs.refl sl s a⟩
  | n + 1, hp, hf => by
    have hl : (fmN g (n + 1)).length = (fmN g n).length + (g + n + 4) := by
      show (fmN g n ++ fmLev (g + n)).length = _
      rw [List.length_append, fmLev_len]
    have h1 : fitsAll (fmN g n) (s.rounds.take (fmN g n).length) = true := by
      have h0 := (fitsAll_app (fmN g n) (fmLev (g + n)) _ hf).1
      rw [hl, take_take_add] at h0
      exact h0
    have ih := levels_goes hrel n (fun l h => hp l (Nat.lt_succ_of_lt h)) h1
    have r := snoc_step sl D P c a s false n ih (hp n (Nat.lt_succ_self n)) hf
    exact ⟨r.1, r.2.2⟩

/-- n + 1 levels, the last of which may be a key tree's last. -/
theorem tree_goes (hrel : RelC sl c a) (keys : Bool) (n : ℕ)
    (hp : ∀ l < n, PlAt sl D P false l (s.own + ownN g l) s.idx)
    (hq : PlAt sl D P keys n (s.own + ownN g n) s.idx)
    (hf : fitsAll (fmN g (n + 1)) (s.rounds.take (fmN g (n + 1)).length) = true) :
    RelC sl (cLevels D keys g (n + 1) 0 c s).1
        (stepsN P (n + 1) a (s.rounds.take (fmN g (n + 1)).length)) ∧
      (cLevels D keys g (n + 1) 0 c s).1.point.length = g + n + 1 ∧
      Outs sl s (cLevels D keys g (n + 1) 0 c s).2 (fmN g (n + 1)).length
        (ownN g n + (if keys then 2 * (g + n) + 5 - 2 else 2 * (g + n) + 5))
        (0 + (if keys then 2 else 0)) a
        (stepsN P (n + 1) a (s.rounds.take (fmN g (n + 1)).length)) := by
  have hl : (fmN g (n + 1)).length = (fmN g n).length + (g + n + 4) := by
    show (fmN g n ++ fmLev (g + n)).length = _
    rw [List.length_append, fmLev_len]
  have h1 : fitsAll (fmN g n) (s.rounds.take (fmN g n).length) = true := by
    have h0 := (fitsAll_app (fmN g n) (fmLev (g + n)) _ hf).1
    rw [hl, take_take_add] at h0
    exact h0
  exact snoc_step sl D P c a s keys n (levels_goes sl D P c a s hrel n hp h1) hq hf

end

/-! ### the plain function of LevRunC.lean -/

theorem fmT_eq (g : ℕ) : ∀ n, fmT g n = fmN g (n + 1)
  | 0 => rfl
  | n + 1 => by
    show fmT g n ++ fmLev (g + (n + 1)) = fmN g (n + 1) ++ fmLev (g + (n + 1))
    rw [fmT_eq g n]

theorem treeStep_eq {g : ℕ} {S₀ : Type} (P : TreeD J g) (x : S₀) (a : Acc GE J) :
    ∀ (n : ℕ) (f : List (RV GE)), treeStep P n (x, a) f = (x, stepsN P (n + 1) a f)
  | 0, _ => rfl
  | n + 1, f => by
    show levStep P (n + 1) (treeStep P n (x, a) (f.take (fmT g n).length))
      (f.drop (fmT g n).length) = _
    rw [treeStep_eq P x a n, fmT_eq]
    rfl

end Lk6.Mid

#print axioms Lk6.Mid.tree_goes
#print axioms Lk6.Mid.treeStep_eq
