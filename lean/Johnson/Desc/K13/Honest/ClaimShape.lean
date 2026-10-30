-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/ClaimShape.lean: kind K13, the members' batching: THE SHAPE OF THE ROW THAT
THE BATCHING HANDS ON (`Batt.rowOf`, OnBytes/Iop/Batt.lean) IS A FUNCTION OF THE PILE's ROWS' SHAPES
AND OF THE SLOTS TAKEN: no sent element and no challenge is in it. Statements with their proofs.
Main names:
  `claimSh`: the function: the two marks on the weights (`bare`: every row is bare; `vars`: the
    first row's); kCol coordinates; the slots taken, then the rows' own.
  `mark_iff`: what the mark says of a list. `flatMap_zip_fst`, `flatMap_zip_snd`, `map_fst_zip'`: on
    lists. `walkOf_length`: the hiding walk at k ≥ 1 variables, where k rounds were heard, has
    1 + 2 k coefficients.
  `rowSh_rowOf`: **the statement**, at a pile that the batching allows.

What is not claimed. Nothing of the row's values. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.Shape
import Johnson.Desc.K13.Law.FitC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.K13.Law

/-- **The shape of the row that is handed on, AT A PILE THAT THE BATCHING ALLOWS** (`formSh`,
Shape.lean of this folder: each row has a weight, and all have one number of variables). At another
pile its two marks need not be the row's: `vars` is taken from the first row alone; `bare` says that
every row is bare. -/
def claimSh (k : Nat) (pile : List RowSh) (fresh : List Slot) : RowSh :=
  ⟨pile.all (·.bare), pile.head?.bind (·.vars), k, fresh ++ pile.flatMap (·.slots)⟩

/-- What the mark says of a list. -/
theorem mark_iff (l : List Nat) (h : Nat) : varsMark l = some h ↔ l ≠ [] ∧ ∀ v ∈ l, v = h := by
  cases l with
  | nil => simp [varsMark]
  | cons a t =>
    show (if t.all (· == a) then some a else none) = some h ↔ _
    constructor
    · intro e
      split at e
      · rename_i ht
        obtain rfl := Option.some.inj e
        refine ⟨by simp, fun v hv => ?_⟩
        rcases List.mem_cons.1 hv with rfl | hv
        · rfl
        · exact eq_of_beq (List.all_eq_true.1 ht v hv)
      · cases e
    · rintro ⟨-, hall⟩
      have ha : a = h := hall a (List.mem_cons_self ..)
      subst ha
      rw [if_pos (List.all_eq_true.2 fun v hv => beq_iff_eq.2 (hall v (List.mem_cons_of_mem _ hv)))]

/-- A function of the first members alone, over two lists of one length zipped. -/
theorem flatMap_zip_fst {α β γ : Type} (f : α → List γ) : ∀ (a : List α) (b : List β),
    a.length = b.length → (a.zip b).flatMap (fun p => f p.1) = a.flatMap f
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    rw [List.zip_cons_cons, List.flatMap_cons, List.flatMap_cons,
      flatMap_zip_fst f a b (Nat.succ.inj h)]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

/-- The like of the second members. -/
theorem flatMap_zip_snd {α β γ : Type} (f : β → List γ) : ∀ (a : List α) (b : List β),
    a.length = b.length → (a.zip b).flatMap (fun p => f p.2) = b.flatMap f
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    rw [List.zip_cons_cons, List.flatMap_cons, List.flatMap_cons,
      flatMap_zip_snd f a b (Nat.succ.inj h)]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

/-- The first members of two lists zipped, where the second is as long. -/
theorem map_fst_zip' {α β : Type} : ∀ (a : List α) (b : List β), a.length ≤ b.length →
    (a.zip b).map (·.1) = a
  | [], _, _ => by simp
  | x :: a, y :: b, h => by
    rw [List.zip_cons_cons, List.map_cons, map_fst_zip' a b (Nat.le_of_succ_le_succ h)]
  | _ :: _, [], h => by cases h

/-- The hiding walk at k variables has 1 + 2 k coefficients. -/
theorem walkOf_length {k : ℕ} {h : Psc.Heard} (hk : 1 ≤ k) (hl : h.rounds.length = k) :
    (walkOf k h).1.length = 1 + 2 * k := by
  have e := OnBytes.Model.Road.walk_length (wsOf k) (h.rounds.map (·.2))
    (by intro e; have := congrArg List.length e; simp at this; omega) (by simp [hl])
    (fun w hw => by rw [List.eq_of_mem_replicate hw]; exact (by decide : 1 ≤ 3))
  rw [e]
  simp [Psc.hidingEntries, Psc.Weight.plain]
  omega

/-- **The shape of the row that the batching hands on is `claimSh`**, at the pile's rows' shapes and
the slots taken. -/
theorem rowSh_rowOf {k : ℕ} {pile : List TensorRow} {x : E} {fresh : List Slot} {h : Psc.Heard}
    {o : Psc.Out} (hf : Batt.fits k pile = true)
    (hr : Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh h = some o) :
    rowSh (Batt.rowOf pile o) = claimSh k (pile.map rowSh) fresh := by
  obtain ⟨hl, -, hfr, hpt, hmk, hmp, -⟩ := run_fields hf hr
  obtain ⟨-, hk, -⟩ := of_fits x hf
  have hpw : (Psc.powers oneE x pile.length).length = pile.length :=
    OnBytes.Road.Hd.powers_len _ _ _
  have hml : pile.length = o.rowMaps.length := by
    rw [hmp, List.length_map, List.length_zip, hpw, Nat.min_self]
  have e1 : (Batt.rowOf pile o).g.map Tensor.vars = pile.flatMap fun r => r.g.map Tensor.vars := by
    show ((zipT pile o.rowMaps).flatMap fun p => p.1.g.map fun t => t.scale p.2).map Tensor.vars = _
    rw [OnBytes.zipT_eq, List.map_flatMap]
    refine Eq.trans (congrArg (fun f => List.flatMap f (pile.zip o.rowMaps)) ?_)
      (flatMap_zip_fst (fun r : TensorRow => r.g.map Tensor.vars) pile o.rowMaps hml)
    funext p
    rw [List.map_map]
    show p.1.g.map (Tensor.vars ∘ fun t => t.scale p.2) = p.1.g.map Tensor.vars
    exact List.map_congr_left fun t _ => by simp only [Function.comp, Tensor.vars, Tensor.scale]
  have e2 : (Batt.rowOf pile o).psi.length = k := by
    show o.point.length = k
    rw [hpt, List.length_map, hl]
  have e3 : (Batt.rowOf pile o).masks.map (·.1) = fresh ++ (pile.map rowSh).flatMap (·.slots) := by
    show o.rowMasks.map (·.1) = _
    rw [hmk, List.map_append, map_fst_zip' fresh _ (by rw [walkOf_length hk hl, hfr])]
    congr 1
    show ((Batt.claimOf pile x).masks.map fun t => (t.1, mulE _ t.2)).map (·.1) = _
    rw [List.map_map]
    show ((zipT (Batt.chiOf pile x) pile).flatMap fun p => Psc.scaleForm p.1 p.2.masks).map _ = _
    rw [OnBytes.zipT_eq, List.map_flatMap, List.flatMap_map]
    refine Eq.trans (congrArg (fun f => List.flatMap f ((Batt.chiOf pile x).zip pile)) ?_)
      (flatMap_zip_snd (fun r : TensorRow => (rowSh r).slots) (Batt.chiOf pile x) pile hpw)
    funext p
    show ((p.2.masks.map fun t => (t.1, mulE p.1 t.2)).map _) = p.2.masks.map (·.1)
    rw [List.map_map]
    rfl
  -- the two marks: by the test on the pile each row has a weight, and all have one number h
  have hf' : formSh k (pile.map rowSh) = true := (formSh_eq k pile).trans hf
  cases pile with
  | nil => cases hf'
  | cons r l =>
    have hall : ∀ s ∈ r :: l, (rowSh s).bare = false ∧ (rowSh s).vars.isSome = true ∧
        (rowSh s).vars = (rowSh r).vars := fun s hs => by
      have h0 : (decide (1 ≤ k) && ((r :: l).map rowSh).all fun s =>
          s.point == k && !s.bare && (s.vars.isSome && s.vars == (rowSh r).vars)) = true := hf'
      have h1 := List.all_eq_true.1 (Bool.and_eq_true _ _ ▸ h0).2 (rowSh s) (List.mem_map_of_mem hs)
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h1
      exact ⟨h1.1.2, h1.2.1, h1.2.2⟩
    obtain ⟨h, hh⟩ := Option.isSome_iff_exists.1 (hall r (List.mem_cons_self ..)).2.1
    have hm : varsMark ((Batt.rowOf (r :: l) o).g.map Tensor.vars) = some h := by
      rw [e1, mark_iff]
      have hr := (mark_iff _ h).1 hh
      refine ⟨fun e => hr.1 ?_, fun v hv => ?_⟩
      · have e' : r.g.map Tensor.vars ++ l.flatMap (fun r => r.g.map Tensor.vars) = [] := e
        exact (List.append_eq_nil_iff.1 e').1
      · obtain ⟨s, hs, hv'⟩ := List.mem_flatMap.1 hv
        exact ((mark_iff _ h).1 ((hall s hs).2.2.trans hh)).2 v hv'
    have hb : (Batt.rowOf (r :: l) o).g.isEmpty = false := by
      cases hg : (Batt.rowOf (r :: l) o).g with
      | nil =>
        rw [hg] at hm
        cases hm
      | cons _ _ => rfl
    show (⟨_, _, _, _⟩ : RowSh) = ⟨_, _, _, _⟩
    rw [hb, hm, e2, e3]
    show (⟨false, some h, _, _⟩ : RowSh) =
      ⟨(rowSh r).bare && (l.map rowSh).all (·.bare), (rowSh r).vars, _, _⟩
    rw [(hall r (List.mem_cons_self ..)).1, hh]
    rfl

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.mark_iff
#print axioms VerifiableInference.Desc.K13.Honest.flatMap_zip_fst
#print axioms VerifiableInference.Desc.K13.Honest.flatMap_zip_snd
#print axioms VerifiableInference.Desc.K13.Honest.map_fst_zip'
#print axioms VerifiableInference.Desc.K13.Honest.walkOf_length
#print axioms VerifiableInference.Desc.K13.Honest.rowSh_rowOf
