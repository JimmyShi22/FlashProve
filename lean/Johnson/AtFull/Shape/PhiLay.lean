-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/PhiLay.lean: THE WEIGHTS OF THE TABLES OF A LAYERS' LINK HAVE AS MANY ENTRIES AS A RUN HAS ROWS. funsOf
(OnBytes/Model/Layer.lean) makes each table's weights by phiOf; phiOf tests the length of a named point. What is public: la = ls + lt,
T = 2 ^ lt. What the lookup heard: the lengths of zb0 and zb1.

  asks_cases       what each family of tableAsks is: one of the three on matrix b, or a family with a named point.
  phiOf_size       phiOf's answer is as long as the family's run.
  funsOf_sizes     so of every table that funsOf makes.

Limits. The premises on the layout and on the lookup's points stay here. Nothing on soundness, completeness or hiding.
-/
import Johnson.Road.FormsKeysEq
import Johnson.Desc.Reads.FoldAll
import OnBytes.Desc.First.K4.HearPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Phi
open OnBytes OnBytes.Model OnBytes.Model.Layer

theorem name_ne {p n t : String} {c d : Char} {u v : List Char} (hp : p.toList = c :: u)
    (ht : t.toList = d :: v) (hc : c ≠ d) : p ++ n ≠ t := by
  intro e
  have := congrArg String.toList e
  rw [String.toList_append, hp, ht] at this
  simp at this
  exact hc this.1

/-- A family with a named point. -/
def Named (y : Lay) (a : TableAsk) : Prop :=
  a.name ≠ "b-bits-0" ∧ a.name ≠ "b-bits-1" ∧ a.name ≠ "b-pin" ∧
    a.L = if a.lng then 2 ^ y.h.la else y.T

theorem named_of {y : Lay} {a : TableAsk} {mn : String} {M0 parts Lv : Nat} {pts : List String}
    {lng : Bool} {c : Char} {u : List Char} (hm : mn.toList = c :: u) (hc : c ≠ 'b')
    (hv : Lv = if lng then 2 ^ y.h.la else y.T)
    (h : a ∈ pts.map fun n => (⟨mn ++ "@" ++ n, M0, parts, Lv, n, lng⟩ : TableAsk)) :
    Named y a := by
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 h
  have hm' : (mn ++ "@").toList = c :: (u ++ ['@']) := by
    rw [String.toList_append, hm]
    rfl
  exact ⟨name_ne hm' rfl hc, name_ne hm' rfl hc, name_ne hm' rfl hc, hv⟩

/-- What a family of tableAsks is. -/
theorem asks_cases {y : Lay} {rd : Reads} {g : Nat} {a : TableAsk} (h : a ∈ tableAsks y rd g) :
    (a.name = "b-bits-0" ∧ a.L = 2 ^ y.h.lmb) ∨ (a.name = "b-bits-1" ∧ a.L = 2 ^ y.h.lmb) ∨
      (a.name = "b-pin" ∧ a.L = 2 ^ y.h.lmb) ∨ Named y a := by
  unfold tableAsks at h
  dsimp only at h
  simp only [List.mem_append] at h
  rcases h with (((((((h | h) | h) | h) | h) | h) | h) | h) | h
  · exact Or.inr (Or.inr (Or.inr (named_of (c := 'a') (u := ['f']) rfl (by decide) (by simp) h)))
  · exact Or.inr (Or.inr (Or.inr (named_of (c := 'q') (u := ['a']) rfl (by decide) (by simp) h)))
  · exact Or.inr (Or.inr (Or.inr (named_of (c := 'x') (u := ['b', 'I']) rfl (by decide) (by simp) h)))
  · split at h
    · exact Or.inr (Or.inr (Or.inr (named_of (c := 'x') (u := ['b', 'I']) rfl (by decide) (by simp) h)))
    · cases h
  · exact Or.inr (Or.inr (Or.inr (named_of (c := 'x') (u := ['b', 'O']) rfl (by decide) (by simp) h)))
  · exact Or.inr (Or.inr (Or.inr (named_of (c := 'a') (u := ['d']) rfl (by decide) (by simp) h)))
  · exact Or.inr (Or.inr (Or.inr (named_of (c := 'a') (u := ['r']) rfl (by decide) (by simp) h)))
  · split at h
    · exact Or.inr (Or.inr (Or.inr (named_of (c := 'q') (u := ['a']) rfl (by decide) (by simp) h)))
    · cases h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

/-- A family on the bits: the weights by the point on the bits. -/
theorem phiB_size {fo : Forest.Heard} {lm e : Nat} {phi : Array E}
    (hz : (fo.zb e).size = 5 + (fo.shape.kT + fo.shape.cK)) (h : Forest.phiB fo lm e = some phi) :
    phi.size = 2 ^ lm := by
  unfold Forest.phiB at h
  dsimp only at h
  split at h
  · rename_i hc
    cases h
    have hb : ¬ (lm < 5 ∨ lm > fo.shape.kT + 5) := by
      intro hn
      unfold Forest.planeCols at hc
      have hn' : (decide (lm < 5) || decide (lm > fo.shape.kT + 5)) = true := by simpa using hn
      rw [if_pos hn'] at hc
      cases hc
    rw [OnBytes.Road.eqTab_size, Array.size_append, Array.size_extract, Array.size_extract, hz]
    congr 1
    omega
  · cases h

/-- **phiOf's answer is as long as the family's run.** -/
theorem phiOf_size {y : Lay} {rd : Reads} {g : Nat} {fo : Forest.Heard}
    {pt : List (String × Array E)} {a : TableAsk} {phi : Array E}
    (hT : y.T = 2 ^ y.h.lt) (hL : y.ls + y.h.lt = y.h.la)
    (h0 : (fo.zb 0).size = 5 + (fo.shape.kT + fo.shape.cK))
    (h1 : (fo.zb 1).size = 5 + (fo.shape.kT + fo.shape.cK))
    (ha : a ∈ tableAsks y rd g) (h : phiOf y fo pt a = some phi) : phi.size = a.L := by
  rcases asks_cases ha with ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩ | ⟨n0, n1, n2, l⟩
  · unfold phiOf at h
    rw [e] at h
    simp only [beq_self_eq_true, if_true] at h
    rw [l]
    exact phiB_size h0 h
  · unfold phiOf at h
    rw [e] at h
    simp at h
    rw [l]
    exact phiB_size h1 h
  · unfold phiOf at h
    rw [e] at h
    simp at h
    subst h
    rw [l]
    simp [Forest.phiP]
  · unfold phiOf at h
    have b0 : (a.name == "b-bits-0") = false := by simpa using n0
    have b1 : (a.name == "b-bits-1") = false := by simpa using n1
    have b2 : (a.name == "b-pin") = false := by simpa using n2
    rw [b0, b1, b2] at h
    simp only [Bool.false_eq_true, if_false] at h
    cases hf : pt.find? (fun p => p.1 == a.point) with
    | none =>
      rw [hf] at h
      cases h
    | some p =>
      rw [hf] at h
      dsimp only at h
      cases hl : a.lng with
      | true =>
        rw [hl] at h l
        by_cases hs : p.2.size = y.h.la
        · simp only [if_true, hs, bne_self_eq_false, Bool.false_eq_true, if_false, Option.some.injEq] at h l
          subst h
          rw [l]
          show (blockRows _ _).size = _
          rw [VerifiableInference.Reads.blockRows_size, OnBytes.Road.eqTab_size, OnBytes.Road.eqTab_size,
            Array.size_extract, Array.size_extract, hs, ← Nat.pow_add]
          congr 1
          omega
        · have hb : (p.2.size != y.h.la) = true := by simpa using hs
          simp [hb] at h
      | false =>
        rw [hl] at h l
        by_cases hs : p.2.size = y.h.lt
        · simp only [Bool.false_eq_true, if_false, hs, bne_self_eq_false, Option.some.injEq] at h l
          subst h
          rw [l, OnBytes.Road.eqTab_size, hs, hT]
        · have hb : (p.2.size != y.h.lt) = true := by simpa using hs
          simp [hb] at h

/-- A family that layTables places is one of the asked. -/
theorem laid_mem {mats : Array (Nat × Nat)} : ∀ {asks : List TableAsk} {p : Nat}
    {tab : List TableAt} {laid : List (TableAsk × List (Nat × Nat))} {n : Nat},
    layTables mats asks p = some (tab, laid, n) → ∀ x ∈ laid, x.1 ∈ asks
  | [], _, _, _, _, h, x, hx => by
    simp only [layTables, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    cases hx
  | a :: rest, p, tab, laid, n, h, x, hx => by
    unfold layTables at h
    dsimp only at h
    split at h
    · cases h
    · obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at e
      obtain ⟨-, rfl, -⟩ := e
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (laid_mem (p := _) (tab := r.1) (laid := r.2.1) (n := r.2.2) hr x hx')

/-- Of every table that funsOf makes: its weights are what phiOf gave to one family laid, its length that family's. -/
theorem funs_of_laid {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)} :
    ∀ {laid : List (TableAsk × List (Nat × Nat))} {l : List (List HFun)},
      (laid.mapM fun x => do
        let phi ← phiOf y fo pt x.1
        pure (x.2.map fun m => ({ mat := m.1, len := x.1.L, phi, tree := 2, start := m.2 } : HFun))) = some l →
      ∀ Fn ∈ l.flatten, ∃ x ∈ laid, phiOf y fo pt x.1 = some Fn.phi ∧ Fn.len = x.1.L
  | [], l, h, Fn, hF => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    cases hF
  | x :: rest, l, h, Fn, hF => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨b, ⟨phi, hp, rfl⟩, l', hl', rfl⟩ := h
    rw [List.flatten_cons] at hF
    rcases List.mem_append.1 hF with hF | hF
    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 hF
      exact ⟨x, List.mem_cons_self, hp, rfl⟩
    · obtain ⟨z, hz, e⟩ := funs_of_laid hl' Fn hF
      exact ⟨z, List.mem_cons_of_mem _ hz, e⟩

/-- **Of every table that funsOf makes at the families of a layers' link.** -/
theorem funsOf_sizes {y : Lay} {rd : Reads} {g : Nat} {fo : Forest.Heard}
    {pt : List (String × Array E)} {mats : Array (Nat × Nat)} {tab : List TableAt}
    {laid : List (TableAsk × List (Nat × Nat))} {n : Nat} {funs : Array HFun}
    (hT : y.T = 2 ^ y.h.lt) (hL : y.ls + y.h.lt = y.h.la)
    (h0 : (fo.zb 0).size = 5 + (fo.shape.kT + fo.shape.cK))
    (h1 : (fo.zb 1).size = 5 + (fo.shape.kT + fo.shape.cK))
    (ht : layTables mats (tableAsks y rd g) 0 = some (tab, laid, n))
    (hf : funsOf y fo pt laid = some funs) : ∀ Fn ∈ funs.toList, Fn.phi.size = Fn.len := by
  intro Fn hF
  unfold funsOf at hf
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hf
  obtain ⟨l, hl, rfl⟩ := hf
  have hm : Fn ∈ l.flatten := by simpa using hF
  obtain ⟨x, hx, e, el⟩ := funs_of_laid hl Fn hm
  rw [el]
  exact phiOf_size hT hL h0 h1 (laid_mem ht x hx) e

end Johnson.AtFull.Shape.Phi

#print axioms Johnson.AtFull.Shape.Phi.asks_cases
#print axioms Johnson.AtFull.Shape.Phi.phiB_size
#print axioms Johnson.AtFull.Shape.Phi.phiOf_size
#print axioms Johnson.AtFull.Shape.Phi.laid_mem
#print axioms Johnson.AtFull.Shape.Phi.funs_of_laid
#print axioms Johnson.AtFull.Shape.Phi.funsOf_sizes
