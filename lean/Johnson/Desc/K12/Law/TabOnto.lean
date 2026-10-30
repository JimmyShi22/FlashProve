-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.ViewK
/-
Johnson/Desc/K12/Law/TabOnto.lean: TWO GENERIC PIECES FOR «THE VIEW's COLUMNS ARE COLUMNS OF TABLES»: neither touches the plan. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  lookup_of_mem   in a list of pairs that is functional (one key, one value) the look-up at a member's key finds its value
  ofFn_getD       a list of n words is List.ofFn of its own words
  table_onto      (T0) A TABLE FOR ONE TREE: columns (position, words) that are functional, each at a position below the written tree's size and as wide as its columns ⇒ ∃ o : (wRound d).Orc, every one of them is colW d o at its position (zeros elsewhere)
  cols_from · cols_of_follows   (T1) FROM «Follows» BACK TO THE COLUMNS: columns whose key, position and width are the wanted ones (Block.step's second test), and which, laid into groups, follow src, ARE colsOf groups src: the converse of follows_colsOf with kpw_colsOf (Johnson/Desc/K12/Law/ViewK.lean)
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Slice _root_.Run
open VerifiableInference.Desc
open H2K.Sw (Want kpw)

theorem lookup_of_mem {β : Type} : ∀ (l : List (ℕ × β)),
    (∀ x ∈ l, ∀ y ∈ l, x.1 = y.1 → x.2 = y.2) → ∀ x ∈ l, l.lookup x.1 = some x.2
  | [], _, _, hx => nomatch hx
  | (k, v) :: l, hf, x, hx => by
    by_cases hk : x.1 = k
    · rw [hk, List.lookup_cons_self]
      exact congrArg some (hf (k, v) List.mem_cons_self x hx hk.symm)
    · have hx' : x ∈ l := by
        rcases List.mem_cons.1 hx with rfl | h
        · exact absurd rfl hk
        · exact h
      have hb : (x.1 == k) = false := by simpa using hk
      rw [List.lookup_cons, hb]
      exact lookup_of_mem l (fun a ha b hb => hf a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb)) x hx'

theorem ofFn_getD (n : ℕ) (v : List UInt64) (h : v.length = n) :
    (List.ofFn fun j : Fin n => v.getD j.val 0) = v := by
  subst h
  have : (fun j : Fin v.length => v.getD j.val 0) = v.get := funext fun j => by
    rw [List.getD_eq_getElem _ _ j.isLt]
    rfl
  rw [this, List.ofFn_get]

/-- (T0) -/
theorem table_onto (d : PQ.RD) (grp : List (ℕ × List UInt64))
    (hf : ∀ x ∈ grp, ∀ y ∈ grp, x.1 = y.1 → x.2 = y.2)
    (hp : ∀ x ∈ grp, x.1 < PQ.posN d.tree) (hw : ∀ x ∈ grp, x.2.length = PQ.colW d.tree) :
    ∃ o : (wRound d).Orc, ∀ x ∈ grp, x.2 = colW d o x.1 := by
  refine ⟨fun i j => ((grp.lookup i.val).getD []).getD j.val 0, fun x hx => ?_⟩
  unfold colW
  rw [dif_pos (hp x hx)]
  show x.2 = List.ofFn fun j : Fin (PQ.colW d.tree) => ((grp.lookup x.1).getD []).getD j.val 0
  rw [lookup_of_mem grp hf x hx, Option.getD_some, ofFn_getD _ _ (hw x hx)]

theorem cols_from (src : ℕ → ℕ → List UInt64) : ∀ (groups : List (List Want)) (n : ℕ)
    (cs : List OpenedColumn), cs.map kpw = groups.flatMap id →
    (∀ (i : ℕ) (grp : List (ℕ × List UInt64)),
      (regroup (groups.map (·.length)) cs)[i]? = some grp → ∀ x ∈ grp, x.2 = src (n + i) x.1) →
    cs = colsFrom n groups src
  | [], _, cs, hk, _ => by
    have : cs = [] := List.map_eq_nil_iff.1 hk
    rw [this]
    rfl
  | g :: gs, n, cs, hk, hf => by
    rw [colsFrom_cons]
    rw [List.flatMap_cons] at hk
    have hlen : g.length ≤ cs.length := by
      have := congrArg List.length hk
      rw [List.length_map, List.length_append] at this
      show (id g).length ≤ _
      omega
    have h1 : (cs.take g.length).map kpw = g := by
      have := congrArg (List.take g.length) hk
      rw [← List.map_take] at this
      rw [this]
      exact List.take_left' rfl
    have h2 : (cs.drop g.length).map kpw = gs.flatMap id := by
      have := congrArg (List.drop g.length) hk
      rw [← List.map_drop] at this
      rw [this]
      exact List.drop_left' rfl
    have e0 : ∀ c ∈ cs.take g.length, c.2.2 = src n c.2.1 := fun c hc =>
      hf 0 ((cs.take g.length).map fun c => (c.2.1, c.2.2)) rfl (c.2.1, c.2.2)
        (List.mem_map.2 ⟨c, hc, rfl⟩)
    have a1 : cs.take g.length = g.map fun w => (w.1, w.2.1, src n w.2.1) := by
      conv_rhs => rw [← h1, List.map_map]
      conv_lhs => rw [← List.map_id (cs.take g.length)]
      refine List.map_congr_left fun c hc => ?_
      show c = (c.1, c.2.1, src n c.2.1)
      rw [← e0 c hc]
    have a2 : cs.drop g.length = colsFrom (n + 1) gs src :=
      cols_from src gs (n + 1) (cs.drop g.length) h2 fun i grp hi x hx => by
        have := hf (i + 1) grp hi x hx
        rwa [show n + (i + 1) = n + 1 + i by omega] at this
    rw [← a1, ← a2, List.take_append_drop]

/-- (T1) -/
theorem cols_of_follows (groups : List (List Want)) (src : ℕ → ℕ → List UInt64) (cs : List OpenedColumn)
    (hk : cs.map kpw = groups.flatMap id)
    (hf : Follows (regroup (groups.map (·.length)) cs) src) : cs = colsOf groups src := by
  rw [colsOf_eq]
  exact cols_from src groups 0 cs hk fun i grp hi x hx => by
    rw [Nat.zero_add]
    exact hf i grp hi x hx

end H2K.JointK

#print axioms H2K.JointK.table_onto
#print axioms H2K.JointK.cols_of_follows
