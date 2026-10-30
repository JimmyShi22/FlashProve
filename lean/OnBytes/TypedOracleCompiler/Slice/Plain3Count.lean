-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Plain3Count.lean.
TWO: CUT OVER THE SIBLING's RD (a list of trees a round) after a file of this project that is not in
this library; the head below is that file's, to the letter but for the paths of files that are not
in this library; a wiring IS given: Plain3Wire.lean.

A file of this project that is not in this library: how many positions the protocol in three
stretches reads.

The library's laws of a wiring (Iop/BatchWire.lean: `ProtocolQueryLayout.OKG`, the clause `opens`) ask for a
number that bounds the positions read in the prover's oracles and in the external string together.
For `Plain3 G dec` (here OnBytes/TypedOracleCompiler/Slice/Plain3.lean's; the head's own file is not in this
library) such a number is the sum over the three stretches of
the library's own two counts: for each round its number of drawn positions times the number of trees
that it opens (Run/PlanQWire.lean: `nOpen`), and for each opening of the stored table the number of
draws that it says.

Asked: what was drawn in a round holds at most the entry's number of positions
(Run/PlanQWireLaws.lean: `DrawnFits`), in each stretch. Nothing is asked of keys or of trees'
numbers, since a request is the stored table's or a tree's by its form.

Main definition: `Stretches.nOpen`.
Main theorems: `asksL_own_len`, `asksL_ext_len` (one stretch), `plain3_opens`.

Not claimed. No wiring is given. The bound is not shown to be reached.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Plain3
import Run.PlanQXLawsProofs

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open _root_.Iop TypedOracleCompiler.Run

/-! ## Tools on lists -/

theorem flat_len {α β : Type} (F : α → List β) (n : ℕ) :
    ∀ l : List α, (∀ t ∈ l, (F t).length ≤ n) → (l.flatMap F).length ≤ n * l.length
  | [], _ => Nat.zero_le _
  | t :: l, h => by
      rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ, Nat.add_comm]
      exact Nat.add_le_add (flat_len F n l fun u hu => h u (List.mem_cons_of_mem _ hu))
        (h t List.mem_cons_self)

theorem flat_sum {β : Type} (F : PQ.XO → List β) (h : ∀ o, (F o).length ≤ o.count) :
    ∀ L : List PQ.XO, (L.flatMap F).length ≤ (L.map (·.count)).sum
  | [] => Nat.le_refl 0
  | o :: L => by
      rw [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h o) (flat_sum F h L)

theorem filterMap_flat_nil {α β γ : Type} (f : β → Option γ) (F : α → List β) (l : List α)
    (h : ∀ t ∈ l, ∀ q ∈ F t, f q = none) : (l.flatMap F).filterMap f = [] :=
  List.filterMap_eq_nil_iff.2 fun q hq => by
    obtain ⟨t, ht, hm⟩ := List.mem_flatMap.1 hq
    exact h t ht q hm

/-! ## One stretch -/

section
variable (a : ℕ) (all : List PQ.RD) (xs : List PQ.XO)

/-- The requests for trees' positions: at most, for each round, its number of positions times the
number of trees that it opens. f: any function that keeps no request for the stored table. -/
theorem asksL_own_len {β : Type} (f : Ask → Option β) (hf : ∀ k x, f (Ask.stored k x) = none)
    (C : PQ.CK) :
    ∀ (i : ℕ) (ds : List PQ.RD), PQ.DrawnFits C ds → ∀ ρ : Rho (PQ.uL C ds),
      ((asksL a all xs i ds (PQ.drawnSL C ds ρ)).filterMap f).length ≤ PQ.nOpen ds
  | _, [], _, _ => Nat.zero_le _
  | i, d :: ds, h, (c, ρ) => by
      show ((asksL a all xs i (d :: ds)
          (C.dr d.entry d.kind (GChal.old (b := d.entry.work) c) :: PQ.drawnSL C ds ρ)).filterMap
            f).length ≤
        (d.entry.poss * d.opens.length :: ds.map fun d => d.entry.poss * d.opens.length).sum
      rw [asksL, List.filterMap_append, List.filterMap_append,
        filterMap_flat_nil f _ (PQ.xsAt xs i) ?_, List.nil_append, List.length_append,
        List.sum_cons]
      · refine Nat.add_le_add
          (le_trans (List.length_filterMap_le _ _) (flat_len _ _ d.opens fun t _ => ?_))
          (asksL_own_len f hf C (i + 1) ds (fun e he => h e (List.mem_cons_of_mem _ he)) ρ)
        split
        · exact Nat.zero_le _
        · rw [List.length_map]
          exact le_trans (Fmt.listOf_len _)
            (by rw [List.length_map]; exact h d List.mem_cons_self _)
      · intro o _ q hq
        obtain ⟨x, _, rfl⟩ := List.mem_map.1 hq
        exact hf _ _

/-- The requests for the stored table's positions, from round i on: at most what the openings from
round i on say. g: any function that keeps no request for a tree. -/
theorem asksL_ext_len {γ : Type} (g : Ask → Option γ) (hg : ∀ n x, g (Ask.own n x) = none) :
    ∀ (i : ℕ) (ds : List PQ.RD) (Ds : List Fmt.Drawn),
      ((asksL a all xs i ds Ds).filterMap g).length ≤
        ((xs.filter fun o => decide (i ≤ o.round)).map (·.count)).sum
  | _, [], _ => by simp [asksL]
  | _, _ :: _, [] => by simp [asksL]
  | i, d :: ds, D :: Ds => by
      rw [asksL, List.filterMap_append, List.filterMap_append,
        filterMap_flat_nil g _ d.opens ?_, List.append_nil, List.length_append, PQ.sum_split i xs]
      · refine Nat.add_le_add
          (le_trans (List.length_filterMap_le _ _) (flat_sum _ (fun o => ?_) _))
          (asksL_ext_len g hg (i + 1) ds Ds)
        rw [List.length_map]
        exact PQ.list_len a o D
      · intro n _ q hq
        split at hq
        · cases hq
        · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hq
          exact hg _ _

/-- The same for a whole stretch. -/
theorem asksL_ext_len0 {γ : Type} (g : Ask → Option γ) (hg : ∀ n x, g (Ask.own n x) = none)
    (ds : List PQ.RD) (Ds : List Fmt.Drawn) :
    ((asksL a all xs 0 ds Ds).filterMap g).length ≤ (xs.map (·.count)).sum := by
  have h := asksL_ext_len a all xs g hg 0 ds Ds
  rw [List.filter_eq_self.2 fun o _ => decide_eq_true (Nat.zero_le _)] at h
  exact h

end

/-! ## Three stretches -/

/-- A bound on the number of positions read: the library's two counts, over the three stretches. -/
def Stretches.nOpen (G : Stretches) : ℕ :=
  PQ.nOpen G.ds₁ + (PQ.nOpen G.ds₂ + PQ.nOpen G.ds₃) +
    ((G.xs₁.map (·.count)).sum + ((G.xs₂.map (·.count)).sum + (G.xs₃.map (·.count)).sum))

/-- The protocol reads at most `G.nOpen` positions, in the prover's oracles and the stored table
together: the clause `opens` of the laws of a wiring, at that number. -/
theorem plain3_opens (G : Stretches) (dec : PQ.View → PQ.View → PQ.View → Bool)
    (h₁ : PQ.DrawnFits G.C G.ds₁) (h₂ : PQ.DrawnFits G.C G.ds₂) (h₃ : PQ.DrawnFits G.C G.ds₃)
    (x : Unit) (ρ : Rho G.sh) (pl : Plains G.sh) :
    ((Plain3 G dec).reads x ρ pl).card + ((Plain3 G dec).extReads x ρ).card ≤ G.nOpen := by
  have ho : ∀ k z, G.own (Ask.stored k z) = none := fun _ _ => rfl
  have hx : ∀ n z, Ask.ext G.a (Ask.own n z) = none := fun _ _ => rfl
  refine Nat.add_le_add (le_trans (List.toFinset_card_le _) ?_)
    (le_trans (List.toFinset_card_le _) ?_)
  · unfold Stretches.asksAt
    rw [List.filterMap_append, List.filterMap_append, List.length_append, List.length_append]
    exact Nat.add_le_add (asksL_own_len G.a G.all G.xs₁ G.own ho G.C 0 G.ds₁ h₁ _)
      (Nat.add_le_add (asksL_own_len G.a G.all G.xs₂ G.own ho G.C 0 G.ds₂ h₂ _)
        (asksL_own_len G.a G.all G.xs₃ G.own ho G.C 0 G.ds₃ h₃ _))
  · unfold Stretches.asksAt
    rw [List.filterMap_append, List.filterMap_append, List.length_append, List.length_append]
    exact Nat.add_le_add (asksL_ext_len0 G.a G.all G.xs₁ _ hx G.ds₁ _)
      (Nat.add_le_add (asksL_ext_len0 G.a G.all G.xs₂ _ hx G.ds₂ _)
        (asksL_ext_len0 G.a G.all G.xs₃ _ hx G.ds₃ _))

end TypedOracleCompiler.Slice
