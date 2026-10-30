-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.PubOk
import OnBytes.Maker.Stage
/-
Johnson/Desc/K12/Law/DataOf.lean: A STRETCH's DATA MADE BY HAND OFF A PLAN: the written rounds of a proximity test (the kind K12), each with its declared round's openings under a numbering of the sources, as the maker's rounds' data (RDT); and lemmas on lists. Definitions, statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  rdtOf num w r: entry · kind · items: the written round's; trees: its tree, if any; opens: the declared round's openings by num; no stored table.
  dataOf num ws rs: round by round.
  like_dataOf: the data are like the written rounds, field by field (the text of the coin's Like, unfolded by hand).
  treeW ws n · treeSh_dataOf: the stretch's n-th own tree is the n-th tree of the written rounds: whatever num.
  flat_of: a tool on lists for the wants at a round's openings.
THESE DATA ARE NO DESCRIPTION's: that a description's stretch at the block has just these data is not shown.

-/
set_option autoImplicit false
namespace H2K.Member
open OnBytes.Maker
open H2K.Pub (WR)

def rdtOf (num : Fmt.TreeSource → ℕ) (w : WR) (r : Fmt.DeclaredRound) : RDT :=
  ⟨⟨w.entry, w.kind, w.items, w.tree.toList, r.opens.map fun o => num o.2⟩, []⟩

def dataOf (num : Fmt.TreeSource → ℕ) : List WR → List Fmt.DeclaredRound → List RDT
  | w :: ws, r :: rs => rdtOf num w r :: dataOf num ws rs
  | _, _ => []

theorem like_dataOf (num : Fmt.TreeSource → ℕ) : ∀ (ws : List WR) (rs : List Fmt.DeclaredRound),
    ws.length = rs.length →
    List.Forall₂ (fun (d : RDT) (w : WR) => d.entry = w.entry ∧ d.kind = w.kind ∧
      d.items = w.items ∧ d.trees = w.tree.toList ∧ d.stored = []) (dataOf num ws rs) ws
  | [], [], _ => .nil
  | _ :: ws, _ :: rs, h =>
    .cons ⟨rfl, rfl, rfl, rfl, rfl⟩ (like_dataOf num ws rs (Nat.succ.inj h))
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

/-- The n-th tree that the written rounds send. -/
def treeW : List WR → ℕ → Option Fmt.Shape
  | [], _ => none
  | w :: ws, n => if n < w.tree.toList.length then w.tree.toList[n]? else
      treeW ws (n - w.tree.toList.length)

theorem treeSh_dataOf (num : Fmt.TreeSource → ℕ) : ∀ (ws : List WR) (rs : List Fmt.DeclaredRound) (n : ℕ),
    ws.length = rs.length → treeShT (dataOf num ws rs) n = treeW ws n
  | [], [], _, _ => rfl
  | w :: ws, r :: rs, n, h => by
    show (if n < w.tree.toList.length then w.tree.toList[n]? else
      treeShT (dataOf num ws rs) (n - w.tree.toList.length)) = _
    rw [treeSh_dataOf num ws rs _ (Nat.succ.inj h)]
    rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h

theorem flat_of {α : Type} (F : ℕ → List α) (G : Fmt.Shape × Fmt.TreeSource → List α)
    (num : Fmt.TreeSource → ℕ) : ∀ (os : List (Fmt.Shape × Fmt.TreeSource)),
    (∀ o ∈ os, F (num o.2) = G o) → (os.map fun o => num o.2).flatMap F = os.flatMap G
  | [], _ => rfl
  | o :: os, h => by
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, h o (List.mem_cons_self ..),
      flat_of F G num os fun o' h' => h o' (List.mem_cons_of_mem _ h')]

end H2K.Member

#print axioms H2K.Member.like_dataOf
#print axioms H2K.Member.treeSh_dataOf
#print axioms H2K.Member.flat_of
