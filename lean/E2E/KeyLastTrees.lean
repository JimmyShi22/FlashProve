-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastTrees.lean: the trees that a file's last chain takes over, at the door: the last thread's table of such a tree
is the table of the chain that sent it, so the clause on trees at the chain's first border follows from the two earlier
threads' clauses on trees at their last borders. General in the threads.

Main names.
  `tableLast`: the last thread's tables: a tree taken from chain 0 or 1 is that chain's own; any other source is `own`.
  `take_app`: a cut of two lists joined.
  `taken_trees`: the premise `htrees` of a door.

What stays open. `hmem`: that each tree taken over is one that the sending chain's thread holds at its last border: a fact
on public numbers, at the key file the closed lines on the own test's rounds and the chains' counts of trees.
Nothing here says that a thread stands.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyThreadBase
import Johnson.Desc.ProofFile.Honest.Law.Thread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest
open VerifiableInference.Desc (Place FileDescription)
open AtPublicFiles.KeyThread (decl₁ decl₂ sentIn sentIn_le fixedLast)

theorem take_app {α : Type} (a b : List α) (j : Nat) : (a ++ b).take (a.length + j) = a ++ b.take j := by
  induction a with
  | nil => simp
  | cons z zs ih =>
    have e : (z :: zs).length + j = (zs.length + j) + 1 := by
      simp only [List.length_cons]
      omega
    rw [e, List.cons_append, List.take_succ_cons, ih, List.cons_append]

section
variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} (F : FileDescription Xi)
  (cm : Local W₀ Rc Xi Tr → Common W₀ Rc Ky)

/-- **The last thread's tables.** -/
def tableLast (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Place × Table)
    (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc Ky → List Fmt.Drawn → Place × Table)
    (own : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Place × Table) :
    Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Place × Table := fun σ k v h =>
  match σ with
  | .taken c j =>
    if c == 0 then tb₁ (.own j) k v h
    else if c == 1 then tb₂ (.own j) k (cm v) (h.drop (decl₁ F).length)
    else own σ k v h
  | .own j => own (.own j) k v h

variable {F} (T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
  (T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
  (T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)

/-- **The trees taken over are at hand at the last chain's first border.** n₁, n₂: the two last borders. -/
theorem taken_trees (own : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Place × Table)
    (hT : T₃.table = tableLast F cm T₁.table T₂.table own)
    (hf₁ : ∀ j, T₁.fixed (.own j) = sentIn (decl₁ F) j) (hf₂ : ∀ j, T₂.fixed (.own j) = sentIn (decl₂ F) j)
    (hf₃ : T₃.fixed = fixedLast F) {n₁ n₂ : Nat}
    (hmem : ∀ σ ∈ T₃.taken, (∃ j, σ = .taken 0 j ∧ Fmt.TreeSource.own j ∈ T₁.hand n₁) ∨
      (∃ j, σ = .taken 1 j ∧ Fmt.TreeSource.own j ∈ T₂.hand n₂))
    {k : Coins Bk} {e₁ : F.S₁} {m₁ : Mid (Local W₀ Rc Xi Tr) X} {E₁ : Env} {e₂ : F.S₂}
    {m₂ : Mid (Common W₀ Rc Ky) X₀} {E₂ : Env} (m₃ : Mid (Local W₀ Rc Xi Tr) X)
    (u₁ : Thr T₁ n₁ k e₁ m₁ E₁) (u₂ : Thr T₂ n₂ k e₂ m₂ E₂)
    (i₁ : m₃.st.input = m₁.st.input) (i₂ : m₂.st.input = cm m₃.st.input)
    (hh : m₃.st.heard = m₁.st.heard ++ m₂.st.heard) (l₁ : m₁.st.heard.length = (decl₁ F).length) :
    T₃.Trees T₃.taken k m₃ (envThird E₁ E₂) := by
  intro σ hσ
  rcases hmem σ hσ with ⟨j, rfl, hj⟩ | ⟨j, rfl, hj⟩
  · have a := u₁.1.2 (.own j) hj
    have eb : T₃.tableAt (.taken 0 j) k m₃ = T₁.tableAt (.own j) k m₁ := by
      unfold Thread.tableAt
      rw [hT, hf₃, i₁, hh, hf₁]
      show T₁.table (.own j) k m₁.st.input ((m₁.st.heard ++ m₂.st.heard).take (sentIn (decl₁ F) j)) = _
      rw [List.take_append_of_le_length (by rw [l₁]; exact sentIn_le _ _)]
    unfold Thread.handAt at a ⊢
    rw [eb]
    exact a
  · have a := u₂.1.2 (.own j) hj
    have eb : T₃.tableAt (.taken 1 j) k m₃ = T₂.tableAt (.own j) k m₂ := by
      unfold Thread.tableAt
      rw [hT, hf₃, hh, hf₂, i₂]
      show T₂.table (.own j) k (cm m₃.st.input)
        (((m₁.st.heard ++ m₂.st.heard).take ((decl₁ F).length + sentIn (decl₂ F) j)).drop (decl₁ F).length) = _
      rw [← l₁, take_app, List.drop_left' rfl]
    unfold Thread.handAt at a ⊢
    rw [eb]
    exact a

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.take_app
#print axioms AtPublicFiles.KeyLastChain.taken_trees
