-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LastTerm.lean: what the last chain's thread (`lettersLast`,
Honest/Thread/LastHead.lean) lays at its fields on trees: the sources taken over, the tables and the
counts, as terms over the two earlier threads' own; and the premise `tk` of `trees_taken_of`
(Honest/Thread/Door.lean) at these terms. General in the threads and in the job.

  `lastTable`, `lastFixed`, `ownLast` stand in WLaidDefs.lean
  `lastTable_first`, `lastTable_shared`   at the second chain's start, a taken tree's table is the table
                 that the earlier thread reads at its own end
  `taken_at_door`   so `tk` of `trees_taken_of`, at the three sources `takenLast`

Why the shared arm drops r₁ challenges. The last chain hears the first chain's challenges, then the
shared chain's (`Ready.start₃`, Honest/Frame.lean): a shared tree's table reads the shared chain's alone.

The premises of `taken_at_door`. hi₁, hi₂: the earlier chains' ends read the run's own input: R.own, and
toCommon of it. hl: the first chain has heard r₁ challenges. hf: a first chain's tree is fixed by them.
hh₁, hh₂: the trees are in hand at the earlier ends: `trees_first` (OpensFirstLine.lean) and
`trees_shared` (TableLines.lean) are the counts at the written lists.

Limits.
- Of `lettersLast`'s letters these are three: wit, Mg, ML, PL, order, ends and the counts n₁, n₂ stay
  letters.
- That own is `ownLast` of the job that the filling lays is for whoever lays the thread.
- `ownLast` names a text of a test's tree: the head of K12/ScriptLots.lean binds it.
- NOT IN FRONT OF A LAW OVER COINS: `taken_at_door` stands behind what the two threads hold of a run.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TableLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLaidDefs
import Johnson.Desc.ProofFile.Honest.Thread.Door

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open VerifiableInference.Desc (FileDescription Place)
open ProofFile.Honest.K12 (TestJob testTbl)

section
variable {Bk : ProverCoinCounts} {W₃ W₂ : Type}

/-- A take that stops inside the first list. -/
theorem take_append_within {α : Type} : ∀ (a b : List α) (n : ℕ), n ≤ a.length →
    (a ++ b).take n = a.take n
  | _, _, 0, _ => by simp
  | [], _, _ + 1, h => by simp at h
  | x :: a, b, n + 1, h => by
    simp only [List.cons_append, List.take_succ_cons]
    rw [take_append_within a b n (by simpa using h)]

/-- What stands behind the first list, of a take that reaches past it. -/
theorem drop_take_append {α : Type} : ∀ (a b : List α) (m : ℕ),
    ((a ++ b).take (a.length + m)).drop a.length = b.take m
  | [], b, m => by simp
  | x :: a, b, m => by
    have e : (x :: a).length + m = (a.length + m) + 1 := by
      simp only [List.length_cons]
      omega
    rw [List.cons_append, e, List.take_succ_cons, List.length_cons, List.drop_succ_cons]
    exact drop_take_append a b m

theorem lastTable_first (r₁ : ℕ) (toCommon : W₃ → W₂)
    (tb₁ : Fmt.TreeSource → Coins Bk → W₃ → List Fmt.Drawn → Place × Table)
    (tb₂ : Fmt.TreeSource → Coins Bk → W₂ → List Fmt.Drawn → Place × Table)
    (own : ℕ → Coins Bk → W₃ → List Fmt.Drawn → Place × Table) (fx₁ fx₂ : Fmt.TreeSource → ℕ)
    (ownF : ℕ → ℕ) (j : ℕ) (k : Coins Bk) (w : W₃) (h₁ h₂ : List Fmt.Drawn)
    (hf : fx₁ (.own j) ≤ h₁.length) :
    lastTable r₁ toCommon tb₁ tb₂ own (.taken 0 j) k w
        ((h₁ ++ h₂).take (lastFixed r₁ fx₁ fx₂ ownF (.taken 0 j))) =
      tb₁ (.own j) k w (h₁.take (fx₁ (.own j))) := by
  show tb₁ (.own j) k w ((h₁ ++ h₂).take (fx₁ (.own j))) = _
  rw [take_append_within h₁ h₂ _ hf]

theorem lastTable_shared (r₁ : ℕ) (toCommon : W₃ → W₂)
    (tb₁ : Fmt.TreeSource → Coins Bk → W₃ → List Fmt.Drawn → Place × Table)
    (tb₂ : Fmt.TreeSource → Coins Bk → W₂ → List Fmt.Drawn → Place × Table)
    (own : ℕ → Coins Bk → W₃ → List Fmt.Drawn → Place × Table) (fx₁ fx₂ : Fmt.TreeSource → ℕ)
    (ownF : ℕ → ℕ) (j : ℕ) (k : Coins Bk) (w : W₃) (h₁ h₂ : List Fmt.Drawn)
    (hl : h₁.length = r₁) :
    lastTable r₁ toCommon tb₁ tb₂ own (.taken 1 j) k w
        ((h₁ ++ h₂).take (lastFixed r₁ fx₁ fx₂ ownF (.taken 1 j))) =
      tb₂ (.own j) k (toCommon w) (h₂.take (fx₂ (.own j))) := by
  show tb₂ (.own j) k (toCommon w)
    (((h₁ ++ h₂).take (r₁ + fx₂ (.own j))).drop r₁) = _
  subst hl
  rw [drop_take_append]

end

section
variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {k : Coins Bk}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}

/-- **`tk` of `trees_taken_of` at the three sources that the last chain takes over**, where its fields
on trees are the terms of this file. -/
theorem taken_at_door (r₁ n₁ n₂ : ℕ) (toCommon : Local W₀ Rc Xi Tr → Common W₀ Rc Ky)
    (own : ℕ → Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Place × Table) (ownF : ℕ → ℕ)
    (ht : T₃.taken = takenLast)
    (htb : T₃.table = lastTable r₁ toCommon T₁.table T₂.table own)
    (hfx : T₃.fixed = lastFixed r₁ T₁.fixed T₂.fixed ownF)
    (m₁ : Mid (Local W₀ Rc Xi Tr) X) (m₂ : Mid (Common W₀ Rc Ky) X₀)
    (hi₁ : m₁.st.input = R.own) (hi₂ : m₂.st.input = toCommon R.own)
    (hl : m₁.st.heard.length = r₁)
    (hf : ∀ j, j = 1 ∨ j = 82 → T₁.fixed (.own j) ≤ r₁)
    (hh₁ : ∀ j, j = 1 ∨ j = 82 → Fmt.TreeSource.own j ∈ T₁.hand n₁)
    (hh₂ : Fmt.TreeSource.own 1 ∈ T₂.hand n₂) :
    ∀ σ ∈ T₃.taken,
      (∃ j, σ = .taken 0 j ∧ Fmt.TreeSource.own j ∈ T₁.hand n₁ ∧
        T₃.tableAt σ k (R.start₃ H m₁ m₂) = T₁.tableAt (.own j) k m₁) ∨
      ∃ j, σ = .taken 1 j ∧ Fmt.TreeSource.own j ∈ T₂.hand n₂ ∧
        T₃.tableAt σ k (R.start₃ H m₁ m₂) = T₂.tableAt (.own j) k m₂ := by
  have first : ∀ j, j = 1 ∨ j = 82 →
      T₃.tableAt (.taken 0 j) k (R.start₃ H m₁ m₂) = T₁.tableAt (.own j) k m₁ := by
    intro j hj
    unfold Thread.tableAt
    show T₃.table _ k R.own ((m₁.st.heard ++ m₂.st.heard).take (T₃.fixed _)) = _
    rw [htb, hfx, lastTable_first r₁ toCommon T₁.table T₂.table own T₁.fixed T₂.fixed ownF j k
      R.own m₁.st.heard m₂.st.heard (by rw [hl]; exact hf j hj), hi₁]
  have shared : T₃.tableAt (.taken 1 1) k (R.start₃ H m₁ m₂) = T₂.tableAt (.own 1) k m₂ := by
    unfold Thread.tableAt
    show T₃.table _ k R.own ((m₁.st.heard ++ m₂.st.heard).take (T₃.fixed _)) = _
    rw [htb, hfx, lastTable_shared r₁ toCommon T₁.table T₂.table own T₁.fixed T₂.fixed ownF 1 k
      R.own m₁.st.heard m₂.st.heard hl, hi₂]
  intro σ hσ
  rw [ht] at hσ
  have e : takenLast = [.taken 0 1, .taken 0 82, .taken 1 1] := by decide
  rw [e] at hσ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl
  · exact .inl ⟨1, rfl, hh₁ 1 (.inl rfl), first 1 (.inl rfl)⟩
  · exact .inl ⟨82, rfl, hh₁ 82 (.inr rfl), first 82 (.inr rfl)⟩
  · exact .inr ⟨1, rfl, hh₂, shared⟩

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.lastTable
#print axioms ProofFile.Honest.K12.AtFile.lastFixed
#print axioms ProofFile.Honest.K12.AtFile.lastTable_first
#print axioms ProofFile.Honest.K12.AtFile.lastTable_shared
#print axioms ProofFile.Honest.K12.AtFile.taken_at_door
