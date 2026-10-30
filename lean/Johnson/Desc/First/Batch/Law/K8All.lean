-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/K8All.lean
(kind K9's soundness lemma): THE SMALLNESS TEST's STEP OF ADDING AS ONE VALUE, WITH EVERY DUTY THAT
K9's ROW ASKS OF A STEP (Law/RowSteps.lean, Law/RowTable.lean, the joining's JoinAsks): gathered
from Law/K8Run.lean, K8Four.lean, K8Step.lean, K8Disc.lean; two duties are new here.
  k8Termed      the run "K8.equations" with its terms (the four values numbered, then the ties' and
                the reads' single equations) and its number of claims.
  k8Step        the step: that one run; behind the adding, k8LsTail.
  vals4_length  the four values are four, where the fixed part holds the record and what was heard.
  k8_disc_all   the discipline's two clauses at k8Termed's own terms (Law/K8Disc.lean had them at
                any four values).
  k8Run_book, k8LsTail_book   both keep the record's book of trees (Law/TableTabs.lean's duty).
WHERE THE OTHER DUTIES STAND: RunOk: k8_runOk_all - QuietOk: k8_lsTail_quietOk - the door's:
k8Run_door, k8LsTail_door.

-/
import Johnson.Desc.First.Batch.Law.K8Four
import Johnson.Desc.First.Batch.Law.K8Step
import Johnson.Desc.First.Batch.Law.K8Disc
import Johnson.Desc.First.Batch.Law.Steps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.K9 (atS Window)
open VerifiableInference.Desc.First (S)

variable {α : Type}

/-- The run with its terms. -/
def k8Termed (π : α → Option HTailF2 × Option (Array HFun))
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8) :
    TermedRun S (α × Option Pub9) GE8 :=
  ⟨k8Run, fun n q y => numbered n (vals4 π ent q y) ++ tmRest π q y, len8 π⟩

/-- The step. ws, cut: the windows' test's letters. -/
def k8Step (π : α → Option HTailF2 × Option (Array HFun))
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8) (ws : S → List Window)
    (cut : List (Nat × String)) : Step S (α × Option Pub9) GE8 :=
  ⟨ws, cut, [k8Termed π ent], k8LsTail⟩

/-- The four values are four. -/
theorem vals4_length (π : α → Option HTailF2 × Option (Array HFun))
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8) (q : α × Option Pub9) (y : Bound GE8)
    (tlb : HTailF2) (v : Pub9) (g : Forest.Heard) (h1 : (π q.1).1 = some tlb) (h2 : q.2 = some v)
    (hg : tlb.heard = some g) : (vals4 π ent q y).length = 4 := by
  simp only [vals4, h1, h2, hg, List.length_map]
  rfl

/-- **The discipline's two clauses at the run's own terms.** -/
theorem k8_disc_all (π : α → Option HTailF2 × Option (Array HFun))
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8) (q : α × Option Pub9) (y : Bound GE8)
    (tlb : HTailF2) (funs : Array HFun) (v : Pub9) (g : Forest.Heard) (n : ℕ)
    (h1 : π q.1 = (some tlb, some funs)) (h2 : q.2 = some v) (hg : tlb.heard = some g)
    (hmS : ∀ mu, mu < tlb.NM → (tlb.shp.getD mu {}).mS = Alg.symRows (tlb.shp.getD mu {}).m)
    (hn : n + 4 ≤ v.F.planClaimsF) :
    (((k8Termed π ent).tm n q y).map (·.1)).Nodup ∧
      ∀ x ∈ (k8Termed π ent).tm n q y,
        InWin n ((k8Termed π ent).len q) v.F.planClaimsF 0 (top8 tlb funs) x.1 :=
  k8_disc π q y tlb funs v n (vals4 π ent q y) h1 h2 hmS
    (vals4_length π ent q y tlb v g (by rw [h1]) h2 hg) hn

/-- A writing of the ledger or of the test's record leaves the book. -/
theorem book_puts (s : S) (tl : HTailF2) (F : Fork) :
    (s.putTl tl).book = s.book ∧ (s.putFork F).book = s.book := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putTl, S.putFork, ho]
  | _ => exact ⟨rfl, rfl⟩

/-- The run keeps the book. -/
theorem k8Run_book (front : Nat) (e e₁ : S) (c : List Claim) (h : k8Run.2 front e = .ok (c, e₁)) :
    e₁.book = e.book := by
  obtain ⟨F, tl, funs, tl', F1, _, _, _, _, rfl⟩ := k8Run_ok front e e₁ c h
  rw [(book_puts (e.putTl tl') tl' F1).2, (book_puts e tl' F1).1]

/-- So does the quiet move behind the adding. -/
theorem k8LsTail_book (e e₁ : S) (h : k8LsTail e = .ok e₁) : e₁.book = e.book := by
  obtain ⟨F, tl, _, _, rfl⟩ := k8LsTail_ok e e₁ h
  exact (book_puts e _ F).1

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.vals4_length
#print axioms VerifiableInference.Desc.K9L.k8_disc_all
#print axioms VerifiableInference.Desc.K9L.k8Run_book
#print axioms VerifiableInference.Desc.K9L.k8LsTail_book
