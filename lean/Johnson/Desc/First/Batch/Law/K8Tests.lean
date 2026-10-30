-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/K8Tests.lean
(kind K9's soundness lemma): THEOREMS: THE SMALLNESS TEST's LAST RUN BEHIND THE BATCHING, "K8.tests"
(Johnson/Desc/First/TailClaims/K8Claims.lean: k8Tests; SelfRows.lean: testsP: the test on the sums,
THEN THE STEP THAT LAYS THE WEIGHTS OF EVERY VIRTUAL ROW INTO THE LEDGER, then the test on the rows'
weights), AS A QUIET MOVE OF K9's ROW: it writes the ledger, so it does not hand the record back.
  k8Tests nU    the move at the real record: the ledger and the test's record are read; testsP; the
                returned ledger is laid (with the test's record, unturned).
  k8Tests_ok    a yes, cut: the three steps' yeses; the ledger behind is coefBody tl g F.
  coef_side     what coefBody leaves: all of the ledger but the arrays' virtual rows.
  coef_later    so the ledger behind is a later one, with the plan's number and the arrays' widths.
  k8_tests_quietOk   **QuietOk**, under one hypothesis on the letter phi (hkeep: Law/K8Run.lean's).
  k8Tests_door, k8Tests_book   it keeps the door and the book.
  k8_tests_full **ITS YES GIVES THE FIRST CLAUSE OF "FULL"** (hFu of Law/K8Run.lean): at the state
                behind, rkSelfTestP says yes of that state's own record and ledger.
NOT CLAIMED: that the run which a description's block states under the name "K8.tests" is this
function (JoinSame); the other clauses of "full"; that no later move turns a weight.

-/
import Johnson.Desc.First.TailClaims.EquationsTests
import Johnson.Desc.First.Batch.Law.Coef
import Johnson.Desc.First.Batch.Law.K8All

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.PscRun (Later Sized Filled)
open VerifiableInference.Desc.K9 (atS there)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (testsP selfTestP coefficientsP rkSelfTestP coefBody)
open VerifiableInference.Desc.First.TailClaims.Law (blank tests_ok coefBody_inv)

/-- The move. nU: the plan's lengths of the three vectors at this place. -/
def k8Tests (nU : Array Nat) (s : S) : Except String S := do
  let F ← there "K9.in-a-segment" s.fork?
  let tl ← there "K9.in-a-segment" s.tl?
  let G ← testsP nU tl F
  pure ((s.putTl tl).putFork G)

theorem k8Tests_ok (nU : Array Nat) (e e₁ : S) (h : k8Tests nU e = .ok e₁) :
    ∃ F tl g, e.fork? = some F ∧ e.tl? = some tl ∧ tl.heard = some g ∧
      selfTestP tl nU F = .ok () ∧ rkSelfTestP tl (coefBody tl g F) = .ok () ∧
      e₁ = (e.putTl tl).putFork (coefBody tl g F) := by
  simp only [k8Tests] at h
  obtain ⟨F, hF, h⟩ := ok_bind h
  obtain ⟨tl, ht, h⟩ := ok_bind h
  obtain ⟨G, hG, h⟩ := ok_bind h
  obtain ⟨h1, h2, h3⟩ := tests_ok hG
  unfold coefficientsP at h2
  split at h2
  · cases h2
  · rename_i g hg
    obtain rfl := Except.ok.inj h2
    exact ⟨F, tl, g, there_ok hF, there_ok ht, hg, h1, h3, (Except.ok.inj h).symm⟩

/-- What the laying of the weights leaves. -/
theorem coef_side (tl : HTailF2) (g : Forest.Heard) (F : Fork) :
    (coefBody tl g F).next = F.next ∧ (coefBody tl g F).ns = F.ns ∧
      (coefBody tl g F).gotF = F.gotF ∧ (coefBody tl g F).vp = F.vp ∧
      (coefBody tl g F).mf = F.mf ∧ (coefBody tl g F).LS = F.LS ∧
      (coefBody tl g F).planClaimsF = F.planClaimsF ∧
      (coefBody tl g F).trees.map (·.K) = F.trees.map (·.K) :=
  coefBody_inv (fun r => r.next = F.next ∧ r.ns = F.ns ∧ r.gotF = F.gotF ∧ r.vp = F.vp ∧
      r.mf = F.mf ∧ r.LS = F.LS ∧ r.planClaimsF = F.planClaimsF ∧
      r.trees.map (·.K) = F.trees.map (·.K))
    (fun r t' r' f h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1, by
        rw [← h.2.2.2.2.2.2.2]
        unfold onRow
        exact map_modify_same (fun X : HTree => X.K)
          (fun X => { X with rows := X.rows.modify r' f }) (fun _ => rfl) r.trees t'⟩)
    tl g F ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- coefBody leaves the arrays' looks: it writes virtual rows that are there. -/
theorem coef_looks (tl : HTailF2) (g : Forest.Heard) (F : Fork) :
    (coefBody tl g F).trees.map LinkJoin.look = F.trees.map LinkJoin.look :=
  coefBody_inv (fun r => r.trees.map LinkJoin.look = F.trees.map LinkJoin.look)
    (fun r t' r' f h => by
      rw [← h]
      unfold onRow
      exact map_modify_same LinkJoin.look (fun X => { X with rows := X.rows.modify r' f })
        (fun X => LinkJoin.look_rows_modify X r' f) r.trees t') tl g F rfl

/-- So the ledger behind is a later one. -/
theorem coef_later (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Later F (coefBody tl g F) := by
  obtain ⟨a1, a2, a3, a4, a5, _, _, _⟩ := coef_side tl g F
  refine ⟨Nat.le_of_eq a1.symm, a2, fun hs => ?_, fun j hj => ?_⟩
  · unfold Sized at hs ⊢
    rw [a2, a3, a4, a5]
    exact hs
  · unfold Filled at hj ⊢
    rw [a3, a4, a5]
    exact ⟨hj, rfl, rfl⟩

section
variable {α : Type}

/-- **"K8.tests" meets QuietOk.** -/
theorem k8_tests_quietOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (u : HTailF2)
    (hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl →
      φ ((s.putTl tl').putFork F1) = φ s) (nU : Array Nat) :
    QuietOk atS (O9 (K := GE8) φ Ok Fu) (Fx9 φ Ok) (k8Tests nU) := by
  intro q e a e₁ hf hg ha hs h
  obtain ⟨F, tl, g, hF, htl, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ h
  obtain ⟨a₁, ha₁, f1, f2, f3, _, _, hF'⟩ := get_put e a ha tl (coefBody tl g F)
  have eF : F = a.F := Option.some.inj (hF.symm.trans hF')
  subst eF
  obtain ⟨_, b2, _, _, _, b6, b7, _⟩ := coef_side tl g a.F
  have hgo : GoesOn (pubOf a) a₁ :=
    ⟨by rw [f1]; exact coef_later tl g a.F, by rw [f1]; exact b7,
      by rw [f1]; exact coef_looks tl g a.F, by rw [f2]; rfl, by rw [f2]; rfl, f3⟩
  have hmore : more9 φ e ((e.putTl tl).putFork (coefBody tl g a.F)) :=
    ⟨hkeep e tl tl _ htl rfl, fun a' ha' => by
      have ea : a' = a := Option.some.inj (ha'.symm.trans ha)
      rw [ea]
      exact ⟨a₁, ha₁, hgo⟩⟩
  obtain ⟨a0, ha0, g1, _⟩ := hg
  have ea0 : a0 = a := Option.some.inj (ha0.symm.trans ha)
  subst ea0
  exact ⟨a₁, ha₁, by rw [f1]; exact core_coefBody tl g a0.F,
    ⟨a₁, ha₁, by rw [f2]; exact g1, by rw [f1, b6, b2]; exact hs⟩, hmore,
    fx_of_more φ Ok q e _ hf hmore⟩

end

/-- It keeps the door. -/
theorem k8Tests_door (nU : Array Nat) (e e₁ : S) (h : k8Tests nU e = .ok e₁) :
    KeepsDoor atS e e₁ := by
  intro a ha
  obtain ⟨F, tl, g, _, _, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ h
  obtain ⟨a₁, ha₁, _, f2, f3, _⟩ := get_put e a ha tl (coefBody tl g F)
  exact ⟨a₁, ha₁, by rw [f2], f3⟩

/-- It keeps the book. -/
theorem k8Tests_book (nU : Array Nat) (e e₁ : S) (h : k8Tests nU e = .ok e₁) :
    e₁.book = e.book := by
  obtain ⟨F, tl, g, _, _, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ h
  rw [(book_puts (e.putTl tl) tl _).2, (book_puts e tl F).1]

/-- **Its yes gives the first clause of "full"**: at the state behind, the test on the rows' weights
says yes of that state's own record and ledger. -/
theorem k8_tests_full (nU : Array Nat) (e e₁ : S) (a : K9.Part) (ha : atS.get? e = some a)
    (h : k8Tests nU e = .ok e₁) :
    ∃ b ts, atS.get? e₁ = some b ∧ e₁.tl? = some ts ∧ e₁.funs? = e.funs? ∧
      rkSelfTestP ts b.F = .ok () := by
  obtain ⟨F, tl, g, _, _, _, _, h3, rfl⟩ := k8Tests_ok nU e e₁ h
  obtain ⟨a₁, ha₁, f1, _, _, f4, f5, _⟩ := get_put e a ha tl (coefBody tl g F)
  exact ⟨a₁, tl, ha₁, f4, f5, by rw [f1]; exact h3⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.coef_side
#print axioms VerifiableInference.Desc.K9L.coef_later
#print axioms VerifiableInference.Desc.K9L.k8_tests_quietOk
#print axioms VerifiableInference.Desc.K9L.k8Tests_door
#print axioms VerifiableInference.Desc.K9L.k8Tests_book
#print axioms VerifiableInference.Desc.K9L.k8_tests_full
