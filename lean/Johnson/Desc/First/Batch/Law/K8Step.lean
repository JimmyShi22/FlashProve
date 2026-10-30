-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/K8Step.lean
(kind K9's soundness lemma): THEOREMS: THE OTHER DUTIES OF THE SMALLNESS TEST's STEP OF ADDING, AT
THE REAL RECORD: beside RunOk of its run of claims (Law/K8Run.lean):
  k8LsTail       the quiet move behind the adding: the ledger's coefficients on the test's window of
                 slots are laid into the test's record. (To the letter the text "k8LsTailAtS" of
                 Batch/ObjectsAtS.lean.)
  get_putTl      what K9's lens reads behind that writing: the ledger, the link's record and the
                 statement are untouched.
  k8_lsTail_quietOk   **QuietOk of k8LsTail** at the letters O9 phi Ok Fu, Fx9 phi Ok.
  k8Run_door, k8LsTail_door   **the door's duty (Law/MovesDoor.lean: KeepsDoor) of both**: the
                 walk's record and the statement stay.
HYPOTHESES ON THE LETTERS: those of Law/K8Run.lean, and hkeepT: phi does not see a writing of the
test's record where the blanked records agree.
Not claimed: that such letters exist together with the other kinds'; h4 (Law/K8Run.lean).

-/
import Johnson.Desc.First.Batch.Law.K8Run
import Johnson.Desc.First.Batch.Law.MovesDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.K9 (atS there)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank blank_lsTail)

/-- The quiet move behind the adding. -/
def k8LsTail (s : S) : Except String S := do
  let F ← there "K9.in-a-segment" s.fork?
  let tl ← there "K9.in-a-segment" s.tl?
  pure (s.putTl { tl with lsTail := F.LS.extract tl.slotA tl.slotB })

theorem k8LsTail_ok (e e₁ : S) (h : k8LsTail e = .ok e₁) :
    ∃ F tl, e.fork? = some F ∧ e.tl? = some tl ∧
      e₁ = e.putTl { tl with lsTail := F.LS.extract tl.slotA tl.slotB } := by
  simp only [k8LsTail] at h
  obtain ⟨F, hF, h⟩ := ok_bind h
  obtain ⟨tl, ht, h⟩ := ok_bind h
  exact ⟨F, tl, there_ok hF, there_ok ht, (Except.ok.inj h).symm⟩

/-- What K9's lens reads behind a writing of the test's record. -/
theorem get_putTl (e : S) (a : K9.Part) (ha : atS.get? e = some a) (tl' : HTailF2) :
    ∃ a₁, atS.get? (e.putTl tl') = some a₁ ∧ a₁.F = a.F ∧ a₁.L = a.L ∧ a₁.d.st = a.d.st := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  cases here with
  | lay x =>
    obtain rfl := Option.some.inj ha
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  | att x =>
    obtain rfl := Option.some.inj ha
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  | head x =>
    by_cases ho : x.opened = true
    · cases hs : x.slot with
      | none => simp [atS, S.link?, S.fork?, S.tl?, K9.usedOf, ho, hs] at ha
      | some n =>
        simp only [atS, S.link?, S.fork?, S.tl?, K9.usedOf, ho, hs, if_true, Option.bind_eq_bind,
          Option.bind_some, Option.pure_def, Option.some.injEq] at ha
        subst ha
        simp [atS, S.putTl, S.link?, S.fork?, S.tl?, K9.usedOf, ho, hs]
    · simp [atS, S.link?, ho] at ha
  | between => simp [atS, S.link?] at ha
  | fin x => simp [atS, S.link?] at ha
  | mem x => simp [atS, S.link?] at ha

section
variable {α : Type}

/-- **The quiet move behind the adding meets QuietOk.** -/
theorem k8_lsTail_quietOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (u : HTailF2)
    (hkeepT : ∀ s tl tl', s.tl? = some tl → blank u tl' = blank u tl → φ (s.putTl tl') = φ s) :
    QuietOk atS (O9 (K := GE8) φ Ok Fu) (Fx9 φ Ok) k8LsTail := by
  intro q e a e₁ hf hg ha hs h
  obtain ⟨F, tl, _, htl, rfl⟩ := k8LsTail_ok e e₁ h
  obtain ⟨a₁, ha₁, f1, f2, f3⟩ :=
    get_putTl e a ha { tl with lsTail := F.LS.extract tl.slotA tl.slotB }
  have hφ1 := hkeepT e tl { tl with lsTail := F.LS.extract tl.slotA tl.slotB } htl
    (blank_lsTail u tl _)
  have hgo : GoesOn (pubOf a) a₁ :=
    ⟨by rw [f1]; exact Later.refl _, by rw [f1]; rfl, by rw [f1]; rfl, by rw [f2]; rfl,
      by rw [f2]; rfl, f3⟩
  have hmore : more9 φ e (e.putTl { tl with lsTail := F.LS.extract tl.slotA tl.slotB }) :=
    ⟨hφ1, fun a' ha' => by
      have ea : a' = a := Option.some.inj (ha'.symm.trans ha)
      rw [ea]
      exact ⟨a₁, ha₁, hgo⟩⟩
  obtain ⟨a0, ha0, g1, _⟩ := hg
  have ea0 : a0 = a := Option.some.inj (ha0.symm.trans ha)
  subst ea0
  exact ⟨a₁, ha₁, by rw [f1], ⟨a₁, ha₁, by rw [f2]; exact g1, by rw [f1]; exact hs⟩, hmore,
    fx_of_more φ Ok q e _ hf hmore⟩

end

/-- The run of claims keeps the door. -/
theorem k8Run_door (front : Nat) (e e₁ : S) (c : List Claim) (h : k8Run.2 front e = .ok (c, e₁)) :
    KeepsDoor atS e e₁ := by
  intro a ha
  obtain ⟨F, tl, funs, tl', F1, _, _, _, _, rfl⟩ := k8Run_ok front e e₁ c h
  obtain ⟨a₁, ha₁, _, f2, f3, _⟩ := get_put e a ha tl' F1
  exact ⟨a₁, ha₁, by rw [f2], f3⟩

/-- So does the quiet move behind the adding. -/
theorem k8LsTail_door (e e₁ : S) (h : k8LsTail e = .ok e₁) : KeepsDoor atS e e₁ := by
  intro a ha
  obtain ⟨F, tl, _, _, rfl⟩ := k8LsTail_ok e e₁ h
  obtain ⟨a₁, ha₁, _, f2, f3⟩ := get_putTl e a ha _
  exact ⟨a₁, ha₁, by rw [f2], f3⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.get_putTl
#print axioms VerifiableInference.Desc.K9L.k8_lsTail_quietOk
#print axioms VerifiableInference.Desc.K9L.k8Run_door
#print axioms VerifiableInference.Desc.K9L.k8LsTail_door
