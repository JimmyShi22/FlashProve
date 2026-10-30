--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/DebtsOfThreads.lean: FROM THE DEBTS AS THEY ARE OWED ON THREADS TO THE PREMISE OF THE THEOREM ON
THE HONEST STRATEGY. General in the description, the book and the prover. By calls. NOTHING IS
CLAIMED OF ANY PROVER.

Two forms of one list of premises stand in another folder.
  ON THREADS (Johnson/Desc/ProofFile/Honest/Thread/File.lean): three threads sit at the description
    and the prover (`Sits`); at every member the debts that say nothing of a fall (`Owes`) and the
    acceptance outside a fall (`Yes`); the two first threads are entered (`Enters₁`, `Enters₂`); the
    second chain's start (`DoorBehind`, `DoorYes`); the last test (`FinYes`). It is the form in
    which whoever hands in a member of a chain pays.
  AS ONE STRUCTURE (`ThreadsC`, Johnson/Desc/ProofFile/Honest/Law/ThreadStratC.lean): three families
    of invariants, three lists of falls, the chain's rule in two forms at every member, the starts,
    the last test. It is what `yes_at_stratC` takes, and so `DebtsOne` (E2E/KeyLink.lean).

What is shown.
  `plays₁`, `plays₂`, `plays₃`, `says₁`, `says₂`, `says₃`: the chain's rule's two forms at every
    member of each flat list, at the thread's own sentences, in the letters of the description and
    the prover; the falls by the member's place (`fallsBy_at`).
  **`threadsC_of`**: the structure, from the premises on threads: its invariants are the threads'
    sentences, its lists of falls the given ones.
  **`debtsOne_of_threads`**: `DebtsOne` at one input and coin, from the premises on threads at the
    rows' own lists of falls, with: the instance's first test accepts; the run can be made ready;
    the plan serves.

Limits.
- CONDITIONAL. No premise on threads is shown here of any description or prover. Every field of a
  thread is a letter: at a thread that cannot be entered all is idle.
- The steps are those of the proof of `file_accepts` (Johnson/Desc/ProofFile/Honest/Thread/
  FileYes.lean), which makes the same terms and hands them to another theorem.
- THE LISTS OF FALLS ARE FREE LETTERS: as in E2E/KeyLink.lean's limits.
- Pointwise: one input, one run's coins.

-/
import E2E.KeyLink
import Johnson.Desc.ProofFile.Honest.Thread.FileViews

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyLink
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {f₁ : List (Fall F.S₁)} {f₂ : List (Fall F.S₂)} {f₃ : List (Fall F.S₃)}

/-! ## 1. The chain's rule's two forms, in the letters of the description and the prover -/

/-- The first form at the first chain. -/
theorem plays₁ (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o : Owes T₁) :
    ∀ j b, F.first.blocksInOrder[j]? = some b →
      PlaysOn .own Bk 0 0 H.first b (Thr T₁ j) (Thr T₁ (j + 1)) := by
  obtain ⟨⟨p, c, f, b, h⟩, -, -, t, -, -⟩ := hS
  have q := playsOn_of_owes T₁ (by rw [b]; exact t) (by rw [b]; exact (planOk_all hp).1) o
  rw [p, c, f, b, h] at q
  exact q

/-- The first form at the shared chain. -/
theorem plays₂ (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o : Owes T₂) :
    ∀ j b, F.shared.blocksInOrder[j]? = some b →
      PlaysOn .shared Bk 1 0 H.shared b (Thr T₂ j) (Thr T₂ (j + 1)) := by
  obtain ⟨-, ⟨p, c, f, b, h⟩, -, -, t, -⟩ := hS
  have q := playsOn_of_owes T₂ (by rw [b]; exact t) (by rw [b]; exact (planOk_all hp).2.1) o
  rw [p, c, f, b, h] at q
  exact q

/-- The first form at the second chain. -/
theorem plays₃ (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o : Owes T₃) :
    ∀ j b, F.second.blocksInOrder[j]? = some b →
      PlaysOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (Thr T₃ j) (Thr T₃ (j + 1)) := by
  obtain ⟨-, -, ⟨p, c, f, b, h⟩, -, -, t⟩ := hS
  have q := playsOn_of_owes T₃ (by rw [b]; exact t) (by rw [b]; exact (planOk_all hp).2.2) o
  rw [p, c, f, b, h] at q
  exact q

/-- A chain's falls by the member's number are those at the member's place. -/
theorem fallsBy_at {S Cl : Type} (fs : List (Fall S))
    (bs : List (VerifiableInference.Desc.Block S Cl)) {j : ℕ}
    {b : VerifiableInference.Desc.Block S Cl} (hb : bs[j]? = some b) :
    fallsBy fs bs j = fallOf fs b.place := by
  unfold fallsBy
  rw [hb]

/-- The second form at the first chain. -/
theorem says₁ (hS : Sits F H T₁ T₂ T₃) (y : Yes T₁ (fallsBy f₁ F.first.blocksInOrder)) :
    ∀ j b, F.first.blocksInOrder[j]? = some b →
      SaysYes .own Bk 0 0 H.first b (fallOf f₁ b.place) (Thr T₁ j) := by
  obtain ⟨⟨p, c, f, b, h⟩, -, -, -⟩ := hS
  have z := saysYes_of_yes T₁ y
  rw [p, c, f, b, h] at z
  intro j m hm
  have e := z j m hm
  rw [fallsBy_at f₁ F.first.blocksInOrder hm] at e
  exact e

/-- The second form at the shared chain. -/
theorem says₂ (hS : Sits F H T₁ T₂ T₃) (y : Yes T₂ (fallsBy f₂ F.shared.blocksInOrder)) :
    ∀ j b, F.shared.blocksInOrder[j]? = some b →
      SaysYes .shared Bk 1 0 H.shared b (fallOf f₂ b.place) (Thr T₂ j) := by
  obtain ⟨-, ⟨p, c, f, b, h⟩, -, -⟩ := hS
  have z := saysYes_of_yes T₂ y
  rw [p, c, f, b, h] at z
  intro j m hm
  have e := z j m hm
  rw [fallsBy_at f₂ F.shared.blocksInOrder hm] at e
  exact e

/-- The second form at the second chain. -/
theorem says₃ (hS : Sits F H T₁ T₂ T₃) (y : Yes T₃ (fallsBy f₃ F.second.blocksInOrder)) :
    ∀ j b, F.second.blocksInOrder[j]? = some b →
      SaysYes .own Bk 2 F.lastChainFirstTreeNumber H.second b (fallOf f₃ b.place) (Thr T₃ j) := by
  obtain ⟨-, -, ⟨p, c, f, b, h⟩, -⟩ := hS
  have z := saysYes_of_yes T₃ y
  rw [p, c, f, b, h] at z
  intro j m hm
  have e := z j m hm
  rw [fallsBy_at f₃ F.second.blocksInOrder hm] at e
  exact e

/-! ## 2. The structure -/

/-- **The premises as one structure, from the premises on threads.** Its invariants are the threads'
sentences; its lists of falls are the given ones. -/
def threadsC_of {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o₁ : Owes T₁) (o₂ : Owes T₂) (o₃ : Owes T₃)
    (y₁ : Yes T₁ (fallsBy f₁ F.first.blocksInOrder)) (y₂ : Yes T₂ (fallsBy f₂ F.shared.blocksInOrder))
    (y₃ : Yes T₃ (fallsBy f₃ F.second.blocksInOrder)) (a₁ : Enters₁ F H T₁ w₀ rc x k R)
    (a₂ : Enters₂ F H T₂ w₀ rc x k R) (a₃ : DoorBehind F H T₁ T₂ T₃ x k R)
    (door : DoorYes F T₁ T₂ x k) (fin : FinYes F T₁ T₂ T₃ x k) :
    ThreadsC F Bk H w₀ rc x k R where
  I₁ := Thr T₁
  I₂ := Thr T₂
  I₃ := Thr T₃
  f₁ := f₁
  f₂ := f₂
  f₃ := f₃
  h₁ := plays₁ hS hp o₁
  h₂ := plays₂ hS hp o₂
  h₃ := plays₃ hS hp o₃
  y₁ := says₁ hS y₁
  y₂ := says₂ hS y₂
  y₃ := says₃ hS y₃
  a₁ := a₁
  a₂ := a₂
  a₃ := fun e₁ m₁ E₁ e₂ m₂ E₂ _ _ u₁ u₂ _ _ => by
    obtain ⟨s₃, hs⟩ := door e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂
    exact ⟨s₃, hs, a₃ e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ hs⟩
  fin := fin

/-! ## 3. The debts at one input and coin -/

/-- **`DebtsOne` from the premises on threads**, at the rows' own lists of falls. -/
theorem debtsOne_of_threads {Sd R₂ R₃ : Type} (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (H₀ : Prover W₀ Rc Xi Ky Tr X₀ X)
    {U₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {U₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    {U₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hS : Sits F (G.prover H₀) U₁ U₂ U₃) (hp : F.planOk = true) (o₁ : Owes U₁) (o₂ : Owes U₂)
    (o₃ : Owes U₃) (y₁ : Yes U₁ (fallsBy G.falls₁ F.first.blocksInOrder))
    (y₂ : Yes U₂ (fallsBy G.falls₂ F.shared.blocksInOrder)) (y₃ : Yes U₃ (fallsBy G.falls₃ F.second.blocksInOrder))
    (w : W₀ × Rc × Sd) (x : Xi) (c : CoinOne Bk R₂ R₃) (h0 : F.okStart x = true)
    {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H₀) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R)
    (hP : PlanServes (G.prover H₀) w.1 w.2.1 R)
    (a₁ : Enters₁ F (G.prover H₀) U₁ w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R)
    (a₂ : Enters₂ F (G.prover H₀) U₂ w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R)
    (a₃ : DoorBehind F (G.prover H₀) U₁ U₂ U₃ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R)
    (door : DoorYes F U₁ U₂ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩)
    (fin : FinYes F U₁ U₂ U₃ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩) :
    DebtsOne F Bk G H₀ w x c :=
  ⟨h0, R, hR, hP, threadsC_of hS hp o₁ o₂ o₃ y₁ y₂ y₃ a₁ a₂ a₃ door fin, rfl, rfl, rfl⟩

end AtPublicFiles.KeyLink

#print axioms AtPublicFiles.KeyLink.plays₁
#print axioms AtPublicFiles.KeyLink.plays₂
#print axioms AtPublicFiles.KeyLink.plays₃
#print axioms AtPublicFiles.KeyLink.fallsBy_at
#print axioms AtPublicFiles.KeyLink.says₁
#print axioms AtPublicFiles.KeyLink.says₂
#print axioms AtPublicFiles.KeyLink.says₃
#print axioms AtPublicFiles.KeyLink.debtsOne_of_threads
#print axioms AtPublicFiles.KeyLink.threadsC_of
