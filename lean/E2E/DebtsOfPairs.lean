--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/DebtsOfPairs.lean: E2E/DebtsOfThreads.lean WITH THE DEBTS ASKED FROM THE PAIR OF A THREAD AND
WHAT IS SAID (`ThrS`, Johnson/Desc/ProofFile/Honest/Thread/Said.lean; the debts: PaysS.lean; the
door and the end: FileD.lean): WEAKER PREMISES. The structure of premises `ThreadsC`
(Honest/Law/ThreadStratC.lean) is general in its three families of invariants: here they are the
three pairs. The steps are those of `file_acceptsD`'s own proof. NOTHING IS CLAIMED OF ANY PROVER.

WHY. No clause of a thread says where the prover's own play stands. So whoever pays a debt at a
sub-protocol with a half cannot know what was seen. The letter "what is said" holds that, and a debt
asked from the pair may spend it.

  `playsS₁`, `playsS₂`, `playsS₃`, `saysS₁`, `saysS₂`, `saysS₃`: the chain's rule's two forms at the
    pairs, in the letters of the description and the prover.
  `threadsC_ofS`: the structure, at the pairs.
  **`debtsOne_of_pairs`**: `DebtsOne` (E2E/KeyLink.lean) from `Sits` · `OwesS` ×3 · `SaidNext` at
    every sub-protocol ×3 · `YesS` ×3 · `Enters₁`, `Enters₂` · the letter at the two starts, at the
    states as `ChainProgress.start` lays them · `DoorBehindS` · `DoorYesS` · `FinYesS`.

Limits.
- All limits of E2E/DebtsOfThreads.lean stand.
- WHERE THE LETTER IS ASKED AT A START: as `ThreadsC` asks its invariants there: at the first and
  the shared chain at the state that `ready` gives with the field `opened` set to `some []`; behind
  the door (`DoorBehindS`, FileD.lean) where both ends' fields hold columns, at the state whose
  field holds the two lists of columns joined. `Enters₁` and `Enters₂` name the states that `ready`
  gives, as they stand: by the head of FileD.lean they serve there because `Thr` does not read the
  field.
- The three letters are free. At the letter "true" a pair says no more than its thread (`ThrS` is
  `Thr` and the letter: read off its text; no statement says it), so there is nothing more to spend.
  Even there the door's premise is not `DoorBehind`'s text: `DoorBehindS` has two hypotheses more
  than `DoorBehind` and ends at the state with the joined columns. With "false" it cannot be
  entered. Who lays the letters, and who pays `SaidNext`, is not said here.
- Whatever is paid in the elder forms passes over: `owesS_of`, `yesS_of`, `doorBehindS_of`,
  `doorYesS_of`,
  `finYesS_of` (PaysS.lean, FileD.lean).

-/
import E2E.DebtsOfThreads
import Johnson.Desc.ProofFile.Honest.Thread.FileD

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
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
  {S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}

/-! ## 1. The chain's rule's two forms, in the letters of the description and the prover -/

/-- The first form at the first chain. -/
theorem playsS₁ (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o : OwesS T₁ S₁)
    (n : ∀ b, SaidNext T₁ S₁ b) :
    ∀ j b, F.first.blocksInOrder[j]? = some b →
      PlaysOn .own Bk 0 0 H.first b (ThrS T₁ S₁ j)
        (ThrS T₁ S₁ (j + 1)) := by
  obtain ⟨⟨p, c, f, b, h⟩, -, -, t, -, -⟩ := hS
  have q := playsOn_of_owesS T₁ S₁ (by rw [b]; exact t) (by rw [b]; exact (planOk_all hp).1) o n
  rw [p, c, f, b, h] at q
  exact q

/-- The first form at the shared chain. -/
theorem playsS₂ (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o : OwesS T₂ S₂)
    (n : ∀ b, SaidNext T₂ S₂ b) :
    ∀ j b, F.shared.blocksInOrder[j]? = some b →
      PlaysOn .shared Bk 1 0 H.shared b (ThrS T₂ S₂ j)
        (ThrS T₂ S₂ (j + 1)) := by
  obtain ⟨-, ⟨p, c, f, b, h⟩, -, -, t, -⟩ := hS
  have q := playsOn_of_owesS T₂ S₂ (by rw [b]; exact t) (by rw [b]; exact (planOk_all hp).2.1) o n
  rw [p, c, f, b, h] at q
  exact q

/-- The first form at the second chain. -/
theorem playsS₃ (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o : OwesS T₃ S₃)
    (n : ∀ b, SaidNext T₃ S₃ b) :
    ∀ j b, F.second.blocksInOrder[j]? = some b →
      PlaysOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (ThrS T₃ S₃ j)
        (ThrS T₃ S₃ (j + 1)) := by
  obtain ⟨-, -, ⟨p, c, f, b, h⟩, -, -, t⟩ := hS
  have q := playsOn_of_owesS T₃ S₃ (by rw [b]; exact t) (by rw [b]; exact (planOk_all hp).2.2) o n
  rw [p, c, f, b, h] at q
  exact q

/-- The second form at the first chain. -/
theorem saysS₁ (hS : Sits F H T₁ T₂ T₃) (y : YesS T₁ S₁ (fallsBy f₁ F.first.blocksInOrder)) :
    ∀ j b, F.first.blocksInOrder[j]? = some b →
      SaysYes .own Bk 0 0 H.first b (fallOf f₁ b.place) (ThrS T₁ S₁ j) := by
  obtain ⟨⟨p, c, f, b, h⟩, -, -, -⟩ := hS
  have z := saysYes_of_yesS T₁ S₁ y
  rw [p, c, f, b, h] at z
  intro j m hm
  have e := z j m hm
  rw [fallsBy_at f₁ F.first.blocksInOrder hm] at e
  exact e

/-- The second form at the shared chain. -/
theorem saysS₂ (hS : Sits F H T₁ T₂ T₃) (y : YesS T₂ S₂ (fallsBy f₂ F.shared.blocksInOrder)) :
    ∀ j b, F.shared.blocksInOrder[j]? = some b →
      SaysYes .shared Bk 1 0 H.shared b (fallOf f₂ b.place) (ThrS T₂ S₂ j) := by
  obtain ⟨-, ⟨p, c, f, b, h⟩, -, -⟩ := hS
  have z := saysYes_of_yesS T₂ S₂ y
  rw [p, c, f, b, h] at z
  intro j m hm
  have e := z j m hm
  rw [fallsBy_at f₂ F.shared.blocksInOrder hm] at e
  exact e

/-- The second form at the second chain. -/
theorem saysS₃ (hS : Sits F H T₁ T₂ T₃) (y : YesS T₃ S₃ (fallsBy f₃ F.second.blocksInOrder)) :
    ∀ j b, F.second.blocksInOrder[j]? = some b →
      SaysYes .own Bk 2 F.lastChainFirstTreeNumber H.second b (fallOf f₃ b.place) (ThrS T₃ S₃ j) := by
  obtain ⟨-, -, ⟨p, c, f, b, h⟩, -⟩ := hS
  have z := saysYes_of_yesS T₃ S₃ y
  rw [p, c, f, b, h] at z
  intro j m hm
  have e := z j m hm
  rw [fallsBy_at f₃ F.second.blocksInOrder hm] at e
  exact e

/-! ## 2. The structure -/

/-- **The premises as one structure, from the premises on the pairs.** Its invariants are the pairs
of a thread's sentence and what is said; its lists of falls are the given ones. -/
def threadsC_ofS {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o₁ : OwesS T₁ S₁) (o₂ : OwesS T₂ S₂)
    (o₃ : OwesS T₃ S₃) (n₁ : ∀ b, SaidNext T₁ S₁ b) (n₂ : ∀ b, SaidNext T₂ S₂ b)
    (n₃ : ∀ b, SaidNext T₃ S₃ b) (y₁ : YesS T₁ S₁ (fallsBy f₁ F.first.blocksInOrder))
    (y₂ : YesS T₂ S₂ (fallsBy f₂ F.shared.blocksInOrder)) (y₃ : YesS T₃ S₃ (fallsBy f₃ F.second.blocksInOrder))
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (e₁ : S₁ 0 k { R.start₁ H with opened := some [] })
    (e₂ : S₂ 0 k { R.start₂ H with opened := some [] })
    (a₃ : DoorBehindS F H T₁ T₂ T₃ S₁ S₂ S₃ x k R) (door : DoorYesS F T₁ T₂ S₁ S₂ x k)
    (fin : FinYesS F T₁ T₂ T₃ S₁ S₂ S₃ x k) : ThreadsC F Bk H w₀ rc x k R where
  I₁ := ThrS T₁ S₁
  I₂ := ThrS T₂ S₂
  I₃ := ThrS T₃ S₃
  f₁ := f₁
  f₂ := f₂
  f₃ := f₃
  h₁ := playsS₁ hS hp o₁ n₁
  h₂ := playsS₂ hS hp o₂ n₂
  h₃ := playsS₃ hS hp o₃ n₃
  y₁ := saysS₁ hS y₁
  y₂ := saysS₂ hS y₂
  y₃ := saysS₃ hS y₃
  a₁ := ⟨a₁, e₁⟩
  a₂ := ⟨a₂, e₂⟩
  a₃ := fun v₁ m₁ E₁ v₂ m₂ E₂ c₁ c₂ u₁ u₂ g₁ g₂ => by
    obtain ⟨s₃, hs⟩ := door v₁ m₁ E₁ v₂ m₂ E₂ u₁ u₂
    exact ⟨s₃, hs, a₃ v₁ m₁ E₁ v₂ m₂ E₂ s₃ c₁ c₂ u₁ u₂ hs g₁ g₂⟩
  fin := fin

/-! ## 3. The debts at one input and coin -/

/-- **`DebtsOne` from the premises on the pairs**, at the rows' own lists of falls. -/
theorem debtsOne_of_pairs {Sd R₂ R₃ : Type} (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (H₀ : Prover W₀ Rc Xi Ky Tr X₀ X)
    {U₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {U₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    {U₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hS : Sits F (G.prover H₀) U₁ U₂ U₃) (hp : F.planOk = true) (o₁ : OwesS U₁ S₁)
    (o₂ : OwesS U₂ S₂) (o₃ : OwesS U₃ S₃) (n₁ : ∀ b, SaidNext U₁ S₁ b)
    (n₂ : ∀ b, SaidNext U₂ S₂ b) (n₃ : ∀ b, SaidNext U₃ S₃ b)
    (y₁ : YesS U₁ S₁ (fallsBy G.falls₁ F.first.blocksInOrder))
    (y₂ : YesS U₂ S₂ (fallsBy G.falls₂ F.shared.blocksInOrder))
    (y₃ : YesS U₃ S₃ (fallsBy G.falls₃ F.second.blocksInOrder))
    (w : W₀ × Rc × Sd) (x : Xi) (c : CoinOne Bk R₂ R₃) (h0 : F.okStart x = true)
    {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H₀) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R)
    (hP : PlanServes (G.prover H₀) w.1 w.2.1 R)
    (a₁ : Enters₁ F (G.prover H₀) U₁ w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R)
    (a₂ : Enters₂ F (G.prover H₀) U₂ w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R)
    (e₁ : S₁ 0 ⟨c.2.1.1, c.1.1, c.2.1.2⟩ { R.start₁ (G.prover H₀) with opened := some [] })
    (e₂ : S₂ 0 ⟨c.2.1.1, c.1.1, c.2.1.2⟩ { R.start₂ (G.prover H₀) with opened := some [] })
    (a₃ : DoorBehindS F (G.prover H₀) U₁ U₂ U₃ S₁ S₂ S₃ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R)
    (door : DoorYesS F U₁ U₂ S₁ S₂ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩)
    (fin : FinYesS F U₁ U₂ U₃ S₁ S₂ S₃ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩) :
    DebtsOne F Bk G H₀ w x c :=
  ⟨h0, R, hR, hP, threadsC_ofS hS hp o₁ o₂ o₃ n₁ n₂ n₃ y₁ y₂ y₃ a₁ a₂ e₁ e₂ a₃ door fin, rfl, rfl,
    rfl⟩

end AtPublicFiles.KeyLink

#print axioms AtPublicFiles.KeyLink.playsS₁
#print axioms AtPublicFiles.KeyLink.playsS₂
#print axioms AtPublicFiles.KeyLink.playsS₃
#print axioms AtPublicFiles.KeyLink.saysS₁
#print axioms AtPublicFiles.KeyLink.saysS₂
#print axioms AtPublicFiles.KeyLink.saysS₃
#print axioms AtPublicFiles.KeyLink.threadsC_ofS
#print axioms AtPublicFiles.KeyLink.debtsOne_of_pairs
