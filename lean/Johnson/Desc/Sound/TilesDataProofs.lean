-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TilesDataProofs.lean: proofs of `FlatSome`, `RowFitOfData` and `FitsOfData`
(Johnson/Desc/Sound/TilesData.lean): the stretches tile the three chains of every description, at
the data that `FileDescription.data` makes of its declared rounds.

The road: `data_ok` reads off `F.data file = .ok D` the three lists of written rounds, the yes of
the makers' tests and what D is; `written_as` reads off `writtenOf` that each declared round is
written round by round; then Johnson/Desc/Sound/TilesOkProofs.lean.
Limits: those of the statements, which stand in Johnson/Desc/Sound/TilesData.lean. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TilesData
import Johnson.Desc.Sound.TilesOkProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker Johnson.G.OfPlan
open OnBytes.Params (Rounds)
open OnBytes.Three (tagRoot tagRun)

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem mapM_except {ε α β : Type} (f : α → Except ε β) : ∀ (l : List α) (bs : List β),
    l.mapM f = .ok bs → List.Forall₂ (fun a b => f a = .ok b) l bs
  | [], bs, h => by
    rw [List.mapM_nil] at h
    have e := Except.ok.inj h
    subst e
    exact .nil
  | a0 :: l, bs, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b0, e0, h⟩ := bind_ok h
    obtain ⟨bs0, e1, h⟩ := bind_ok h
    have e := Except.ok.inj h
    subst e
    exact .cons e0 (mapM_except f l bs0 e1)

/-- What `writtenOf`'s yes says, chain by chain. -/
theorem written_as (file : String) (D : Decl3) (R : Rounds × Rounds × Rounds)
    (h : writtenOf file D = .ok R) :
    WrittenAs [] D.1 R.1 ∧ WrittenAs [] D.2.1 R.2.1 ∧
      WrittenAs [((List.range (rootsOf D.1)).map tagRoot, tagRun 1),
        ((List.range (rootsOf D.2.1)).map tagRoot, tagRun 2)] D.2.2 R.2.2 := by
  unfold writtenOf at h
  try dsimp only at h
  obtain ⟨A, hA, h⟩ := bind_ok h
  obtain ⟨B, hB, h⟩ := bind_ok h
  obtain ⟨E, hE, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  refine ⟨(mapM_except _ _ _ hA).imp ?_, (mapM_except _ _ _ hB).imp ?_,
    (mapM_except _ _ _ hE).imp ?_⟩
  all_goals
    intro r x hx
    try dsimp only at hx
    split at hx
    · rename_i y hy
      have e := Except.ok.inj hx
      subst e
      exact ⟨hy, rfl⟩
    · have hx' : (Except.error _ : Except String (Fmt.Round × List Fmt.Stored)) = .ok x := hx
      cases hx'

/-- What `FileDescription.data`'s yes says. -/
theorem data_ok {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) : ∃ R : Rounds × Rounds × Rounds, writtenOf file F.roundsDeclaredByBlocks = .ok R ∧
      okAt F.tableDepth (some R) = true ∧ D = dataOf F.tableDepth R.1 R.2.1 R.2.2 := by
  unfold FileDescription.data at h
  obtain ⟨R, hR, h⟩ := bind_ok h
  cases hok : okAt F.tableDepth (some R) with
  | false =>
    rw [hok] at h
    have h' : (Except.error _ : Except String WholeD) = .ok D := h
    cases h'
  | true =>
    rw [hok] at h
    exact ⟨R, hR, hok, (Except.ok.inj h).symm⟩

theorem flat_of_map {S T Cl Cl' : Type} (l : List (Block S Cl)) (l' : List (Block T Cl'))
    (h : l.map (·.rounds) = l'.map (·.rounds)) :
    l.flatMap (·.rounds) = l'.flatMap (·.rounds) := by
  show (l.map (·.rounds)).flatten = (l'.map (·.rounds)).flatten
  rw [h]

theorem lastRounds_eq {S Cl : Type} : ∀ (l : List (Block S Cl)) (b : Block S Cl),
    lastRounds b l = ((((b :: l).map (·.rounds)).getLast?).map (·.length)).getD 0
  | [], _ => rfl
  | b' :: l, b => by
    have e : ((b :: b' :: l).map (·.rounds)).getLast? = ((b' :: l).map (·.rounds)).getLast? := by
      simp only [List.map_cons, List.getLast?_cons_cons]
    rw [e]
    exact lastRounds_eq l b'

theorem fits_second {R₁ R₂ R₃ : Rounds} {m : ℕ} (h : Three.Whole.fits R₁ R₂ R₃ m = true) :
    R₂ ≠ [] := by
  unfold Three.Whole.fits at h
  simp only [Bool.and_eq_true] at h
  have h5 := List.all_eq_true.1 h.1.2 R₂ (by simp)
  intro e
  subst e
  simp at h5

theorem flatSome : FlatSome := by
  intro Xi F file D h
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hok, -⟩ := data_ok F file D h
  obtain ⟨w₁, w₂, w₃⟩ := written_as file F.roundsDeclaredByBlocks _ hR
  have P := okAt_parts hok
  have hsome : someFit (R₁, R₂, R₃) = true := P.rounds
  unfold someFit at hsome
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsome
  obtain ⟨h2, h3⟩ := hsome
  have n₂ : R₂ ≠ [] := fits_second P.fits
  have l₁ := List.Forall₂.length_eq w₁
  have l₂ := List.Forall₂.length_eq w₂
  have l₃ := List.Forall₂.length_eq w₃
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · have z : F.roundsDeclaredByBlocks.1 = [] := by show F.first.blocksInOrder.flatMap (·.rounds) = []; rw [e]; rfl
    rw [z] at l₁
    have h2' : 2 ≤ R₁.length := h2
    have l₁' : R₁.length = 0 := l₁.symm
    omega
  · have z : F.roundsDeclaredByBlocks.2.1 = [] := by show F.shared.blocksInOrder.flatMap (·.rounds) = []; rw [e]; rfl
    rw [z] at l₂
    exact n₂ (List.eq_nil_of_length_eq_zero l₂.symm)
  · have z : F.roundsDeclaredByBlocks.2.2 = [] := by show F.second.blocksInOrder.flatMap (·.rounds) = []; rw [e]; rfl
    rw [z] at l₃
    have e3 : R₃ = [] := List.eq_nil_of_length_eq_zero l₃.symm
    subst e3
    simp at h3

theorem rowFitOfData : RowFitOfData := by
  intro Xi F file D h
  obtain ⟨⟨R₁, R₂, R₃⟩, -, hok, rfl⟩ := data_ok F file D h
  exact rowFitOfOk _ R₁ R₂ R₃ hok

/-- The seal's test, said of the last block of the first chain's flat list. -/
theorem sealLast_any {Xi : Type} (F : FileDescription Xi) (hs : F.sealLast = true) :
    (F.first.blocksInOrder.getLast?.any fun b => !b.rounds.isEmpty) = true := by
  first
    | exact hs
    | (unfold FileDescription.sealLast at hs
       have hg : F.first.blocksInOrder.getLast? =
           some { F.first.last with planOk := F.first.last.planOk && F.first.last.hasNoClaimsAndNothingAfter } := by
         first
           | (unfold Chain.blocksInOrder; exact List.getLast?_concat)
           | simp [Chain.flat]
       rw [hg]
       simpa using hs)

/-- **The stretches tile the three chains of every description.** -/
theorem fitsOfData : FitsOfData := by
  intro Xi F file D h hs C Y S₁ S₂ S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r g₁ g₂ g₃ hc
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hok, rfl⟩ := data_ok F file D h
  obtain ⟨w₁, w₂, w₃⟩ := written_as file F.roundsDeclaredByBlocks _ hR
  refine fitsOfOk _ R₁ R₂ R₃ _ _ _ _ _ _ w₁ w₂ w₃ hok C Y S₁ S₂ S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂ b₃ l₃
    rest₁ rest₂ rest₃ r (flat_of_map _ _ g₁) (flat_of_map _ _ g₂) (flat_of_map _ _ g₃) ?_ hc
  rw [lastRounds_eq, g₁, List.getLast?_map]
  have hq := sealLast_any F hs
  cases hg : F.first.blocksInOrder.getLast? with
  | none => rw [hg] at hq; cases hq
  | some b =>
    rw [hg] at hq
    have hne : b.rounds ≠ [] := by
      intro e
      simp [e] at hq
    show 1 ≤ b.rounds.length
    exact List.length_pos_iff.2 hne

end VerifiableInference.Desc.Sound
