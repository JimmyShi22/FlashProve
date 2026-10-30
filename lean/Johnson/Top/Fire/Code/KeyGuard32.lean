-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyGuard32.lean (guard_32 SAYS WHICH TREE ω IS THE NUMBER OF: Omega's tree in the HANDED shared chain's book): THE KEY FILE's LAST CHAIN, ROW 3.2 (the own proximity test): THE WOVEN PROMISE's HISTORY HANDS THE K12 LAW ITS GUARD BEHIND THE DOOR: «the book is in order BY THE ORDER» (BookOrdW, Johnson/Desc/K12/Law/FirstBookW.lean) at the verifier's state that Seat.enterOwn hands the kind's block. NO CLAUSE OF THE TABLES (the history).
OBJECT: the guard of the law at row 3.2 · USER: row 3.2's payers (K12's files: the law's half; other files: the promise's half) · LETTERS: X N P D.
  ok_of_toOption       glue
  guard_32           PROVED: Hist₃ (Fk X N P) D 2 a · BookAtEnd ⟹ ∀ t, Seat.enterOwn a.2 = .ok t → ∃ q tO, ‹the handed shared state's book›.place[‹its oOmega›]? = some q ∧ ‹that book›.trees[q.1]? = some tO ∧ BookOrdW ‹the first chain's end's roots› tO.number t.book ∧ t.book.trees.size = ‹these› + 1 ∧ t.roots = 0: ONE CALL of door_W (Johnson/Desc/K12/Law/BookWDoor.lean), at the start's yes (starts_fkD) and the two blocks' yeses (Reached.last, twice; second_flat).
  roots_of_aSide19     PROVED: at the first chain's end the roots received are the stages of the ranges' test + 2 (the book-keeping's count of trees, and BookStep's first half): so guard_32's «a.1.2.1.d.roots» is a PUBLIC number where ASide … 19 holds
  bookAtEnd_of_aSide   PROVED: BookAtEnd from «ASide … 19 at every state reached at 19» (aSide_of_hist): moreB's last conjunct.
BookAtEnd X N P D: A NAMED PREMISE: at every verifier's state that the first chain reaches behind its last block the book is in order (BookStep 0). BY READING, NO TERM OF On₃' HANDS «the handed first state meets shape₁ … 19» (shapeB₃ reads St₃ alone; Free₃ the last chain's own state alone): BUT Hist₃ hands Hist₂'s end and that Hist₁'s end (hist₃_handed | hist₂_handed, RowsWoven.lean). WHO PAYS IT: aSide_of_hist at 19 (under its seven Gaps) · or the lighter walk «every block's yes keeps BookStep 0», whose five blocks (4 | 5 | 10 | 11 | 15) are open. (Where
this and lean/THEOREM.md differ, the page holds.) «The mask has come»: by report
paid by the step's own yes: not here. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.KeyASideAtFk
import Johnson.RunOne.KeySeams23
import Johnson.RunOne.KeyCut23
import Johnson.Desc.K12.Law.BookWDoor
import Johnson.Desc.Sound.BookInOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Xi)
open VerifiableInference.Desc.K12 (T12)
open Johnson.RunOne.KeyRows1 Johnson.RunOne.KeyRows23

theorem ok_of_toOption {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok b => exact congrArg Except.ok (Option.some.inj h)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)

/-- **At the first chain's end the book is in order.** -/
def BookAtEnd : Prop := ∀ a : Xi × FirstState, Hist₁ (Fk X N P) D (Fk X N P).first.blocksInOrder.length a → BookStep 0 a.2.d.book a.2.d.roots

theorem guard_32 (hE : BookAtEnd X N P D) (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D 2 a) (t : T12)
    (ht : VerifiableInference.Desc.K12.Seat.enterOwn a.2 = .ok t) :
    ∃ (q : Nat × Nat) (tO : Tree), a.1.2.2.book.place[a.1.2.2.loc.oOmega]? = some q ∧ a.1.2.2.book.trees[q.1]? = some tO ∧
      H2K.First.BookOrdW a.1.2.1.d.roots tO.number t.book ∧ t.book.trees.size = a.1.2.1.d.roots + 1 ∧ t.roots = 0 := by
  obtain ⟨f, hfl, -, -, hfd⟩ := second_flat X N P
  obtain ⟨a₁, b₁, rs₁, cols₁, hr₁, hb₁, hd₁, -⟩ := Reached.last h
  obtain ⟨a₀, b₀, rs₀, cols₀, hr₀, hb₀, hd₀, -⟩ := Reached.last hr₁
  have hfl' : (Fk X N P).second.blocksInOrder = [f, seat (VerifiableInference.Desc.Third.takenSources (ownTest P)), seat (own₃ P), seat (end₃At X P)] := hfl
  rw [hfl'] at hb₀ hb₁
  have q₀ : b₀ = (held f : Block ((Xi × FirstState × St₂) × St₃) Claim) := (Option.some.inj hb₀).symm
  have q₁ : b₁ = (held (seat (Cl := Claim) (VerifiableInference.Desc.Third.takenSources (ownTest P))) : Block ((Xi × FirstState × St₂) × St₃) Claim) := (Option.some.inj hb₁).symm
  rw [q₀] at hd₀
  rw [q₁] at hd₁
  obtain ⟨e₀, d₀⟩ := held_decide f a₀ _ _ a₁ hd₀
  obtain ⟨e₁, d₁⟩ := held_decide (seat (Cl := Claim) (VerifiableInference.Desc.Third.takenSources (ownTest P))) a₁ _ _ a hd₁
  obtain ⟨hH, hst⟩ : Hist₂ (Fk X N P) D (Fk X N P).shared.blocksInOrder.length ((a₀.1.1, a₀.1.2.1), a₀.1.2.2) ∧
      ((Fk X N P).start₃ a₀.1.1 a₀.1.2.1 a₀.1.2.2).toOption = some a₀.2 := hr₀
  obtain ⟨o, l, -, ⟨-, ob, -, oo⟩, hs⟩ := starts_fkD X N P a₀.1.1 a₀.1.2.1 a₀.1.2.2 a₀.2 (ok_of_toOption hst)
  have hB := hE (a₀.1.1, a₀.1.2.1) (hist₂_handed (Fk X N P) D _ _ hH)
  rw [hfd] at d₀
  rw [seat_decide] at d₁
  have ea : a.1 = a₀.1 := e₁.trans e₀
  obtain ⟨q, tO, h1, h2, h3, h4, h5⟩ := H2K.First.door_W (Cl := Unit) (thirdPar X.chains) (ownTest P) _ _ _ _ _ _ _ o a₀.2 a₁.2 a.2 _ _ _ _ hs d₀ d₁
    (fun z T hT => by have := hB.2 z T hT; rwa [Nat.zero_add] at this) t ht
  rw [ob, oo] at h1
  rw [ob] at h2
  rw [ea]
  exact ⟨q, tO, h1, h2, h3, h4, h5⟩

/-- The roots received at the first chain's end: a public number. -/
theorem roots_of_aSide19 (one : OneTime) (at_ : Where) (s : FirstState) (h : ASide one at_ 19 s) : s.d.roots = one.ranges.stages.length + 2 := by
  have ht : ties₁ one 19 s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h.1).1
  have hb : BookStep 0 s.d.book s.d.roots := by
    have ht' := ht
    unfold ties₁ moreB at ht'
    simp only [Bool.and_eq_true] at ht'
    exact (bookStep_iff 0 s.d.book s.d.roots).1 ht'.1.2.2
  unfold ties₁ sizesB at ht
  simp only [Bool.and_eq_true, beq_iff_eq, counts₁] at ht
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨-, -⟩, c⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := ht
  rw [hb.1]
  simpa using c

/-- From the state's side at the end. -/
theorem bookAtEnd_of_aSide (at_ : Where) (hlen : (Fk X N P).first.blocksInOrder.length = 19)
    (h : ∀ a : Xi × FirstState, Hist₁ (Fk X N P) D 19 a → ASide (oneAt X) at_ 19 a.2) : BookAtEnd X N P D := by
  intro a ha
  rw [hlen] at ha
  have hs := (h a ha).1
  have ht : ties₁ (oneAt X) 19 a.2 = true := ((shape₁_iff _ _ _ _ _ _ _).1 hs).1
  unfold ties₁ moreB at ht
  simp only [Bool.and_eq_true] at ht
  exact (bookStep_iff 0 a.2.d.book a.2.d.roots).1 ht.1.2.2

end

end LPFD

#print axioms LPFD.guard_32
#print axioms LPFD.roots_of_aSide19
#print axioms LPFD.bookAtEnd_of_aSide
