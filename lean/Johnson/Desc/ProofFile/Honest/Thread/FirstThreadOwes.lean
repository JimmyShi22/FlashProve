-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstThreadOwes.lean: `OwesS` AT THE FIRST THREAD OF A RETURN OF THE
MAKER. `owesS_firstK` (GatherFirstJ.lean) is stated at letters; here its letters are the values of
`firstThread` (TheFirstThread.lean), so the kinds' columns are asked at that one thread.

  `owesS_firstThread`   the statement at any letter `Said` that gives `SaidOk`
  `FirstWalk`   `SaidWalk` from `firstStand`: the letter of the field `owes₁`; `saidOk_of_walk` gives
    `hSaid` there

What these are. Conditional lemmas on our own definitions. None is one of the library's goals.

Limits.
  * All limits of GatherFirstJ.lean stand. The columns stay to be paid by the kinds.
  * `hB`: the seat makes a base. `seatGround` is then that base's ground.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.GatherFirstJ
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.DoorWalk
import Johnson.Desc.ProofFile.Honest.Thread.SaidOkOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName Block)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T parts4)

variable {W₀ Rc Tr X₀ X : Type}

/-- **`OwesS` at the first thread of a return of the maker.** -/
theorem owesS_firstThread {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf A.Z Bs.G₀) s s' →
      digitsStand A.Z 24 s → digitsStand A.Z 24 s')
    (noHalf : ∀ g ∈ A.H.first, g.place.kind ≠ KindName.frame) {Vh : Nat}
    (hno : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 6 → ∀ p,
      P5J.At.ps[14 * l + IM.nAt l + j]? = some p → ∀ g ∈ A.H.first, g.place ≠ p)
    (hhalf : A.H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh))
    (htst : ∀ l, l < 25 → ∀ blk, h.firstChain.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk →
      ∀ s rs cols s' n, blk.step 0 s rs cols = .ok (s', n) →
        fallsAfterBatching (firstFalls A parts.numbers) h.firstChain l s = none)
    (hPhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → PlaysS (firstLetters h parts w).thread Said (14 * l + i + 2))
    (hPback : ∀ l, l < 25 → PlaysS (firstLetters h parts w).thread Said (14 * l + IM.nAt l + 5))
    (hP353 : PlaysS (firstLetters h parts w).thread Said 353) (hP354 : PlaysS (firstLetters h parts w).thread Said 354)
    (hP355 : PlaysS (firstLetters h parts w).thread Said 355) (hP356 : PlaysS (firstLetters h parts w).thread Said 356)
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l →
      ∀ j : VerifiableInference.Desc.First.Item, j ∈ ((firstLetters h parts w).thread.row (14 * l + i + 2)).owes →
      (j ∈ (firstLetters h parts w).thread.opened (14 * l + i + 2) →
        (∀ m t, j ≠ VerifiableInference.Desc.First.Item.pin m t) ∧ j ≠ VerifiableInference.Desc.First.Item.pinI ∧ j ≠ VerifiableInference.Desc.First.Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ VerifiableInference.Desc.First.Item.constr m q) →
      ExchangeAtS (firstLetters h parts w).thread Said (14 * l + i + 2) j)
    (hXback : ∀ l, l < 25 → ∀ c, c = 2 ∨ c = 4 ∨ c = 5 →
      ∀ j : VerifiableInference.Desc.First.Item, j ∈ ((firstLetters h parts w).thread.row (14 * l + IM.nAt l + c)).owes →
      (j ∈ (firstLetters h parts w).thread.opened (14 * l + IM.nAt l + c) →
        (∀ m t, j ≠ VerifiableInference.Desc.First.Item.pin m t) ∧ j ≠ VerifiableInference.Desc.First.Item.pinI ∧ j ≠ VerifiableInference.Desc.First.Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ VerifiableInference.Desc.First.Item.constr m q) →
      ExchangeAtS (firstLetters h parts w).thread Said (14 * l + IM.nAt l + c) j)
    (hX353 : ∀ j : VerifiableInference.Desc.First.Item, j ∈ ((firstLetters h parts w).thread.row (353)).owes →
      (j ∈ (firstLetters h parts w).thread.opened (353) →
        (∀ m t, j ≠ VerifiableInference.Desc.First.Item.pin m t) ∧ j ≠ VerifiableInference.Desc.First.Item.pinI ∧ j ≠ VerifiableInference.Desc.First.Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ VerifiableInference.Desc.First.Item.constr m q) →
      ExchangeAtS (firstLetters h parts w).thread Said (353) j)
    (hX355 : ∀ j : VerifiableInference.Desc.First.Item, j ∈ ((firstLetters h parts w).thread.row (355)).owes →
      (j ∈ (firstLetters h parts w).thread.opened (355) →
        (∀ m t, j ≠ VerifiableInference.Desc.First.Item.pin m t) ∧ j ≠ VerifiableInference.Desc.First.Item.pinI ∧ j ≠ VerifiableInference.Desc.First.Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ VerifiableInference.Desc.First.Item.constr m q) →
      ExchangeAtS (firstLetters h parts w).thread Said (355) j)
    (hX356 : ∀ j : VerifiableInference.Desc.First.Item, j ∈ ((firstLetters h parts w).thread.row (356)).owes →
      (j ∈ (firstLetters h parts w).thread.opened (356) →
        (∀ m t, j ≠ VerifiableInference.Desc.First.Item.pin m t) ∧ j ≠ VerifiableInference.Desc.First.Item.pinI ∧ j ≠ VerifiableInference.Desc.First.Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ VerifiableInference.Desc.First.Item.constr m q) →
      ExchangeAtS (firstLetters h parts w).thread Said (356) j)
    (hnx : LaysAtS (firstLetters h parts w).thread Said 345 (riderHead 346 346 fun a => a.F.next = nextSlotBehindTheHead))
    (hs : LaysAtS (firstLetters h parts w).thread Said 345 ⟨346, 347, fun _ _ s => digitsStand A.Z 24 s⟩)
    (hstl : ∀ l, l < 24 →
      LaysAtS (firstLetters h parts w).thread Said (14 * l + 8) ⟨14 * l + 9, 14 * l + 9, fun _ _ s => digitsStand A.Z l s⟩)
    (hatt : ∀ g, g < 12 → LaysAtS (firstLetters h parts w).thread Said (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => heardByAttention A.Z g a.g)) :
    OwesS (firstThread h parts w) Said := by
  show OwesS (firstLetters h parts w).thread Said
  refine owesS_firstK h.head A.H parts.script
    (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain) 0 h.description.t₁
    h.description.t₂ 339 (ReadyInput h.description A.H) w Said hSaid hB hσ rfl noHalf hno hhalf
    (L := firstLetters h parts w) ?_ htst hPhear hPback hP353 hP354 hP355 hP356 hXhear hXback hX353
    hX355 hX356 hnx hs hstl hatt
  unfold firstLetters firstClauses
  rw [seatGround_of_base hB]

/-- **The field `owes₁`**: at `SaidWalk` from the first stand that `ready` gives. -/
abbrev FirstWalk {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)
    (parts : FirstThreadParts A) (R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X) :=
  SaidWalk (firstThread h parts R.own) BaseNil (firstStand (Bk := A.B) A.H R)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.owesS_firstThread
