-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesByKind.lean: owesS_firstThread (Honest/Thread/FirstThreadOwes.lean) ASKED BY THE
PLACE's KIND, AND ITS PREMISES AS ONE STRUCTURE, A HOUSE A FIELD. A joining; nothing is evaluated.

* OwedAt T Said b: ExchangeAtS at each item that the row at b owes, but for an item that is open before
  it and is a pin, pinI, pinW or a constr at one of the four parts: the sentence that hXk asks.
* owedAt_of_exchange, paidAt_of_five, paidAt_of_fiveJ: the bridges from ExchangeS and the two Five forms.
* PlayAsked, OwedAsked: the numbers at which owesS_firstThread asks PlaysS and the sentence, and no
  others. PaidAt: PlaysS and OwedAt at b, each where it is asked. KindPaid T Said κ: PaidAt at every
  number at which the written list of places has a place of kind κ.
* **FirstOwed h parts w Said**: the fields: one a kind; at K12 PlaysS alone (owesS_firstThread asks no
  exchange at 354); the rest of owesS_firstThread's premises by their names there.
* **owes_of_kinds**: OwesS at the first thread from FirstOwed.

Limits. Every field is a premise here. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstThreadOwes
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc (Chain Strs Wit Place KindName Block)
open VerifiableInference.Desc.First (Item)
open ProofFile.Honest ProofFile.Honest.FirstThread
open P5J (parts4)

open VerifiableInference.Desc.Sound (MsgT)
open P5J (CellsM)

section
variable {W₀ Rc Tr X : Type} {Bk : ProverCoinCounts}

/-- The first thread's letters. -/
abbrev LettersF (Bk : ProverCoinCounts) (W₀ Rc Tr X : Type) : Type :=
  Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT

/-- The sentence at one number. -/
def OwedAt (L : LettersF Bk W₀ Rc Tr X)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (b : Nat) : Prop :=
  ∀ j : Item, j ∈ (L.thread.row b).owes →
    (j ∈ L.thread.opened b →
      (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
    ExchangeAtS L.thread Said b j

/-- The numbers at which owesS_firstThread asks that the sender plays. -/
def PlayAsked (b : Nat) : Prop :=
  (∃ l i, l < 25 ∧ i < IM.nAt l ∧ b = 14 * l + i + 2) ∨ (∃ l, l < 25 ∧ b = 14 * l + IM.nAt l + 5) ∨
    b = 353 ∨ b = 354 ∨ b = 355 ∨ b = 356

/-- The numbers at which owesS_firstThread asks the sentence. -/
def OwedAsked (b : Nat) : Prop :=
  (∃ l i, l < 25 ∧ i < IM.nAt l ∧ b = 14 * l + i + 2) ∨
    (∃ l c, l < 25 ∧ (c = 2 ∨ c = 4 ∨ c = 5) ∧ b = 14 * l + IM.nAt l + c) ∨
    b = 353 ∨ b = 355 ∨ b = 356

/-- The sender plays, and the sentence, each where it is asked. -/
def PaidAt (L : LettersF Bk W₀ Rc Tr X)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (b : Nat) : Prop :=
  (PlayAsked b → PlaysS L.thread Said b) ∧ (OwedAsked b → OwedAt L Said b)

/-- From the whole exchange at b. -/
theorem owedAt_of_exchange {L : LettersF Bk W₀ Rc Tr X}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {b : Nat}
    (h : ExchangeS L.thread Said b) : OwedAt L Said b :=
  fun j hj _ => (exchangeS_iff L.thread Said).1 h j hj

/-- From the five statements at b. -/
theorem paidAt_of_five {L : LettersF Bk W₀ Rc Tr X}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    {fall : Nat → VerifiableInference.Desc.First.S → List Fmt.Drawn → Option String} {b : Nat}
    (h : FiveAtBorder L.thread Said fall b) : PaidAt L Said b :=
  ⟨fun _ => h.plays, fun _ => owedAt_of_exchange h.exchange⟩

/-- From the five statements with J at b. -/
theorem paidAt_of_fiveJ {L : LettersF Bk W₀ Rc Tr X}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    {J : Nat → VerifiableInference.Desc.First.S → Prop}
    {fall : Nat → VerifiableInference.Desc.First.S → List Fmt.Drawn → Option String} {b : Nat}
    (h : FiveAtBorderJ L.thread Said J fall b) : PaidAt L Said b :=
  ⟨fun _ => h.plays, fun _ => owedAt_of_exchange h.exchange⟩

/-- **A kind's debt.** -/
def KindPaid (L : LettersF Bk W₀ Rc Tr X)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (κ : KindName) : Prop :=
  ∀ b p, P5J.At.ps[b]? = some p → p.kind = κ → PaidAt L Said b

end

variable {W₀ Rc Tr X₀ X : Type}

/-- What the written list says of the kinds, by the kernel. -/
theorem ps_check : (P5J.At.ps.zipIdx.all fun x =>
    (x.1.kind != KindName.K12 || x.2 == 354) && x.1.kind != KindName.K14 &&
      x.1.kind != KindName.K15) = true := by
  decide +kernel

/-- K12 stands at 354 alone; K14 and K15 stand nowhere on this list. -/
theorem ps_kinds {b : Nat} {p : Place} (h : P5J.At.ps[b]? = some p) :
    (p.kind = KindName.K12 → b = 354) ∧ p.kind ≠ KindName.K14 ∧ p.kind ≠ KindName.K15 := by
  have m : (p, b) ∈ P5J.At.ps.zipIdx := List.mem_zipIdx_iff_getElem?.2 h
  have e := List.all_eq_true.1 ps_check (p, b) m
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, ne_eq] at e
  obtain ⟨⟨e1, e2⟩, e3⟩ := e
  refine ⟨fun k => ?_, e2, e3⟩
  rcases e1 with e1 | e1
  · exact absurd k e1
  · exact e1

/-- The numbers at which owesS_firstThread asks the exchange are not 354. -/
theorem hear_ne : ((List.range 25).all fun l => (List.range (IM.nAt l)).all fun i =>
    14 * l + i + 2 != 354) = true := by
  decide +kernel

theorem back_ne : ((List.range 25).all fun l => [2, 4, 5].all fun c =>
    14 * l + IM.nAt l + c != 354) = true := by
  decide +kernel

/-- **THE FIRST THREAD's DEBT, A HOUSE A FIELD.** -/
structure FirstOwed {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)
    (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (Bs : ProofFile.PureBase) : Prop where
  k1 : KindPaid (firstLetters h parts w) Said KindName.K1
  k2 : KindPaid (firstLetters h parts w) Said KindName.K2
  k3 : KindPaid (firstLetters h parts w) Said KindName.K3
  k4 : KindPaid (firstLetters h parts w) Said KindName.K4
  k5 : KindPaid (firstLetters h parts w) Said KindName.K5
  k6 : KindPaid (firstLetters h parts w) Said KindName.K6
  k7 : KindPaid (firstLetters h parts w) Said KindName.K7
  k8 : KindPaid (firstLetters h parts w) Said KindName.K8
  k9 : KindPaid (firstLetters h parts w) Said KindName.K9
  k10 : KindPaid (firstLetters h parts w) Said KindName.K10
  k11 : KindPaid (firstLetters h parts w) Said KindName.K11
  /-- at K12's one place the sender plays; owesS_firstThread asks no exchange there -/
  k12 : PlaysS (firstLetters h parts w).thread Said 354
  k13 : KindPaid (firstLetters h parts w) Said KindName.K13
  hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf A.Z Bs.G₀) s s' →
    digitsStand A.Z 24 s → digitsStand A.Z 24 s'
  noHalf : ∀ g ∈ A.H.first, g.place.kind ≠ KindName.frame
  hno : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 6 → ∀ p,
    P5J.At.ps[14 * l + IM.nAt l + j]? = some p → ∀ g ∈ A.H.first, g.place ≠ p
  hhalf : ∃ Vh, A.H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh)
  htst : ∀ l, l < 25 → ∀ blk, h.firstChain.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk →
    ∀ s rs cols s' n, blk.step 0 s rs cols = .ok (s', n) →
      fallsAfterBatching (firstFalls A parts.numbers) h.firstChain l s = none
  hnx : LaysAtS (firstLetters h parts w).thread Said 345
    (riderHead 346 346 fun a => a.F.next = nextSlotBehindTheHead)
  hs : LaysAtS (firstLetters h parts w).thread Said 345 ⟨346, 347, fun _ _ s => digitsStand A.Z 24 s⟩
  hstl : ∀ l, l < 24 → LaysAtS (firstLetters h parts w).thread Said (14 * l + 8)
    ⟨14 * l + 9, 14 * l + 9, fun _ _ s => digitsStand A.Z l s⟩
  hatt : ∀ g, g < 12 → LaysAtS (firstLetters h parts w).thread Said (14 * (2 * g + 1) + 3)
    (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => heardByAttention A.Z g a.g)

/-- 354 is not asked the sentence. -/
theorem not_owed_354 : ¬ OwedAsked 354 := by
  rintro (⟨l, i, hl, hi, e⟩ | ⟨l, c, hl, hc, e⟩ | e | e | e)
  · have k := List.all_eq_true.1 (List.all_eq_true.1 hear_ne l (List.mem_range.2 hl)) i
      (List.mem_range.2 hi)
    rw [← e] at k
    exact absurd k (by decide)
  · have k := List.all_eq_true.1 (List.all_eq_true.1 back_ne l (List.mem_range.2 hl)) c
      (by rcases hc with rfl | rfl | rfl <;> decide)
    rw [← e] at k
    exact absurd k (by decide)
  · omega
  · omega
  · omega

/-- A place of the written list that is no frame: what is asked there. -/
theorem paid_of_kinds {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {h : HeadAtReturn files A}
    {parts : FirstThreadParts A} {w : Local W₀ Rc ProofFile.Inst Tr}
    {Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {Bs : ProofFile.PureBase}
    (F : FirstOwed h parts w Said Bs) {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind ≠ KindName.frame) : PaidAt (firstLetters h parts w) Said b := by
  obtain ⟨k12, k14, k15⟩ := ps_kinds hp
  cases hκ : p.kind with
  | K1 => exact F.k1 b p hp hκ
  | K2 => exact F.k2 b p hp hκ
  | K3 => exact F.k3 b p hp hκ
  | K4 => exact F.k4 b p hp hκ
  | K5 => exact F.k5 b p hp hκ
  | K6 => exact F.k6 b p hp hκ
  | K7 => exact F.k7 b p hp hκ
  | K8 => exact F.k8 b p hp hκ
  | K9 => exact F.k9 b p hp hκ
  | K10 => exact F.k10 b p hp hκ
  | K11 => exact F.k11 b p hp hκ
  | K12 =>
    have e := k12 hκ
    subst e
    exact ⟨fun _ => F.k12, fun n => absurd n not_owed_354⟩
  | K13 => exact F.k13 b p hp hκ
  | K14 => exact absurd hκ k14
  | K15 => exact absurd hκ k15
  | frame => exact absurd hκ hk

/-- **OwesS AT THE FIRST THREAD, FROM ITS DEBT BY HOUSES.** -/
theorem owes_of_kinds {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)
    (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (F : FirstOwed h parts w Said Bs) : OwesS (firstThread h parts w) Said := by
  obtain ⟨Vh, hhalf⟩ := F.hhalf
  have Ph : ∀ b, (∃ p, P5J.At.ps[b]? = some p ∧ p.kind ≠ KindName.frame) →
      PaidAt (firstLetters h parts w) Said b :=
    fun b ⟨_, hp, hk⟩ => paid_of_kinds F hp hk
  exact owesS_firstThread h parts w Said hSaid hB F.hσ F.noHalf F.hno hhalf F.htst
    (fun l hl i hi => (Ph _ (house_hear hl hi)).1 (Or.inl ⟨l, i, hl, hi, rfl⟩))
    (fun l hl => (Ph _ (house_back hl (Or.inr (Or.inr (Or.inl rfl))))).1
      (Or.inr (Or.inl ⟨l, hl, rfl⟩)))
    ((Ph _ (house_tail (b := 353) (by decide))).1 (Or.inr (Or.inr (Or.inl rfl))))
    F.k12
    ((Ph _ (house_tail (b := 355) (by decide))).1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    ((Ph _ (house_tail (b := 356) (by decide))).1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    (fun l hl i hi => (Ph _ (house_hear hl hi)).2 (Or.inl ⟨l, i, hl, hi, rfl⟩))
    (fun l hl c hc => (Ph _ (house_back hl (by omega))).2 (Or.inr (Or.inl ⟨l, c, hl, hc, rfl⟩)))
    ((Ph _ (house_tail (b := 353) (by decide))).2 (Or.inr (Or.inr (Or.inl rfl))))
    ((Ph _ (house_tail (b := 355) (by decide))).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    ((Ph _ (house_tail (b := 356) (by decide))).2 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    F.hnx F.hs F.hstl F.hatt

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.ps_kinds
#print axioms Johnson.AtFull.Shape.Scope.paid_of_kinds
#print axioms Johnson.AtFull.Shape.Scope.owes_of_kinds
