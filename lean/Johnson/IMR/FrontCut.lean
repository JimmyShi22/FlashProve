-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FrontCut.lean: IN FRONT OF THE BLOCKS BEHIND THE LAST LINK THE WALK
OF Johnson/IMR/SeatKeeps.lean ASKS NOTHING OF KINDS K12 AND K13, AND NO YES OF THE WHOLE FILE:

  descPure_stretch: SeatKeeps R okB okP, its two premises at the seat, onlineDescription's return: over ANY
    STRETCH l₂ of frontOf c (Johnson/Goal/Meaning/KeepsDriver.lean), from any record: where the
    fold over l₂ returns, the record in front is related to the record behind (the library's
    Keeps.foldBlocks_keeps).
  seatKeeps_front: Johnson/IMR/BookSeat.lean's seatKeeps_sentence from its two clauses recv and same
    alone.
  descPure_sentenceFront: so a sentence P on the book and the count of roots that holds of an empty
    book holds at every record that a fold from the first record over a front part of frontOf c
    returns: UNDER recv AND same ALONE.
  descPure_fitsFront: Book.BookFits there: NO PREMISE BUT onlineDescription's RETURN.
  descPure_placesFront: PlacesStay (Johnson/IMR/BookFitsSeat.lean) over any stretch of frontOf c: NO
    PREMISE
    BUT onlineDescription's RETURN.
OBJECT: ProofFile.onlineDescription's value, at every o. USER: whoever shows the row on the book's names (its
records stand inside the links).
seatKeeps_front REPEATS seatKeeps_sentence's twenty lines
(Johnson/IMR/BookSeat.lean).
No soundness.
-/
import Johnson.IMR.BookFitsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Book (BookFits)
open ProofFile (Pub)

variable {R : S → S → Prop} {P : TreeBook → Nat → Prop} {okB : Array Stages.LinkH → Prop}
  {okP : K2.HeadPar → Prop}

/-- **Over any stretch in front of the blocks behind the last link.** -/
theorem descPure_stretch (H : SeatKeeps R okB okP) {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst}
    (hB : ∀ Z, ProofFile.pureRoad.pub o pol lay KL = .ok Z → okB Z.p.built.links)
    (hP : ∀ Z, ProofFile.pureRoad.pub o pol lay KL = .ok Z → ∀ G,
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G → ∀ l Q, P1K2.pureLetters G l = some Q → okP Q)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      ∀ (l₁ l₂ l₃ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ ++ l₃ →
        ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
          (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn),
          foldBlocks ft l₂ s rs cols = .ok r → R s r.1 := by
  obtain ⟨Z, A, B, c, hZ, e, k0, k⟩ := descPure_keepsP H hB hP h
  refine ⟨Z, A, B, c, hZ, e, flat_eq k0, fun l₁ l₂ l₃ hl ft s rs cols r hf => ?_⟩
  exact Keeps.foldBlocks_keeps R H.refl H.trans ft l₂
    (fun b hb => k b (by rw [hl]; simp [hb])) s rs cols r hf

theorem seatKeeps_front
    (recv : ∀ {L : Type} (d d' : _root_.Desc.Plain.DState L) (sent : Array OracleNotice)
      (ids : Array Nat), Ground.recvP 0 d sent = some (ids, d') → P d.book d.roots →
      P d'.book d'.roots)
    (same : ∀ (A B : TreeBook) (r : Nat), K2.SameNumbers A B → P A r → P B r) :
    SeatKeeps (PR P) where
  refl := fun _ => id
  trans := fun _ _ _ h k x => k (h x)
  frames := fun _ h => framesOf_core pr_same h
  k1First := fun q gp h0 => firstAtS_core (coreRecv_sentence recv) q gp h0
  k1Later := fun q gp l p m a h0 => laterAt_core (coreRecv_sentence recv) q gp l p m a h0
  reads := fun h => whole_core pr_same (readsQuietAt_quiet h)
  k3 := fun c r X cs sh a _ h => whole_core pr_same (theStated_quiet c r X cs sh a h)
  k4 := fun p => whole_core pr_same (blockAtC_quiet p)
  k5 := fun W l g bf _ h => whole_core pr_same (k5AtN_quiet W l g bf h)
  k6 := fun h => whole_core pr_same (seatedClaims_quiet h)
  k7 := fun W l => whole_core pr_same (k7Of_quiet W l)
  k8 := fun p => whole_core pr_same (k8Whole_quiet p)
  closeOf := closeOf_core pr_same
  batch := fun p _ hcl => batch_core pr_same (fun h k x => k (h x)) p hcl
  k11 := fun Q => whole_core pr_same (headMerge11_quiet Q)
  k2 := fun _ h0 => ⟨fun _ _ _ _ h hN => K2.yes_hands (P := P)
      (fun d d₁ sent ids e k => recv d d₁ sent ids (h0 ▸ e) k) same h hN,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  front := fun _ => pr_fn fun _ _ h => K2.headFrontQ_book h
  openQ := fun _ _ => pr_fn fun _ _ h => K2.headOpenQ_book h
  finFront := pr_fn fun _ _ h => K2.finishFrontQ_book h
  finBehind := pr_fn fun _ _ h => K2.finishBehindQ_book h

/-- **The sentence at every record in front of the blocks behind the last link.** -/
theorem descPure_sentenceFront
    (recv : ∀ {L : Type} (d d' : _root_.Desc.Plain.DState L) (sent : Array OracleNotice)
      (ids : Array Nat), Ground.recvP 0 d sent = some (ids, d') → P d.book d.roots →
      P d'.book d'.roots)
    (same : ∀ (A B : TreeBook) (r : Nat), K2.SameNumbers A B → P A r → P B r)
    (h0 : P { trees := #[], place := #[] } 0)
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      ∀ (p : ProofFile.InstPub) (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
        ∀ (ft : Nat) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
          (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn),
          foldBlocks ft l₁ (ProofFile.startS Z p) rs cols = .ok r → P r.1.book r.1.roots := by
  obtain ⟨Z, A, B, c, hZ, e, hf, k⟩ := descPure_stretch (seatKeeps_front recv same)
    (fun _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) h
  refine ⟨Z, A, B, c, hZ, e, hf, fun p l₁ l₂ hl ft rs cols r hr => ?_⟩
  refine k [] l₁ l₂ (by rw [hl]; rfl) ft _ rs cols r hr ?_
  show P (ProofFile.startS Z p).book (ProofFile.startS Z p).roots
  rw [(start_empty hZ p).1, (start_empty hZ p).2]
  exact h0

/-- **THE BOOK's TWO TABLES FIT AT EVERY RECORD IN FRONT OF THE BLOCKS BEHIND THE LAST LINK.** -/
theorem descPure_fitsFront {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      ∀ (p : ProofFile.InstPub) (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
        ∀ (ft : Nat) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
          (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn),
          foldBlocks ft l₁ (ProofFile.startS Z p) rs cols = .ok r → BookFits r.1.book :=
  descPure_sentenceFront (P := fun B _ => BookFits B)
    (fun d d' sent ids e k => Book.recvP_fits 0 d d' sent ids e k)
    (fun _ _ _ hs k => K2.fits_same hs k) Book.bookFits_empty h

/-- **EVERY OLDER PLACE STAYS, OVER ANY STRETCH IN FRONT OF THE BLOCKS BEHIND THE LAST LINK.** -/
theorem descPure_placesFront {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      ∀ (l₁ l₂ l₃ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ ++ l₃ →
        ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
          (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn),
          foldBlocks ft l₂ s rs cols = .ok r → PlacesStay s.book r.1.book :=
  descPure_stretch seatKeeps_places (fun _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) h

#print axioms descPure_stretch
#print axioms descPure_sentenceFront
#print axioms descPure_fitsFront
#print axioms descPure_placesFront

end Meaning.K2
