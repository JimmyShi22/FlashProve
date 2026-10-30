-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/MemberInScope.lean: THE SHARED "SENDING" (the kind K1): IN THE
GOALS' SCOPE, THE FIRST CHAIN's OWN MEMBERS AT NUMBER 2 (the opening) AND AT THE FIFTY LATER
SENDINGS HAVE THE KIND's PLACE, ROUNDS AND ORACLE MESSAGES, ARE SENDINGS, AND DO TO THE VERIFIER's
BOOK WHAT A SENDING DOES: three fields of the record of premises K1Seated (Honest/K1/Seated.lean:
shape, isSend, books), to the letter, at the plan of the description's own ground. Six theorems; no
definition. It stands over the library alone; it does not name the record.

Why. A member of the chain's flat list is not the kind's block: it is a seated copy of it: marked,
guarded, renamed, carried to the fold's type of claims (seatedAs, seatedWith,
Johnson/IMR/SeatForm.lean); at number 2 with link 0's "opened" joined behind (Joined,
Johnson/IMR/SameSpot.lean); at "reads" the kind's block has a quiet block joined (k1Reads,
Johnson/IMR/K1Seat.lean).

  - books_under: "books" rides up Under (Johnson/Desc/Sound/HearsOnce.lean): a block that says yes
    only where another does, with the same record behind, books as that one does. Its fellows for
    IsSend lie in the library: isSend_under (Johnson/Desc/K1/Law/AtTable.lean), isSend_underR,
    isSend_retype (Johnson/Desc/K1/Law/SitsLaw.lean).
  - shape_of_joined: a lot's block with a link's "opened" joined behind has the address, and that
    block's rounds and oracle messages. Its rounds: the library's Joined.rounds
    (Johnson/IMR/FirstSeats.lean).
  - k1_two_inScope: UNDER hS, hR, O (the scope, the files read, the description opened: the binders
    of the library's own lemmas on the flat list) and hb : c.blocksInOrder[2]? = some blk: the three fields
    at K1.firstPar Bs.G₀.first (K1.gpOf Z).
  - k1_fifty_inScope: UNDER the same three, hl : l < 25 and hb : c.blocksInOrder[K1.noL l d]? = some blk: the
    three fields at K1.parL Z Bs.G₀ l d (d = false: "reads"; d = true: "digits").
  - k1_two_noMark, k1_fifty_noMark: under the same premises: A YES OF THE MEMBER's DECISION LEAVES
    NO MARK (t.failed = none): the seat's own guard says so (yes_alone, Johnson/IMR/SeatForm.lean;
    Joined.yes, Johnson/IMR/FirstSeats.lean).

By calls: k1_first_sits, hear_at_flat, flatIx_scope, first_under (Johnson/IMR/) ·
isSend_openingZero, openingZero_rec (Johnson/Desc/K1/Law/OpeningZero.lean) · k01_flat_reads,
k01_flat_digits (Johnson/Desc/K1/Law/K01LawTied.lean) · alone_place, alone_rounds, alone_oracles,
alone_underR (Johnson/IMR/SeatForm.lean) · rounds_blk (Johnson/Desc/K1/Law/LettersAtFifty.lean) ·
oracles_k1Quiet (Johnson/Desc/K1/Law/QuietTellsNothing.lean) · isSend_laterAt
(Johnson/Desc/K1/Law/GoodSendPlaces.lean), isSend_k1Reads (Johnson/Desc/K1/Law/BlocksAtLater.lean) ·
commitAtS_booked (Johnson/Desc/K1/Law/BookAtRecord.lean), booked_blkL
(Johnson/Desc/K1/Law/K01Law.lean).

Kin in the library. k01_law_reads, k01_law_digits, k01_law_first (Johnson/Desc/K1/Law/SitsLaw.lean):
IsSend at the real member, told by the link and its place, with PlaceOk, under two premises more on
the written codes and shape (k01_law_reads under a third: LeavesAtt); at the opening in the arm
"alone" only.

Limits. THE PLAN IS THE DESCRIPTION's OWN GROUND's (Z, Bs.G₀): that a prover's job has that plan is
not said here: neither that its ground is this one, nor that its piece's number is k1Ix l d + 1.
That a member stands at the number is a premise (hb). W's sending is not here. Nothing on the
record's seventeen other fields. Nothing on soundness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.LettersAtFifty
import Johnson.Desc.K1.Law.K01LawTied
import Johnson.Desc.K1.Law.K01Law
import Johnson.Desc.K1.Law.SitsLaw
import Johnson.Desc.K1.Law.QuietTellsNothing
import Johnson.Desc.K1.Law.BlocksAtLater
import Johnson.Desc.K1.Law.OpeningZero
import Johnson.IMR.FirstUnder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S)

/-- **"books" rides up Under**: at two types of claims, so that it serves a block carried over by
Block.retype too. -/
theorem books_under {Cl Cl' : Type} {P : K1.Par} {c : Block S Cl'} {b : Block S Cl}
    (hU : c.Under b)
    (h : ∀ s s' r₁ r₂ gs, b.decide s [r₁, r₂] gs = .ok s' →
      K1.Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size) :
    ∀ s s' r₁ r₂ gs, c.decide s [r₁, r₂] gs = .ok s' →
      K1.Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size :=
  fun s s' r₁ r₂ gs hd => h s s' r₁ r₂ gs (hU s _ gs s' hd)

/-- A lot's block with link l's "opened" joined behind: place, rounds and oracle messages. -/
theorem shape_of_joined {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S ProofFile.Cl} {a : Place}
    (h : IM.Joined Z l b b' a) : b.place = a ∧ b.rounds = b'.rounds ∧ b.oracles = b'.oracles := by
  refine ⟨?_, h.rounds, ?_⟩
  · obtain ⟨fs, f, -, -, e⟩ := h
    rw [e]
    rfl
  · obtain ⟨fs, f, -, -, e⟩ := h
    rw [e]
    show b'.oracles ++ [] = b'.oracles
    rw [List.append_nil]

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **NUMBER 2, IN SCOPE**: the member has the opening's place, rounds and oracle messages; it is a
sending of the opening's plan; it books as one. -/
theorem k1_two_inScope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {blk : Block S ProofFile.Cl}
    (hb : c.blocksInOrder[2]? = some blk) :
    (blk.place = (K1.firstPar Bs.G₀.first (K1.gpOf Z)).place ∧
      blk.rounds = K1.rounds (K1.firstPar Bs.G₀.first (K1.gpOf Z)) ∧
      blk.oracles = K1.oracles (K1.firstPar Bs.G₀.first (K1.gpOf Z))) ∧
    K1.IsSend (K1.firstPar Bs.G₀.first (K1.gpOf Z)) (fun s : S => s.st) blk ∧
    ∀ s s' r₁ r₂ gs, blk.decide s [r₁, r₂] gs = .ok s' →
      K1.Booked (K1.firstPar Bs.G₀.first (K1.gpOf Z)) s.book s.st.oracles.size s'.book
        s'.st.oracles.size := by
  obtain ⟨Lk, b, e1, e2, hj⟩ := IM.k1_first_sits hS hR O
  have hix : IM.flatIx c 0 0 = 2 := IM.flatIx_scope hS hR O (l := 0) (by decide) 0
  have hfl : c.blocksInOrder[2]? = some b := by
    have h := IM.hear_at_flat e1 e2
    rwa [hix] at h
  obtain rfl : b = blk := Option.some.inj (hfl.symm.trans hb)
  obtain ⟨e, nm, X, he, -, hu⟩ := IM.first_under hS hR O
  obtain rfl : e = b := Option.some.inj (he.symm.trans hb)
  obtain ⟨hp, hr, ho⟩ := shape_of_joined hj
  exact ⟨⟨hp, hr, ho⟩, K1.isSend_underR hu (K1.isSend_openingZero _ _ _ _ _ _),
    books_under hu.2 fun s s' r₁ r₂ gs hd => (K1.openingZero_rec hd).2.2.2.2.1⟩

/-- **THE FIFTY, IN SCOPE**: the like at link l's "reads" (d = false) and "digits" (d = true). -/
theorem k1_fifty_inScope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) (d : Bool)
    {blk : Block S ProofFile.Cl} (hb : c.blocksInOrder[K1.noL l d]? = some blk) :
    (blk.place = (K1.parL Z Bs.G₀ l d).place ∧ blk.rounds = K1.rounds (K1.parL Z Bs.G₀ l d) ∧
      blk.oracles = K1.oracles (K1.parL Z Bs.G₀ l d)) ∧
    K1.IsSend (K1.parL Z Bs.G₀ l d) (fun s : S => s.st) blk ∧
    ∀ s s' r₁ r₂ gs, blk.decide s [r₁, r₂] gs = .ok s' →
      K1.Booked (K1.parL Z Bs.G₀ l d) s.book s.st.oracles.size s'.book s'.st.oracles.size := by
  cases d with
  | true =>
    obtain ⟨b, digits, h5, h⟩ := K1.k01_flat_digits hS hR O l hl
    obtain rfl : b = blk := Option.some.inj (h5.symm.trans hb)
    exact ⟨⟨IM.alone_place h, IM.alone_rounds h, IM.alone_oracles h⟩,
      K1.isSend_underR (IM.alone_underR h) (K1.isSend_retype (K1.isSend_laterAt _ _ _ _ _ _)),
      books_under (IM.alone_underR h).2 fun s s' r₁ r₂ gs hd =>
        K1.commitAtS_booked _ _ _ _ s s' r₁ r₂ gs hd⟩
  | false =>
    obtain ⟨b, Xl, reads, h5, -, h⟩ := K1.k01_flat_reads hS hR O l hl
    obtain rfl : b = blk := Option.some.inj (h5.symm.trans hb)
    refine ⟨⟨IM.alone_place h, (IM.alone_rounds h).trans (K1.rounds_blk Z Bs.G₀ l false Xl reads),
      (IM.alone_oracles h).trans ?_⟩,
      K1.isSend_underR (IM.alone_underR h) (K1.isSend_retype (K1.isSend_k1Reads _ _ _ _ _ _)),
      books_under (IM.alone_underR h).2 fun s s' r₁ r₂ gs hd =>
        K1.booked_blkL Z Bs.G₀ l false Xl reads s s' r₁ r₂ gs hd⟩
    show (K1.laterAt Bs.G₀.first (K1.gpOf Z) l (IM.k1Ix l false + 1) 1 reads :
      Block S Unit).oracles ++ (IM.k1Quiet Bs.G₀ l Xl).oracles = _
    rw [K1.oracles_k1Quiet, List.append_nil]
    rfl

/-- **A yes of number 2 leaves no mark.** -/
theorem k1_two_noMark (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {blk : Block S ProofFile.Cl}
    (hb : c.blocksInOrder[2]? = some blk) :
    ∀ s rs gs t, blk.decide s rs gs = .ok t → t.failed = none := by
  intro s rs gs t hy
  obtain ⟨Lk, b, e1, e2, hj⟩ := IM.k1_first_sits hS hR O
  have hix : IM.flatIx c 0 0 = 2 := IM.flatIx_scope hS hR O (l := 0) (by decide) 0
  have hfl : c.blocksInOrder[2]? = some b := by
    have h := IM.hear_at_flat e1 e2
    rwa [hix] at h
  obtain rfl : b = blk := Option.some.inj (hfl.symm.trans hb)
  obtain ⟨-, -, -, -, -, -, -, -, h0, -⟩ := hj.yes hy
  exact h0

/-- **A yes of one of the fifty leaves no mark.** -/
theorem k1_fifty_noMark (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) (d : Bool)
    {blk : Block S ProofFile.Cl} (hb : c.blocksInOrder[K1.noL l d]? = some blk) :
    ∀ s rs gs t, blk.decide s rs gs = .ok t → t.failed = none := by
  intro s rs gs t hy
  cases d with
  | true =>
    obtain ⟨b, digits, h5, h⟩ := K1.k01_flat_digits hS hR O l hl
    obtain rfl : b = blk := Option.some.inj (h5.symm.trans hb)
    exact ((IM.yes_alone h (show KindName.K1 ≠ KindName.K7 by decide) s t rs gs).1 hy).2.1
  | false =>
    obtain ⟨b, Xl, reads, h5, -, h⟩ := K1.k01_flat_reads hS hR O l hl
    obtain rfl : b = blk := Option.some.inj (h5.symm.trans hb)
    exact ((IM.yes_alone h (show KindName.K1 ≠ KindName.K7 by decide) s t rs gs).1 hy).2.1

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.books_under
#print axioms ProofFile.Honest.K1.shape_of_joined
#print axioms ProofFile.Honest.K1.k1_two_inScope
#print axioms ProofFile.Honest.K1.k1_fifty_inScope
#print axioms ProofFile.Honest.K1.k1_two_noMark
#print axioms ProofFile.Honest.K1.k1_fifty_noMark
