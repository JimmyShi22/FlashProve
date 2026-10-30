-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/DebtByKind.lean: THE SHARED "SENDING" (the kind K1): K1's WHOLE
DEBT UNDER "THE EXCHANGE", IN THE FORM IN WHICH L25's GATHER BY KIND ASKS IT (its hypothesis hXk,
with "p.kind = KindName.K1" for "p.kind ≠ KindName.frame"), AT lettersHead
(Honest/Thread/FirstHead.lean), THE PROVER H AND THE SCRIPT Q FREE. One theorem; no definition. A
JOIN OF LAWS THAT LIE; NO NEW ARGUMENT.

  - k1_exchange_by_kind: at every number b at which the library's written list of places P5J.At.ps
    has a place of the kind K1, and every item j that the thread's row at b owes, but for an item
    that is open in front of b and is a pin, pinI, pinW, or a constr at one of the library's parts4:
    ExchangeAtS (Honest/Thread/SharesS.lean) at b and j.

THE PREMISES: FAMILIES OF WHAT THE LAWS THAT ARE JOINED TAKE; NO NEW FORM. h: the head · RT, RR, RD,
RW: THE RECORD K1Seated (Honest/K1/Seated.lean) AT EACH OF THE 52 NUMBERS: at 2 (the sort
"opening"); at K1.noL l false ("reads l") and K1.noL l true ("digits l") for each l < 25; at 356
(".w"): each "there are a block, a job and the other letters with the record" · hSaid: the family
gives ProofFile's SaidOk · hTie: THE SHARE AT THE ITEM tie l, at each l < 25 · hPile, hWrow: THE SHARES AT
pileOne AND wrow AT 356.

IT PAYS NOTHING AT A SCRIPT. THE 52 RECORDS ARE PREMISES, WHOLE: their fields msgs and pads, THE
TIE, ARE EQUATIONS ON THE SCRIPT Q, PROVED HERE OF NO SCRIPT THAT A RUN HAS. OF THE 232 ITEMS THAT
ARE ASKED AT THE 52 NUMBERS (an evaluation outside this library: 3 at 2 · 176 at "reads" · 50 at
"digits" · 3 at 356) 25 ARE hTie ITSELF, HANDED THROUGH; TWO, pileOne AND wrow AT 356, ARE NOT
PAID HERE AND ARE HANDED THROUGH (kind K13's: k13_seated_m4, Honest/K13/SeatedM4.lean, has them in
the form ExchangeOf, under its own record): THE KIND OF A PLACE IS NOT THE OWNER OF A SHARE;
 205 ARE DERIVED.

For the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: this file imports part 5's twins at the honest meaning
(`noColl`/`shown`/`decodes` := True). (A fence.
HOW IT COMES HERE: by SharesAtMembers.lean, whose k1_shares_reads calls a
fenced law, exchangeAtS_forms_of_tie.)

WHICH LAW PAYS WHAT. From the kind to the number: k1_number_of_kind (NumbersOfKind.lean) · at 2,
"reads", "digits": k1_shares_two, k1_shares_reads, k1_shares_digits (SharesAtMembers.lean) · at 356:
what is asked: asked_w (ShareAtW.lean); pinV: exchange_pinV (ExchangeAtPins.lean).

AT A RETURNED PROVER AND ITS OWN BOOK (H := A.H, onlineProverFromPublicFiles … P = .ok A, P a letter): NO SECOND LAW IS
TYPED: this one is general in H, and its four families of records are what k1Seated_two_at_book
, k1Seated_fifty_at_book (at each l < 25 and both d; its sort is written cond d
(.digits l) (.reads l)), k1Seated_w_at_book (RecordAtBookFill.lean) end in, under two premises on
the lots and THE TIE.

THE BOOK. The sentence, to the letter, with
its first arm, in marks: "At a book whose count at the part's address does not cover the part's due
this law holds for nothing, and it is never quoted as if it spoke there: hasCoins is a premise
here." OUR OWN WORDS: it stands among the premises as the field hasCoins of the record K1Seated, in
each of the four families RT, RR, RD, RW, at k1_exchange_by_kind.

THE THREAD. A rider, which by its word rides
with every quotation, in marks: "an implication: no member: that the thread stands in front of that
member at any run is shown by nobody". OUR OWN WORDS: it was said of another house's bridge;
k1_exchange_by_kind sets it beside "IT PAYS NOTHING AT A
SCRIPT".

Limits. THE FULL SIZE ALONE; the format's second hash function alone. L25's gather by kind is not imported:
that the end is its hypothesis's is held by reading its letter, not by Lean. Each end stands under
the pair ThrS and the member's accepted step, inside ExchangeAtS: an implication. That the premises
can be met together is not proved. It stands over files of L25's, of another house's and of ours;
some are on no seal. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.SharesAtMembers
import Johnson.Desc.ProofFile.Honest.K1.Law.NumbersOfKind
import Johnson.Desc.ProofFile.Honest.K1.Law.ShareAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT Mem)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T parts4)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- IT PAYS NOTHING AT A SCRIPT: THE 52 RECORDS ARE PREMISES, WHOLE; hTie IS THE SHARE AT tie l,
HANDED THROUGH; hPile AND hWrow ARE ANOTHER HOUSE's SHARES AT 356, HANDED THROUGH.
**K1's WHOLE DEBT UNDER "THE EXCHANGE", BY KIND**, in the form of L25's gather by kind. -/
theorem k1_exchange_by_kind
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (RT : ∃ (blk : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst)
      (J : SendJob (PlaceIn ProofFile.Inst) X) (own₀ : X) (arr : ℕ → ℕ → ℕ) (seats₀ : List (ℕ × ℕ))
      (ms : List Mem) (rad : ℕ → ℕ),
      K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 2 blk wit J
        own₀ .opening arr seats₀ ms rad)
    (RR : ∀ l, l < 25 → ∃ (blk : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst)
      (J : SendJob (PlaceIn ProofFile.Inst) X) (own₀ : X) (arr : ℕ → ℕ → ℕ) (seats₀ : List (ℕ × ℕ))
      (ms : List Mem) (rad : ℕ → ℕ),
      K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) (K1.noL l false) blk wit J
        own₀ (.reads l) arr seats₀ ms rad)
    (RD : ∀ l, l < 25 → ∃ (blk : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst)
      (J : SendJob (PlaceIn ProofFile.Inst) X) (own₀ : X) (arr : ℕ → ℕ → ℕ) (seats₀ : List (ℕ × ℕ))
      (ms : List Mem) (rad : ℕ → ℕ),
      K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) (K1.noL l true) blk wit J
        own₀ (.digits l) arr seats₀ ms rad)
    (RW : ∃ (blk : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst)
      (J : SendJob (PlaceIn ProofFile.Inst) X) (own₀ : X) (arr : ℕ → ℕ → ℕ) (seats₀ : List (ℕ × ℕ))
      (ms : List Mem) (rad : ℕ → ℕ),
      K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 356 blk wit J
        own₀ .w arr seats₀ ms rad)
    (hTie : ∀ l, l < 25 →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (K1.noL l false) (.tie l))
    (hPile : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      356 Item.pileOne)
    (hWrow : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      356 Item.wrow) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K1 →
      ∀ j : Item, j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b j := by
  intro b p hb hk j hj hmid
  rcases k1_number_of_kind hb hk with rfl | ⟨l, hl, d, rfl⟩ | rfl
  · obtain ⟨_, _, _, _, _, _, _, _, R⟩ := RT
    exact k1_shares_two h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w R Said j hj hmid
  · cases d
    · obtain ⟨_, _, _, _, _, _, _, _, R⟩ := RR l hl
      exact k1_shares_reads h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl R Said hSaid
        (hTie l hl) j hj hmid
    · obtain ⟨_, _, _, _, _, _, _, _, R⟩ := RD l hl
      exact k1_shares_digits h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl R Said j hj hmid
  · rcases asked_w hj (fun ho => (hmid ho).2.2.1) with rfl | rfl | rfl
    · obtain ⟨_, _, _, _, _, _, _, _, R⟩ := RW
      exact exchange_pinV R Said
    · exact hPile
    · exact hWrow

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_exchange_by_kind
