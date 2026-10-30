-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Carry/Exact.lean: THE EXACT CARRY: the item "carry" of the first chain's
table of joints AS A SENTENCE ON THE WITNESS: the folds, at the carried rows' challenges, of the
closed group's members' and the fresh mask's tables as the witness's words have them, with the kept
members' main tables as they stand, meet the one claim of the carried rows. One definition; and laws
on what the sentence reads. The term of which it is made (`leftAt`) stands in a file of its own
beneath: Johnson/Desc/K2/Honest/Carry/Left.lean. It is meant for the honest side's threads, in the
stead of the library's `carryAtZ` (Johnson/Top/H0/K2Caller/CarryClosed.lean), which reads nothing of
the witness: there the open word's pair stands under a "there is".

  `carryExact` THE SENTENCE: the library's way in (`doorZ`) and the front (`K2.frontAt`) return, and
                    `ClaimTrue` (Johnson/Desc/K2/Honest/Inner/Statement.lean) holds of `leftAt` at
                    the ruled reader's words
  `carryExact_iff` at a state whose way in and front are known: the sentence is the claim there
  `sizesAt_same` with `membersAt_same`, `leftAt_same`: the sizes, the members and what the fold left
                    read of a statement the codes and the shapes alone (the library's `SameShapes`,
                    Johnson/Top/H0/K2Hands/FrameOfFront.lean)
  `carryExact_alike` THE SENTENCE IS ONE AT TWO STATES WHOSE WAYS IN AND FRONTS AGREE IN: the codes
                    and every message's shape (`SameShapes`) · every message's seat under the book ·
                    the carried rows · the target. It is blind to ledgers, marks, sample rows,
                    groups

Places from a code's length up to the next power of two: `ClaimTrue`'s sums on the kept members run
over them. Under `Codes.lengthsOk` (every length is a power of two: OnBytes/Iop/Ground.lean), which
the law that spends the sentence asks, there are none. NEAR, NOT CALLED: `Alike.sizes` and
`AlikeKept`'s like (Johnson/Desc/K2/Honest/Returns/Alike.lean, AlikeKept.lean): `sizesAt_same` under
stronger premises (the messages' sample rows and pads alike too; or the kept members' alone).

Limits. THE SENTENCE IS FALSE WHERE THE WAY IN OR THE FRONT REFUSES; `carryExact_alike` asks both
ways in and both fronts known: where one refuses it says nothing, and there the two sentences may
part. THE SENTENCE SPEAKS AT THE CARRIED ROWS' OWN LAYOUT; an honest prover's closing folds by
`foldEnd`, which makes the layout anew: THAT THE TWO LAYOUTS ARE ONE IS NOT PROVED HERE: it is owed
by whoever spends the sentence at what such a closing returns (Carry/LayoutSame.lean and
Johnson/Desc/K2/Honest/Returns/LayoutReached.lean treat it). OF m IT READS `ProofFile.pAtK2 Zp m` ALONE
(Johnson/Desc/ProofFile/CarryAt.lean): where Zp has no place whose switch opens group m + 1 that is
`deadP2`, whose field `stands` is `.link`: THERE NO PLACE OF THE DESCRIPTION ANSWERS TO THE
SENTENCE. That the layout's lists are as long as its members' list is not asked. Whether the
sentence can be met is not proved here. Nothing here ties it to `carryAtZ`, nor to what an honest
prover's closing returns. Nothing on tails, pads or symbols. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Carry.Left
import Johnson.Top.H0.K2Caller.CarryClosed
import Johnson.Desc.Sound.WordsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE formAt)
open OnBytes.Means (Words)
open Johnson.Prover.Send (Rows)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.Sound (MsgT wordsFirst wordsBy_congr seatBy noFirst)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.First.K2 (SameShapes)

/-- **THE EXACT CARRY.** Exact: of an arithmetic carry; no law on distributions; not the frame's
`Good.exact`. Zp: the public parameters. arr: the numbering of the seats. m: the segment whose
closing owes the item; the switch into group m + 1 spends it. Places from a code's length up to the
next power of two are read; under `Codes.lengthsOk` there are none. -/
def carryExact {P Cells Tok : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) :
    Nat → P × S → Strs → Wit Cells Tok MsgT → Prop :=
  fun m a _ v => ∃ t fx, doorZ Zp m a.2 = some t ∧
    First.K2.frontAt (ProofFile.pAtK2 Zp m) t = some fx ∧
    ClaimTrue (sizesAt fx.st fx.f.rows fx.T) fx.f.rows
      (leftAt fx.st fx.f.rows (wordsFirst arr fx.st t.book v))

theorem sizesAt_same {S S' : Statement} (h : SameShapes S S') (old : SingleRows)
    (T : SwitchTarget) : sizesAt S' old T = sizesAt S old T := by
  unfold sizesAt
  simp only [h.codes, h.getD]

theorem membersAt_same {S S' : Statement} (h : SameShapes S S') (old : SingleRows) :
    membersAt S' old = membersAt S old := by
  unfold membersAt
  simp only [h.getD]

theorem leftAt_same {S S' : Statement} (h : SameShapes S S') (old : SingleRows) (w : Words GE) :
    leftAt S' old w = leftAt S old w := by
  unfold leftAt
  simp only [h.codes, membersAt_same h, h.getD]

/-- At a state whose way in and front are known the sentence is the claim there. -/
theorem carryExact_iff {P Cells Tok : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (m : Nat)
    (a : P × S) (y : Strs) (v : Wit Cells Tok MsgT) {t : S} {fx : _root_.Tw.K2.Front}
    (hd : doorZ Zp m a.2 = some t) (hf : First.K2.frontAt (ProofFile.pAtK2 Zp m) t = some fx) :
    carryExact Zp arr m a y v ↔ ClaimTrue (sizesAt fx.st fx.f.rows fx.T) fx.f.rows
      (leftAt fx.st fx.f.rows (wordsFirst arr fx.st t.book v)) := by
  constructor
  · rintro ⟨t', fx', h1, h2, h3⟩
    obtain rfl : t = t' := Option.some.inj (hd.symm.trans h1)
    obtain rfl : fx = fx' := Option.some.inj (hf.symm.trans h2)
    exact h3
  · exact fun h => ⟨t, fx, hd, hf, h⟩

/-- **THE SENTENCE IS ONE AT TWO STATES WHOSE WAYS IN AND FRONTS AGREE** in the codes, the shapes,
the seats, the carried rows and the target. -/
theorem carryExact_alike {P Cells Tok : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (m : Nat)
    (a a' : P × S) (y y' : Strs) (v : Wit Cells Tok MsgT) {t t' : S}
    {fx fx' : _root_.Tw.K2.Front}
    (hd : doorZ Zp m a.2 = some t) (hf : First.K2.frontAt (ProofFile.pAtK2 Zp m) t = some fx)
    (hd' : doorZ Zp m a'.2 = some t')
    (hf' : First.K2.frontAt (ProofFile.pAtK2 Zp m) t' = some fx')
    (hs : SameShapes fx.st fx'.st)
    (hb : ∀ o : Nat, seatBy noFirst t'.book o = seatBy noFirst t.book o)
    (hr : fx'.f.rows = fx.f.rows) (hT : fx'.T = fx.T) :
    carryExact Zp arr m a' y' v ↔ carryExact Zp arr m a y v := by
  rw [carryExact_iff Zp arr m a' y' v hd' hf', carryExact_iff Zp arr m a y v hd hf, hr, hT,
    sizesAt_same hs, leftAt_same hs]
  have hw : wordsFirst arr fx'.st t'.book v = wordsFirst arr fx.st t.book v := by
    funext o part i
    exact wordsBy_congr arr _ _ fx.st fx'.st v o o hs.codes (hb o) (hs.shape o) part i
  rw [hw]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.carryExact
#print axioms VerifiableInference.Desc.K2.Honest.sizesAt_same
#print axioms VerifiableInference.Desc.K2.Honest.membersAt_same
#print axioms VerifiableInference.Desc.K2.Honest.leftAt_same
#print axioms VerifiableInference.Desc.K2.Honest.carryExact_iff
#print axioms VerifiableInference.Desc.K2.Honest.carryExact_alike
