-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/LendRowOfFit.lean: kind K13, the members' batching: WHERE A BOOK
OF COINS PASSES ITS OWN TESTS AND HAS, AT THE KIND's TWO ADDRESSES, WHAT THE ROW's TWO PARTS STATE,
THE FRAME's `lendRow` (Honest/Frame.lean) RETURNS AT THE KIND's ROW, AT EVERY RUN's COINS. Two
conditional statements with their proofs: one law in two forms; no definition. General in the book,
the description, the kind's numbers, the reader of the weights and the filler of the pile: no
hypothesis on a proof file, no closed fact. PUBLIC DATA ALONE in the premises: a book's tables and
entries (names, addresses, starts, counts) and a description's places and rounds.

Main names: `k13_lendRow_of_lists`: **the law, its premises on the entries as `lendPart` itself
reads them**: what the two parts spend (`spentE`) and what they carry (`carryE`, both
Honest/Law/Rule/Cell.lean). `k13_lendRow_of_fit`: the same from the entries that name each part as
their spender, whole: a corollary.

Why. The kind's tie `CoinsTie` (ExchangeAtM3.lean of this folder) is asked where `lendRow` returns
at the kind's row: where it errs the tie holds for nothing. This is the law by which that return can
be had: `k13_lendRow_at_head` (AtFullSide/K13/LendRowAtHead.lean) has it so, under the library's
head.

What the row states. Two parts (`k13Row`, Part.lean of this folder). Number 0, `quietPart`: it takes
no coin, spends none, carries none. Number 1, the sumcheck's part: it takes none, carries none, and
spends one run, under the name `runName indexMaskRun ⟨k13Place P, 1⟩ "sum"`, 2 kCol + 1 values of
the extension field long.

The premises. hw: the book passes its own tests at a description F. hp: the library's test
`placesOk` at F. hpl: the kind's place is one of the first chain's. hd: the book's first table has,
at the two addresses, the count 0 of each sort, or no row. IN THE FIRST FORM: hs0, hs1: part 0
spends by no entry; the entries by which part 1 spends have, as names and counts, the one run that
the part states: NO MORE IS ASKED OF THEM: `lendPart` holds names and counts alone against the part.
hc: neither part carries by any entry. IN THE SECOND FORM: hm0, hm1: of the book's entries those
that name part 0 as their spender are none; those that name part 1 are one: with the part's own name
and count, spent once. ITS OWNER AND START ARE BOUND IN THE PREMISE BY "there is": `lendPart` holds
neither against the part: that the run can be cut from its owner's coins is had of the book's tests.
So no entry that carries names either part.

How. The frame's `lendPart_of_fit` (Honest/BookLends.lean), twice; its three equations are hd, hs0 |
hs1, hc; in the second form `spentE` and `carryE` are the entries that name the part, cut by the
field once; the run's length by the library's `ownSlots_one_add`
(Johnson/Desc/Part/MaskedSumLedger.lean); `Part.lift` keeps the count and the two lists, by its
text.

Limits. A CONDITIONAL: NONE OF THE PREMISES IS SHOWN HERE, at any book; no instance of the premises
together is typed here. IT SPEAKS AT THE CHAIN NUMBER 0 AND AT `k13Place P`; the tie is asked at the
thread's chain number and at the member's place: that these are the same is not shown here. OF PART
1's ENTRIES NAMES AND COUNTS ALONE ARE ASKED: THE LAW HOLDS AS WELL AT A BOOK THAT LENDS PART 1
ANOTHER OWNER's COINS, OR ANOTHER STRETCH OF THE RIGHT OWNER's: that `lendRow` returns is no word
that the stretch lent is the one that the sender lays. WHAT IS RETURNED IS NOT DESCRIBED: only that
something is. Nothing on the tests that `chainSteps` makes before it gives a row its coins, or on
`ready`. The second form calls the first; `k13_lendRow_at_head` calls the first; nothing else calls
either.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookLends
import Johnson.Desc.ProofFile.Honest.K13.Part
import Johnson.Desc.Part.MaskedSumLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.K13 (Where)

variable {W₀ Rc Xi Tr X : Type}

/-- **WHERE THE BOOK PASSES ITS OWN TESTS AND ITS ENTRIES FOR THE KIND's TWO PARTS ARE, AS NAMES AND
COUNTS, WHAT THE PARTS STATE: `lendRow` RETURNS AT THE KIND's ROW, AT EVERY RUN's COINS.** General
in the book and the description. What it returns is bound by that equation alone. CONDITIONAL: hw,
hp, hpl, hd, hs0, hs1, hc: the head tells them. -/
theorem k13_lendRow_of_lists {Xi' : Type} {F : FileDescription Xi'} {Bk : ProverCoinCounts} (weights : W₀ → Weights)
    (pile : PileOf Xi) (P : Where)
    (hw : Bk.word F = none) (hp : F.placesOk = true) (hpl : k13Place P ∈ placesAt F 0)
    (hd : ∀ j, j < 2 → dueAt (Bk.rowsOf 0) ⟨k13Place P, j⟩ = ⟨0, 0⟩)
    (hs0 : spentE Bk ⟨k13Place P, 0⟩ = [])
    (hs1 : (spentE Bk ⟨k13Place P, 1⟩).map Ahead.named =
      [(runName indexMaskRun ⟨k13Place P, 1⟩ "sum", ⟨0, 2 * P.lin.kCol + 1⟩)])
    (hc : ∀ j, j < 2 → carryE Bk ⟨k13Place P, j⟩ = [])
    (k : Coins Bk) :
    ∃ c, lendRow Bk (Bk.rowsOf 0) (k.look 0) (k13Place P)
      (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts 0 = .ok c := by
  obtain ⟨c0, e0⟩ := lendPart_of_fit (V := Local W₀ Rc Xi Tr) (W := Local W₀ Rc Xi Tr) (Y := X)
    (p := quietPart) hw hp (Or.inl rfl) (a := ⟨k13Place P, 0⟩) hpl (hd 0 (by decide)).symm
    (by rw [hs0]; rfl) (by rw [hc 0 (by decide)]; rfl) k
  obtain ⟨c1, e1⟩ := lendPart_of_fit (V := Local W₀ Rc Xi Tr) (W := Local W₀ Rc Xi Tr) (Y := X)
    (p := (k13Sum P).lift (fun _ => ()) (k13Ask weights pile) (fun _ => ()) fun x _ => x)
    hw hp (Or.inl rfl) (a := ⟨k13Place P, 1⟩) hpl (hd 1 (by decide)).symm
    (by
      rw [hs1]
      show [(runName indexMaskRun ⟨k13Place P, 1⟩ "sum", (⟨0, 2 * P.lin.kCol + 1⟩ : Due))] =
        [(runName indexMaskRun ⟨k13Place P, 1⟩ "sum", (⟨0, ownRun (k13Shape P.lin.kCol)⟩ : Due))]
      congr 3
      show 2 * P.lin.kCol + 1 =
        0 + VerifiableInference.Desc.Part.MaskedSum.ownSlots
          (List.replicate P.lin.kCol (VerifiableInference.Desc.Part.MaskedSum.Var.plain 3))
      rw [VerifiableInference.Desc.Part.MaskedSum.ownSlots_one_add, List.map_replicate,
        List.sum_replicate]
      show 2 * P.lin.kCol + 1 = 0 + (1 + P.lin.kCol * 2)
      omega)
    (by rw [hc 1 (by decide)]; rfl) k
  refine ⟨(c0, c1, ()), ?_⟩
  show lendRow Bk (Bk.rowsOf 0) (k.look 0) (k13Place P)
    [quietPart, (k13Sum P).lift (fun _ => ()) (k13Ask weights pile) (fun _ => ()) fun x _ => x]
    0 = .ok (c0, c1, ())
  simp only [lendRow]
  rw [e0, e1]
  rfl

/-- **THE SAME, FROM THE ENTRIES THAT NAME EACH PART AS THEIR SPENDER, WHOLE**: none at part 0; at
part 1 one, with the part's own name and count, spent once. Its owner and start are bound in the
premise. CONDITIONAL: hw, hp, hpl, hd, hm0, hm1. -/
theorem k13_lendRow_of_fit {Xi' : Type} {F : FileDescription Xi'} {Bk : ProverCoinCounts} (weights : W₀ → Weights)
    (pile : PileOf Xi) (P : Where)
    (hw : Bk.word F = none) (hp : F.placesOk = true) (hpl : k13Place P ∈ placesAt F 0)
    (hd : ∀ j, j < 2 → dueAt (Bk.rowsOf 0) ⟨k13Place P, j⟩ = ⟨0, 0⟩)
    (hm0 : Bk.ahead.filter (fun e => e.spender == ⟨k13Place P, 0⟩) = [])
    (hm1 : ∃ o s, Bk.ahead.filter (fun e => e.spender == ⟨k13Place P, 1⟩) =
      [⟨runName indexMaskRun ⟨k13Place P, 1⟩ "sum", o, s, ⟨0, 2 * P.lin.kCol + 1⟩,
        ⟨k13Place P, 1⟩, true⟩])
    (k : Coins Bk) :
    ∃ c, lendRow Bk (Bk.rowsOf 0) (k.look 0) (k13Place P)
      (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts 0 = .ok c := by
  obtain ⟨o, s, hm1⟩ := hm1
  refine k13_lendRow_of_lists weights pile P hw hp hpl hd (by unfold spentE; rw [hm0]; rfl)
    (by unfold spentE; rw [hm1]; rfl) (fun j hj => ?_) k
  unfold carryE
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h0 | rfl
  · obtain rfl : j = 0 := Nat.lt_one_iff.1 h0
    rw [hm0]
    rfl
  · rw [hm1]
    rfl

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_lendRow_of_lists
#print axioms ProofFile.Honest.K13.k13_lendRow_of_fit
