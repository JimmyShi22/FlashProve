-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/FirstSizeAtHead.lean: the kind "the code switch" (K2): WHERE THE HEAD's PREMISE h AND
THE OPENING O HOLD, THE PLAN's FIRST SEGMENT BEGINS WITH A SENDING OF FOUR MESSAGES. One statement
with its proof: calls; no definition. PUBLIC DATA ALONE. A small file of its own, so that both of
K2's authors' joins at the maker's book can import it (AtFullSide/K2/FreshFirstAtTheBook.lean ·
AtFullSide/K2/OpeningRowsAtTheBook.lean). Its place is AtFullSide/, since its one import lives
there.

  `first_size_at_head` h · O · the first segment is Sg ⊢ `(Sg.sent.headD #[]).size = 4`

WHY. A law that runs over "every message n below the size", or speaks at "the size less one", holds
of nothing where the size is 0: this pins it.

How. `segments_at_head` (Johnson/Desc/ProofFile/Honest/K2/Law/PlacesWritten.lean): under the head
and the opening the plan's segments are the written list · `head_mem_take_one` and the first half of
`openingCarriedW` (AtFullSide/K2/CarriedAtTheBook.lean, by the writers of K11's merge): at the
written list's first segment the size is 4: a closed fact that Lean's kernel evaluates. These three
steps stand inside that file's own proof of `carried_opening_at_book`, which drops the size.

Limits. The first sending of the first segment alone. CarriedAtTheBook.lean's own limits come with
it, among them, in its words: "The full size; the format's second hash function."; and the closed fact is
evaluated under two raised options. Nothing on any property.
-/
import AtFullSide.K2.CarriedAtTheBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open AtFullSide.K2 (openingCarriedW head_mem_take_one)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- Under the head and the opening the first segment's first sending has four messages. -/
theorem first_size_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) :
    (Sg.sent.headD #[]).size = 4 := by
  rw [segments_at_head h.toAtMg O] at hS
  have k := List.all_eq_true.1 openingCarriedW.1 Sg (head_mem_take_one hS)
  exact of_decide_eq_true (Bool.and_eq_true_iff.1 k).1

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.first_size_at_head
