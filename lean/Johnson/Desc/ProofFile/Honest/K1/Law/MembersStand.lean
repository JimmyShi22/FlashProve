-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/MembersStand.lean: THE SHARED "SENDING" (the kind K1): UNDER
THE LIBRARY's HEAD A BLOCK STANDS AT EACH OF K1's 52 NUMBERS OF THE FIRST CHAIN's FLAT LIST: number
2, the fifty numbers K1.noL l d, and number 356. PUBLIC: a list's length and numbers. Four theorems;
no definition.

  - stands_head: UNDER h (the library's head: A HYPOTHESIS): at every number b below 358 the first
    chain's flat list holds a block.
  - stands_two, stands_fifty, stands_w: so at number 2, at K1.noL l d (hl : l < 25), and at number
    356.

For whom. ProofFile's forms at a member (PlaysS, BehindS, ExchangeS, AcceptedS: Honest/Thread/PaysS.lean;
ExchangeAtS, LaysAtS: Honest/Thread/SharesS.lean) begin "for every blk with T.bs[b]? = some blk":
where no block stands at the number they ask nothing. With this file that way to be idle is shut at
K1's numbers: so for playsS_k1_two and playsS_k1_fifty (PlaysAtMembers.lean), which do not ask the
member. And the record's field member (K1Seated, Honest/K1/Seated.lean) is not idle for want of a
block.

The road. The sealed Meaning.Carry.flat_len (Johnson/IMR/RootsWhole.lean): in scope the list has 358
entries; the head hands it its three premises (h.scope, h.reads, and the opening out of
h.laid.opened). Kin: the sealed Meaning.K2.flat_358; ProofFile's head_len (Honest/Thread/SteppedYes.lean).
The fifty numbers lie below 357: the sealed noL_lt
(Johnson/Desc/K1/Law/K01Law.lean).
Kin, too: the sealed block_at_no (Johnson/P1K2R/DebtsConst.lean): stands_head's end, from the scope
and an opening as premises: what the head hands.

Limits. WHICH block stands there is not said here: its shape: k1_two_inScope, k1_fifty_inScope
(MemberInScope.lean). THE FULL SIZE ALONE. IT STANDS OVER THE SEAL ALONE. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.IMR.RootsWhole
import Johnson.P5J.MgAtAll
import Johnson.Desc.K1.Law.K01Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **UNDER THE HEAD A BLOCK STANDS AT EVERY NUMBER BELOW 358.** -/
theorem stands_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : ℕ} (hb : b < 358) :
    ∃ blk, cF.blocksInOrder[b]? = some blk := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hl : b < cF.blocksInOrder.length := by
    rw [Meaning.Carry.flat_len h.scope h.reads O]
    exact hb
  exact ⟨cF.blocksInOrder[b], List.getElem?_eq_getElem hl⟩

/-- **AT NUMBER 2.** -/
theorem stands_two (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ blk, cF.blocksInOrder[2]? = some blk := stands_head h (by decide)

/-- **AT EACH OF THE FIFTY.** -/
theorem stands_fifty (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (d : Bool) : ∃ blk, cF.blocksInOrder[K1.noL l d]? = some blk :=
  stands_head h (Nat.lt_succ_of_lt (K1.noL_lt l hl d))

/-- **AT NUMBER 356**, W's sending. -/
theorem stands_w (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ blk, cF.blocksInOrder[356]? = some blk := stands_head h (by decide)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.stands_head
#print axioms ProofFile.Honest.K1.stands_two
#print axioms ProofFile.Honest.K1.stands_fifty
#print axioms ProofFile.Honest.K1.stands_w
