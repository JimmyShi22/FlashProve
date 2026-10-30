-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/UnderAtReads.lean: WHO PAYS THE PREMISE hU OF THE LAWS ON THE
ROAD TO THE ITEM "tie m" AT THE TRUE CHAIN: IN THE GOALS' SCOPE THE FLAT LIST's ENTRY AT A READS'
PLACE LIES UNDER THE LIBRARY's OWN READS' BLOCK, RETYPED. One statement and its proof. No
definition. PUBLIC: blocks of a chain; no thread, no letters, no Script, no witness, no coin, no
state stands in it.

  underR_reads   from the sealed laws' own three premises (the scope; the files read; IM.Open) and a
                 look-up hb : c.blocksInOrder[K1.noL l false]? = some blk, l < 25:
                 there are X and reads with Bs.G₀.built[l]? = some X and
                 blk.UnderR ((IM.k1Reads Z Bs.G₀ l X (IM.k1Ix l false + 1) reads).retype)

BY TWO SEALED CALLS: k01_flat_reads (Johnson/Desc/K1/Law/K01LawTied.lean), alone_underR
(Johnson/IMR/SeatForm.lean). ITS NEAREST KIN: k01_flat (Johnson/Desc/K1/Law/LettersAtFifty.lean):
the same at both kinds of places, at the block blkL, under "there is" for the entry, WITHOUT the
built link: this keeps the built link at the same X, which the laws that take hU ask for (hY,
hquiet), and speaks of a named entry.

WHAT IT IS FOR: hU in layers_record, head_record, tieStateS_layers, tieStateS_head,
tieStateP_layers, tieRowsS_first, exchangeAtS_tie_first, tieBy_behind_first, tiePlanS_first,
exchangeAtS_tie_plan_first (Johnson/Desc/ProofFile/Honest/K1/Law/). Under ProofFile's head its three
premises are h.scope, h.reads and the O that h.laid.opened hands out.

Limits. X and reads stand under "there is": a caller opens that first and feeds the ten at those
letters. It pays hU and no other premise of the ten. THE FULL SIZE, THE FORMAT's EARLIER HASH.
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.K01LawTied
import Johnson.Desc.K1.Law.LaterOne
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open OnBytes.Model.Stages (LinkH)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **In scope the flat list's entry at a reads' place lies under the library's own reads' block,
retyped, at the built link of that number.** Public. -/
theorem underR_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {blk : Block S ProofFile.Cl} (hb : c.blocksInOrder[K1.noL l false]? = some blk) :
    ∃ (X : LinkH) (reads : Option (List ℕ)), Bs.G₀.built[l]? = some X ∧
      blk.UnderR
        ((IM.k1Reads Z Bs.G₀ l X (IM.k1Ix l false + 1) reads).retype : Block S ProofFile.Cl) := by
  obtain ⟨e, X, reads, he, hX, hu⟩ := K1.k01_flat_reads hS hR O l hl
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  exact ⟨X, reads, hX, IM.alone_underR hu⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.underR_reads
