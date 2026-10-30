-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowLenAtConst.lean.
WHAT IT DOES NOT SHOW. No soundness. ONE NUMBER. AT THE SECOND HASH FUNCTION ITSELF (o :=
OnBytes.secondHashFunction) ALONE: the stone beneath stands there. The full size alone. No example.
WORDS. "The flat list": the first chain's sub-protocols, in order.
LETTERS. No "there is".
OBJECT. The first chain cF of the table's files' head AtMg.
USER. Law/RowAtConst.lean: atRow_more's premise k + 1 < cF.blocksInOrder.length, at K7's and K6's two places
(338, 341) and at every other kind's.
WHAT IT IS. IN SCOPE THE FIRST CHAIN HAS 358 SUB-PROTOCOLS.
atRow_length: by At.places_paid (P5J/PlacesPaid.lean: the sub-protocols' places
are the written list) and the written list's length, by the kernel. atRow_in: so k + 1 <
cF.blocksInOrder.length for every k < 357.
NEAREST RELATIVES (by report): Desc/Sound/EndFirstAt: places_358
(the written list's length), which does not lie beneath this file; len₁ in other files, at the
tower's own letter. No line joins them to cF.blocksInOrder.length.

-/
import Johnson.P5J.PlacesPaid
import Johnson.P5J.AtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- The written list of places has 358 entries. -/
theorem ps_length : P5J.At.ps.length = 358 := by
  decide +kernel

/-- **In scope the first chain has 358 sub-protocols.** -/
theorem atRow_length (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : cF.blocksInOrder.length = 358 := by
  have e := congrArg List.length (P5J.At.places_paid h.scope h.reads h.laid)
  unfold VerifiableInference.Desc.First.blockPlaces at e
  rw [List.length_map, ps_length] at e
  exact e

/-- So every place but the last has a place behind it. -/
theorem atRow_in (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (k : Nat) (hk : k < 357) :
    k + 1 < cF.blocksInOrder.length := by
  rw [atRow_length h]
  omega

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.ps_length
#print axioms VerifiableInference.Desc.Kinds.Head.Law.atRow_length
#print axioms VerifiableInference.Desc.Kinds.Head.Law.atRow_in
