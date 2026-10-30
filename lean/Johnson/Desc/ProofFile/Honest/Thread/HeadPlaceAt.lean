-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadPlaceAt.lean: under the library's hypothesis `AtMgA`, the
place of the sub-protocol that stands at number `14 * l + i + 2` of the first chain, for a segment
`l` below 25 and an index `i` into the segment's list `kindsBeforeBatching`. By the library's
`P5J.At.places_paid` (the chain's places are the written ones) and `IM.hear_placeW`
(Johnson/IMR/SendsK1.lean). Lemmas that prove a kind's clause at a number use it to name the kind of
the sub-protocol's place. No definition.

  1  `head_place_hear`   the place
  2  `head_kind_att`, `head_kind_lay`   the kinds at an attention segment's and a feed-forward
     segment's indices, as equations on `kindsBeforeBatching` in the form that `head_place_hear` takes

Limits.
  * Full size only, and only under `AtMgA` at the hash function `secondHashFunction` (FirstAt.lean says which
    that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HeadKeepsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName Block)
open VerifiableInference.Desc.First (ModelPart kindsBeforeBatching blockPlaces)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The place of the sub-protocol at number `14 * l + i + 2`. -/
theorem head_place_hear (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l i : Nat} {k : KindName}
    (hl : l < 25) (hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[i]? = some k) {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[14 * l + i + 2]? = some blk) :
    blk.place = { chain := 1, link := some l, piece := i + 1, kind := k } := by
  have e : blockPlaces cF.blocksInOrder = P5J.At.ps := P5J.At.places_paid h.scope h.reads h.laid
  have e' : IM.placesW = P5J.At.ps := HashBuild.placesW_full
  have h1 : (blockPlaces cF.blocksInOrder)[14 * l + i + 2]? = some blk.place := by
    unfold blockPlaces
    rw [List.getElem?_map, hb]
    rfl
  rw [e, ← e', IM.hear_placeW hl hk] at h1
  exact (Option.some.inj h1).symm

/-- At an attention segment the list is that of the sort "attention". -/
theorem head_kind_att {g i : Nat} {k : KindName} (hg : g < 12)
    (hk : (kindsBeforeBatching ModelPart.attention false)[i]? = some k) :
    (kindsBeforeBatching (IM.subAt (2 * g + 1)) ((2 * g + 1) == 0))[i]? = some k := by
  have hz : ((2 * g + 1) == 0) = false := beq_eq_false_iff_ne.2 (by omega)
  rw [att_sub g hg, hz]
  exact hk

/-- At a feed-forward segment the list is that of the sort "layers". -/
theorem head_kind_lay {g i : Nat} {k : KindName} (hg : g < 12)
    (hk : (kindsBeforeBatching ModelPart.layers ((2 * g) == 0))[i]? = some k) :
    (kindsBeforeBatching (IM.subAt (2 * g)) ((2 * g) == 0))[i]? = some k := by
  rw [lay_sub g hg]
  exact hk

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_place_hear
#print axioms ProofFile.Honest.FirstThread.head_kind_att
#print axioms ProofFile.Honest.FirstThread.head_kind_lay
