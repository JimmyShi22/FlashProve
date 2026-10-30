-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/MergeTie.lean: ONE TIE OF THE LINK's LAW, WHOLE, AT THE SEAT: at the link
of the description's first chain whose hearing block number 8 is of the kind K11, whatever run
stands at the entry (8, «the merge») of its order stands under the merge's own run `headMergeClaim`:
`HeadTake.tMerge` (Johnson/Desc/First/Link/Law/PayHead.lean) to the letter. Theorems.

What is said. `merge_claims`: a block of the merge's lot states one list: («the merge»,
`headMergeClaim`). `merge_tie`: **the tie**: through `ties_at_seat` (Johnson/LPFK9R/TiesAtSeat.lean:
the driver's guard and the seat's wrappers), «a block of the kind K11 comes from the merge's own
lot» (Johnson/IMR/LotKinds.lean: `lot_of_kind`) and `merge_claims`.

Limits. One of 21 ties. Under the seat's three yeses. Nothing on soundness.

-/
import Johnson.LPFK9R.TiesAtSeat

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.LinkJoin (At Under)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open ProofFile (Cl)

/-- A block of the merge's lot states one list. -/
theorem merge_claims {Z : ProofFile.Pub} {G : ProofFile.Ground} {b : Block S Cl}
    (hb : b ∈ (K11.lot Z).blocks G) : b.claims = [("the merge", headMergeClaim)] := by
  rcases IM.blocks_mem hb with ⟨x, hx, _⟩ | h
  · exact absurd hx (List.not_mem_nil)
  · obtain rfl := List.mem_singleton.1 h
    rfl

variable {o : ProofFile.SecondHashFunctionArgument}

/-- **THE MERGE's TIE, WHOLE, AT THE SEAT.** -/
theorem merge_tie {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub)
    (hk : (kindsBeforeBatching sub (l == 0))[8]? = some KindName.K11) :
    ∃ Lk, c.links[l]? = some Lk ∧
      ∀ run, At Lk (8, "the merge") run → Under run headMergeClaim := by
  obtain ⟨Lk, e1, L, hL, b', hb', ep, t1, _⟩ :=
    ties_at_seat hB hb hc l sub hl 8 .K11 hk (by decide) (by decide) (by decide)
  obtain rfl : L = K11.lot Z := IM.lot_of_kind hL hb' (by rw [ep]; rfl)
  refine ⟨Lk, e1, fun run h => ?_⟩
  obtain ⟨r', h1, hu⟩ := t1 "the merge" run h
  rw [merge_claims hb'] at h1
  obtain rfl : headMergeClaim = r' := Option.some.inj h1
  exact hu

end LPFK9

#print axioms LPFK9.merge_claims
#print axioms LPFK9.merge_tie
