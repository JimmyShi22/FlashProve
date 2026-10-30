-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/KeepsAtFifty.lean: BEHIND AN ACCEPTING STEP OF ONE OF THE KIND
K1's FIFTY LATER MEMBERS, UNDER THE LIBRARY's HEAD: THE MEMBER's PLACE, THE KIND's CLAUSE AT THAT
PLACE AND THE SIX RELATIONS OF `K1LaterRels`. A join of laws that lie.

  `k1_place_fifty`, `k1_clause_fifty`, `k1_rels_fifty`

Limits. The step is a hypothesis. Nothing on any property. Full size, the format's second hash function.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.KeepsMember
import Johnson.Desc.ProofFile.Honest.Thread.K1LaterRels
import Johnson.Desc.K1.Law.K01LawTied
import Johnson.Desc.K1.Law.LaterOne
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open Johnson.Desc.First.Walk.Tied (StepYes)
open ProofFile.Honest.FirstThread (K1LaterRels rels_commit_member rels_reads_member)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE MEMBER's PLACE.** -/
theorem k1_place_fifty (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) (d : Bool)
    {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[K1.noL l d]? = some blk) :
    blk.place = IM.k1PlaceL l d := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  cases d with
  | true =>
    obtain ⟨e, digits, he, hla⟩ := K1.k01_flat_digits h.scope h.reads O l hl
    obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
    exact IM.alone_place hla
  | false =>
    obtain ⟨e, Xl, reads, he, -, hla⟩ := K1.k01_flat_reads h.scope h.reads O l hl
    obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
    exact IM.alone_place hla

/-- **THE KIND's CLAUSE AT THE PLACE.** -/
theorem k1_clause_fifty (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) (d : Bool)
    {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[K1.noL l d]? = some blk) {s s' : TS}
    (y : StepYes 0 blk s s') : K1KeepsAt (IM.k1PlaceL l d) s s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  cases d with
  | true =>
    obtain ⟨e, digits, he, hla⟩ := K1.k01_flat_digits h.scope h.reads O l hl
    obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
    have k := k1_commit_member hla y
    by_cases e24 : l = 24
    · subst e24
      exact k
    · have ep : IM.k1PlaceL l true = { chain := 1, link := some l, piece := 6, kind := .K1 } := by
        show (⟨1, some l, (5 + if l = 24 then 1 else 0) + 1, KindName.K1⟩ : Place) = _
        rw [if_neg e24]
      rw [ep]
      exact k
  | false =>
    obtain ⟨e, Xl, reads, he, -, hla⟩ := K1.k01_flat_reads h.scope h.reads O l hl
    obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
    have k := k1_reads_member hla y
    by_cases e24 : l = 24
    · subst e24
      exact k
    · have ep : IM.k1PlaceL l false = { chain := 1, link := some l, piece := 4, kind := .K1 } := by
        show (⟨1, some l, (3 + if l = 24 then 1 else 0) + 1, KindName.K1⟩ : Place) = _
        rw [if_neg e24]
      rw [ep]
      exact k

/-- **THE SIX RELATIONS.** -/
theorem k1_rels_fifty (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) (d : Bool)
    {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[K1.noL l d]? = some blk) {s s' : TS}
    (y : StepYes 0 blk s s') : K1LaterRels s s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  cases d with
  | true =>
    obtain ⟨e, digits, he, hla⟩ := K1.k01_flat_digits h.scope h.reads O l hl
    obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
    exact rels_commit_member hla y
  | false =>
    obtain ⟨e, Xl, reads, he, -, hla⟩ := K1.k01_flat_reads h.scope h.reads O l hl
    obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
    exact rels_reads_member hla y

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_place_fifty
#print axioms ProofFile.Honest.K1.k1_clause_fifty
#print axioms ProofFile.Honest.K1.k1_rels_fifty
