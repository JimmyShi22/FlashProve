-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/AtD.lean: THE FORM's HALF AT THE COPY's FILE's OWN PLAN: the public premises of
the link's front's law (front6_all, Johnson/Prover/Link/FormFront6More.lean) ARE MET at the typed
parameters frP (Johnson/Desc/K15/TypedP.lean) and at every pair of written keys.

Main names.
  flat_planOk     a block of the chain's flat list passes its own test on the plan, where the
    description's tests on the plan pass.
  plan_gives      GENERAL IN THE PARAMETERS: the description's tests on the plan give the four.
  plan_full       the four at frP.
  planWord_full   at frP the run's first step passes.
  keyFits_item    the test on a key's sizes does not read which item holds the root.
  keys_full       the two written keys fit frP's table; no seed of theirs has the factor 0.
  front6_full     front6_all at frP and the written keys.

How. NO NEW RUN OF THE KERNEL's decide: planOk_full and okAt_full
(Johnson/Desc/Link/LinkWrittenMade.lean), fr_recordShape (OnBytes/Slice/FullRecBlkFacts.lean),
keyOf_fits (OnBytes/Slice/KeyOfRec.lean) and keyOf_nz (OnBytes/Slice/KeyOfRecBack.lean) are called.

Limits. front6_full keeps Block.step's own two tests as premises: roundsFit at the five rounds, cut
by blocks, and "the columns" at "LINK". That frP is the parameters of the public files in scope is
another file's law (Johnson/Goal/Conditions/LinkInScope.lean [not in this library]). It ends in
front of the proximity
test. Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormFront6More
import Johnson.Desc.Link.LinkWrittenMade
import OnBytes.Slice.KeyOfRecBack
import OnBytes.Flat.EntryTerm
import OnBytes.Slice.FullRecBlkFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Flat
open VerifiableInference.Desc
open Desc.K15 (St Par15 P15 frP linkDeclaredRounds linkRoundsMatchPlan linkDescriptionAt)

/-- Where the description's tests on the plan pass, the first block and every block of the chain's
back pass their own. -/
theorem flat_planOk (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (h : (linkDescriptionAt P plan ok).planOk = true) :
    (Desc.K15.frontBlock P).planOk = true ∧ ∀ b ∈ Desc.K15.blocksOrV P, b.planOk = true := by
  unfold OneChainFileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  have hb : blocksOk (Desc.K15.linkProtocolChain P).blocksInOrder = true := h.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  unfold blocksOk at hb
  rw [List.all_eq_true] at hb
  constructor
  · have := hb { Desc.K15.frontBlock P with
      planOk := (Desc.K15.frontBlock P).planOk && (Desc.K15.frontBlock P).hasNoClaimsAndNothingAfter }
      (by
        unfold Chain.blocksInOrder
        exact List.mem_cons_self)
    simp only [Bool.and_eq_true] at this
    exact this.1.1
  · intro b hbm
    have := hb { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }
      (by
        unfold Chain.blocksInOrder
        refine List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ ?_))
        exact List.mem_map.2 ⟨b, List.mem_append_left _ hbm, rfl⟩)
    simp only [Bool.and_eq_true] at this
    exact this.1.1

/-- **GENERAL IN THE PARAMETERS: the description's tests on the plan give front6_whole's four public
premises.** -/
theorem plan_gives (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (h : (linkDescriptionAt P plan ok).planOk = true) :
    Desc.K15.entries P = some (Desc.K15.fiveOf P) ∧ P.codes.lengthsOk = true ∧
      linkOk P.codes P.S P.set.samples = true ∧ K1.planOkOwn (Desc.K15.parK1 P) = true := by
  obtain ⟨h0, hB⟩ := flat_planOk P plan ok h
  have h0' : (P.codes.lengthsOk && linkOk P.codes P.S P.set.samples) = true := h0
  rw [Bool.and_eq_true] at h0'
  cases he : Desc.K15.entries P with
  | none =>
    have hm : ({ roundlessBlock "the kind's rounds cannot be said" 1 none 1 .ok with
        planOk := false } : Block St Unit) ∈ Desc.K15.blocksOrV P := by
      unfold Desc.K15.blocksOrV Desc.K15.linkBlocksBeforeTest
      simp [he]
    exact absurd (hB _ hm) (by simp)
  | some es =>
    obtain ⟨_, _, rfl⟩ := Desc.K15.entries_inv P es he
    have hm : Desc.K15.sendK1 P ∈ Desc.K15.blocksOrV P := by
      rw [Desc.K15.blocksV_eq P _ he]
      simp
    have hs : (K1.planOkOwn (Desc.K15.parK1 P) && true && true) = true := hB _ hm
    simp only [Bool.and_true] at hs
    exact ⟨rfl, h0'.1, h0'.2, hs⟩

/-- **The four at the copy's file's own parameters.** -/
theorem plan_full :
    Desc.K15.entries frP = some (Desc.K15.fiveOf frP) ∧ frP.codes.lengthsOk = true ∧
      linkOk frP.codes frP.S frP.set.samples = true ∧
      K1.planOkOwn (Desc.K15.parK1 frP) = true :=
  plan_gives frP _ _ Desc.K15.planOk_full

/-- **There the run's first step passes.** -/
theorem planWord_full :
    (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).planWord = none ∧
      linkRoundsMatchPlan frP recordPlan = true := by
  refine ⟨?_, Desc.K15.okAt_full⟩
  unfold OneChainFileDescription.planWord
  rw [if_pos Desc.K15.planOk_full]

/-- The test on a key's sizes does not read which item holds the table's root. -/
theorem keyFits_item (k : TableKey) (s : IndexShape) (i : Nat) (h : Own.keyFits k s = true) :
    Own.keyFits { k with item := i } s = true := h

/-- **The two written keys fit the table, and no seed of theirs has the factor 0.** -/
theorem keys_full (rr : RecFull × RecFull) :
    Own.keyFits (keyOf (fun β : NZ => β.val) rr.1) frP.S.table = true ∧
    Own.keyFits { keyOf (fun β : NZ => β.val) rr.2 with item := 1 } frP.S.table = true ∧
    (keyOf (fun β : NZ => β.val) rr.1).seeds.all (!isZeroE ·.beta) = true ∧
    ({ keyOf (fun β : NZ => β.val) rr.2 with item := 1 } : TableKey).seeds.all
      (!isZeroE ·.beta) = true := by
  have eS : frP.S = recordRead.link := rfl
  have hv : frP.S.table.v = frS.P.v := rfl
  have hs : frP.S.table.answers = 1 := by
    rw [eS]
    exact fr_recordShape.2
  have hl : frP.S.table.cubeBits = 29 := by
    rw [eS]
    exact fr_recordShape.1
  have f1 : Own.keyFits (keyOf (fun β : NZ => β.val) rr.1) frP.S.table = true :=
    (Own.keyFits_eq _ _).trans (keyOf_fits _ rr.1 frP.S.table hv hs hl)
  have f2 : Own.keyFits (keyOf (fun β : NZ => β.val) rr.2) frP.S.table = true :=
    (Own.keyFits_eq _ _).trans (keyOf_fits _ rr.2 frP.S.table hv hs hl)
  exact ⟨f1, keyFits_item _ _ 1 f2, keyOf_nz rr.1, keyOf_nz rr.2⟩

/-- **front6 AT THE COPY's FILE's OWN PLAN AND KEYS**: no premise is left but Block.step's own two
tests. -/
theorem front6_full (rr : RecFull × RecFull) (r0 r1 r2 r3 r4 : Fmt.RoundView) (cols : List OpenedColumn)
    (f0 : roundsFit (Desc.K15.bPoint frP (Desc.K15.fiveOf frP)).rounds [r0] = true)
    (f12 : roundsFit (K1.rounds (Desc.K15.parK1 frP)) [r1, r2] = true)
    (f3 : roundsFit (Desc.K15.bLink frP (Desc.K15.fiveOf frP)).rounds [r3] = true)
    (hc : (cols.take (linkWant frP.S r3).length).map (fun c => (c.1, c.2.1, c.2.2.length)) =
      linkWant frP.S r3)
    (f4 : roundsFit (Desc.K15.bPhi frP (Desc.K15.fiveOf frP)).rounds [r4] = true) :
    ∃ d' G', foldBlocks 0 (Desc.K15.frontBlock frP :: Desc.K15.blocksOrV frP)
        (Desc.K15.first frP.codes (keyOf (fun β : NZ => β.val) rr.1,
          { keyOf (fun β : NZ => β.val) rr.2 with item := 1 })) [r0, r1, r2, r3, r4] cols =
        .ok (d', [], cols.drop (linkWant frP.S r3).length) ∧ LinkSeats frP.par d' G' ∧
      Means.InOrder d'.st ∧
      G'.rows.size =
        2 * frP.S.table.answers + (frP.S.columnsFirst + frP.S.columnsFurther) + 1 := by
  obtain ⟨p1, p2, p3, p4⟩ := plan_full
  obtain ⟨k0, k1, z0, z1⟩ := keys_full rr
  exact front6_all frP _ r0 r1 r2 r3 r4 cols p1 p2 p3 p4 k0 k1 z0 z1 f0 f12 f3 hc f4

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.flat_planOk
#print axioms Johnson.Prover.Link.plan_gives
#print axioms Johnson.Prover.Link.plan_full
#print axioms Johnson.Prover.Link.planWord_full
#print axioms Johnson.Prover.Link.keyFits_item
#print axioms Johnson.Prover.Link.keys_full
#print axioms Johnson.Prover.Link.front6_full
