-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/K3/LookupsOwnNoCoin.lean:
AT ANY FILLING: at the book of whatever onlineProverFromPublicFiles returns, the maker's filling a letter.
The kind "lookup" (K3). No entry of the book of coins that onlineProverFromPublicFiles (Honest/AtPure.lean) returns names
a part of the kind K3 as its owner. So no part spends a coin of a lookup's part: the one premise of
the frame's fresh_of_nil (Honest/Law/ToyLaw.lean) at the lookup's rows. "Honest/" stands for
Johnson/Desc/ProofFile/Honest/.

  ownerKindIsNot                        the test on one entry, at a kind
  noWantedEntryIsOwnedByALookup, noSegmentCarryIsOwnedByALookup, noShortEntryIsOwnedByALookup
                                        the three evaluations in Lean's kernel, one for each of the
                                        three parts of rawAheadW that rawAll_whole asks of
  noWrittenEntryIsOwnedByALookup        no entry of rawAheadW has an owner of the kind K3
  aWrittenEntryIsOwnedByTheKindOne      A NEGATIVE TEST: the same test at the kind K1 says no
  publicPartAtAnyFillingIsTheHeads      what onlineProverFromPublicFiles returns under the head has the head's public
                                        part
  lookupsOwnNoCoinInTheBookAtAnyFilling
                                        at every site of lookSites at that public part, every part
                                        number and every spender: the returned book has no spent
                                        run of that part's coins

How it goes. The evaluations follow AtFullSide/K14/RawTest6Written.lean. rawAll_whole
(AtFullSide/K14/RawEntriesKit.lean) joins them. makers_ahead_at_atPure
(AtFullSide/K14/MakersBookOne.lean) says that the returned book's entries are rawAheadW.
site_place_head
(Honest/K3/Law/Thread/AtLink.lean) says that a site's place is IM.k3Place, whose kind is K3.
spentBy_of_lendsNone (Honest/Small/Book.lean) gives the empty list.

Kin. plain_no_owner (Honest/BookPlainOwner.lean)
is the general law: it names no kind and needs no evaluation: it reads the makers' text and says the
same of any sub-protocol of the first chain none of whose rounds is named "SEND seed". This file
evaluates the written book instead.

Where the sites are read: at the head's public part, and publicPartAtAnyFillingIsTheHeads says
that this is the public part of what onlineProverFromPublicFiles returns.

Hypotheses that remain. head: the library's one hypothesis at the full size. made: that onlineProverFromPublicFiles
returns. The filling is general: the book does not read it (atPure_book_same,
Honest/AtPureBook.lean).

Limits. A fact on written values: WP's limit and the written sendings' stand, and the merges are
mergesByName's guess. The test reads an entry's owner alone. It says nothing of what a sender lays,
and nothing of the owners' own field fresh. That onlineProverFromPublicFiles returns is not shown here. No property of
the protocol is claimed.
-/
import AtFullSide.K14.MakersBookOne
import AtFullSide.K14.RawEntriesKit
import AtFullSide.K14.RawK3Rest
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLink
import Johnson.Desc.ProofFile.Honest.Small.Book

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest.K3
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law
open AtFullSide.K14
open VerifiableInference.Desc (KindName Chain)

/-- The entry's owner stands at a place of another kind than k. -/
def ownerKindIsNot (k : KindName) (e : Ahead) : Bool := e.owner.place.kind != k

/-- The test accepts the stretches' entries: an evaluation by Lean's kernel. -/
theorem noWantedEntryIsOwnedByALookup :
    (rawWantsW.map (·.entry)).all (ownerKindIsNot .K3) = true := by
  decide +kernel

/-- The test accepts the carrying entries of the chain of segments: an evaluation, after the reader
of labels is rewritten as in raw6_seg (AtFullSide/K14/RawTest6Written.lean). -/
theorem noSegmentCarryIsOwnedByALookup : rawSegW.all (ownerKindIsNot .K3) = true := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test accepts the eight written pieces: an evaluation. -/
theorem noShortEntryIsOwnedByALookup : rawShortW.all (ownerKindIsNot .K3) = true := by
  decide +kernel

/-- **No entry of the written book has an owner of the kind K3.** -/
theorem noWrittenEntryIsOwnedByALookup :
    rawAheadW.all (fun e => e.owner.place.kind != .K3) = true :=
  rawAll_whole (ownerKindIsNot .K3) noWantedEntryIsOwnedByALookup noSegmentCarryIsOwnedByALookup
    noShortEntryIsOwnedByALookup

/-- A NEGATIVE TEST: at the kind K1 the stretches' entries are refused: the owner of link 0's mask
row is a part of that kind. An evaluation. -/
theorem aWantedEntryIsOwnedByTheKindOne :
    (rawWantsW.map (·.entry)).all (ownerKindIsNot .K1) = false := by
  decide +kernel

/-- **A NEGATIVE TEST: the same test at the kind K1 says no, at the whole written book.** -/
theorem aWrittenEntryIsOwnedByTheKindOne :
    rawAheadW.all (fun e => e.owner.place.kind != .K1) = false := by
  have h : (rawWantsW.map (·.entry)).all (fun e => e.owner.place.kind != .K1) = false :=
    aWantedEntryIsOwnedByTheKindOne
  rw [rawAhead_split, List.all_append, h, Bool.false_and]

section AnyFilling
variable {files : VerifierAndGoals.PublicFiles} {description : OnBytes.Maker.WholeD} {proofRun : LPFD.Full.RunPF}
  {publicPart : ProofFile.Pub} {places : H2U.Places4} {firstChain : Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {W₀ Rc Tr X₀ X : Type}
  {makersFilling : OnlineProverParts W₀ Rc Tr X₀ X} {returned : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- Where onlineProverFromPublicFiles returns under the head, what it returns has the head's public part. CONDITIONAL:
head, made. -/
theorem publicPartAtAnyFillingIsTheHeads
    (head : P5J.AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain x)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL makersFilling = .ok returned) :
    returned.Z = publicPart :=
  Except.ok.inj ((atPure_ok made).1.symm.trans head.laid.pub)

/-- **AT THE BOOK OF WHATEVER onlineProverFromPublicFiles RETURNS, AT ANY FILLING: NO PART SPENDS A COIN OF A LOOKUP's
PART**, at every site of lookSites at the head's public part, every part number i and every spender
p. CONDITIONAL: head, made. -/
theorem lookupsOwnNoCoinInTheBookAtAnyFilling
    (head : P5J.AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain x)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL makersFilling = .ok returned) :
    ∀ s ∈ lookSites publicPart, ∀ (i : Nat) (p : Addr),
      returned.B.spentBy ⟨s.at_.place, i⟩ p = [] := by
  intro s hs i p
  have hahead : returned.B.ahead = rawAheadW := (makers_ahead_at_atPure head made).1
  have hkind : s.at_.place.kind = .K3 := by
    rw [AtThr.site_place_head head s hs]
  have hnone : Small.lendsNone returned.B ⟨s.at_.place, i⟩ = true := by
    unfold Small.lendsNone
    rw [hahead]
    refine List.all_eq_true.2 fun e he => bne_iff_ne.2 fun heq => ?_
    have hne := List.all_eq_true.1 noWrittenEntryIsOwnedByALookup e he
    have hk : e.owner.place.kind = .K3 := by
      rw [heq]
      exact hkind
    rw [hk] at hne
    exact absurd hne (by decide)
  exact Small.spentBy_of_lendsNone hnone p

end AnyFilling

end AtFullSide.Honest.K3

#print axioms AtFullSide.Honest.K3.noWantedEntryIsOwnedByALookup
#print axioms AtFullSide.Honest.K3.noSegmentCarryIsOwnedByALookup
#print axioms AtFullSide.Honest.K3.noShortEntryIsOwnedByALookup
#print axioms AtFullSide.Honest.K3.noWrittenEntryIsOwnedByALookup
#print axioms AtFullSide.Honest.K3.aWantedEntryIsOwnedByTheKindOne
#print axioms AtFullSide.Honest.K3.aWrittenEntryIsOwnedByTheKindOne
#print axioms AtFullSide.Honest.K3.publicPartAtAnyFillingIsTheHeads
#print axioms AtFullSide.Honest.K3.lookupsOwnNoCoinInTheBookAtAnyFilling
