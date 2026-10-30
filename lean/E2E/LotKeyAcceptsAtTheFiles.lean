-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotKeyAcceptsAtTheFiles.lean: the two statements on the honest offline prover from which
completeness of the offline part follows, at the level of the interactive oracle proof. The offline
part is the proof in the key file, one of the protocol's three proofs. The prover is
`(thePartsAt Z).prover d`, exactly as it is written in Lean.

What is proved. `Z` stands for the three public files. All premises are public: `Z` yields a
description `d` of the offline protocol (`offlineDescription Z = .ok d`), is in scope (`InScope Z`,
Ladder.lean), passes the public test `protocolDataWellFormed (asDescriptionFiles Z)`, can be read (`readFiles Z = .ok pp`),
and `fullPub = some K₀` (some such `K₀` exists: `full_made`).
  `theKeyLots`: all twelve fields of `TheKeyLots Z d K₀` hold
    (AtFullSide/Honest/TheKeyLetters.lean). They are the premises from which E2E/OfflineJoin.lean
    derives the two statements below.
  `keyAccepts_at_the_files`: `KeyAccepts`: at every weight matrix at which some request is served,
    every randomness of the table, every out-of-domain seed (none is set aside) and every coin of
    the prover, the offline part's interactive verifier accepts every transcript that is the
    prover's own run, whatever the nonces, that passes the proof-of-work tests and whose challenges
    lie outside the set at which the prover stops. No further challenge is excepted.
  `offlineDebts_at_the_files`: `OfflineDebts`, the list of facts that the completeness theorem for
    the honest provers asks of the offline prover, for two predicates on inputs, bound by "there
    are", which every such input meets (fields `tied`, `tiedM`). Here the set of challenges at
    which an honest run may be refused is empty, and the three bounds are 0 (they bound measures
    over all challenges; the error of completeness is 0 among the challenges that pass the
    proof-of-work tests: see below): on the measure of the challenges at which the prover stops for
    a public reason, of those at which it stops for a private reason, and of the refusals
    (trivially, the set being empty). What carries the weight is the field `accepted`, read as
    below.
  `OfflineDebtsAt Z`, `KeyAcceptsAt Z`: the same two statements as propositions about the public
    files alone: a description exists, and the statement holds at it. `offlineDebtsAt_of_live` and
    `keyAcceptsAt_of_live` prove them for all files that are in scope and pass that test.
  `offlineDebtsAt_zFull`, `keyAcceptsAt_zFull`: at the stored full-size public files `storedPublicFiles`, with
    no premise. `read_zFull`: these files can be read. That some request is served there is
    `servedRequest_met` (E2E/CompleteAsIOPServedLaws.lean), not used here.

How to read the zeros. The acceptance law (`AccLaw`, Johnson/Prover/Law/Defs.lean) speaks of the
transcripts that pass the verifier's proof-of-work tests. So the error of completeness that follows
from these statements is 0 among the challenges that pass these tests; of the raw space of
challenges nearly all fail them. The search for nonces, and its chance of failure, belongs to the
compiled protocol and is not counted here.

Limits. The file states no completeness: that completeness of the offline part follows is
`offlineEveryCoin_of_debts` (E2E/CompleteAsIOPOffline.lean), which also asks
`(workAtFiles Z).Faithful`. This file only calls other theorems: every field is proved in a file
named in the header comment of E2E/LotAtTheKeyLetters.lean, in E2E/OfflineLastThree.lean or in
E2E/LotDoorBehindLaid.lean, and it is worth no more than these; some of the files beneath call
themselves provisional in their own header comments: rely on their statements, not on their
comments. In scope, at the sizes and the allocation of the prover's coins (`book`) that are fixed
in the library. At weight matrices at which some request is served. It speaks of the offline prover
alone: nothing on the online prover, and so, by itself, nothing on the completeness of the protocol
as a whole. `KeyAccepts` and `OfflineDebts` say what their definitions say (E2E/RoadHonDebts.lean,
E2E/CompleteAsIOPOffline.lean), with the measures of the sets at which the prover stops as the
header comment of E2E/OfflineJoin.lean says. It is about the Lean prover as written, including the
default values that its definitions return where a list or a table has no entry. Nothing on
soundness, hiding or binding.
-/
import E2E.LotAtTheKeyLettersDoor
import E2E.LotDoorBehindLaid
import E2E.LotStandLaidAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest.TheKeyLetters
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes.Slice (frS)
open AtPublicFiles.Bridge (KeyAccepts)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub full_made)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles storedPublicFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open AtPublicFiles.Committed (PadZ pads_nonempty)

local instance (priority := high) keyAcceptsAtTheFilesPad : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) keyAcceptsAtTheFilesRun : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) keyAcceptsAtTheFilesRunDefault : Inhabited RunValue := ⟨fun _ => 0⟩

section
variable {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub}

/-- `BehindTheDoor Z d K₀` (E2E/LotAtTheKeyLetters.lean): one instance of `lotDoorBehindLaid`. -/
theorem behindTheDoor_at_letters (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀) : BehindTheDoor Z d K₀ :=
  fun w x c ht R hR =>
    AtPublicFiles.FirstH.Lots.lotDoorBehindLaid (tableUnused Z K₀) (rest Z K₀) publicPart hd scope live hK₀ w x ht
      ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R hR

/-- **All twelve fields of `TheKeyLots`.** -/
theorem theKeyLots (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀) : TheKeyLots Z d K₀ :=
  theKeyLots_of_door hd scope live hK₀ (behindTheDoor_at_letters hd scope live hK₀)

/-- **What the completeness theorem asks of the offline prover, at public files `Z`.** -/
theorem offlineDebts_at_the_files {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hK₀ : fullPub = some K₀) :
    ∃ Tied TiedM, OfflineDebts Z (descOf d) (thePartsAt Z).book ((thePartsAt Z).prover d) runValueBytes
      runValueBytes (offlineStart d) (ServedRequest committerCoinCountLessOne Z hr) (fun _ _ _ => ∅) Tied TiedM 0 0 0 :=
  offlineDebts_at_letters hr hd scope live hK₀ (theKeyLots hd scope live hK₀)

/-- **The offline verifier accepts the honest prover's own run at every transcript that passes the
proof-of-work tests, outside the challenges at which the prover stops; at public files `Z`.** -/
theorem keyAccepts_at_the_files {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hK₀ : fullPub = some K₀) :
    KeyAccepts (offlineProverWithEncodedTable Z (descOf d) (thePartsAt Z).book ((thePartsAt Z).prover d) runValueBytes runValueBytes
        (offlineStart d))
      (lettersZ Z allZeroDigest []).W (fun _ _ _ => ∅) (fun _ _ => ∅) (ServedRequest committerCoinCountLessOne Z hr) :=
  keyAccepts_at_letters hr hd scope live hK₀ (theKeyLots hd scope live hK₀)

end

/-- `OfflineDebts` for the offline prover, as a proposition about the public files alone. The
theorems below prove it for a variable `Z` and apply it once: at the concrete files Lean's kernel
would unfold them. -/
def OfflineDebtsAt (Z : PublicFiles) : Prop :=
  ∀ {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp), ∃ d, offlineDescription Z = .ok d ∧
    ∃ Tied TiedM, OfflineDebts Z (descOf d) (thePartsAt Z).book ((thePartsAt Z).prover d) runValueBytes
      runValueBytes (offlineStart d) (ServedRequest committerCoinCountLessOne Z hr) (fun _ _ _ => ∅) Tied TiedM 0 0 0

/-- `KeyAccepts` for the offline prover, as a proposition about the public files alone. -/
def KeyAcceptsAt (Z : PublicFiles) : Prop :=
  ∀ {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp), ∃ d, offlineDescription Z = .ok d ∧
    KeyAccepts (offlineProverWithEncodedTable Z (descOf d) (thePartsAt Z).book ((thePartsAt Z).prover d) runValueBytes runValueBytes
        (offlineStart d))
      (lettersZ Z allZeroDigest []).W (fun _ _ _ => ∅) (fun _ _ => ∅) (ServedRequest committerCoinCountLessOne Z hr)

theorem offlineDebtsAt_of_live (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) : OfflineDebtsAt Z := by
  intro pp hr
  obtain ⟨d, hd⟩ := AtPublicFiles.FirstH.Lots.described_of_live Z live
  obtain ⟨K₀, hK₀⟩ := full_made
  exact ⟨d, hd, offlineDebts_at_the_files hr hd scope live hK₀⟩

theorem keyAcceptsAt_of_live (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) : KeyAcceptsAt Z := by
  intro pp hr
  obtain ⟨d, hd⟩ := AtPublicFiles.FirstH.Lots.described_of_live Z live
  obtain ⟨K₀, hK₀⟩ := full_made
  exact ⟨d, hd, keyAccepts_at_the_files hr hd scope live hK₀⟩

/-- The stored full-size public files can be read. -/
theorem read_zFull : ∃ pp, readFiles storedPublicFiles = .ok pp :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  ⟨pp, hr⟩

/-- **At the stored full-size public files, with no premise.** -/
theorem offlineDebtsAt_zFull : OfflineDebtsAt storedPublicFiles :=
  offlineDebtsAt_of_live storedPublicFiles VerifierAndGoals.inScope_full AtFullSide.Top.theLive_zFull

/-- **At the stored full-size public files, with no premise.** -/
theorem keyAcceptsAt_zFull : KeyAcceptsAt storedPublicFiles :=
  keyAcceptsAt_of_live storedPublicFiles VerifierAndGoals.inScope_full AtFullSide.Top.theLive_zFull

end AtFullSide.Honest.TheKeyLetters

#check @AtFullSide.Honest.TheKeyLetters.theKeyLots
#check @AtFullSide.Honest.TheKeyLetters.offlineDebts_at_the_files
#check @AtFullSide.Honest.TheKeyLetters.keyAccepts_at_the_files
#check @AtFullSide.Honest.TheKeyLetters.offlineDebtsAt_zFull
#check @AtFullSide.Honest.TheKeyLetters.keyAcceptsAt_zFull
#print AtFullSide.Honest.TheKeyLetters.KeyAcceptsAt
#print AtFullSide.Honest.TheKeyLetters.OfflineDebtsAt
#print axioms AtFullSide.Honest.TheKeyLetters.behindTheDoor_at_letters
#print axioms AtFullSide.Honest.TheKeyLetters.theKeyLots
#print axioms AtFullSide.Honest.TheKeyLetters.offlineDebts_at_the_files
#print axioms AtFullSide.Honest.TheKeyLetters.keyAccepts_at_the_files
#print axioms AtFullSide.Honest.TheKeyLetters.offlineDebtsAt_of_live
#print axioms AtFullSide.Honest.TheKeyLetters.keyAcceptsAt_of_live
#print axioms AtFullSide.Honest.TheKeyLetters.read_zFull
#print axioms AtFullSide.Honest.TheKeyLetters.offlineDebtsAt_zFull
#print axioms AtFullSide.Honest.TheKeyLetters.keyAcceptsAt_zFull
