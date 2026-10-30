-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Top/GatesOpen.lean: what the yes of the description's test on the public files
(`protocolDataWellFormed`, Johnson/Goal/Description/Live.lean) gives at `VerifierAndGoals.storedPublicFiles`, at `VerifierAndGoals.zGap` and at
`storedPublicFiles` under every policy within four bounds: each of the description's three gates is the decision
behind it; the key file's and the proof file's seats return, and their gates are the seats' own
decisions; the rounds' data that the verifier reads are the written data. Calls alone. No
definition: no goal is stated.
Why. The description's three decisions stand behind gates (Johnson/Goal/Description/Gates.lean):
where `protocolDataWellFormed` says no, each gate says no to all, and the verifier rejects every proof
(`theDescription_dead_all`, Johnson/Goal/Description/DeadParser.lean); a statement "whatever the
verifier accepts is right" is empty there. In scope the library shows: the verifier rejects
everything, or the rounds' data of both files are the written ones (`written_or_no_all`,
Johnson/Goal/Description/KeyWritten.lean; both may hold). Here `protocolDataWellFormed`'s yes is spent.
  `gates_of_live`: the three laws `theKeyGate_live`, `theProofGate_live`, `theLinkGate_live`
    as one statement, general in the files. BY ITSELF AN EQUATION "gate = decision" SAYS LITTLE: it
    holds of whatever stands behind the gate, also of a decision that says no to all, and so at some
    files at which `protocolDataWellFormed` says no.
  **`gates_zFull`**, `gates_zGap`, `gates_zAt`: its instances.
  `seats_of_live`: the key file's and the proof file's seats return (`theLive_made`): `theKeyRun`,
    `theProofRun` are the seats' own decisions, not the arm "no to all" (`theKeyRun_ok`,
    `theProofRun_ok`: Johnson/Goal/Description/KeyFold.lean, ProofFold.lean). `protocolDataWellFormed` does not ask the entry file's
    decision whether it says no to all (Live.lean's own limit); its outer match: ThreeTests.lean.
  **`seats_zFull`**, `seats_zGap`, `seats_zAt`: its instances.
  `data_of_live`: in scope and live, the two fields that the verifier reads, `(dataAtFiles flashProveData Z).DK`
    and `.DP`, are `writtenKFull` and `writtenPFull` (`key_built_written`, `proof_built_written`:
    Johnson/Goal/Description/KeyWritten.lean, ProofWritten.lean). These data are the written LISTS
    OF ROUNDS of the two files (entries, stored parts, openings): the shape of the interaction, not
    the bytes of a key file or of a proof file, and nothing of weights. This is not the second arm
    of `written_or_no_all` to the letter: that arm speaks of `theKeyDataAt o`, `theProofDataAt o`;
    under `protocolDataWellFormed`'s yes the two are one at the second hash function.
  **`data_zFull`**, `data_zGap`, `data_zAt`: its instances.
Limits. THAT A GATE IS THE DECISION BEHIND IT IS NOT THAT ANYTHING PASSES IT, and to pass the three
decisions is needed for an accept and is not enough: the commitment's code, the instance's build and
the compiled verifier's own checks on hashes stand beside them. That the verifier accepts some proof
at these files is not shown here; one accept would be less than completeness, which is not shown
either. The decisions are those of the Lean description, on typed views, at the constant `fixedConfigurationDigest` in
the digest's place: no theorem here ties them to the protocol that the programs run. ALL OF IT IS AS
GOOD AS `theLive_zFull` (LiveAtFull.lean), on which every instance here stands. The files are terms
of the Lean library, made of those written in Ladder/Stored.lean, at the full size alone: no Lean
code ties them to the top-level folder examples/; the example's weights are synthetic. `protocolDataWellFormed` is
a fact at a fixed function, the second hash function `OnBytes.secondHashFunction`, and at the constant `fixedConfigurationDigest`
in the digest's place. WHICH THEOREM SPEAKS WHERE. The soundness theorem at exact match
(`VerifierAndGoals.AtTheName.sound_of_verify_at`, Johnson/Goal/Skeleton/SoundOfVerifyAt.lean) has the premise
that the files' policy is (256, 256, 0): it speaks at `storedPublicFiles` alone and is silent, for that other
reason, at `zGap` and at every other policy. There the form under the files' policy alone speaks
(`soundUnderPolicy_of_verify_at`, Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean); the four bounds
take in policies at which it says nothing of the counted tokens (theta = C with a large cap: the
docstring of `G8`, Ladder.lean). This file lies in the side library AtFullSide, which is built with
a larger thread stack (lake build AtFullSide). Nothing on soundness, on a binding of the commitment
(the opening form, `BindsWith`), on correctness of extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import AtFullSide.Top.LiveAtPolicies
import Johnson.Goal.Description.Gates
import Johnson.Goal.Description.KeyWritten
import Johnson.Goal.Description.ProofWritten
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Top
open VerifierAndGoals FlashProve FlashProve

/- Lean compares the named files by their names: unfolded, they are whole files of bytes. -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles VerifierAndGoals.zGap VerifierAndGoals.zAt

/-- Where the test says yes, each gate is the decision itself. -/
theorem gates_of_live {Z : PublicFiles} (h : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    theKeyGate (asDescriptionFiles Z) = theKeyRun (asDescriptionFiles Z) ∧
      theProofGate (asDescriptionFiles Z) = theProofRun (asDescriptionFiles Z) ∧
      theLinkGate (asDescriptionFiles Z) = linkDecisionAtFiles (asDescriptionFiles Z) :=
  ⟨theKeyGate_live _ h, theProofGate_live _ h, theLinkGate_live _ h⟩

/-- **At `VerifierAndGoals.storedPublicFiles` each of the three gates is the decision behind it.** -/
theorem gates_zFull :
    theKeyGate (asDescriptionFiles storedPublicFiles) = theKeyRun (asDescriptionFiles storedPublicFiles) ∧
      theProofGate (asDescriptionFiles storedPublicFiles) = theProofRun (asDescriptionFiles storedPublicFiles) ∧
      theLinkGate (asDescriptionFiles storedPublicFiles) = linkDecisionAtFiles (asDescriptionFiles storedPublicFiles) :=
  gates_of_live theLive_zFull

/-- The same at `VerifierAndGoals.zGap`. -/
theorem gates_zGap :
    theKeyGate (asDescriptionFiles zGap) = theKeyRun (asDescriptionFiles zGap) ∧
      theProofGate (asDescriptionFiles zGap) = theProofRun (asDescriptionFiles zGap) ∧
      theLinkGate (asDescriptionFiles zGap) = linkDecisionAtFiles (asDescriptionFiles zGap) :=
  gates_of_live theLive_zGap

/-- The same at `storedPublicFiles` under every policy within the four bounds. -/
theorem gates_zAt {C theta cap : Nat} (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024)
    (h4 : 2 ^ 8 ≤ theta) :
    theKeyGate (asDescriptionFiles (zAt C theta cap)) = theKeyRun (asDescriptionFiles (zAt C theta cap)) ∧
      theProofGate (asDescriptionFiles (zAt C theta cap)) = theProofRun (asDescriptionFiles (zAt C theta cap)) ∧
      theLinkGate (asDescriptionFiles (zAt C theta cap)) = linkDecisionAtFiles (asDescriptionFiles (zAt C theta cap)) :=
  gates_of_live (theLive_zAt h1 h2 h3 h4)

/-- Where the test says yes, both files' seats return, and the key file's and the proof file's gates
are the seats' own decisions: not the arm that says no to all. -/
theorem seats_of_live {Z : PublicFiles} (h : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∃ K P, theKeyLaid (asDescriptionFiles Z) = .ok K ∧ theProofLaid (asDescriptionFiles Z) = .ok P ∧
      theKeyGate (asDescriptionFiles Z) = K.2 ∧ theProofGate (asDescriptionFiles Z) = P.2 := by
  obtain ⟨K, P, -, hK, hP, -⟩ := theLive_made (asDescriptionFiles Z) h
  exact ⟨K, P, hK, hP, (theKeyGate_live _ h).trans (theKeyRun_ok hK),
    (theProofGate_live _ h).trans (theProofRun_ok hP)⟩

/-- **At `VerifierAndGoals.storedPublicFiles` both seats return, and the two gates are their decisions.** -/
theorem seats_zFull :
    ∃ K P, theKeyLaid (asDescriptionFiles storedPublicFiles) = .ok K ∧ theProofLaid (asDescriptionFiles storedPublicFiles) = .ok P ∧
      theKeyGate (asDescriptionFiles storedPublicFiles) = K.2 ∧ theProofGate (asDescriptionFiles storedPublicFiles) = P.2 :=
  seats_of_live theLive_zFull

/-- The same at `VerifierAndGoals.zGap`. -/
theorem seats_zGap :
    ∃ K P, theKeyLaid (asDescriptionFiles zGap) = .ok K ∧ theProofLaid (asDescriptionFiles zGap) = .ok P ∧
      theKeyGate (asDescriptionFiles zGap) = K.2 ∧ theProofGate (asDescriptionFiles zGap) = P.2 :=
  seats_of_live theLive_zGap

/-- The same at `storedPublicFiles` under every policy within the four bounds. -/
theorem seats_zAt {C theta cap : Nat} (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024)
    (h4 : 2 ^ 8 ≤ theta) :
    ∃ K P, theKeyLaid (asDescriptionFiles (zAt C theta cap)) = .ok K ∧
      theProofLaid (asDescriptionFiles (zAt C theta cap)) = .ok P ∧
      theKeyGate (asDescriptionFiles (zAt C theta cap)) = K.2 ∧
      theProofGate (asDescriptionFiles (zAt C theta cap)) = P.2 :=
  seats_of_live (theLive_zAt h1 h2 h3 h4)

/-- In scope, where the test says yes, the rounds' data that the verifier reads are the written
data. -/
theorem data_of_live {Z : PublicFiles} (hs : InScope Z = true) (h : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).DK = Johnson.G.writtenKFull ∧
      (dataAtFiles flashProveData Z).DP = Johnson.G.writtenPFull :=
  ⟨key_built_written Z hs h, proof_built_written Z hs h⟩

/-- **The data that the verifier reads at `VerifierAndGoals.storedPublicFiles` are the written data.** -/
theorem data_zFull :
    (dataAtFiles flashProveData storedPublicFiles).DK = Johnson.G.writtenKFull ∧
      (dataAtFiles flashProveData storedPublicFiles).DP = Johnson.G.writtenPFull :=
  data_of_live filesRead.full.1 theLive_zFull

/-- The same at `VerifierAndGoals.zGap`. -/
theorem data_zGap :
    (dataAtFiles flashProveData zGap).DK = Johnson.G.writtenKFull ∧
      (dataAtFiles flashProveData zGap).DP = Johnson.G.writtenPFull :=
  data_of_live filesRead.other.1 theLive_zGap

/-- The same at `storedPublicFiles` under every policy within the four bounds. -/
theorem data_zAt {C theta cap : Nat} (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024)
    (h4 : 2 ^ 8 ≤ theta) :
    (dataAtFiles flashProveData (zAt C theta cap)).DK = Johnson.G.writtenKFull ∧
      (dataAtFiles flashProveData (zAt C theta cap)).DP = Johnson.G.writtenPFull :=
  data_of_live (inScope_zAt h1 h2 h3 h4) (theLive_zAt h1 h2 h3 h4)

end AtFullSide.Top

#print axioms AtFullSide.Top.gates_of_live
#print axioms AtFullSide.Top.gates_zFull
#print axioms AtFullSide.Top.gates_zGap
#print axioms AtFullSide.Top.gates_zAt
#print axioms AtFullSide.Top.seats_of_live
#print axioms AtFullSide.Top.seats_zFull
#print axioms AtFullSide.Top.seats_zGap
#print axioms AtFullSide.Top.seats_zAt
#print axioms AtFullSide.Top.data_of_live
#print axioms AtFullSide.Top.data_zFull
#print axioms AtFullSide.Top.data_zGap
#print axioms AtFullSide.Top.data_zAt
