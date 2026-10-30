-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/AskAllLink.lean: the last link of the chain of tables behind a yes of the one term of
Johnson/RunOne/AskAll.lean (verifyAllAskSmall): the ground of the proof file's check holds a table
(Z.A.further), and inside its yes the check has tested that this is the table which the parsed proof
file names. Proofs.

No soundness: a test. This module states laws on the term verifyAllAskSmall, which has the value of
verifyAllAskRun (verifyAllAskRun_eq, AskAllLaws.lean), the form whose tests the runs of lean/Ask/
make one by one (tellAll); that a run's answer is that value is in part by a reading of two texts
(that file's head). It states nothing on soundness.

Main names.
  proofYes_table: if verifyProofAskSmall H F k = true (Johnson/RunOne/AskProof.lean), then the
    ground Z is made of the files F, and the test tableOk Z k has said yes: k's root and answers
    are those of Z.A.further, a field of the ground.
  verifyAllAskSmall_link: so behind a yes of verifyAllAskSmall there are kp, which Carrier.read
    makes of the parsed proof file, and the ground Z of the proof file's check, with
    tableOk Z kp = true.
  tableOk_eq: where tableOk Z k says yes, Z.A.further is the table that k names.
  verifyAllAskSmall_chain: behind a yes of verifyAllAskSmall: the value a that the entry file's
    reader makes of the parsed key file and the parsed leaf file, and the ground Z of the proof
    file's check, have Z.A.further = a.further. With verifyAllAskSmall_yes
    (Johnson/RunOne/AskAllYes.lean; the reader is a function, so a is the same there and here) the
    chain is: the user's ID; a.first, the key file's table; a.further, at which the entry file's
    check ends and which is the ground's Z.A.further.

Limits. The statements speak of the field Z.A.further. That the ground reads it off the original
leaf file (lettersAt, Johnson/RunOne/ProofAt.lean), and that the record, the list of commitments and
the instance at which the term judges (Z.cmsv, Z.x) are made of it (groundC,
Johnson/RunOne/ProofGround.lean), is by these two definitions' texts; no statement says it. That the
term that judges says yes at Z is part of the yes at kp and is not spelt out. Z does not stand in
verifyAllAskSmall_yes. Those of AskAllYes.lean. Nothing on soundness.
The program does not import this file.


-/
import Johnson.RunOne.AskAllYes
import OnBytes.Model.VerifyDigest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Ask.All
open OnBytes OnBytes.Maker

/-- **Inside a yes of the proof file's check**: the ground is made, and the parsed proof file names
the ground's table Z.A.further. -/
theorem proofYes_table (H : ByteArray → ByteArray) (F : Proof.Files) (k : Carrier.File)
    (h : Proof.verifyProofAskSmall H F k = true) :
    ∃ Z, F.ground H = .ok Z ∧ Proof.tableOk Z k = true := by
  unfold Proof.verifyProofAskSmall at h
  cases e : F.ground H with
  | error m =>
    rw [e] at h
    exact (Bool.false_ne_true h).elim
  | ok Z =>
    rw [e] at h
    have h' : (((Proof.frontOf Z H k).all fun x => x.2) && Proof.verifyProofSmall Z H k) = true := h
    rw [Bool.and_eq_true] at h'
    have hf := h'.1
    unfold Proof.frontOf at hf
    simp only [List.all_cons, Bool.and_eq_true] at hf
    exact ⟨Z, rfl, hf.1⟩

/-- **The last link behind a yes of the one term.** -/
theorem verifyAllAskSmall_link (H : ByteArray → ByteArray) (U : User) (G : Given)
    (h : verifyAllAskSmall H U G = true) :
    ∃ (kp : Carrier.File) (Z : GroundC),
      Carrier.read Carrier.magicProof G.proof = .ok kp ∧
      (proofFiles U G).ground H = .ok Z ∧ Proof.tableOk Z kp = true := by
  obtain ⟨_, kp, _, _, _, hr, _, _, _, _, _, hp, _, _⟩ := verifyAllAskSmall_yes H U G h
  obtain ⟨Z, hZ, ht⟩ := proofYes_table H (proofFiles U G) kp hp
  exact ⟨kp, Z, hr, hZ, ht⟩

/-- Where the test says yes, the ground's further table is the table that the parsed file names. -/
theorem tableOk_eq (Z : GroundC) (k : Carrier.File) (h : Proof.tableOk Z k = true) :
    Z.A.further = ⟨(headOf k).1, (headOf k).2⟩ := by
  unfold Proof.tableOk at h
  rw [Bool.and_eq_true] at h
  have h1 : k.root = Z.A.further.root := OnBytes.Params.bytes_of_beq h.1
  have h2 : k.answers.map OnBytes.E.ofTriple = Z.A.further.answers := eq_of_beq h.2
  show Z.A.further = ⟨k.root, k.answers.map OnBytes.E.ofTriple⟩
  rw [h1, h2]

/-- **The chain closes**: the table Z.A.further in the ground of the proof file's check is the table
at which the entry file's check ends. -/
theorem verifyAllAskSmall_chain (H : ByteArray → ByteArray) (U : User) (G : Given)
    (h : verifyAllAskSmall H U G = true) :
    ∃ (id : String) (a : OnBytes.Tie.AskedE) (Z : GroundC),
      Model.Verify.idAsked U.id = some id ∧
      OnBytes.ShellOf.EntryParsed.parseP Tie.smallRecordGround H ⟨id, ⟨U.pol, U.lay, U.KL⟩⟩ G.key
        G.leaf = .ok a ∧
      (proofFiles U G).ground H = .ok Z ∧ Z.A.further = a.further := by
  obtain ⟨_, kp, id, a, _, _, hid, hpa, _, _, _, hp, _, hfu⟩ := verifyAllAskSmall_yes H U G h
  obtain ⟨Z, hZ, ht⟩ := proofYes_table H (proofFiles U G) kp hp
  exact ⟨id, a, Z, hid, hpa, hZ, (tableOk_eq Z kp ht).trans hfu.symm⟩

end Johnson.RunOne.Ask.All

#print axioms Johnson.RunOne.Ask.All.verifyAllAskSmall_chain
#print axioms Johnson.RunOne.Ask.All.proofYes_table
#print axioms Johnson.RunOne.Ask.All.verifyAllAskSmall_link
