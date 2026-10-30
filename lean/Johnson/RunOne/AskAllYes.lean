-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/AskAllYes.lean: what a yes of the one term of Johnson/RunOne/AskAll.lean
(verifyAllAskSmall) holds, in one statement that starts from that yes: the three checks have said
yes, and they have said it at one chain of tables, the last link of which is spelt out in
AskAllLink.lean. A proof.

No soundness: a test. This module states laws on the term verifyAllAskSmall, which has the value of
verifyAllAskRun (verifyAllAskRun_eq, AskAllLaws.lean), the form whose tests the runs of lean/Ask/
make one by one (tellAll); that a run's answer is that value is in part by a reading of two texts
(that file's head). It states nothing on soundness.

Main name.
  verifyAllAskSmall_yes: if verifyAllAskSmall H U G = true, then there are kk and kp, which
    Carrier.read makes of the parsed key file and of the parsed proof file, the user's commitment ID
    id in lower-case digits, and a value a, which the entry file's reader parseP makes of the parsed
    key file and the parsed leaf file, such that: the key file's check says yes at kk; the closed
    check of the entry file (verifyEntrySmall) says yes at a; the commitment ID that the hash gives
    of the public files and a.first is id; the proof file's check says yes at kp; a.first is the
    table that kk names; and a.further is the table that kp names.

Limits. One way: from a yes. That any input gets a yes is a fact of a run, not of this file. The
chain of tables is one link short in the statement: the ground of the proof file's check holds a
table of its own (Z.A.further); that this is the table which kp names is a test inside that check
(its line "parsed file 1"): it is part of the yes at kp and is not spelt out here:
Johnson/RunOne/AskAllLink.lean (verifyAllAskSmall_chain) spells it out, and its Limits say what of
that table is by the definitions' texts alone. The parts "read 2" and
"join 2" are not used in the proof: parseP makes both tests again; what "join 2" has tested:
Johnson/RunOne/AskAllCopy.lean.
The table that kk names is written by its two fields: it is Key.tableOf kk by unfolding. What each
of the three checks' yes is worth: its own file's head; no more is said here. The readers are
trusted for nothing: the statement says which values were judged, not that they are those of any
original file. Those of AskAll.lean. Nothing on soundness.
The program does not import this file.


-/
import Johnson.RunOne.AskAllLaws
import OnBytes.ShellOf.EntryJoinLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Ask.All
open OnBytes OnBytes.Maker
open OnBytes.ShellOf.EntryParsed (rdLeaf rdKeyHead yesSmallP rdProofHead furtherIs parseP
  yesSmallP_true parseP_tables furtherIs_joins)

/-- **What a yes of the one term holds.** -/
theorem verifyAllAskSmall_yes (H : ByteArray → ByteArray) (U : User) (G : Given)
    (h : verifyAllAskSmall H U G = true) :
    ∃ (kk kp : Carrier.File) (id : String) (a : OnBytes.Tie.AskedE),
      Carrier.read Carrier.magicKey G.key = .ok kk ∧
      Carrier.read Carrier.magicProof G.proof = .ok kp ∧
      Model.Verify.idAsked U.id = some id ∧
      parseP Tie.smallRecordGround H ⟨id, ⟨U.pol, U.lay, U.KL⟩⟩ G.key G.leaf = .ok a ∧
      Key.verifyKeyAskSmall (keyNeed H U) H (keyUser U) kk = true ∧
      TypedOracleCompiler.Slice.verifyEntrySmall
        (OnBytes.ShellOf.EntryProg.cfgOf ⟨U.pol, U.lay, U.KL⟩) a
        (TypedOracleCompiler.Run.EntryPageSafe.gOf H) = true ∧
      TypedOracleCompiler.Slice.idOfG Tie.smallRecordGround.q.link.table
        (OnBytes.ShellOf.EntryProg.cfgOf ⟨U.pol, U.lay, U.KL⟩) a.first
        (TypedOracleCompiler.Run.EntryPageSafe.gOf H) = id ∧
      Proof.verifyProofAskSmall H (proofFiles U G) kp = true ∧
      a.first = ⟨(headOf kk).1, (headOf kk).2⟩ ∧ a.further = ⟨(headOf kp).1, (headOf kp).2⟩ := by
  unfold verifyAllAskSmall testsWith at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, _, h3, h4, h5, _, h7, h8, h9, h10⟩ := h
  cases ek : Carrier.read Carrier.magicKey G.key with
  | error e =>
    rw [ek] at h1
    exact (Bool.false_ne_true h1).elim
  | ok kk =>
    cases ep : Carrier.read Carrier.magicProof G.proof with
    | error e =>
      rw [ep] at h3
      exact (Bool.false_ne_true h3).elim
    | ok kp =>
      rw [ek] at h4 h8
      rw [ep] at h5 h10
      have hk : Key.verifyKeyAskSmall (keyNeed H U) H (keyUser U) kk = true := h8
      have hp : Proof.verifyProofAskSmall H (proofFiles U G) kp = true := h10
      have hy : yesSmallP H U.id ⟨U.pol, U.lay, U.KL⟩ G.key G.leaf = true := h9
      have hj : furtherIs G.leaf G.proof = true := h7
      have e4 : ((rdKeyHead G.key).isSome && decide (rdKeyHead G.key = some (headOf kk))) = true :=
        h4
      have e5 : ((rdProofHead G.proof).isSome &&
          decide (rdProofHead G.proof = some (headOf kp))) = true := h5
      rw [Bool.and_eq_true, decide_eq_true_eq] at e4 e5
      obtain ⟨id, a, hid, _, hpa, hv, hI⟩ := yesSmallP_true H hy
      obtain ⟨K, _, hK, _, hf, _⟩ := parseP_tables hpa
      obtain ⟨P, hP, hfu⟩ := furtherIs_joins hpa hj
      obtain rfl : K = headOf kk := Option.some.inj (hK.symm.trans e4.2)
      obtain rfl : P = headOf kp := Option.some.inj (hP.symm.trans e5.2)
      exact ⟨kk, kp, id, a, rfl, rfl, hid, hpa, hk, hv, hI, hp, hf, hfu⟩

end Johnson.RunOne.Ask.All

#print axioms Johnson.RunOne.Ask.All.verifyAllAskSmall_yes
