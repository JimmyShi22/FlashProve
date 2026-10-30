-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/TieServed.lean: where the public files Z are in scope and the reader returns a
table, every request that can be served and whose output is the model's builds an instance of which
yesAt holds at the index of the weights. And every pair in yesAt lies in the relation Ryes of the
configuration from which the protocols at Z are made.

What this file has (namespace OnBytes.FrontRoad).
The names. homeR b Z is the compiler's input (Johnson/Goal/Conditions/HomeAtWider.lean). backB b Z s
w is the index given by the weights w, at valid settings s, as the settings read off a table are.
yesAt b Z hr holds of a pair (index, instance) if the index is given by some weights and the
instance is true under the files' policy at these weights (Johnson/Goal/Conditions/HomeServed.lean).
backTok reads the prompt and the output off an instance (Johnson/FrontRoad/LaidIdSpec.lean).
CanServe asks that every token is in the vocabulary, that the output is not empty, and that the
model has a value on the whole window of 1,024 tokens (VerifiableInference/CanServe.lean).
ModelOutput asks that each output token is the model's next token (Ladder.lean).
served_tie: let Z be public files in scope at which the library's reader returns a table pp of
scales and policy, and let s be the settings read off pp. Take any weights w at s, and any prompt p
and output o with CanServe and ModelOutput. Then the input's builder, with no further tokens, builds
an instance x from (p, o). yesAt b Z hr holds of x at the index backB b Z s w. backTok reads (p, o)
back from x.
yesAt_below_object: where the reader returns a table, every pair in yesAt b Z hr lies in the
relation Ryes of the configuration Cz Z (E2E/ObjectAtFiles.lean), from which the three protocols at
Z are made.

  tieOn_yesAt   served_tie in the form of the premise TieOn of this folder's implications
      (Johnson/FrontRoad/FromPremisesSpec.lean).
  served_tie_some   where the reader returns a table, some weights, prompt and output satisfy the
      two premises of served_tie on a request.
  served_tie_met   all premises of served_tie hold together at some public files. So served_tie is
      not vacuous. The proof takes the stored full-size files (storedPublicFiles), which are in scope and which
      the reader reads (VerifierAndGoals.filesRead, Johnson/Goal/Files/FilesReadProof.lean). That these are
      the bytes of the package's examples is not said.

How it fits. The theorems of this folder on index privacy at the commitment ID take a relation Yes
between indices and instances, and a premise that connects true requests to Yes (hrel of
threeOfId_of_laws, Johnson/FrontRoad/IdAlone.lean). For the scheme with placeholder provers Yes may
hold of everything (tie_taken, at Yes := True, Johnson/FrontRoad/LaidId.lean). The protocol's own
prover of the sessions can compute its messages at true instances alone, so for it Yes has to be
narrower; that is the reason for this file, an argument that is not proved here.
served_tie is that premise for the relation «the request can be served (CanServe) and its output is
the model's (ModelOutput)». The request is split into its prompt p and its output o. The other
arguments are Yes := yesAt b Z hr, idx := backB b Z s and back := backTok b Z. It asks in addition
that Z is in scope. yesAt_below_object is for theorems on the sessions' honest prover that are
stated at every relation below Ryes of Cz Z.
All five only apply theorems of the library: true_of_served and served_met
(Johnson/Goal/Meaning/ServedMeans.lean), build_home and build_home_of_built
(Johnson/Prover/At/HomeMore.lean), Flat.buildReq_reads (Johnson/Flat/BuiltOK.lean),
VerifierAndGoals.filesRead, and frameRel_of_yesAt (Johnson/Goal/Conditions/HomeYesFrame.lean). That last file
states its theorem at the configuration's field Rno and says nothing of Ryes. At this configuration
the fields Ryes and Rno are the same relation by definition (relationsAndEncodingOfClaims, OnBytes/Flat/FilesAt.lean), so
frameRel_of_yesAt gives Ryes as it is. Lemmas on the way to index privacy; not one of the release's
goal statements.

Limits.
  These are statements on relations, not on a protocol. Nothing is said on whether an honest prover
      is accepted at all of yesAt, nothing on completeness, and nothing on soundness.
      Johnson/Goal/Conditions/HomeServed.lean notes that its clause «honest» is false at this set if
      the description's lookups admit less than the integer model's 16 bits.
      Johnson/Goal/Meaning/ServedMeans.lean gives the reason as an argument, not a theorem.
  Written out, Ryes of Cz Z is: the matrix is in range, and it holds an index at which some trace
      meets the model's relation relaxed with the cost ledger (RelLAt,
      Johnson/Top/H/TargetAtPolicy.lean). That is at the protocol's prime, and at the table that the
      reader returns for Z's files, or the reference table where the reader refuses.
      yesAt_below_object is an inclusion. It does not say how much wider Ryes is than yesAt.
  served_tie_some gives one request, the prompt [0] with the output [1]. Its weights are made up,
      and by the head of Johnson/Goal/Meaning/ServedMeans.lean all their layers are zero
      (served_met). That yesAt, or Ryes, holds at two different indices is not proved here.
  The builder is called with an empty list of further tokens, and each statement speaks of one
      request.
Terms: Johnson/FrontRoad/Front.lean and Johnson/FrontRoad/Spec.lean.
-/
import Johnson.FrontRoad.LaidIdSpec
import Johnson.FrontRoad.FromPremisesSpec
import Johnson.Goal.Conditions.HomeYesFrame
import E2E.ObjectAtFiles
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false
set_option maxRecDepth 100000

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.FrontRoad
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifierAndGoals (PublicFiles InScope readFiles settingsOfRead)
open FlashProve (homeR backB build_home build_home_of_built yesAt frameRel_of_yesAt flashProveDescription allZeroDigest)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows

variable (b : PublicFiles → ℕ) (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy}

/-- **If Z is in scope and the reader returns a table, a request that can be served, with the
model's own output, builds with no further tokens an instance in yesAt at the index of the weights,
and the request is read back from it.** -/
theorem served_tie (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) (p o : List Token)
    (hd : CanServe (settingsOfRead pp) w p o) (hm : VerifierAndGoals.ModelOutput (settingsOfRead pp) w p o) :
    ∃ x, (homeR b Z).buildInstance (p, o) [] = some x ∧
      yesAt b Z hr (backB b Z (settingsOfRead pp) w) x ∧ backTok b Z x = (p, o) := by
  obtain ⟨x, hx, hT⟩ := Meaning.true_of_served scope hr w p o hd hm
  have hb := build_home_of_built b Z hx
  exact ⟨_, hb, ⟨w, rfl, hT⟩,
    Flat.buildReq_reads ((congrFun (congrFun (build_home b Z) (p, o)) []).symm.trans hb)⟩

/-- served_tie in the form of the premise TieOn (Johnson/FrontRoad/FromPremisesSpec.lean), at the
requests that can be served and at Yes := yesAt b Z hr. -/
theorem tieOn_yesAt (scope : InScope Z = true) (hr : readFiles Z = .ok pp) :
    TieOn (flashProveDescription.reBound b) Z allZeroDigest [] (settingsOfRead pp) (backB b Z (settingsOfRead pp))
      (backTok b Z) (CanServe (settingsOfRead pp)) (yesAt b Z hr) :=
  fun w p o hd hm => served_tie b Z scope hr w p o hd hm

/-- Where the reader returns a table, the two premises of served_tie on a request are satisfied
together, at made-up weights. -/
theorem served_tie_some (hr : readFiles Z = .ok pp) :
    ∃ (w : ModelWeights (settingsOfRead pp)) (p o : List Token),
      CanServe (settingsOfRead pp) w p o ∧ VerifierAndGoals.ModelOutput (settingsOfRead pp) w p o :=
  Meaning.served_met hr

/-- All premises of served_tie are satisfied together, at some public files. -/
theorem served_tie_met :
    ∃ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true ∧ readFiles Z = .ok pp ∧
      ∃ (w : ModelWeights (settingsOfRead pp)) (p o : List Token),
        CanServe (settingsOfRead pp) w p o ∧ VerifierAndGoals.ModelOutput (settingsOfRead pp) w p o := by
  obtain ⟨hs, pp, hr, -⟩ := VerifierAndGoals.filesRead.full
  exact ⟨_, pp, hs, hr, Meaning.served_met hr⟩

/-- **Every pair in yesAt lies in the relation Ryes of the configuration at Z.** -/
theorem yesAt_below_object (hr : readFiles Z = .ok pp) (i : (homeR b Z).Index) (x : (homeR b Z).Instance)
    (h : yesAt b Z hr i x) :
    (AtPublicFiles.AtFiles.Cz Z).Ryes (show AtPublicFiles.AtFiles.FullSizeMatrix from i) (show LPFD.Full.XF from x) () :=
  frameRel_of_yesAt b Z hr i x h

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.served_tie
#print axioms OnBytes.FrontRoad.tieOn_yesAt
#print axioms OnBytes.FrontRoad.served_tie_some
#print axioms OnBytes.FrontRoad.served_tie_met
#print axioms OnBytes.FrontRoad.yesAt_below_object
