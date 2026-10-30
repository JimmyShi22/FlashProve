-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/ServedMeans.lean: no request that can be served is lost: at all public files in
the goals' scope, for all weights and every request that can be served and whose output is the
model's own, there are integers that meet the model's relation Means and the head's record. A
theorem on integers and on the library's tables; it names no form and no block of the protocol's
description.

Why. The final line of completeness (completeOnCanServe, AtFullSide/Face/TheSixLines.lean) speaks of
the requests in CanServe (VerifiableInference/CanServe.lean), whose third clause admits every value
that the integer model admits: 16 bits, up to 32,767. If the protocol's lookups admitted less, an
honest prover would have no keys to show at some request of that domain (an argument; this file has
no theorem on what follows for completeness; what is argued: Johnson/Goal/Conditions/HomeEnd.lean,
limit 2). Means (Johnson/Goal/Meaning/Row.lean) holds, for the 24 sub-proofs of the layers and of
attention, "every entry of every key vector is an entry of its table"; the head's record
Hd.HeadOrdLB holds the like for the head. These are the LIBRARY's key vectors and the LIBRARY's
tables. So the statement here says: on CanServe no entry of the library's key vectors falls out of
the library's tables.

Main names.
  true_of_served   in scope: what can be served, with the model's own output, is built without
    padding, and is true under the files' policy at the index of the weights' own digits.
  means_of_served   THE STATEMENT: so there are lists of integers w and a head's list Mh with Means,
    Hd.HeadOrdLB and the tie of the stream's copy: the end of trace_of_true.
  means_of_served_zFull, means_of_served_zGap the same at the two named sets of files. That the
    verifier's publicOf returns there is the hypothesis "returns".
  served_met   the two premises on a request are met together wherever the reader returns.

It adds no strength: a composition of lemmas. inScope_at (Johnson/Goal/Scope/ScopeLines.lean):
the scope's floor on theta; Policy.meetsPolicy_of_isModelOutput
(Policy/Front/MeetsPolicyGuards.lean); weightsOfIndex_indexOfWeights
(IntegerModel/Arrays/OfIndex.lean); isTrueUnder_of_served (Johnson/Goal/Meaning/NextToken.lean);
trace_of_true (Johnson/Goal/Meaning/HidTwelveMet.lean); VerifierAndGoals.filesRead
(Johnson/Goal/Files/FilesReadProof.lean).
Nearest kin. isTrueUnder_of_served and MeaningAt.served (NextToken.lean), frameRel_of_served
(Johnson/Goal/Meaning/Spent.lean [not in this library]): at an index and an output that meets the
policy; they end in
"true", ModelSays and frameRel, not in Means. VerifierAndGoals.completeOn_of_completeFor (Ladder/Ties.lean)
makes the step from the model's own output to the policy as true_of_served makes it.

Every "there is", walked. x: pinned by requestOfTokens (prompt, output) [] = some x. w, Mh: PINNED
BY NOTHING but the clauses: in trace_of_true's proof they are the lists of the library's honest
trace.

Limits. A statement on integers and tables alone. It does not say that a block of the protocol's
description says yes on these integers, nor that an honest prover is accepted: no completeness. The
keys in Means are the library's key vectors, its tables the library's (that the verifier's record
has the layers' eight tables row by row: Johnson/Goal/Meaning/TabsScope.lean; that the value of the
layers' own forms line and joinPart is the extension of the part of these vectors that is affine in
the cells: alg_line, Johnson/Road/Ends/AlgLin.lean, and alg_call, Johnson/Road/Ends/AlgKv.lean,
under their premises; the products with weights are tied by no theorem). X is what publicOf
returns; the description's own public part is pubPlain's: the two are one where protocolDataWellFormed says yes, at
lay := some Z.lay alone (live_atFiles, AtFiles.public_is,
Johnson/Goal/Tie/TwoPublics.lean [not in this library]): not
called here. No witness here has a value from 32,640 to 32,767: at that edge the statement rests on
its "for all" alone. Not in Means: the digits of the
smallness test; the counts of a lookup, for which the library's trace has no cell. Cells are bounded
by 2^18 here, not by 128. That publicOf returns at lay := some Z.lay follows wherever protocolDataWellFormed
accepts (kseat_name, Johnson/Goal/Description/KeySeat.lean, with publicOfO_older,
Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean); at storedPublicFiles the side library states it outright
(publicOf_zFull_returns, AtFullSide/Planner/PublicReturns.lean). Neither is called here:
means_of_served_zFull and means_of_served_zGap take the return as a hypothesis.
served_met's weights are made up, and all their layers are zero. Hid is Row.lean's name for the type
of the lists w.
This file states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Meaning.HidTwelveMet
import Johnson.Goal.Meaning.NextToken
import Johnson.Goal.Scope.ScopeLines
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Layer (matIx)
open VerifiableInference
open VerifiableInference.Meaning (isTrueUnder_of_served)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **What can be served, with the model's own output, is true under the files' policy**, at the
index of the weights' own digits. -/
theorem true_of_served (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (weights : ModelWeights (VerifierAndGoals.settingsOfRead pp)) (prompt output : List Token)
    (served : CanServe (VerifierAndGoals.settingsOfRead pp) weights prompt output)
    (own : VerifierAndGoals.ModelOutput (VerifierAndGoals.settingsOfRead pp) weights prompt output) :
    ∃ x, requestOfTokens (prompt, output) [] = some x ∧
      Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol
        (indexOfWeights (VerifierAndGoals.valid_of_read hR) weights) x := by
  have floor : 2 ^ 8 ≤ pp.pol.theta := (Johnson.G.ScopeLines.inScope_at hZ hR).2.2
  have clip : 2 ^ 8 ≤ pp.pol.C :=
    le_trans floor (OnBytes.Flat.settingsAtRef_lawful hR).pol.2.1
  have meets : Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol weights prompt output :=
    Policy.meetsPolicy_of_isModelOutput floor clip served.2.1 own
  have back := weightsOfIndex_indexOfWeights (VerifierAndGoals.valid_of_read hR) weights
  exact isTrueUnder_of_served (VerifierAndGoals.valid_of_read hR) (lawful_of_read hR) rfl pp.pol
    (indexOfWeights (VerifierAndGoals.valid_of_read hR) weights) (by rw [back]; exact served)
    (by rw [back]; exact meets)

/-- **No request that can be served is lost.** -/
theorem means_of_served (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X)
    (weights : ModelWeights (VerifierAndGoals.settingsOfRead pp)) (prompt output : List Token)
    (served : CanServe (VerifierAndGoals.settingsOfRead pp) weights prompt output)
    (own : VerifierAndGoals.ModelOutput (VerifierAndGoals.settingsOfRead pp) weights prompt output) :
    ∃ (x : Instance ppref) (w : Hid) (Mh : Mats ℤ),
      requestOfTokens (prompt, output) [] = some x ∧ w.tok = x.y ∧
      Means X pp (indexOfWeights (VerifierAndGoals.valid_of_read hR) weights) x w ∧
      Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS)
        (indexOfWeights (VerifierAndGoals.valid_of_read hR) weights).mat x Mh ∧
      ∀ r c, Mh (X.hS.NHf + 3) r c = w.MG 11 (matIx X.y).iXO r c := by
  obtain ⟨x, built, T⟩ := true_of_served hZ hR weights prompt output served own
  obtain ⟨w, Mh, tok, M, OH, copy⟩ := trace_of_true hZ hR h _ x T
  exact ⟨x, w, Mh, built, tok, M, OH, copy⟩

/-- **The same at the stored full-size files.** returns: the verifier's own function has returned X
there: a hypothesis. -/
theorem means_of_served_zFull
    (returns : publicOf VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL lay = .ok X) :
    ∃ (pp : ScalesAndPolicy) (hR : VerifierAndGoals.readFiles VerifierAndGoals.storedPublicFiles = .ok pp), pp.pol = AcceptancePolicy.exact ∧
      ∀ (weights : ModelWeights (VerifierAndGoals.settingsOfRead pp)) (prompt output : List Token),
        CanServe (VerifierAndGoals.settingsOfRead pp) weights prompt output →
        VerifierAndGoals.ModelOutput (VerifierAndGoals.settingsOfRead pp) weights prompt output →
        ∃ (x : Instance ppref) (w : Hid) (Mh : Mats ℤ),
          requestOfTokens (prompt, output) [] = some x ∧ w.tok = x.y ∧
          Means X pp (indexOfWeights (VerifierAndGoals.valid_of_read hR) weights) x w ∧
          Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS)
            (indexOfWeights (VerifierAndGoals.valid_of_read hR) weights).mat x Mh ∧
          ∀ r c, Mh (X.hS.NHf + 3) r c = w.MG 11 (matIx X.y).iXO r c := by
  obtain ⟨hZ, pp, hR, exactMatch⟩ := VerifierAndGoals.filesRead.full
  exact ⟨pp, hR, exactMatch, fun weights prompt output served own =>
    means_of_served hZ hR returns weights prompt output served own⟩

/-- **The same at the other named set of files**: the stored files with the policy
(25856, 512, 1). -/
theorem means_of_served_zGap
    (returns : publicOf VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL lay = .ok X) :
    ∃ (pp : ScalesAndPolicy) (hR : VerifierAndGoals.readFiles VerifierAndGoals.zGap = .ok pp), pp.pol = ⟨25856, 512, 1⟩ ∧
      ∀ (weights : ModelWeights (VerifierAndGoals.settingsOfRead pp)) (prompt output : List Token),
        CanServe (VerifierAndGoals.settingsOfRead pp) weights prompt output →
        VerifierAndGoals.ModelOutput (VerifierAndGoals.settingsOfRead pp) weights prompt output →
        ∃ (x : Instance ppref) (w : Hid) (Mh : Mats ℤ),
          requestOfTokens (prompt, output) [] = some x ∧ w.tok = x.y ∧
          Means X pp (indexOfWeights (VerifierAndGoals.valid_of_read hR) weights) x w ∧
          Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS)
            (indexOfWeights (VerifierAndGoals.valid_of_read hR) weights).mat x Mh ∧
          ∀ r c, Mh (X.hS.NHf + 3) r c = w.MG 11 (matIx X.y).iXO r c := by
  obtain ⟨hZ, pp, hR, policy⟩ := VerifierAndGoals.filesRead.other
  exact ⟨pp, hR, policy, fun weights prompt output served own =>
    means_of_served hZ hR returns weights prompt output served own⟩

/-- The two premises on a request are met together, wherever the reader returns: the library's
weights under which the model answers 1 after any one token; the prompt [0], the output [1]. -/
theorem served_met (hR : VerifierAndGoals.readFiles Z = .ok pp) :
    ∃ (weights : ModelWeights (VerifierAndGoals.settingsOfRead pp)) (prompt output : List Token),
      CanServe (VerifierAndGoals.settingsOfRead pp) weights prompt output ∧
        VerifierAndGoals.ModelOutput (VerifierAndGoals.settingsOfRead pp) weights prompt output :=
  ⟨_, [0], [1], VerifierAndGoals.voting_served (VerifierAndGoals.valid_of_read hR) 1 (by decide)⟩

end Meaning

#print axioms Meaning.true_of_served
#print axioms Meaning.means_of_served
#print axioms Meaning.means_of_served_zFull
#print axioms Meaning.means_of_served_zGap
#print axioms Meaning.served_met
