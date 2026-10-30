-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/FiveAtFree.lean: THE TOWER's FIVE ROWS THAT ARE LAWS, AT THE TWO CLOSED VALUES (the
composed meaning's constant h.𝔇 and the tower's letters at h.free, Johnson/P5J/FreeAll.lean), FROM
WHAT IS LEFT OF THEM, BY NAME. ITS IMPORTS HOLD 140 FILES OF ThirdParty/. One structure, one
theorem: A JOINING OF FIVE GROUPS OF ENDS: no weight of its own.

  FiveLeft h dB dt r Ld   what no end pays, each field under its own name
  **five_at_free**        the head h · the gate's accept hl · FiveLeft → h.Five h.free (depthZ Z):
                          by the structure's own maker (AtMgA.five_mk, Johnson/P5J/FiveFields.lean)

WHICH LIST OF ENTRY TESTS. NONE IS READ: this file holds over the proof file's list of entry tests
(LPFD.lawsAsk, Johnson/Desc/Laid/ProofAsks.lean): a public test that is among the
thirteen rows of ProofAsksFirstThirteenTests.lean (guard) IS A FIELD OF FiveLeft
here. Over the thirteen rows the head pays it: Johnson/P5J/FiveAtFreeLaid2.lean.

OF THE FIVE ROWS: THREE ARE STRUCK, ONE IS TURNED, ONE IS KEPT.
  head_cuts           STRUCK: head_cuts_of_guard h L.guard
                      (Johnson/Desc/Kinds/Law/HeadCutsFive.lean)
  reply_leaves        STRUCK: reply_leaves_at_mg (Johnson/P5J/ReplyLeavesAtMg.lean): the head at the
                      second hash function, and FreeAll's three equations on the chains' flat lists
  shared_joint_count  STRUCK: k14_at_free_head (Johnson/Desc/K14/Law/LedgerAtFreeHead.lean): the
                      head · the one pin, which is guard in another spelling (pinnedAt_of_row,
                      Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean) · at most 64 slots, by
                      FlashProve.slots_le_the
                      (Johnson/Goal/Numbers/DepthAtThe.lean), which reads the gate's accept
  leads3_last_chains_table   TURNED into L.last: AtMgA.LastLeft (Johnson/P5J/L0/LastFreeT.lean):
                      five premises: hT · hP (closed tests) · hRc · hS (facts on reached states) ·
                      row0B (a law). IT MAY ASK MORE THAN THE ROW: the row does not give it back
  tables_fit          KEPT: L.tables_fit IS THE ROW ITSELF, WHOLE (h.TablesFitF; the depth is idle
                      in it): here the theorem is the identity

LETTERS. dB · dt · r · Ld stand in "last" alone, never in the conclusion: so the theorem says "if
there are such four with FiveLeft, then …". That ONE Ld serves hRc and hP together is not shown.
Limits. NO MEMBER OF FiveLeft IS KNOWN. The head and the gate's accept are premises. guard is a
condition on the public files. At OnBytes.secondHashFunction alone. No soundness statement. Nothing on hiding.
-/
import Johnson.P5J.FiveFields
import Johnson.P5J.FreeAll
import Johnson.Desc.Kinds.Law.HeadCutsFive
import Johnson.P5J.ReplyLeavesAtMg
import Johnson.Desc.K14.Law.LedgerAtFreeHead
import Johnson.Goal.Numbers.DepthAtThe
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.P5J.L0.LastFreeT

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (madeRow keyOfScan fullKey pinnedAt_of_row)
open _root_.Run _root_.Run.PQ
open VerifierAndGoals FlashProve FlashProve VerifierAndGoals.AtTheName

variable {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **What is left of the five rows at the two closed values.** -/
structure FiveLeft (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x)
    (dB : RDT) (dt : List RDT) (r : Fmt.M1.Stage → ℕ)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) : Prop where
  /-- A CLOSED TEST on the public files: not at the full size's key, or the made plan's row -/
  guard : (!Decidable.decide (keyOfScan Zp.p.X.P = fullKey) || madeRow Zp) = true
  /-- the last chain's row: closed tests, facts on reached states and one law: its own five -/
  last : h.LastLeft dB dt r Ld
  /-- the three tables fit the starts and each other: THE ROW ITSELF, whole -/
  tables_fit : h.TablesFitF h.free (depthZ Z)

set_option maxHeartbeats 8000000 in
/-- **THE FIVE ROWS AT THE TWO CLOSED VALUES, FROM WHAT IS LEFT.** -/
theorem five_at_free (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) {dB : RDT} {dt : List RDT} {r : Fmt.M1.Stage → ℕ}
    {Ld : VerifiableInference.Desc.K12.Door.Laid} (L : FiveLeft h dB dt r Ld) :
    h.Five h.free (depthZ Z) :=
  h.five_mk h.free (depthZ Z)
    (VerifiableInference.Desc.Kinds.Head.Law.head_cuts_of_guard h L.guard)
    (reply_leaves_at_mg h.toAtMg h.free h.free_q₁ h.free_q₂ h.free_q₃ _)
    (_root_.Desc.K14.Law.k14_at_free_head h (pinnedAt_of_row L.guard) (depthZ Z)
      (slots_le_the Z h.scope hl) _ _ _ _ _ _ _)
    (h.leads3_of_left L.last)
    L.tables_fit

end P5J

#print axioms P5J.five_at_free
