-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/StartOfLive.lean: AT ALL PUBLIC FILES IN THE GOALS' SCOPE AT WHICH THE PROOF FILE'S
DESCRIPTION IS LAID, THE PROOF FILE'S FIRST TEST ON AN INSTANCE ACCEPTS EVERY INSTANCE OF THE TYPE.
Statements and proofs, by calls; nothing is evaluated here.

Why. The theorem on zero knowledge at served requests has a guard: there is an instance of the type
that the description's first test accepts. It is a public, all-or-none sentence on the files
(`okStart_of_one`, E2E/StartInScope.lean). E2E/StartInScope.lean leaves one clause of it open in scope:
at every string of the request file's length the request's item is made, and its comparison with
the public part (`Verify.statementHeld`) accepts. At the library's two named sets of public files that
clause is a theorem (AtFullSide/E2E/StartAtWrittenFiles.lean). Here it is one at all files in scope.

How. In scope the parameter file is `VerifierAndGoals.policyFile v`: the stored example's, byte for byte, but
for eight free numbers. The item's reader of that file and the public part's strict scan of it agree
on every number that the item holds, at all v at which the scan returns (ItemLinesAtPolicy.lean).
The three digests of call lines in the public part are made of lists that read none of the free
numbers and nothing of the scale file, so they are the digests of the stored example's call lines,
which are this file's too (DigestsInScope.lean). The scale file's tree hash returns wherever the
public part is made, since its maker hashes the three files and drops the value.

Main names.
  `treeHash_of_public`   where the public part is made, the tree hash of the scale file returns
  `parts_in_scope`       the sixteen facts `Parts` (Johnson/AtFull/Item/HeldOfParts.lean) in scope
  **`item_of_live`**     the clause on the item
  **`okStart_of_live`**  so the first test accepts what is written for every instance of the type

Limits.
- The premise live is not read: that the description is laid (`LaidAt`) is a premise of its own, and
  `laid_of_live` (AtFullSide/E2E/StartAtWrittenFiles.lean) gives such letters where the test accepts.
- The first test on an instance alone: it reads no prover. Nothing on any later test, round or
  decision.
- At the format's second hash function (`OnBytes.secondHashFunction`), not at a variable.
- It stands over the side library, which no independent checker has replayed.
- Nothing on completeness as such, on soundness or on what is hidden.
-/
import E2E.StartInScope
import Johnson.AtFull.Item.ItemAtGap
import Johnson.Desc.ProofFile.Law.CarryAtLaw
import Johnson.HonestTrace.Run.SetUpScan
import AtFullSide.T3.ItemLinesAtPolicy
import AtFullSide.T3.DigestsInScope

set_option autoImplicit false

namespace AtPublicFiles.Start
open OnBytes OnBytes.Model Inst.Model
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord XF)
open OnBytes.Flat (RecFull)
open VerifiableInference.Desc (Chain)
open P5J

/-- **Where the public part is made, the tree hash of the scale file returns**: the maker forms one
digest of the three files, of which that hash is a part, before it goes on. -/
theorem treeHash_of_public {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : VerifiableInference.PlanWritten.publicOfO secondHashFunction pol KL layout = .ok X) :
    ∃ s, secondHashFunctionTree KL = some s := by
  obtain ⟨x, hx⟩ := HonestTraceRun.SetUp.hPar_of_public h
  rw [VerifiableInference.PlanWritten.hParO_older] at hx
  unfold hPar at hx
  obtain ⟨D, hD, -⟩ := OnBytes.Params.exc_bind hx
  obtain ⟨-, k, -, -, -, hk, -, -⟩ := LPFPol.parDigests_parts hD
  exact ⟨k, hk⟩

/-- **In scope the two readers of the parameter file agree**, at whatever the maker of the public
part returns, with or without the layout file. -/
theorem parts_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Verify.publicOf Z.pol Z.KL lay = .ok X) :
    Johnson.AtFull.Item.Parts X (OnBytes.Proof.ParamLines.read Z.pol) (4 * (2 ^ 10 + 2)) := by
  obtain ⟨c, cA, cH⟩ := digests_in_scope hZ hR h
  have hS := OnBytes.Road.Hd.scan_of_public h
  have T := text_at_policy (VerifierAndGoals.freeLinesOf pp)
  rw [OnBytes.Road.Hd.policy_of_scope hZ hR] at hS ⊢
  exact Johnson.AtFull.Item.parts_of_tests (numbers_at_policy hS)
    ((Johnson.AtFull.Item.calls_of_same_text (T "call" (by simp))).trans c)
    ((Johnson.AtFull.Item.calls_of_same_text (T "callA" (by simp))).trans cA)
    ((Johnson.AtFull.Item.calls_of_same_text (T "callH" (by simp))).trans cH)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl}

/-- **The clause on the item, from scope and protocolDataWellFormed.** The premise «item» of startHeld_of_laid and okStart_of_item. -/
theorem item_of_live (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (Ld : LaidAt secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∀ req : ByteArray, req.size = 4 * (Zp.p.X.T + 2) →
      ∃ it, Fmt.requestItem secondHashFunction Zp.pol Zp.KL req = some it ∧
        Verify.statementHeld Zp.p.X it = .ok () := by
  obtain ⟨pp, hR⟩ := IM.reads_of_scope scope
  have hX : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact Ld.publicO
  have hP := parts_in_scope scope hR hX
  have hT : Zp.p.X.T = 1024 := (numbers_of_laid scope Ld).1
  obtain ⟨s, hs⟩ := treeHash_of_public Ld.publicO
  rw [(ProofFile.Law.pub_files Ld.pub).1, (ProofFile.Law.pub_files Ld.pub).2]
  intro req hreq
  rw [hT] at hreq
  obtain ⟨t, ht, ht32⟩ := Johnson.AtFull.Item.olderTK_returns (w := req) (by
    rw [hreq]
    decide)
  obtain ⟨it, h1, h2⟩ := Johnson.AtFull.Item.held_of_parts hP hs ht32
  refine ⟨it, ?_, h2⟩
  rw [← OnBytes.Tie.Decl.RequestItemLaw.requestItem_eq, OnBytes.K.requestItem_eq_itemWith, ht, hreq]
  exact h1

/-- So the first test accepts what is written for every instance of the type. -/
theorem okStart_of_live (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (Ld : LaidAt secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (z : XF × RecFull) :
    (F0T secondHashFunction Zp Np cF).okStart (instanceAsPlainRecord z) = true :=
  okStart_of_item scope Ld (item_of_live scope live Ld) z

end AtPublicFiles.Start

#print axioms AtPublicFiles.Start.treeHash_of_public
#print axioms AtPublicFiles.Start.parts_in_scope
#print axioms AtPublicFiles.Start.item_of_live
#print axioms AtPublicFiles.Start.okStart_of_live
