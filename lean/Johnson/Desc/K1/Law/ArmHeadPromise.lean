-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmHeadPromise.lean: THE OUTPUT HEAD's HALF OF THE BINDER hArm: TWO MORE CLAUSES OF
HeadLeft AND OF PlanesLeft2 (Johnson/Desc/K1/Law/ArmHeadPaid.lean, ArmPlanesPaid.lean), READ OFF THE
PROMISE IN FRONT OF THE READS' PLACE ITSELF: no fact along reached states is wanted for them. They
fall to two sentences ON LETTERS. Statements with their proofs: calls.

  hArr   the open segment's list of arrays has an entry at the number of the array of reads: the public
         item linkFresh 24 is open at that border and says: the open link's list of arrays is the
         written one (First.pubAll_linkFresh; Look.linkFreshC). LEFT: hU: the written list has that
         entry.
  hwide  that array is wide enough: the public item "ledger.treesAre" at segment 24 is open there and
         says: the ledger's arrays look as the plan's list says (First.pubAll_more_treesAre;
         FillSent.treesAreB). LEFT: hK: the plan's list's entry at that number is wide enough.
Main names:
  open342 [kernel] · open342_fails   the two items are open at that border; the test can fail.
  pub_at342           what the promise says of an item that is open there, at pubAll.
  arrays_at342        A.L.arrayOf is the written list.
  wide_at342          the clause hwide.
What is not claimed. hU, hK. Nothing on soundness, on an honest prover or on hiding.
THE RECURSION LIMIT IS RAISED IN THIS FILE (maxRecDepth 1000000): for the kernel's evaluations'
elaboration alone.

-/
import Johnson.Desc.K1.Law.ArmPlanesPaid
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers pubAll flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgBase)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (withTables withTables_iff p8K6)

theorem open342 :
    (openB mwMore linksFull (flatPlacesOf linksFull true) (noL 24 false) (.linkFresh 24) &&
      openB mwMore linksFull (flatPlacesOf linksFull true) (noL 24 false)
        (.more (some 24) "ledger.treesAre")) = true := by
  decide +kernel

/-- The test can fail: another segment's items are not open there. -/
theorem open342_fails :
    openB mwMore linksFull (flatPlacesOf linksFull true) (noL 24 false) (.linkFresh 23) = false ∧
      openB mwMore linksFull (flatPlacesOf linksFull true) (noL 24 false)
        (.more (some 23) "ledger.treesAre") = false := by
  decide +kernel

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)

/-- What the promise says of an item that is open in front of the output head's reads' place. -/
theorem pub_at342 (q : Pub)
    (hq : openB mwMore linksFull (flatPlacesOf linksFull true) (noL 24 false) q = true)
    {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) :
    pubAll Dm.pubD (plus13 (d13 Dm) dk mgBase).pub q x = true := by
  have hin : q ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more linksFull
        (flatPlacesOf linksFull true))[noL 24 false]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL 24 false)) := by
    have e : (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more = mwMore :=
      plus13_more_closed Dm dk mgBase rfl
    rw [e]
    exact open_of hq
  have h0 : (plus13 (d13 Dm) dk (mgAll Dm mgBase)).pub q x = true := inAt_pub hIn _ hin
  rw [pub_plus13] at h0
  exact h0

/-- **The open segment's list of arrays is the written one.** -/
theorem arrays_at342 {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) {A : K9.Part}
    (hA : K9.segAt? x.2 = some A) : A.L.arrayOf = Dm.pubD.d3.arrayOf.getD 24 #[] := by
  have h0 := pub_at342 Dm dk (.linkFresh 24) (Bool.and_eq_true_iff.1 open342).1 hIn
  rw [First.pubAll_linkFresh] at h0
  unfold First.Look.linkFreshC at h0
  have h1 := (Bool.and_eq_true_iff.1 h0).2
  have hL : x.2.link? = some A.L := by
    unfold K9.segAt? at hA
    cases e1 : x.2.link? with
    | none =>
      rw [e1] at hA
      cases hA
    | some L =>
      cases e2 : x.2.fork? with
      | none =>
        rw [e1, e2] at hA
        cases hA
      | some F0 =>
        cases e3 : x.2.tl? with
        | none =>
          rw [e1, e2, e3] at hA
          cases hA
        | some t0 =>
          rw [e1, e2, e3] at hA
          rw [← Option.some.inj hA]
  rw [hL] at h1
  exact eq_of_beq h1

/-- **The clause hwide**, from a sentence on the plan's list of the ledger's arrays. -/
theorem wide_at342 (i n : ℕ)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[i]? = some t → n ≤ t.2.1) {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) (P : K8.ReadsQuiet.PH) :
    ∀ e F tr, withTables P x.2 = some e → e.fork? = some F → F.trees[i]? = some tr → n ≤ tr.K := by
  intro e F tr he hF htr
  obtain ⟨a, cov, xx, tt, ha, hop, _, _, _, rfl⟩ := (withTables_iff P x.2 e).1 he
  have e1 : ({ x.2 with here := .head { a with t := some tt } } : S).fork? = x.2.fork? := by
    unfold S.fork?
    rw [ha]
  rw [e1] at hF
  have h0 := pub_at342 Dm dk (.more (some 24) "ledger.treesAre")
    (Bool.and_eq_true_iff.1 open342).2 hIn
  rw [First.pubAll_more_treesAre] at h0
  unfold First.FillSent.treesAreB at h0
  rw [hF] at h0
  have h1 : F.trees.toList.map First.FillSent.treeLook = Dm.pubD.dS.trees 24 := by
    simpa using h0
  have h2 : (Dm.pubD.dS.trees 24)[i]? = some (First.FillSent.treeLook tr) := by
    rw [← h1, List.getElem?_map, Array.getElem?_toList, htr]
    rfl
  exact hK _ h2

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.open342
#print axioms VerifiableInference.Desc.K1.open342_fails
#print axioms VerifiableInference.Desc.K1.pub_at342
#print axioms VerifiableInference.Desc.K1.arrays_at342
#print axioms VerifiableInference.Desc.K1.wide_at342
