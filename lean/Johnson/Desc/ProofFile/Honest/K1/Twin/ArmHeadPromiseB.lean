-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmHeadPromiseB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmHeadPromise.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 3
OF ITS DECLARATIONS: pub_at342_b · arrays_at342_b · wide_at342_b. THE PROOFS ARE COPIES.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

The map of names. ReadsFence to ReadsFenceB; each twinned theorem n to n_b; the library's closed
facts at its wider table of names (mwMore) to their likes at mgMore, and its laws on the wider
meaning to their likes on "honest" over mgAll (both in Twin/HonestAt.lean, typed by hand).
The turn of the meaning. Where the elder has the wider meaning (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀),
or plus13 (d13 Dm) dk (mgAll Dm Mg₀)), the twin has honest (mgAll Dm Mg₀) ans test
(Johnson/Desc/ProofFile/Honest/Thread/First.lean): the meaning at which the honest thread's own
promise stands; at the item "tie": mgAll Dm Mg₀. The step down from mw1 to plus13 (inAt_down) falls.
The promise itself is the library's InAt: no new text of a promise.
Laid in, on no line of a statement: the letters ans and test, behind each block of letters: implicit
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the source's block
binds dk (no twin's statement names it; it is kept so that a copied call has the source's number
of arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmHeadPromise
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers pubAll flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgBase)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (withTables withTables_iff p8K6)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
/-- What the promise says of an item that is open in front of the output head's reads' place. -/
theorem pub_at342_b (q : Pub)
    (hq : openB mgMore linksFull (flatPlacesOf linksFull true) (noL 24 false) q = true)
    {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (honest (mgAll Dm mgBase) ans test) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) :
    pubAll Dm.pubD (mgBase : Meaning _ (Wit (CellsQ rows cols) Tok MsgT)).pub q x = true := by
  have hin : q ∈ (First.pubSets (honest (mgAll Dm mgBase) ans test).more linksFull
        (flatPlacesOf linksFull true))[noL 24 false]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL 24 false)) := by
    have e : (honest (mgAll Dm mgBase) ans test).more = mgMore :=
      honest_more_closed Dm mgBase ans test rfl
    rw [e]
    exact open_of hq
  have h0 : (honest (mgAll Dm mgBase) ans test).pub q x = true := inAt_pub hIn _ hin
  rw [honest_pub_all] at h0
  exact h0

/-- **The open segment's list of arrays is the written one.** -/
theorem arrays_at342_b {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (honest (mgAll Dm mgBase) ans test) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) {A : K9.Part}
    (hA : K9.segAt? x.2 = some A) : A.L.arrayOf = Dm.pubD.d3.arrayOf.getD 24 #[] := by
  have h0 := pub_at342_b Dm dk (.linkFresh 24) (Bool.and_eq_true_iff.1 open342_mg).1 hIn
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
theorem wide_at342_b (i n : ℕ)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[i]? = some t → n ≤ t.2.1) {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (honest (mgAll Dm mgBase) ans test) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) (P : K8.ReadsQuiet.PH) :
    ∀ e F tr, withTables P x.2 = some e → e.fork? = some F → F.trees[i]? = some tr → n ≤ tr.K := by
  intro e F tr he hF htr
  obtain ⟨a, cov, xx, tt, ha, hop, _, _, _, rfl⟩ := (withTables_iff P x.2 e).1 he
  have e1 : ({ x.2 with here := .head { a with t := some tt } } : S).fork? = x.2.fork? := by
    unfold S.fork?
    rw [ha]
  rw [e1] at hF
  have h0 := pub_at342_b Dm dk (.more (some 24) "ledger.treesAre")
    (Bool.and_eq_true_iff.1 open342_mg).2 hIn
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

#print axioms VerifiableInference.Desc.K1.pub_at342_b
#print axioms VerifiableInference.Desc.K1.arrays_at342_b
#print axioms VerifiableInference.Desc.K1.wide_at342_b
