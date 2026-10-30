-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/NamesTieAll.lean: THE NAMES' TIE AT ALL 25 SEGMENTS, IN ONE SENTENCE: in the goals'
scope, where the public part is computed: at every segment k < 25 and every matrix of it, the name
that the public part's own built segment lists at the matrix's tree (the field arrayOf) is (owner,
name) by the public parameters' label: the first conjunct of the test entryTieB
(Johnson/Goal/Meaning/ReadingsOne.lean), in its own letters. ONE THEOREM: A JOIN OF THREE OTHER
FILES' THEOREMS BY CASES ON k: nothing of theirs is typed anew.
  **names_tie_all**   k = 2 g, g < 12: OnBytes.Road.K4.names_tie_plain
      (Johnson/Road/K4/NamesTie.lean) · k = 2 g + 1: H2K5.Names.names_tie_att_plain
      (Johnson/Desc/First/Att/Door/Law/K5NamesTie.lean) · k = 24:
      VerifiableInference.Desc.K1.HeadNames.names_tie_head_all
      (Johnson/Desc/AtSeats/NamesTieHeadStream.lean).
WHAT IS NEW HERE AT k = 24: two small steps, by the library's lemmas: names_tie_head_all stands at
Z.p.X.H.tl and at μ < 8: here Meaning.tlAt Z.p.X 24 is that very term (by its text: a step inside
the proof: as a theorem it stands in two other files already: tlAt_head), and
the library's number of matrices of segment 24 is 8 in scope (Meaning.follows_of_core ·
Meaning.size_head).
Limits. AT OnBytes.secondHashFunction ALONE. THAT THE PUBLIC PART IS COMPUTED AT ANY FILES IN SCOPE IS A
PREMISE. The matrices' trees alone: of a vector's tree (U1 to U4 · ZZ · BZ) nothing is said. The
other conjuncts of entryTieB are not spoken of. Nothing on soundness.

-/
import Johnson.Road.K4.NamesTie
import Johnson.Desc.First.Att.Door.Law.K5NamesTie
import Johnson.Desc.AtSeats.NamesTieHeadStream
import Johnson.Goal.Meaning.HidOwner
import Johnson.Goal.Meaning.HidPlanNM

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace P2Law.Names
open _root_.Meaning (labAt ownerK ownerA nameOf)

/-- **THE NAMES' TIE AT ALL 25 SEGMENTS.** -/
theorem names_tie_all {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {Z : ProofFile.Pub}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z) {k : ℕ} (hk : k < 25) {μ : ℕ}
    (hμ : μ < (_root_.Meaning.sizesOf Z.p.X k).NM) :
    ((Z.p.built.links.map (·.arrayOf)).getD k #[])[(_root_.Meaning.tlAt Z.p.X k).gtTree.getD μ 0]? =
      some (ownerK (labAt Z.p.X k μ), nameOf (ownerA (labAt Z.p.X k μ))) := by
  obtain ⟨g, rfl | rfl⟩ := Nat.even_or_odd' k
  · by_cases hg : g < 12
    · exact OnBytes.Road.K4.names_tie_plain hS hR hZ hg hμ
    · obtain rfl : g = 12 := by omega
      have hpub : OnBytes.Model.Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X := by
        rw [← VerifiableInference.PlanWritten.publicOfO_older]
        exact ProofFile.Law.pub_public
          (show ProofFile.pureRoad.pub OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z from hZ)
      have C := OnBytes.Road.Hd.core_of_scope hS hR hpub
      have e : (_root_.Meaning.sizesOf Z.p.X 24).NM = 8 :=
        ((_root_.Meaning.follows_of_core hpub C).NM 24 (by decide)).trans
          (_root_.Meaning.size_head hpub C)
      have h8 : μ < 8 := by
        have hμ' : μ < (_root_.Meaning.sizesOf Z.p.X 24).NM := hμ
        rw [e] at hμ'
        exact hμ'
      show ((Z.p.built.links.map (·.arrayOf)).getD 24 #[])[(_root_.Meaning.tlAt Z.p.X
          24).gtTree.getD μ 0]? =
        some (ownerK (labAt Z.p.X 24 μ), nameOf (ownerA (labAt Z.p.X 24 μ)))
      have et : _root_.Meaning.tlAt Z.p.X 24 = Z.p.X.H.tl := by
        unfold _root_.Meaning.tlAt
        simp
      rw [et]
      exact VerifiableInference.Desc.K1.HeadNames.names_tie_head_all hS hR hZ h8
  · exact H2K5.Names.names_tie_att_plain hS hR hZ (by omega) hμ

end P2Law.Names

#print axioms P2Law.Names.names_tie_all
#print axioms OnBytes.Road.K4.names_tie_plain
#print axioms H2K5.Names.names_tie_att_plain
#print axioms VerifiableInference.Desc.K1.HeadNames.names_tie_head
#print axioms VerifiableInference.Desc.K1.HeadNames.names_tie_head_stream
#print axioms VerifiableInference.Desc.K1.HeadNames.names_tie_head_all
