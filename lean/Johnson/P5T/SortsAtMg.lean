-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/SortsAtMg.lean: **THE CLOSED TEST `linkPlanB`
(Johnson/Desc/First/Link/Law/HtinPaid.lean) ACCEPTS AT EVERY BUILT SEGMENT, IN THE GOALS' SCOPE: A
THEOREM AT THE HEAD: NO TEST ON THE PUBLIC FILES IS WANTED FOR IT.** It is the one closed conjunct
at a segment that is left in what is left of the kind K9's condition. Four theorems. A joining. IT
IMPORTS NO FILE OF A CANDIDATE ROW's.
  `built_sorts`: in scope, at every segment X that `Verify.builtOf` returns: `sortsB
  (X.Fp.trees.toList.map look) X.tl = true`. By `public_G_sorts`, `public_A_sorts`,
  `public_H_sorts` (Johnson/Desc/First/Link/Law/SortsOfMade.lean) and `zip_tails`
  (Johnson/P5T/DigFiveAtMg.lean).
  `sorts_of_pub`: where the proof file's public part Zp is made, at every l below 25.
  `AtMg.sorts`: at the head.
  `AtMg.linkPlan`: **`linkPlanB Zp m X = true` at every m below 25 and the built segment X
  there.** By `AtMg.linkPlan_of_sorts` (Johnson/P5T/NamesAtMg.lean).
Limits. "At every built segment" means: at every X that the public reader returns: the equation
`Zp.p.built.links[m]? = some X` stays a premise; that 25 segments are returned is not said here.
At the second hash function alone. The full size alone. No probability: no soundness
follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Link.Law.SortsOfMade
import Johnson.P5T.DigFiveAtMg
import Johnson.P5T.NamesAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf builtOf)
open OnBytes.L5.LinksOrder (ok_bind zipped zipped_layers zipped_attention zipped_head linksOf_size)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {W : Verify.Public}
  {ch : Verify.Chains} {Bt : Stages.LinksH}

/-- In scope every array of each built segment's ledger is of one of the four sorts. -/
theorem built_sorts (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hW : publicOf Z.pol Z.KL lay = .ok W) (hB : builtOf W ch = .ok Bt) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Bt.links[l]? = some X) :
    sortsB (X.Fp.trees.toList.map look) X.tl = true := by
  obtain ⟨hq, hN, -, hA⟩ := _root_.Meaning.scope_plans hZ hR hW
  have hB' := hB
  unfold builtOf at hB'
  obtain ⟨ls, hls, _⟩ := ok_bind hB'
  have hG : W.G.size = 12 := (linksOf_size hls).1.trans hN
  have hc : l = 24 ∨ ∃ g, g < 12 ∧ (l = 2 * g ∨ l = 2 * g + 1) := by
    by_cases h : l = 24
    · exact .inl h
    · exact .inr ⟨l / 2, by omega, by omega⟩
  rcases hc with rfl | ⟨g, hg, rfl | rfl⟩
  · obtain ⟨ar, e⟩ := zipped_head hB hls
    rw [if_pos hq, hN] at e
    unfold zipped at e
    obtain ⟨b, hb, u1, u2⟩ := zip_tails e
    have hb' : Bt.links[24]? = some b := hb
    rw [hX] at hb'
    obtain rfl := Option.some.inj hb'
    have e1 : X.tl = W.H.tl := u1.symm
    have e2 : X.Fp = W.H.Fp := u2.symm
    rw [e1, e2]
    exact public_H_sorts hW
  · have hg' : W.G[g]? = some W.G[g] := Array.getElem?_eq_getElem (by omega)
    obtain ⟨ar, e⟩ := zipped_layers hB hls g _ hg'
    have el : Stages.layersLink W.p4 g = 2 * g := by
      unfold Stages.layersLink
      rw [if_pos hq]
    rw [el] at e
    unfold zipped at e
    obtain ⟨b, hb, u1, u2⟩ := zip_tails e
    rw [hX] at hb
    obtain rfl := Option.some.inj hb
    have e1 : X.tl = W.G[g].tl := u1.symm
    have e2 : X.Fp = W.G[g].Fp := u2.symm
    rw [e1, e2]
    exact public_G_sorts hW g _ hg'
  · obtain ⟨a, ha, -⟩ := hA g hg
    obtain ⟨ar, e⟩ := zipped_attention hB hls hq g a ha
    unfold zipped at e
    obtain ⟨b, hb, u1, u2⟩ := zip_tails e
    rw [hX] at hb
    obtain rfl := Option.some.inj hb
    have e1 : X.tl = a.seam.tl := u1.symm
    have e2 : X.Fp = a.seam.Fp := u2.symm
    rw [e1, e2]
    exact public_A_sorts hW g a ha

/-- Where the proof file's public part is made. -/
theorem sorts_of_pub {Z : VerifierAndGoals.PublicFiles} {lay : ByteArray} {Zp : ProofFile.Pub}
    (hZ : VerifierAndGoals.InScope Z = true)
    (hpub : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol lay Z.KL = .ok Zp) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[l]? = some X) :
    sortsB (X.Fp.trees.toList.map look) X.tl = true := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hZ
  have hW : Verify.publicOf Z.pol Z.KL (some lay) = .ok Zp.p.X :=
    (PlanWritten.publicOfO_older Z.pol Z.KL (some lay)).symm.trans (ProofFile.Law.pub_public hpub)
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf hpub
  rw [← e] at hX
  have hX' : (b.links.map ProofFile.Law.blank)[l]? = some X := hX
  rw [Array.getElem?_map] at hX'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hX'
  have k : sortsB (Y.Fp.trees.toList.map look) Y.tl = true := built_sorts hZ hR hW hb hl hY
  exact k

end VerifiableInference.Desc.LinkJoin

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.LinkJoin (linkPlanB sortsB look sorts_of_pub)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- At the head. -/
theorem AtMg.sorts (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {m : ℕ} (hm : m < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[m]? = some X) :
    sortsB (X.Fp.trees.toList.map look) X.tl = true :=
  sorts_of_pub h.scope h.laid.pub hm hX

/-- **The closed test accepts, at each of the 25 segments.** -/
theorem AtMg.linkPlan (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {m : ℕ} (hm : m < 25) :
    ∀ X, Zp.p.built.links[m]? = some X → linkPlanB Zp m X = true :=
  fun _ hX => h.linkPlan_of_sorts hm hX (h.sorts hm hX)

end P5J

#print axioms VerifiableInference.Desc.LinkJoin.built_sorts
#print axioms VerifiableInference.Desc.LinkJoin.sorts_of_pub
#print axioms P5J.AtMg.sorts
#print axioms P5J.AtMg.linkPlan
