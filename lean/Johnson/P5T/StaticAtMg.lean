-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/StaticAtMg.lean: **THREE OF THE FOUR FIELDS OF `StaticOk`
(Johnson/Desc/First/Link/Law/OkJoin.lean: `apart`, `units`, `coef`) AT EVERY BUILT SEGMENT, IN THE
GOALS' SCOPE, AS THEOREMS AT THE HEAD: NO TEST ON THE PUBLIC FILES IS WANTED FOR THEM.** Five
theorems. A joining. IT IMPORTS NO FILE OF A CANDIDATE ROW's.
  `built_two`: in scope, at every segment X that `Verify.builtOf` returns: `TwoStatic X.tl X.Fp`
  (Johnson/Desc/First/Link/Law/StaticOfMade.lean). `two_of_pub`: where the proof file's public
  part Zp is made. `AtMg.two`: at the head.
  `AtMg.static_of_blocks`: **`StaticOk X.tl X.Fp` IS LEFT WITH ONE PREMISE: ITS FIELD `blocks`.**
  `coef` by `AtMg.tests` (Johnson/P5T/DigFiveAtMg.lean) and `Fo.coefOK_of_test`.
  `AtMg.static_ground_of_blocks`: at the segment of the blank letters' list, of which the spending
  laws speak.
Limits. "At every built segment" means: at every X that the public reader returns: the equation
`Zp.p.built.links[m]? = some X` stays a premise; that 25 segments are returned is not said here.
At the second hash function alone. The full size alone. `blocks` STAYS A PREMISE.
No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Link.Law.StaticOfMade
import Johnson.P5T.DigFiveAtMg
import Johnson.IMR.OwnSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf builtOf)
open OnBytes.L5.LinksOrder (ok_bind zipped zipped_layers zipped_attention zipped_head linksOf_size)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {W : Verify.Public}
  {ch : Verify.Chains} {Bt : Stages.LinksH}

/-- In scope the two fields hold at each built segment. -/
theorem built_two (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hW : publicOf Z.pol Z.KL lay = .ok W) (hB : builtOf W ch = .ok Bt) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Bt.links[l]? = some X) : TwoStatic X.tl X.Fp := by
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
    exact public_H_two hW
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
    exact public_G_two hW g _ hg'
  · obtain ⟨a, ha, -⟩ := hA g hg
    obtain ⟨ar, e⟩ := zipped_attention hB hls hq g a ha
    unfold zipped at e
    obtain ⟨b, hb, u1, u2⟩ := zip_tails e
    rw [hX] at hb
    obtain rfl := Option.some.inj hb
    have e1 : X.tl = a.seam.tl := u1.symm
    have e2 : X.Fp = a.seam.Fp := u2.symm
    rw [e1, e2]
    exact public_A_two hW g a ha

/-- Where the proof file's public part is made. -/
theorem two_of_pub {Z : VerifierAndGoals.PublicFiles} {lay : ByteArray} {Zp : ProofFile.Pub}
    (hZ : VerifierAndGoals.InScope Z = true)
    (hpub : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol lay Z.KL = .ok Zp) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[l]? = some X) : TwoStatic X.tl X.Fp := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hZ
  have hW : Verify.publicOf Z.pol Z.KL (some lay) = .ok Zp.p.X :=
    (PlanWritten.publicOfO_older Z.pol Z.KL (some lay)).symm.trans (ProofFile.Law.pub_public hpub)
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf hpub
  rw [← e] at hX
  have hX' : (b.links.map ProofFile.Law.blank)[l]? = some X := hX
  rw [Array.getElem?_map] at hX'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hX'
  have k : TwoStatic Y.tl Y.Fp := built_two hZ hR hW hb hl hY
  exact k

end VerifiableInference.Desc.LinkJoin

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.LinkJoin (StaticOk TwoStatic two_of_pub zip_tails)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- At the head. -/
theorem AtMg.two (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {m : ℕ} (hm : m < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[m]? = some X) : TwoStatic X.tl X.Fp :=
  two_of_pub h.scope h.laid.pub hm hX

/-- **The four fields are left with one premise.** -/
theorem AtMg.static_of_blocks (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {m : ℕ} (hm : m < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[m]? = some X)
    (hb : X.tl.wants.map (·.1) = some X.tl.zzBlocks) : StaticOk X.tl X.Fp :=
  ⟨hb, fun Fn _ => (h.two hm hX).1 Fn, (h.two hm hX).2, Fo.coefOK_of_test (h.tests hm hX).t9⟩

/-- At the segment of the blank letters' list. -/
theorem AtMg.static_ground_of_blocks (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    {mk : ProofFile.LinksBy} {G : ProofFile.Ground} (hG : ProofFile.blankBy mk Zp = some G) {m : ℕ} (hm : m < 25)
    {Xl : Stages.LinkH} (e3 : G.built[m]? = some Xl)
    (hb : Xl.tl.wants.map (·.1) = some Xl.tl.zzBlocks) : StaticOk Xl.tl Xl.Fp := by
  obtain ⟨links, e⟩ := _root_.Meaning.K2.blank_built hG
  rw [e] at e3
  obtain ⟨b, hb', eT, eF⟩ := zip_tails e3
  rw [eT] at hb
  rw [eT, eF]
  exact h.static_of_blocks hm hb' hb

end P5J

#print axioms VerifiableInference.Desc.LinkJoin.built_two
#print axioms VerifiableInference.Desc.LinkJoin.two_of_pub
#print axioms P5J.AtMg.two
#print axioms P5J.AtMg.static_of_blocks
#print axioms P5J.AtMg.static_ground_of_blocks
