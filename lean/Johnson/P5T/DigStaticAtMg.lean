-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/DigStaticAtMg.lean: **`DigStatic` WHOLE (Johnson/Desc/First/Link/Law/RestStatic.lean:
all six fields) AT EVERY BUILT SEGMENT, IN THE GOALS' SCOPE, AT THE STRUCTURE THAT `digAt` GIVES:
A THEOREM: NO TEST ON THE PUBLIC FILES IS WANTED FOR IT: NEITHER THE DIGITS' ROW OF THE ENTRY
TESTS NOR A CANDIDATE ROW.** Five theorems. A joining. IT IMPORTS NO FILE OF A CANDIDATE ROW's.
Why. Five fields: Johnson/P5T/DigFiveAtMg.lean. The sixth, `same`: `digAt_is`
(Johnson/Desc/First/Look/DigitsShapeAt.lean): what `digAt X i` gives is what `tlAt X i` gives (the
shape that it lays anew is the one that stood there); and `tlAt W l` is the built segment's own
`tl` (`tlAt_of_built`, here). So the two structures are ONE.
  `tlAt_of_built`: in scope, at every segment X that `Verify.builtOf` returns: `tlAt W l = some
  X.tl`.
  `dig_is_built`: **where the proof file's public part Zp is made: `digAt Zp.p.X l = some (x,
  tlD)` and `Zp.p.built.links[l]? = some X` give `tlD = X.tl`.**
  `digStatic_of_pub`: **so `DigStatic tlD X.tl X.Fp`.**
  `AtMg.digStatic`: at the head. `AtMg.digStatic_ground`: at the segment of the blank letters'
  list, of which the spending laws speak.
Limits. "At every built segment" means: at every X that the public reader returns: the equation
`Zp.p.built.links[m]? = some X` stays a premise; that 25 segments are returned is not said here.
At the second hash function alone. The full size alone. No probability: no soundness
follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.DigFiveAtMg
import Johnson.Desc.First.Look.DigitsShapeAt
import Johnson.IMR.OwnSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf builtOf)
open OnBytes.L5.LinksOrder (ok_bind zipped zipped_layers zipped_attention zipped_head linksOf_size)
open VerifiableInference.Desc.First.Look (tlAt digAt digAt_is shapeZAll_of_public)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {W : Verify.Public}
  {ch : Verify.Chains} {Bt : Stages.LinksH}

/-- In scope `tlAt` gives the built segment's own structure. -/
theorem tlAt_of_built (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hW : publicOf Z.pol Z.KL lay = .ok W) (hB : builtOf W ch = .ok Bt) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Bt.links[l]? = some X) : tlAt W l = some X.tl := by
  obtain ⟨hq, hN, -, hA⟩ := _root_.Meaning.scope_plans hZ hR hW
  have hB' := hB
  unfold builtOf at hB'
  obtain ⟨ls, hls, _⟩ := ok_bind hB'
  have hG : W.G.size = 12 := (linksOf_size hls).1.trans hN
  have hc : l = 24 ∨ ∃ g, g < 12 ∧ (l = 2 * g ∨ l = 2 * g + 1) := by
    by_cases h : l = 24
    · exact .inl h
    · exact .inr ⟨l / 2, by omega, by omega⟩
  unfold tlAt
  simp only [hq, hN, ↓reduceIte]
  rcases hc with rfl | ⟨g, hg, rfl | rfl⟩
  · obtain ⟨ar, e⟩ := zipped_head hB hls
    rw [if_pos hq, hN] at e
    unfold zipped at e
    obtain ⟨b, hb, u1, _⟩ := zip_tails e
    have hb' : Bt.links[24]? = some b := hb
    rw [hX] at hb'
    obtain rfl := Option.some.inj hb'
    have e1 : X.tl = W.H.tl := u1.symm
    rw [if_pos (by decide), e1]
  · have hg' : W.G[g]? = some W.G[g] := Array.getElem?_eq_getElem (by omega)
    obtain ⟨ar, e⟩ := zipped_layers hB hls g _ hg'
    have el : Stages.layersLink W.p4 g = 2 * g := by
      unfold Stages.layersLink
      rw [if_pos hq]
    rw [el] at e
    unfold zipped at e
    obtain ⟨b, hb, u1, _⟩ := zip_tails e
    rw [hX] at hb
    obtain rfl := Option.some.inj hb
    have e1 : X.tl = W.G[g].tl := u1.symm
    rw [if_neg (by simp; omega), if_pos (by simp), show 2 * g / 2 = g by omega, hg', e1]
    rfl
  · obtain ⟨a, ha, -⟩ := hA g hg
    obtain ⟨ar, e⟩ := zipped_attention hB hls hq g a ha
    unfold zipped at e
    obtain ⟨b, hb, u1, _⟩ := zip_tails e
    rw [hX] at hb
    obtain rfl := Option.some.inj hb
    have e1 : X.tl = a.seam.tl := u1.symm
    rw [if_neg (by simp; omega), if_neg (by simp), show (2 * g + 1) / 2 = g by omega, ha, e1]
    rfl

/-- **What `digAt` gives is the built segment's own structure.** -/
theorem dig_is_built {Z : VerifierAndGoals.PublicFiles} {lay : ByteArray} {Zp : ProofFile.Pub}
    (hZ : VerifierAndGoals.InScope Z = true)
    (hpub : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol lay Z.KL = .ok Zp) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[l]? = some X) {x : First.Look.Place}
    {tlD : HTailF2} (hD : digAt Zp.p.X l = some (x, tlD)) : tlD = X.tl := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hZ
  have hW : Verify.publicOf Z.pol Z.KL (some lay) = .ok Zp.p.X :=
    (PlanWritten.publicOfO_older Z.pol Z.KL (some lay)).symm.trans (ProofFile.Law.pub_public hpub)
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf hpub
  rw [← e] at hX
  have hX' : (b.links.map ProofFile.Law.blank)[l]? = some X := hX
  rw [Array.getElem?_map] at hX'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hX'
  have k1 : tlAt Zp.p.X l = some tlD := digAt_is (shapeZAll_of_public hW) hD
  have k2 : tlAt Zp.p.X l = some Y.tl := tlAt_of_built hZ hR hW hb hl hY
  exact Option.some.inj (k1.symm.trans k2)

/-- **All six fields.** -/
theorem digStatic_of_pub {Z : VerifierAndGoals.PublicFiles} {lay : ByteArray} {Zp : ProofFile.Pub}
    (hZ : VerifierAndGoals.InScope Z = true)
    (hpub : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol lay Z.KL = .ok Zp) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[l]? = some X) {x : First.Look.Place}
    {tlD : HTailF2} (hD : digAt Zp.p.X l = some (x, tlD)) : DigStatic tlD X.tl X.Fp := by
  obtain rfl := dig_is_built hZ hpub hl hX hD
  exact digStatic_of_tests ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (tests_of_pub hZ hpub hl hX)

end VerifiableInference.Desc.LinkJoin

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.LinkJoin (DigStatic digStatic_of_pub zip_tails)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **At the head.** -/
theorem AtMg.digStatic (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {m : ℕ} (hm : m < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[m]? = some X) {x : Desc.First.Look.Place}
    {tlD : HTailF2} (hD : Desc.First.Look.digAt Zp.p.X m = some (x, tlD)) :
    DigStatic tlD X.tl X.Fp :=
  digStatic_of_pub h.scope h.laid.pub hm hX hD

/-- **At the segment of the blank letters' list.** -/
theorem AtMg.digStatic_ground (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {mk : ProofFile.LinksBy}
    {G : ProofFile.Ground} (hG : ProofFile.blankBy mk Zp = some G) {m : ℕ} (hm : m < 25)
    {Xl : Stages.LinkH} (e3 : G.built[m]? = some Xl) {x : Desc.First.Look.Place}
    {tlD : HTailF2} (hD : Desc.First.Look.digAt Zp.p.X m = some (x, tlD)) :
    DigStatic tlD Xl.tl Xl.Fp := by
  obtain ⟨links, e⟩ := _root_.Meaning.K2.blank_built hG
  rw [e] at e3
  obtain ⟨b, hb, eT, eF⟩ := zip_tails e3
  rw [eT, eF]
  exact h.digStatic hm hb hD

end P5J

#print axioms VerifiableInference.Desc.LinkJoin.tlAt_of_built
#print axioms VerifiableInference.Desc.LinkJoin.dig_is_built
#print axioms VerifiableInference.Desc.LinkJoin.digStatic_of_pub
#print axioms P5J.AtMg.digStatic
#print axioms P5J.AtMg.digStatic_ground
