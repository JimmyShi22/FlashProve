-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/DigFiveAtMg.lean: **FIVE OF THE SIX FIELDS OF `DigStatic`
(Johnson/Desc/First/Link/Law/RestStatic.lean: `small`, `pieces`, `apart`, `coef`, `inside`) AT
EVERY BUILT SEGMENT, IN THE GOALS' SCOPE, AS THEOREMS: NO TEST ON THE PUBLIC FILES IS WANTED FOR
THEM: NEITHER THE DIGITS' ROW OF THE ENTRY TESTS NOR A CANDIDATE ROW.** Six theorems. A joining of
laws of other files. IT IMPORTS NO FILE OF A CANDIDATE ROW's.
Why. This library has `Fo.ZTests tl tl Fp` at every member of the public parameters, from the
return of `Verify.publicOf` alone (`Fo.ZPlan.public_G_zTests0`, `public_A_zTests0`,
`public_H_zTests0`, OnBytes/Tie/Pv/Lookup/Ends/FoZTests0.lean). Five of its ten clauses are these
five fields: two to the letter (t8, t10), three as tests with code whose meaning has theorems
(`Fo.pieceOK_of_test`, `Fo.apart_of_test`, `Fo.coefOK_of_test`).
  `digStatic_of_tests`: **`SameDig tlD tl` and `Fo.ZTests tl tl F` give `DigStatic tlD tl F`.**
  `zip_tails`: an entry of the built segments with their routines exchanged has the segment's `tl`
  and `Fp`.
  `built_tests`: in scope, at every segment X that `Verify.builtOf` returns: `Fo.ZTests X.tl X.tl
  X.Fp`. `tests_of_pub`: where the proof file's public part Zp is made, at every l below 25.
  `AtMg.tests`: at the head. `AtMg.digStatic_of_same`: **at the head `DigStatic tlD X.tl X.Fp` IS
  LEFT WITH ONE PREMISE: `SameDig tlD X.tl`.**
Limits. "At every built segment" means: at every X that the public reader returns: the equation
`Zp.p.built.links[m]? = some X` stays a premise; that 25 segments are returned is not said here.
At the second hash function alone. The full size alone. `SameDig` STAYS A PREMISE (of its
six equations five are by unfolding where tlD is what `digAt` gives; the sixth says that the
kind's own shape is the built segment's). No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Link.Law.RestStatic
import OnBytes.Tie.Pv.Lookup.Ends.FoZTests0
import Johnson.P5T.ShapeAtMg
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf builtOf)
open OnBytes.L5.LinksOrder (ok_bind zipped zipped_layers zipped_attention zipped_head linksOf_size)
open VerifiableInference.OnPublicFiles (SameDig)

/-- **The five fields off the tests `Fo.ZTests`.** -/
theorem digStatic_of_tests {tlD tl : HTailF2} {F : Fork} (hs : SameDig tlD tl)
    (T : Fo.ZTests tl tl F) : DigStatic tlD tl F :=
  ⟨hs, T.t8, fun q hq => Fo.pieceOK_of_test (T.t2 q hq), fun q hq => Fo.apart_of_test (T.t3 q hq),
    Fo.coefOK_of_test T.t9, T.t10⟩

/-- An entry of the built segments with their routines exchanged. -/
theorem zip_tails {bs ls : Array Stages.LinkH} {j : ℕ} {Y : Stages.LinkH}
    (h : (bs.zipWith (fun b l => { b with run := l.run }) ls)[j]? = some Y) :
    ∃ b, bs[j]? = some b ∧ Y.tl = b.tl ∧ Y.Fp = b.Fp := by
  rw [Array.getElem?_zipWith] at h
  cases hb : bs[j]? with
  | none =>
    rw [hb] at h
    cases h
  | some b =>
    rw [hb] at h
    cases hx : ls[j]? with
    | none =>
      rw [hx] at h
      cases h
    | some y =>
      rw [hx] at h
      obtain rfl := Option.some.inj h
      exact ⟨b, rfl, rfl, rfl⟩

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {W : Verify.Public}
  {ch : Verify.Chains} {Bt : Stages.LinksH}

/-- In scope the tests `Fo.ZTests` hold at each built segment. -/
theorem built_tests (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hW : publicOf Z.pol Z.KL lay = .ok W) (hB : builtOf W ch = .ok Bt) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Bt.links[l]? = some X) : Fo.ZTests X.tl X.tl X.Fp := by
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
    exact Fo.ZPlan.public_H_zTests0 hW
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
    exact Fo.ZPlan.public_G_zTests0 hW g _ hg'
  · obtain ⟨a, ha, -⟩ := hA g hg
    obtain ⟨ar, e⟩ := zipped_attention hB hls hq g a ha
    unfold zipped at e
    obtain ⟨b, hb, u1, u2⟩ := zip_tails e
    rw [hX] at hb
    obtain rfl := Option.some.inj hb
    have e1 : X.tl = a.seam.tl := u1.symm
    have e2 : X.Fp = a.seam.Fp := u2.symm
    rw [e1, e2]
    exact Fo.ZPlan.public_A_zTests0 hW g a ha

/-- **Where the proof file's public part is made.** -/
theorem tests_of_pub {Z : VerifierAndGoals.PublicFiles} {lay : ByteArray} {Zp : ProofFile.Pub}
    (hZ : VerifierAndGoals.InScope Z = true)
    (hpub : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol lay Z.KL = .ok Zp) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[l]? = some X) : Fo.ZTests X.tl X.tl X.Fp := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hZ
  have hW : Verify.publicOf Z.pol Z.KL (some lay) = .ok Zp.p.X :=
    (PlanWritten.publicOfO_older Z.pol Z.KL (some lay)).symm.trans (ProofFile.Law.pub_public hpub)
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf hpub
  rw [← e] at hX
  have hX' : (b.links.map ProofFile.Law.blank)[l]? = some X := hX
  rw [Array.getElem?_map] at hX'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hX'
  have k : Fo.ZTests Y.tl Y.tl Y.Fp := built_tests hZ hR hW hb hl hY
  exact k

end VerifiableInference.Desc.LinkJoin

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.LinkJoin (DigStatic digStatic_of_tests tests_of_pub)
open VerifiableInference.OnPublicFiles (SameDig)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- At the head. -/
theorem AtMg.tests (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {m : ℕ} (hm : m < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[m]? = some X) : Fo.ZTests X.tl X.tl X.Fp :=
  tests_of_pub h.scope h.laid.pub hm hX

/-- **At the head the six fields are left with one premise.** -/
theorem AtMg.digStatic_of_same (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {m : ℕ} (hm : m < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[m]? = some X) {tlD : HTailF2}
    (hs : SameDig tlD X.tl) : DigStatic tlD X.tl X.Fp :=
  digStatic_of_tests hs (h.tests hm hX)

end P5J

#print axioms VerifiableInference.Desc.LinkJoin.digStatic_of_tests
#print axioms VerifiableInference.Desc.LinkJoin.zip_tails
#print axioms VerifiableInference.Desc.LinkJoin.built_tests
#print axioms VerifiableInference.Desc.LinkJoin.tests_of_pub
#print axioms P5J.AtMg.tests
#print axioms P5J.AtMg.digStatic_of_same
