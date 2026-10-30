-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/StaticWholeAtMg.lean: **`StaticOk` WHOLE (Johnson/Desc/First/Link/Law/OkJoin.lean: all
four fields) AT EVERY BUILT SEGMENT, IN THE GOALS' SCOPE: A THEOREM AT THE HEAD: NO TEST ON THE
PUBLIC FILES IS WANTED FOR IT.** Six theorems. A joining. IT IMPORTS NO FILE OF A CANDIDATE ROW's.
Why. Three fields: Johnson/P5T/StaticAtMg.lean. The fourth, `blocks`:
the two computations of how many runs of rows tile the array ZZ agree
at whatever `HTailF2.piecesF` returns (`P1K9.wants_of_piecesF`, Johnson/P1K9R/WantsBlocks.lean);
and every member of the public parameters is what `piecesF` returned, but for fields that the
sentence does not read (`Fo.ZPlan.FromPieces` with `public_G_from`, `public_A_from`,
`public_H_from`, OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean; `Fo.SameP` keeps `tau`, `mz` and
`blocks`).
  `blocks_of_from`: `FromPieces tl` gives the field at tl. `built_blocks`: in scope, at every
  segment that `Verify.builtOf` returns. `blocks_of_pub`: where the proof file's public part Zp is
  made. `AtMg.blocks`: at the head.
  `AtMg.staticOk`: **`StaticOk X.tl X.Fp` at every m below 25 and the built segment X there.**
  `AtMg.staticOk_ground`: at the segment of the blank letters' list, of which the spending laws
  speak.
Limits. "At every built segment" means: at every X that the public reader returns: the equation
`Zp.p.built.links[m]? = some X` stays a premise; that 25 segments are returned is not said here.
At the second hash function alone. The full size alone. No probability: no soundness
follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.StaticAtMg
import Johnson.P1K9R.WantsBlocks
import OnBytes.Tie.Pv.Lookup.Ends.FoZTests0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf builtOf)
open OnBytes.L5.LinksOrder (ok_bind zipped zipped_layers zipped_attention zipped_head linksOf_size)
open _root_.Fo.ZPlan (FromPieces public_G_from public_A_from public_H_from)

/-- The field at whatever `piecesF` returned, but for fields that it does not read. -/
theorem blocks_of_from {tl : HTailF2} (h : FromPieces tl) :
    tl.wants.map (·.1) = some tl.zzBlocks := by
  obtain ⟨tl0, tlp, hp, hs⟩ := h
  have k := P1K9.wants_of_piecesF hp
  have e1 : tl.wants = tlp.wants := by
    unfold HTailF2.wants
    rw [hs.tau, hs.mz]
  have e2 : tl.zzBlocks = tlp.zzBlocks := by
    unfold HTailF2.zzBlocks
    rw [hs.same.blocks]
  rw [e1, e2]
  exact k

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {W : Verify.Public}
  {ch : Verify.Chains} {Bt : Stages.LinksH}

/-- In scope the field holds at each built segment. -/
theorem built_blocks (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hW : publicOf Z.pol Z.KL lay = .ok W) (hB : builtOf W ch = .ok Bt) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Bt.links[l]? = some X) :
    X.tl.wants.map (·.1) = some X.tl.zzBlocks := by
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
    obtain ⟨b, hb, u1, _⟩ := zip_tails e
    have hb' : Bt.links[24]? = some b := hb
    rw [hX] at hb'
    obtain rfl := Option.some.inj hb'
    have e1 : X.tl = W.H.tl := u1.symm
    rw [e1]
    exact blocks_of_from (public_H_from hW)
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
    rw [e1]
    exact blocks_of_from (public_G_from hW g _ hg')
  · obtain ⟨a, ha, -⟩ := hA g hg
    obtain ⟨ar, e⟩ := zipped_attention hB hls hq g a ha
    unfold zipped at e
    obtain ⟨b, hb, u1, _⟩ := zip_tails e
    rw [hX] at hb
    obtain rfl := Option.some.inj hb
    have e1 : X.tl = a.seam.tl := u1.symm
    rw [e1]
    exact blocks_of_from (public_A_from hW g a ha)

/-- Where the proof file's public part is made. -/
theorem blocks_of_pub {Z : VerifierAndGoals.PublicFiles} {lay : ByteArray} {Zp : ProofFile.Pub}
    (hZ : VerifierAndGoals.InScope Z = true)
    (hpub : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol lay Z.KL = .ok Zp) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[l]? = some X) :
    X.tl.wants.map (·.1) = some X.tl.zzBlocks := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hZ
  have hW : Verify.publicOf Z.pol Z.KL (some lay) = .ok Zp.p.X :=
    (PlanWritten.publicOfO_older Z.pol Z.KL (some lay)).symm.trans (ProofFile.Law.pub_public hpub)
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf hpub
  rw [← e] at hX
  have hX' : (b.links.map ProofFile.Law.blank)[l]? = some X := hX
  rw [Array.getElem?_map] at hX'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hX'
  have k : Y.tl.wants.map (·.1) = some Y.tl.zzBlocks := built_blocks hZ hR hW hb hl hY
  exact k

end VerifiableInference.Desc.LinkJoin

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.LinkJoin (StaticOk blocks_of_pub zip_tails)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- At the head. -/
theorem AtMg.blocks (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {m : ℕ} (hm : m < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[m]? = some X) :
    X.tl.wants.map (·.1) = some X.tl.zzBlocks :=
  blocks_of_pub h.scope h.laid.pub hm hX

/-- **All four fields, at each of the 25 segments.** -/
theorem AtMg.staticOk (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {m : ℕ} (hm : m < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[m]? = some X) : StaticOk X.tl X.Fp :=
  h.static_of_blocks hm hX (h.blocks hm hX)

/-- **At the segment of the blank letters' list.** -/
theorem AtMg.staticOk_ground (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {mk : ProofFile.LinksBy}
    {G : ProofFile.Ground} (hG : ProofFile.blankBy mk Zp = some G) {m : ℕ} (hm : m < 25)
    {Xl : Stages.LinkH} (e3 : G.built[m]? = some Xl) : StaticOk Xl.tl Xl.Fp := by
  obtain ⟨links, e⟩ := _root_.Meaning.K2.blank_built hG
  rw [e] at e3
  obtain ⟨b, hb, eT, eF⟩ := zip_tails e3
  rw [eT, eF]
  exact h.staticOk hm hb

end P5J

#print axioms VerifiableInference.Desc.LinkJoin.blocks_of_from
#print axioms VerifiableInference.Desc.LinkJoin.built_blocks
#print axioms VerifiableInference.Desc.LinkJoin.blocks_of_pub
#print axioms P5J.AtMg.blocks
#print axioms P5J.AtMg.staticOk
#print axioms P5J.AtMg.staticOk_ground
