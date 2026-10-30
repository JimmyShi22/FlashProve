-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/NamesAtMg.lean: **"EVERY ARRAY OF A BUILT SEGMENT's LEDGER HAS AN ENTRY IN THE
SEGMENT's LIST OF NAMES", IN THE GOALS' SCOPE, AS A THEOREM: WITH EQUALITY: NO TEST ON THE PUBLIC
FILES IS WANTED FOR IT.** It is one of the two clauses on the built segment that are left of the
closed test `linkPlanB` (Johnson/Desc/First/Link/Law/HtinPaid.lean), and the conjunct `namesB` of
a candidate row of the entry tests. Five theorems. A joining. IT IMPORTS NO FILE OF THAT CANDIDATE
ROW's.
  `zip_lists`: an entry of the built segments with their routines exchanged has the segment's `Fp`
  and `Tp`.
  `built_trees`: in scope, at every segment X that `Verify.builtOf` returns: `X.Fp.trees.size =
  X.Tp.nt.size`. By `public_trees` (Johnson/Desc/First/Link/Law/PlanTreesSize.lean) and
  `zipped_layers`, `zipped_attention`, `zipped_head`.
  `names_of_pub`: **where the proof file's public part Zp is made, at every l below 25:
  `X.Fp.trees.size = X.arrayOf.size`.** With `names_size_of_built` (Law/NamesSizeOfBuilt.lean).
  `AtMg.names`: at the head, in `linkPlanB`'s own form. `AtMg.linkPlan_of_sorts`: **so `linkPlanB
  Zp m X` is left with ONE clause: `sortsB`.**
Limits. "At every built segment" means: at every X that the public reader returns: the equation
`Zp.p.built.links[m]? = some X` stays a premise; that 25 segments are returned is not said here.
At the second hash function alone. The full size alone. `sortsB` STAYS A PREMISE. No
probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Link.Law.NamesSizeOfBuilt
import Johnson.Desc.First.Link.Law.PlanTreesSize
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

/-- An entry of the built segments with their routines exchanged. -/
theorem zip_lists {bs ls : Array Stages.LinkH} {j : ℕ} {Y : Stages.LinkH}
    (h : (bs.zipWith (fun b l => { b with run := l.run }) ls)[j]? = some Y) :
    ∃ b, bs[j]? = some b ∧ Y.Fp = b.Fp ∧ Y.Tp = b.Tp := by
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

/-- In scope each built segment's ledger has as many arrays as its list has entries. -/
theorem built_trees (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hW : publicOf Z.pol Z.KL lay = .ok W) (hB : builtOf W ch = .ok Bt) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Bt.links[l]? = some X) : X.Fp.trees.size = X.Tp.nt.size := by
  obtain ⟨hq, hN, -, hA⟩ := _root_.Meaning.scope_plans hZ hR hW
  obtain ⟨pG, pA, pH⟩ := public_trees hW
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
    obtain ⟨b, hb, u1, u2⟩ := zip_lists e
    have hb' : Bt.links[24]? = some b := hb
    rw [hX] at hb'
    obtain rfl := Option.some.inj hb'
    have e1 : X.Fp = W.H.Fp := u1.symm
    have e2 : X.Tp = W.H.Tp := u2.symm
    rw [e1, e2]
    exact pH
  · have hg' : W.G[g]? = some W.G[g] := Array.getElem?_eq_getElem (by omega)
    obtain ⟨ar, e⟩ := zipped_layers hB hls g _ hg'
    have el : Stages.layersLink W.p4 g = 2 * g := by
      unfold Stages.layersLink
      rw [if_pos hq]
    rw [el] at e
    unfold zipped at e
    obtain ⟨b, hb, u1, u2⟩ := zip_lists e
    rw [hX] at hb
    obtain rfl := Option.some.inj hb
    have e1 : X.Fp = W.G[g].Fp := u1.symm
    have e2 : X.Tp = W.G[g].Tp := u2.symm
    rw [e1, e2]
    exact pG g _ hg'
  · obtain ⟨a, ha, -⟩ := hA g hg
    obtain ⟨ar, e⟩ := zipped_attention hB hls hq g a ha
    unfold zipped at e
    obtain ⟨b, hb, u1, u2⟩ := zip_lists e
    rw [hX] at hb
    obtain rfl := Option.some.inj hb
    have e1 : X.Fp = a.seam.Fp := u1.symm
    have e2 : X.Tp = a.seam.Tp := u2.symm
    rw [e1, e2]
    exact pA g a ha

/-- **Where the proof file's public part is made.** -/
theorem names_of_pub {Z : VerifierAndGoals.PublicFiles} {lay : ByteArray} {Zp : ProofFile.Pub}
    (hZ : VerifierAndGoals.InScope Z = true)
    (hpub : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol lay Z.KL = .ok Zp) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[l]? = some X) :
    X.Fp.trees.size = X.arrayOf.size := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hZ
  have hW : Verify.publicOf Z.pol Z.KL (some lay) = .ok Zp.p.X :=
    (PlanWritten.publicOfO_older Z.pol Z.KL (some lay)).symm.trans (ProofFile.Law.pub_public hpub)
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf hpub
  rw [← e] at hX
  have hX' : (b.links.map ProofFile.Law.blank)[l]? = some X := hX
  rw [Array.getElem?_map] at hX'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hX'
  exact (built_trees hZ hR hW hb hl hY).trans (names_size_of_built hb l Y hY).symm

end VerifiableInference.Desc.LinkJoin

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.LinkJoin (linkPlanB sortsB look names_of_pub)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- At the head, in the closed test's own form. -/
theorem AtMg.names (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {m : ℕ} (hm : m < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[m]? = some X) :
    X.Fp.trees.size ≤ X.arrayOf.size :=
  Nat.le_of_eq (names_of_pub h.scope h.laid.pub hm hX)

/-- **The closed test is left with one clause.** -/
theorem AtMg.linkPlan_of_sorts (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {m : ℕ} (hm : m < 25)
    {X : Stages.LinkH} (hX : Zp.p.built.links[m]? = some X)
    (hs : sortsB (X.Fp.trees.toList.map look) X.tl = true) : linkPlanB Zp m X = true :=
  h.linkPlan_of_two m hm X hs (h.names hm hX)

end P5J

#print axioms VerifiableInference.Desc.LinkJoin.zip_lists
#print axioms VerifiableInference.Desc.LinkJoin.built_trees
#print axioms VerifiableInference.Desc.LinkJoin.names_of_pub
#print axioms P5J.AtMg.names
#print axioms P5J.AtMg.linkPlan_of_sorts
