--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K9AtPub.lean: **THE FIRST LAW OF THE CANDIDATE ROW `k9Entry`, AT THE
OBJECTS THAT ITS SPENDERS TAKE.** In the goals' scope, at the public part Zp that the proof file's
own maker makes at the format's second hash function, from the accepts of the digits' row (row 11) and of
`k9Entry`: at each number below 25: (1) at the built segment that the row tests; (2) AT THE
SEGMENT OF THE BLANK LETTERS' LIST `G.built`, of which the laws on the kind K9 speak. Two
theorems. A joining.
  `k9_at_pub`: at X := `Zp.p.built.links[l]`: `StaticOk X.tl X.Fp` and `DigStatic tlD X.tl X.Fp`,
  BOTH WHOLE, at the tlD of `digAt`; the test `fitsB` of the law's own text; the two clauses of
  `linkPlanB` on the built segment.
  `k9_at_ground`: **the same three at every Xl with `G.built[l]? = some Xl`**, G the blank
  letters' ground (`ProofFile.blankBy mk Zp = some G`): THE FORM OF THE PREMISES H1, H2 OF `ok_at_batch`
  (Law/OkAtBatch.lean) AND H OF `fits_at_batch_B` (Law/FitsAtBatch.lean). By `blank_built`
   (Johnson/IMR/OwnSeat.lean) and `zip_at`: the two lists differ in the routines
  alone.
How Zp is reached: `pub_public` with `publicOfO_older`; `pub_builtOf`
(Johnson/Desc/ProofFile/Law/).
Limits. THE ACCEPT OF `k9Entry` IS A PREMISE: the row is a candidate: no verifier asks it today.
At the earlier hash alone (the landed laws on the scope speak of `publicOf`). The layout file is a
letter of its own (lay), as in the laws that spend this. That Bs.G₀ of an opening is the blank
letters' ground: the seats' house's `IM.Open.blank`: joined in Law/K9OkCall.lean. No probability:
no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Link.Law.K9DigStatic
import Johnson.Desc.First.Look.K3AsksDoor
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope
import Johnson.IMR.OwnSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model
open VerifiableInference.Desc.LinkJoin (StaticOk DigStatic look)
open VerifiableInference.Desc.K3Asks (digAt digEntry)

variable {Z : VerifierAndGoals.PublicFiles} {lay : ByteArray} {Zp : ProofFile.Pub}

/-- **At the built segment that the row tests.** -/
theorem k9_at_pub (hZ : VerifierAndGoals.InScope Z = true)
    (hpub : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol lay Z.KL = .ok Zp)
    (hd : digEntry Zp = true) (hk : k9Entry Zp = true) {l : ℕ} (hl : l < 25) :
    ∃ X x tlD, Zp.p.built.links[l]? = some X ∧ digAt Zp.p.X l = some (x, tlD) ∧
      StaticOk X.tl X.Fp ∧ DigStatic tlD X.tl X.Fp ∧ First.TailClaims.Law.fitsB X.tl = true ∧
      LinkJoin.sortsB (X.Fp.trees.toList.map look) X.tl = true ∧
      X.Fp.trees.size ≤ X.arrayOf.size := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hZ
  have hW : Verify.publicOf Z.pol Z.KL (some lay) = .ok Zp.p.X :=
    (PlanWritten.publicOfO_older Z.pol Z.KL (some lay)).symm.trans (ProofFile.Law.pub_public hpub)
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf hpub
  obtain ⟨X, hX, hs, hm, -, -, -⟩ := k9Entry_gives hk hl
  have hX' : (ProofFile.Law.blankB b).links[l]? = some X := by
    rw [e]
    exact hX
  obtain ⟨x, tlD, hD, hS⟩ := digStatic_of_rows hZ hR hW hb hd hl hX' hs hm
  have hs' := hs
  unfold segOk at hs'
  simp only [Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, _⟩, h3⟩, _⟩, _⟩, _⟩, h7⟩, _⟩, _⟩ := hs'
  exact ⟨X, x, tlD, hX, hD, static_of_seg hs, hS, h7, sorts_gives h1, names_gives h3⟩

/-- **At the segment of the blank letters' list, of which the laws speak.** -/
theorem k9_at_ground (hZ : VerifierAndGoals.InScope Z = true)
    (hpub : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol lay Z.KL = .ok Zp)
    (hd : digEntry Zp = true) (hk : k9Entry Zp = true) {mk : ProofFile.LinksBy} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Zp = some G) {l : ℕ} (hl : l < 25) {Xl : Stages.LinkH}
    (e3 : G.built[l]? = some Xl) :
    ∃ x tlD, digAt Zp.p.X l = some (x, tlD) ∧ StaticOk Xl.tl Xl.Fp ∧
      DigStatic tlD Xl.tl Xl.Fp ∧ First.TailClaims.Law.fitsB Xl.tl = true := by
  obtain ⟨links, e⟩ := _root_.Meaning.K2.blank_built hG
  rw [e] at e3
  obtain ⟨b, hb, eT, eF, _⟩ := zip_at e3
  obtain ⟨X, x, tlD, hX, hD, h1, h2, h3, _, _⟩ := k9_at_pub hZ hpub hd hk hl
  rw [hX] at hb
  obtain rfl := Option.some.inj hb
  rw [eT, eF]
  exact ⟨x, tlD, hD, h1, h2, h3⟩

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.k9_at_pub
#print axioms VerifiableInference.Desc.K9Asks.k9_at_ground
