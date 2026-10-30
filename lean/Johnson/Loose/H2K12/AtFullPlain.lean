-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.PlainParts
import Johnson.Loose.H2K12.PlainPartsCut
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.K12.Law.Sizes.PublicOAtScope
import Johnson.Desc.K12.Law.Sizes.LastAtScope
/-
Johnson/Loose/H2K12/AtFullPlain.lean:
ON THE PLAIN ROAD, AT EVERY o, AT EVERY THREE PUBLIC FILES IN THE GOALS' SCOPE: WHAT THE
PLANNER HAS MADE IS SIZED AS AT THE FULL SIZE: H2K.Sizes.AtFull (Law/Sizes/StageSizesAtScope.lean)
at ProofFile.Plain.planned's, ProofFile.PlainG.madeOf's and ProofFile.pubPlain's return. An assembly:
H2K12/PlainParts.lean's plain_parts hands the three conjuncts that Law/Sizes/PublicOAtScope.lean's
atFull_of_publicO takes (publicOfO o's yes; configure's yes; the sub-proofs' record). And the first
chain's last test: H2K12/PlainPartsCut.lean's plain_shapesOf_cut hands Law/Sizes/LastAtScope.lean's
last_of_public its reqFrame, its count of links and the file as read.
ON THE PLAN ALONE. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  atFull_of_plain      InScope Z · ProofFile.Plain.planned o Z.pol Z.KL lay = .ok p
                       ⇒ AtFull p.chains.made
  atFull_of_plainMade  InScope Z · ProofFile.PlainG.madeOf o Z.pol Z.lay Z.KL = .ok m
                       ⇒ AtFull m.p.chains.made
  atFull_of_pubPlain   InScope Z · ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Y
                       ⇒ AtFull Y.made.p.chains.made
  last_of_plain        as the first, at lay := some Z.lay, and hg0 : the group lines of Z's own
                       layout file, as read, are the typed lines
                       ⇒ the last test's stages are szLFull
LIMITS: one direction: from a run that returns; at no o and no file is the plain road shown to
return. last_of_plain stands under hg0, which is proved nowhere (LastAtScope.lean's head).
-/
set_option autoImplicit false
namespace H2K.Sizes
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify

/-- ON THE PLAIN ROAD, at every o. -/
theorem atFull_of_plain {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true) {lay : Option ByteArray} {p : Verify.Planned}
    (hp : ProofFile.Plain.planned o Z.pol Z.KL lay = .ok p) : AtFull p.chains.made := by
  obtain ⟨_, shapes, _, _, _, rl, _, hX, _, _, _, _, hc, _, _, _, he⟩ := H2K.Made.plain_parts hp
  exact atFull_of_publicO hZ hX hc he

/-- The same at the record that the plain madeOf makes. -/
theorem atFull_of_plainMade {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true) {m : Johnson.G.OfPlan.Made}
    (hm : ProofFile.PlainG.madeOf o Z.pol Z.lay Z.KL = .ok m) : AtFull m.p.chains.made :=
  atFull_of_plain hZ (ProofFile.Law.madeOf_planned hm)

/-- The same at the plain road's public part: the seated description's own «made». -/
theorem atFull_of_pubPlain {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true) {Y : ProofFile.Pub}
    (hY : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Y) : AtFull Y.made.p.chains.made :=
  atFull_of_plainMade hZ (ProofFile.Law.pubBy_made
    (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts Z.pol Z.lay Z.KL = .ok Y from hY))

/-- The first chain's last test on the plain road, under the test on Z's own layout file. -/
theorem last_of_plain {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true)
    (hg0 : (Plan.layoutRead Z.lay).map (·.groups) = some groupsFull) {p : Verify.Planned}
    (hp : ProofFile.Plain.planned o Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.proof.last.stages = H2K.Member.szLFull := by
  obtain ⟨links, shapes, _, _, _, _, _, hX, _, hs, _, _, hc, _, _, _, _⟩ := H2K.Made.plain_parts hp
  obtain ⟨rl, lay, _, declared, file, _, _, hf, hr, hw⟩ := H2K.Made.plain_shapesOf_cut hs
  obtain ⟨hn0, he⟩ := shapesWith_count hw
  have hg : file.groups = groupsFull := by
    have e : Plan.layoutRead Z.lay = some file := hf
    rw [e] at hg0
    exact Option.some.inj hg0
  exact last_of_public (publicO_at_scope hZ hX) hc he hr hn0 hg

end H2K.Sizes

#print axioms H2K.Sizes.atFull_of_plain
#print axioms H2K.Sizes.atFull_of_plainMade
#print axioms H2K.Sizes.atFull_of_pubPlain
#print axioms H2K.Sizes.last_of_plain
