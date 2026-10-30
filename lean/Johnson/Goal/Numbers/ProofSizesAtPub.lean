-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/ProofSizesAtPub.lean: the fields of ProofSizesAtPlain.lean and
ProofLinksAtScope.lean at the public part Z of the proof file's description
(`ProofFile.pureRoad.pub o`, Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean): at `Z.p.chains.made.sized.proof`.
Statements and proofs; no definition.

Why. The laws of the kinds at the proof file's description speak of Z. `Z.p` is `Z.made.p` by
definition, and `Z.made` is what `ProofFile.PlainG.madeOf o` returns (`ProofFile.Law.pubBy_made`,
Johnson/Desc/ProofFile/Law/MakerPublic.lean). So the fields carry over by one call.

Main statements, all at three public files P in the goals' scope and `pureRoad.pub o P.pol P.lay
P.KL = .ok Z`, o a letter.
  `made_of_pub`: `Z.made` is `madeOf`'s value.
  `atFull_of_pub`: `H2K.Sizes.AtFull Z.p.chains.made`.
  `set_ownFirst_of_pub`: the setting and the first group of the request's own test.
  `eight_of_pub_groups`: nine equations, UNDER A TEST ON P's OWN LAYOUT FILE: its group lines, as
    read, are the typed list.
  `eight_of_pub`: the same under the closed premise `H2K.Sizes.LayoutGroupsAre`.

Limits. As in the two files named: seven of the nine equations stand under the premise on the layout
file, whose closed form is proved nowhere. Nothing on the frames. Nothing on soundness.

-/
import Johnson.Goal.Numbers.ProofLinksAtScope
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifierAndGoals.Sizes
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify
open H2K.Sizes H2K.Member Lk6.AtPlan Johnson.G

variable {o : VerifierAndGoals.SecondHashFunctionType} {P : VerifierAndGoals.PublicFiles} (hP : VerifierAndGoals.InScope P = true) {Z : ProofFile.Pub}
  (h : ProofFile.pureRoad.pub o P.pol P.lay P.KL = .ok Z)

include h in
/-- The planner's record in Z is what the plain `madeOf` returns. -/
theorem made_of_pub : ProofFile.PlainG.madeOf o P.pol P.lay P.KL = .ok Z.made :=
  ProofFile.Law.pubBy_made (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts P.pol P.lay P.KL = .ok Z
          from h)

include hP h

theorem atFull_of_pub : AtFull Z.p.chains.made := atFull_of_made hP (made_of_pub h)

theorem set_ownFirst_of_pub :
    Z.p.chains.made.sized.proof.set = setLit ∧
      Z.p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } :=
  set_ownFirst_of_made hP (made_of_pub h)

/-- **The nine equations at Z, under the test on P's own layout file.** -/
theorem eight_of_pub_groups (hg0 : (Plan.layoutRead P.lay).map (·.groups) = some groupsFull) :
    Z.p.chains.made.sized.proof.set = setLit ∧ Z.p.chains.made.sized.proof.codes = codesFull2 ∧
      Z.p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } ∧
      Z.p.chains.made.sized.proof.last.stages = szLFull ∧
      Z.p.chains.made.sized.proof.link = ⟨gLink, 219⟩ ∧
      Z.p.chains.made.sized.proof.request.link = linksFull ∧
      Z.p.chains.made.sized.proof.request.code = 0 ∧
      Z.p.chains.made.sized.proof.request.maskCode = 0 ∧
      Z.p.chains.made.sized.proof.request.answers = 1 :=
  eight_of_made_groups hP (made_of_pub h) hg0

/-- **The same under the closed premise.** -/
theorem eight_of_pub (hG : LayoutGroupsAre) :
    Z.p.chains.made.sized.proof.set = setLit ∧ Z.p.chains.made.sized.proof.codes = codesFull2 ∧
      Z.p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } ∧
      Z.p.chains.made.sized.proof.last.stages = szLFull ∧
      Z.p.chains.made.sized.proof.link = ⟨gLink, 219⟩ ∧
      Z.p.chains.made.sized.proof.request.link = linksFull ∧
      Z.p.chains.made.sized.proof.request.code = 0 ∧
      Z.p.chains.made.sized.proof.request.maskCode = 0 ∧
      Z.p.chains.made.sized.proof.request.answers = 1 :=
  eight_of_made hP (made_of_pub h) hG

end VerifierAndGoals.Sizes

#print axioms VerifierAndGoals.Sizes.made_of_pub
#print axioms VerifierAndGoals.Sizes.atFull_of_pub
#print axioms VerifierAndGoals.Sizes.set_ownFirst_of_pub
#print axioms VerifierAndGoals.Sizes.eight_of_pub_groups
#print axioms VerifierAndGoals.Sizes.eight_of_pub
