-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/StaticAtBuilt.lean: THE SMALLNESS TEST: AT EACH OF THE 25 BUILT SEGMENTS OF AN OPENING
OF THE DESCRIPTION, IN THE GOALS' SCOPE: LinkJoin.StaticOk
(Johnson/Desc/First/Link/Law/OkJoin.lean), WHOLE, AND Fo.ZTests
(OnBytes/Tie/Pv/Lookup/Ends/FoLookDigitsRun.lean). UNDER THE SCOPE AND IM.Open ALONE: no state, no
test on the public files, no head. Lemmas; none of the library's goals. A joining. No prover stands
in them; nothing on completeness, soundness or hiding. Why. The library ends in `StaticOk Xl.tl
Xl.Fp` at the head AtMg (P5J.AtMg.staticOk_ground, Johnson/P5T/StaticWholeAtMg.lean); its proof
spends of the head the scope and "the public part is made" alone, and an opening has both.

  `at_built`   a built segment of the blank letters' list has the data and the planned ledger of a
      segment of the public part's list: Meaning.K2.blank_built (Johnson/IMR/OwnSeat.lean),
      LinkJoin.zip_tails (Johnson/P5T/DigFiveAtMg.lean). Its three lines are the first three of the
      proof of P5J.AtMg.staticOk_ground
  **`static_at_built`**   LinkJoin.blocks_of_pub (StaticWholeAtMg.lean), two_of_pub
      (Johnson/P5T/StaticAtMg.lean), tests_of_pub (DigFiveAtMg.lean), Fo.coefOK_of_test
      (OnBytes/Tie/Pv/Lookup/Ends/FoTailPlanes.lean): the term of P5J.AtMg.static_of_blocks with
      these three in the stead of the head's
  **`tests_at_built`**   tests_of_pub there
Limits. At the format's second hash function alone. The full size's 25 segments. That the description can be
opened is a premise. On the built segment alone: nothing on the data or the ledger of any state
(`static_at_batch`, Johnson/P1K8R/StaticAtBatch.lean, carries `StaticOk` to the states reached in
front of a batching).
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.StaticWholeAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

section
variable {P : VerifierAndGoals.PublicFiles} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- A built segment of the blank letters' list has the data and the planned ledger of the segment
of that number in the public part's list. -/
theorem at_built (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ}
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) :
    ∃ b, Z.p.built.links[l]? = some b ∧ Xl.tl = b.tl ∧ Xl.Fp = b.Fp := by
  obtain ⟨links, e⟩ := _root_.Meaning.K2.blank_built O.blank
  rw [e] at e3
  exact LinkJoin.zip_tails e3

/-- **`StaticOk`, WHOLE, AT EACH BUILT SEGMENT.** -/
theorem static_at_built (hS : VerifierAndGoals.InScope P = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) : LinkJoin.StaticOk Xl.tl Xl.Fp := by
  obtain ⟨b, hb, eT, eF⟩ := at_built O e3
  rw [eT, eF]
  exact ⟨LinkJoin.blocks_of_pub hS O.pub hl hb,
    fun Fn _ => (LinkJoin.two_of_pub hS O.pub hl hb).1 Fn, (LinkJoin.two_of_pub hS O.pub hl hb).2,
    Fo.coefOK_of_test (LinkJoin.tests_of_pub hS O.pub hl hb).t9⟩

/-- **The lookup on the digits' premises on public numbers, at each built segment.** -/
theorem tests_at_built (hS : VerifierAndGoals.InScope P = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) : Fo.ZTests Xl.tl Xl.tl Xl.Fp := by
  obtain ⟨b, hb, eT, eF⟩ := at_built O e3
  rw [eT, eF]
  exact LinkJoin.tests_of_pub hS O.pub hl hb

end

end P1K8

#print axioms P1K8.at_built
#print axioms P1K8.static_at_built
#print axioms P1K8.tests_at_built
