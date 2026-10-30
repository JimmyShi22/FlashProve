-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/LinkAtSeat.lean: THE SEAT LAID INTO THE LINK's LAW's LISTS OF DEBTS: what
k09_sits shows of a link of the description's first chain (`SitsAt`, Johnson/LPFK9R/Sits.lean) pays
`OwesBlocks` whole and `SegAt` (Johnson/Desc/First/Link/Law/LinkOwes.lean, LinkJoinRuns.lean).
Theorems.

What is said. `segAt_of_sits`: the seated link is the segment number l of its sort.
`blocks_of_sits`: **`OwesBlocks` at the seated link**, at the block b₃ that stands first in its
closing and at the number 14 l + n + 4 of the chain's flat list; pw := p. `blocks_each`: so at each
of the 25 links of the description's first chain, in scope.

Limits. Two of the link's law's debts and the premise on the segment: the other seven lists are not
touched. Under `k09_sits`' own premises. Nothing on soundness.

-/
import Johnson.LPFK9R.Sits
import Johnson.Desc.First.Link.Law.LinkOwes

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Where)
open VerifiableInference.Desc.LinkJoin (SegAt OwesBlocks)
open ProofFile (Cl)
open IM (Open subAt k9At)

/-- The seated link is the segment number l of its sort. -/
theorem segAt_of_sits {c : Chain S Cl} {l : ℕ} {Lk : Link S Cl} {p : Where}
    {Q : VerifiableInference.Desc.First.Close.Par} (h : SitsAt c l Lk p Q) :
    SegAt l (subAt l) Lk := ⟨h.order, h.orderAfter, h.hear⟩

/-- **OwesBlocks AT THE SEATED LINK.** -/
theorem blocks_of_sits {c : Chain S Cl} {l : ℕ} {Lk : Link S Cl} {p : Where}
    {Q : VerifiableInference.Desc.First.Close.Par} (h : SitsAt c l Lk p Q) :
    ∃ b₃ : Block S Cl, Lk.close[0]? = some b₃ ∧
      c.blocksInOrder[14 * l + Lk.hear.length + 4]? = some b₃ ∧ OwesBlocks Lk p p b₃ := by
  obtain ⟨b₃, h1, h2, _, h4⟩ := h.equation
  exact ⟨b₃, h1, h2, h.draw, h4⟩

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT EACH OF THE 25 LINKS OF THE DESCRIPTION's FIRST CHAIN, IN SCOPE.** -/
theorem blocks_each (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (p : Where) (b₃ : Block S Cl), c.links[l]? = some Lk ∧
      k9At Z l = some p ∧ SegAt l (subAt l) Lk ∧ Lk.close[0]? = some b₃ ∧
      c.blocksInOrder[14 * l + Lk.hear.length + 4]? = some b₃ ∧ OwesBlocks Lk p p b₃ := by
  intro l hl
  obtain ⟨Lk, p, Q, hp, _, h⟩ := k09_sits hS hR O l hl
  obtain ⟨b₃, h1, h2, h3⟩ := blocks_of_sits h
  exact ⟨Lk, p, b₃, h.link, hp, segAt_of_sits h, h1, h2, h3⟩

end LPFK9

#print axioms LPFK9.segAt_of_sits
#print axioms LPFK9.blocks_of_sits
#print axioms LPFK9.blocks_each
