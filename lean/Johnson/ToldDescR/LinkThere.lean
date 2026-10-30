-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/LinkThere.lean: THE LINK IS THERE: in the goals' scope, where the proof file's IOP as written in Lean can be opened (IM.Open, Johnson/IMR/SeatOpen.lean, at the second hash function), ProofFile.linkAt Z l (Johnson/Desc/ProofFile/LinkAt.lean: link number l of the first chain, as a term off the public part alone) returns a link at each l ≤ 24, and it is the opened chain's own link; at 25 it returns none. Statements and proofs. A JOIN OF RESULTS THAT LIE; nothing of them is typed anew:
  linkAt_of_open (Johnson/ToldDescR/PureChainOfOpen.lean: IM.Open … → ProofFile.linkAt Z m = c.links[m]?; over Johnson/Desc/ProofFile/Law/LinkAtLaw.lean) · IM.links_25 (Johnson/IMR/LinkSeat.lean: c.links.length = 25, in scope).
  link_there       InScope P · readFiles P = .ok pp · IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B ⊢ ∀ l ≤ 24, ∃ Lk, ProofFile.linkAt Z l = some Lk ∧ c.links[l]? = some Lk.
  link_not_there     A NEGATIVE TWIN, under the same three: ProofFile.linkAt Z 25 = none: the bound 24 is sharp.
Limits. It is wanted under the head P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF (Johnson/P5J/AtMg.lean), at P5J.At.lk Zp l := ProofFile.linkAt Zp l: what that head's file imports is not laid here: its fields scope · reads · laid.opened are, BY READING of a text of this project that is not in this repository, this theorem's three premises: one line where AtMg.lean lies. At secondHashFunction alone (links_25 is). No soundness is claimed.

-/
import Johnson.ToldDescR.PureChainOfOpen
import Johnson.IMR.LinkSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}


theorem link_there (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l ≤ 24, ∃ Lk, ProofFile.linkAt Z l = some Lk ∧ c.links[l]? = some Lk := by
  intro l hl
  have h25 := IM.links_25 hS hR O
  have hlt : l < c.links.length := by omega
  exact ⟨c.links[l],
    (linkAt_of_open O l).trans (List.getElem?_eq_getElem hlt),
    List.getElem?_eq_getElem hlt⟩

/-- A negative twin: the bound is sharp. -/
theorem link_not_there (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : ProofFile.linkAt Z 25 = none := by
  have h25 := IM.links_25 hS hR O
  exact (linkAt_of_open O 25).trans (List.getElem?_eq_none (by omega))

end

end ToldDesc

#print axioms ToldDesc.link_there
#print axioms ToldDesc.link_not_there
