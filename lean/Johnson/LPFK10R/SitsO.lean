-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/SitsO.lean: THE ROW K10_sits, LINK BY LINK, WITH NO PREMISE ON SCOPE, AT EVERY o FOR THE SECOND HASH FUNCTION AND AT ANY SIZE: at every link of the row of links of a description that onlineDescription
returns, the second closing block IS K10's own block at the lot's own numbers, seated alone; with K10's law at it.
WHY. k10_sits and k10_sits_each (Sits.lean, SitsAll.lean, beside this file) are typed AT OnBytes.secondHashFunction, in scope: a bound that stands in no Limit of their heads. The seats' files
have a form without scope, at a letter o (Johnson/IMR/CloseSeat.lean: close_alone).
  k10_sits_alone   O : Open o pol lay KL F Z Bs base c A B (o a letter) · hk2 : HeadIsTwo Z · (ProofFile.subsOf Z)[l]? = some sub: there are Lk, p, Q, b: c.links[l]? = some Lk · k9At Z l = some p ·
                   ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q · Lk.close[1]? = some b · LaidAlone ProofFile.sameReply b (K9.closing Q).retype b.name (cAt l sub 1 K10). close_alone at j = 1.
  k10_law_alone    and K10LawAt b Q (SitsLaw.lean): the law at the piece of that very block.
LIMITS. (1) IT RUNS OVER THE LINKS, NOT OVER THE PLACES OF THE KIND: "no other place of the kind in the first chain" is typed in scope, at secondHashFunction, at the 25 sorts alone (k10_sits_each: its table is evaluated at these sorts).
(2) HeadIsTwo Z (the driver's "head" is the frames' "kind 2") is a premise: shown in scope, at secondHashFunction (head_is_two). (3) That onlineDescription returns is a premise (Open). (4) All limits of Sits.lean and
SitsLaw.lean but the two that the title names. Nothing on soundness of the protocol.
Statements and proofs.
-/
import Johnson.LPFK10R.SitsLaw

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Close (Par K10LawAt k10LawAt_of)
open ProofFile (Cl)
open IM

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **K10_sits at a link of the row of links: no scope; every o.** -/
theorem k10_sits_alone (O : Open o pol lay KL F Z Bs base c A B) (hk2 : HeadIsTwo Z) (l : ℕ)
    (sub : ModelPart) (hsub : (ProofFile.subsOf Z)[l]? = some sub) :
    ∃ (Lk : Link S Cl) (p : VerifiableInference.Desc.K9.Where) (Q : Par) (b : Block S Cl),
      c.links[l]? = some Lk ∧ k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
      Lk.close[1]? = some b ∧
      LaidAlone ProofFile.sameReply b
        (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype b.name
        (cAt l sub 1 KindName.K10) := by
  obtain ⟨Lk, p, Q, h1, h2, h3, h4⟩ := close_alone O hk2 l sub hsub
  obtain ⟨b, x, hb, hx, hL⟩ := h4 1 KindName.K10 rfl
  have ex : x = (VerifiableInference.Desc.K9.closing Q : Block S Unit) := (Option.some.inj hx).symm
  subst ex
  exact ⟨Lk, p, Q, b, h1, h2, h3, hb, hL⟩

/-- **And the law at that very block.** -/
theorem k10_law_alone (O : Open o pol lay KL F Z Bs base c A B) (hk2 : HeadIsTwo Z) (l : ℕ)
    (sub : ModelPart) (hsub : (ProofFile.subsOf Z)[l]? = some sub) :
    ∃ (Lk : Link S Cl) (p : VerifiableInference.Desc.K9.Where) (Q : Par) (b : Block S Cl),
      c.links[l]? = some Lk ∧ k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
      Lk.close[1]? = some b ∧ K10LawAt b Q := by
  obtain ⟨Lk, p, Q, b, h1, h2, h3, h4, h5⟩ := k10_sits_alone O hk2 l sub hsub
  exact ⟨Lk, p, Q, b, h1, h2, h3, h4, k10LawAt_of h5 (by simp)⟩

end LPFK10

#print axioms LPFK10.k10_sits_alone
#print axioms LPFK10.k10_law_alone
