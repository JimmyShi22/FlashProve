-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/FirstLenOfOpen.lean: WHEREVER onlineDescription RETURNS, THE FIRST ROW OF PIECES IS AS
LONG AS THE FIRST TABLE's WALK. Theorems.

WHY. Sh.hlen_at_seat (Johnson/Desc/K14/Law/SharedConstLenAt.lean) asks hc (the first chain is one
that ProofFile.chainBy returns) and hsev (a sub-protocol of the kind K13 is among its base). Both are had
from "onlineDescription returns", by IM.Open, IM.seat_open
(Johnson/IMR/SeatOpen.lean) and IM.places_any (Johnson/IMR/PlacesScope.lean).
  hlen_of_open      IM.Open o pol lay KL F Z Bs base c A B · OfDesc F T ⊢
                    1 + T.l₁.length = (First.flatPlaces true (ProofFile.subsOf Z) true).length.
  hlen_of_descPure  ProofFile.onlineDescription o pol lay KL = .ok F ⊢ there is a public part Z, the one that the
                    road makes, at which that holds for every T with OfDesc F T.
What is not claimed. OfDesc at the pieces that are meant. That the first table's open letter links
is ProofFile.subsOf Z. No number. Nothing on soundness.

-/
import Johnson.IMR.PlacesScope
import Johnson.Desc.Sound.DescThree
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block Chain FileDescription First.S)
open VerifiableInference.Desc.First (flatPlaces flatPlacesOf)
open VerifiableInference.Desc.Sound

namespace Sh

/-- **From the opened seat.** -/
theorem hlen_of_open {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
    {c : Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) {C : CK} {D : WholeD} {all : List LeftT}
    {X₁ X₂ W : Type} (T : ThreeAt C D all F X₁ X₂ W) (hO : OfDesc F T) :
    1 + T.l₁.length = (flatPlaces true (ProofFile.subsOf Z) true).length := by
  have h1 := congrArg List.length hO.b₁
  simp only [List.length_map, List.length_cons] at h1
  have h2 := congrArg List.length (IM.places_any O)
  rw [List.length_map] at h2
  have e : F.first.blocksInOrder.length = c.blocksInOrder.length := by
    rw [O.desc]
    rfl
  show 1 + T.l₁.length = (flatPlacesOf (ProofFile.subsOf Z) true).length
  omega

/-- **From "onlineDescription returns".** -/
theorem hlen_of_descPure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (hF : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ Z, ProofFile.pubPlain o pol lay KL = .ok Z ∧
      ∀ {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type} (T : ThreeAt C D all F X₁ X₂ W),
        OfDesc F T → 1 + T.l₁.length = (flatPlaces true (ProofFile.subsOf Z) true).length := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  exact ⟨Z, O.pub, fun T hO => hlen_of_open O T hO⟩

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.hlen_of_open
#print axioms Desc.K14.Law.Sh.hlen_of_descPure
