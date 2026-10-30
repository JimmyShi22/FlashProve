-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/PlacesScope.lean: THE PLACES OF onlineDescription's FIRST CHAIN's FLAT LIST ARE THE DRIVER's WRITTEN LIST: THE SCOPE's HALF. Compiled with the whole library.
OBJECT. c.blocksInOrder.map (·.place). USER. The kinds' files («at each place of the kind»: on the written list a kind's places are decided by the kernel) · Johnson/IMR/GrownBK.lean.
THE EQUATION ITSELF IS NOT THIS FILE's: chainBy_places (Johnson/Desc/ProofFile/Law/OrderCovered.lean: c.blocksInOrder.map (·.place) = flatPlacesOf (subsOf Z) (base.any fun b => b.place.kind == K13)), over flat_places (Johnson/Desc/First/Driver/PlacesLaw.lean): CALLED, NOT TYPED.
The two letters in it are named here.

  several_true      (AT EVERY o; NO SCOPE) base.any (kind == K13) = true: off
                    Johnson/IMR/BackSeat.lean's base_has_K13.
  places_any        (AT EVERY o; NO SCOPE) c.blocksInOrder.map (·.place) = flatPlacesOf (subsOf Z) true.
  subs_len · subs_all   in scope: (subsOf Z).length = 25; subsOf Z = (List.range 25).map subAt.
  subW_eq           Johnson/IMR/WrittenList.lean's subW is Johnson/IMR/LinkSeat.lean's subAt.
  places_scope      in scope: c.blocksInOrder.map (·.place) = placesW.
  place_at          in scope: c.blocksInOrder[k]? = some b → placesW[k]? = some b.place.

What is not claimed. Nothing on the shared and the second chain. Nothing in scope at an o other than secondHashFunction. No soundness.
-/
import Johnson.IMR.BackSeat
import Johnson.IMR.WrittenList
import Johnson.Desc.ProofFile.Law.OrderCovered

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart flatPlacesOf)
open ProofFile (Cl)

theorem subW_eq (l : ℕ) : subW l = subAt l := rfl

section
variable {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem several_true (O : Open o pol lay KL F Z Bs base c A B) :
    (base.any fun b => b.place.kind == KindName.K13) = true := by
  obtain ⟨b0, hb0, hk⟩ := base_has_K13 O
  exact List.any_eq_true.2 ⟨b0, hb0, by simpa using hk⟩

/-- **The places of the flat list, at every o.** -/
theorem places_any (O : Open o pol lay KL F Z Bs base c A B) :
    c.blocksInOrder.map (·.place) = flatPlacesOf (ProofFile.subsOf Z) true := by
  rw [ProofFile.Law.chainBy_places O.chain, several_true O]

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem subs_len (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : (ProofFile.subsOf Z).length = 25 := by
  have h25 := links_25 hS hR O
  by_contra hne
  have h24 : 24 < (ProofFile.subsOf Z).length :=
    (List.getElem?_eq_some_iff.1 (subs_scope hS hR O 24 (by omega))).1
  have h : 25 < (ProofFile.subsOf Z).length := by omega
  obtain ⟨Lk, e, -⟩ := (link_flat_places O.chain).2 25 _ (List.getElem?_eq_getElem h)
  have := (List.getElem?_eq_some_iff.1 e).1
  omega

theorem subs_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : ProofFile.subsOf Z = linksW := by
  apply List.ext_getElem?
  intro l
  unfold linksW
  by_cases hl : l < 25
  · rw [subs_scope hS hR O l hl, List.getElem?_map, List.getElem?_range hl]
    rfl
  · rw [List.getElem?_eq_none (by rw [subs_len hS hR O]; omega),
      List.getElem?_eq_none (by simp; omega)]

/-- **IN SCOPE THE PLACES OF onlineDescription's FIRST CHAIN's FLAT LIST ARE THE WRITTEN LIST.** -/
theorem places_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    c.blocksInOrder.map (·.place) = placesW := by
  rw [places_any O, subs_all hS hR O]
  rfl

theorem place_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {b : Block S Cl}
    (h : c.blocksInOrder[k]? = some b) : placesW[k]? = some b.place := by
  rw [← places_scope hS hR O, List.getElem?_map, h]
  rfl

end

end IM

#print axioms IM.several_true
#print axioms IM.places_any
#print axioms IM.subs_all
#print axioms IM.places_scope
#print axioms IM.place_at
