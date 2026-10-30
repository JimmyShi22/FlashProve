-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallsAddress.lean: THREE PREMISES OF THE CALLS' LAWS AT THE SEATED
CONSTANT (Johnson/Desc/First/Look/K3CallsStatedCap.lean: hl, hpc, e) OUT OF "K3.theStated ... a =
some B" AND ONE NUMBER: the address's piece is below 7. One lemma. A tie of texts: no error term.

OBJECT: K3.theStated claim readers X codes shape a (Johnson/Desc/First/Look/K3Stated.lean).
USER: calls_address: nobody yet (whoever calls k3_att_stated_cap, k3_lay_stated_cap or the rows at a
  real address). lookAt_link: K3Fill.lean, K3PlanLetters.lean, K3PlanLettersLay.lean and others.
LETTERS: all free.

Why. hpc (a.piece = K3.pieceAt X i false) wants no fact on the public record in
scope (which link is the head's): where theStated returns,
theOwn_is (K3OwnIs.lean) hands a.piece = K3.pieceAt X i digits for one of the two sorts, and the
digits' pieces are 7 and 8.

Also: `lookAt_link`: lookAt's place bears the link's number: statement and proof taken over (two
binders written otherwise: Nat; the place's type by its short name) from the file
(Johnson/IMR/K3Seat.lean),
so that it can be called.

Limits. Nothing on which sort of link i is: x is what lookAt returns.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3OwnIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look

/-- lookAt's place bears the link's number. -/
theorem lookAt_link {X : Verify.Public} {i : Nat} {digits : Bool}
    {x : Place} (h : lookAt X i digits = some x) :
    x.link = i := by
  unfold lookAt at h
  dsimp only at h
  generalize (if X.p4 = true then 2 else 1) = step at h
  split at h
  · split at h
    · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
      rfl
    · obtain rfl := Option.some.inj h
      rfl
  · split at h
    · obtain ⟨hp, _, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        rfl
      · obtain rfl := Option.some.inj h
        rfl
    · obtain ⟨a, _, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        rfl
      · obtain rfl := Option.some.inj h
        rfl

/-- **Where theStated returns at an address whose piece is below 7, the address is a link's lookup
on the calls, and the public record has its place.** -/
theorem calls_address {Cl : Type} (claim : Aff → Cl)
    (readers : Nat → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hlt : a.piece < 7) :
    ∃ i x, a.link = some i ∧ a.piece = Desc.K3.pieceAt X i false ∧ lookAt X i false = some x ∧
      placeAt X i false = some (P.ofPlace (Params.settingOf X.P.frame) false x) := by
  obtain ⟨B₁, hB₁, -⟩ := Desc.K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, -⟩ := Desc.K3.theWhole_is claim true X codes shape a B₁ hB₁
  obtain ⟨i, digits, P, sent, laid, hi, hpc, hP, -⟩ :=
    Desc.K3.theOwn_is claim true X codes shape a b hb
  cases digits with
  | true =>
    exfalso
    unfold Desc.K3.pieceAt at hpc
    split at hpc
    · have e8 : a.piece = 8 := hpc
      omega
    · have e7 : a.piece = 7 := hpc
      omega
  | false =>
    have hP' := hP
    unfold placeAt at hP'
    obtain ⟨x, hx, hxP⟩ := Option.map_eq_some_iff.1 hP'
    exact ⟨i, x, hi, hpc, hx, by rw [hP, hxP]⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.lookAt_link
#print axioms VerifiableInference.OnPublicFiles.calls_address
