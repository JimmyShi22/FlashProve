-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03MaskBAt.lean: THE LOOKUP ARGUMENTS' FIRST TEST ON THE MASK ROW ("the segment's mask
row is there and reaches the place's number of slots"): THE FIELD hB OF `ObjEndR`
(Johnson/P5J/K03End.lean) AT THE 25 LOOKUPS ON THE CALLS AND OF `DigTestsR`
(Johnson/P5J/K03Due4.lean) AT THE 25 ON THE DIGITS, IN THEIR OWN TEXTS, AT THE CLOSED CONSTANT,
UNDER THE HEAD `AtMgA` ALONE. A JOIN: calls alone: NO TEST IS EVALUATED AND NO WRITTEN VALUE IS
SPENT: the planner's own check holds it.
  `masks_of_built` (Johnson/Desc/First/Att/K05PublicOfBuilt.lean; the attention kind's authors';
    general in the segment): a return of buildLinksH gives `masksUpTo (sentOfBuilt p B) x x.ns` at a
    place x of segment l whose number of slots is that of the link number l that was handed in.
  `built_of_pub` (Johnson/H2K5R/BuiltOfPub.lean): the built links are such a return.
  `buildLinksH_keeps` (OnBytes/TieK/LinksEnd.lean): it keeps each link's number of slots.
  `k03_slots_look_any`, `k03_slots_head_look` (Johnson/P5J/K03SlotsHeadAt.lean): the built link l's
    number of slots is the place's, at either lookup, at all 25.
  `maskCallsB_of_upTo`, `digits_maskB_of_upTo` (Johnson/Desc/First/Look/K3CallsMaskPublic.lean,
    K3DigitsMaskPublic.lean; the lookups' authors'): that one test gives both of ours, at every
    radius.
OURS: `k03_slots_all` · `k03_link_in` (the link that was handed in, with the place's number of
slots) · `k03_masksUpTo` · **`k03_hB_calls`** · **`k03_hB_digits`**.

Limits. The head `AtMgA` is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at
secondHashFunction; side library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone. The two other tests
on the mask row (hTests, h6) are not here. Nothing on soundness.

-/
import Johnson.P5J.K03SlotsHeadAt
import Johnson.H2K5R.BuiltOfPub
import Johnson.Desc.First.Att.K05PublicOfBuilt
import Johnson.Desc.First.Look.K3CallsMaskPublic
import Johnson.Desc.First.Look.K3DigitsMaskPublic
import Johnson.Desc.First.Look.K3CallsAddress
import OnBytes.TieK.LinksEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open OnBytes.Model.Stages (LinkH buildLinksH)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.First.Look (Place lookAt sigListCalls digList maskCallsB maskB
  maskCallsB_of_upTo digits_maskB_of_upTo)
open VerifiableInference.Desc.First.Att.P (masksUpTo sentOfBuilt masks_of_built built_of_pub)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Place}

/-- The built link l's number of slots is the place's, at either lookup, at all 25. -/
theorem k03_slots_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {d : Bool}
    {y : Place} (hy : lookAt (At.X Zp) l d = some y) :
    (Zp.p.built.links[l]?).map (·.ns) = some y.ns := by
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · exact k03_slots_look_any h h24 hy
  · obtain rfl : l = 24 := by omega
    exact k03_slots_head_look h hy

/-- The link number l that the planner handed to buildLinksH has the place's number of slots. -/
theorem k03_link_in (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l₀ : Array LinkH}
    (hb : buildLinksH l₀ Zp.p.X.NGr Zp.p.X.p4 Zp.p.X.layers.wsLay Zp.first = .ok Zp.p.built)
    {l : ℕ} (hl : l < 25) {d : Bool} {y : Place} (hy : lookAt (At.X Zp) l d = some y) :
    ∃ Y, l₀[l]? = some Y ∧ y.ns = Y.ns := by
  have hk := OnBytes.TieK.buildLinksH_keeps (fun Y : LinkH => Y.ns) (fun _ _ => rfl) hb
  have e := congrArg (fun t : List ℕ => t[l]?) hk
  simp only [List.getElem?_map, Array.getElem?_toList] at e
  rw [k03_slots_all h hl hy] at e
  obtain ⟨Y, hY, eY⟩ := Option.map_eq_some_iff.1 e.symm
  exact ⟨Y, hY, eY.symm⟩

/-- **The attention kind's authors' test, at all 25 segments, at either lookup's place.** -/
theorem k03_masksUpTo (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {d : Bool}
    {y : Place} (hy : lookAt (At.X Zp) l d = some y) :
    masksUpTo (sentOfBuilt Zp.first Zp.p.built) y y.ns = true := by
  obtain ⟨l₀, -, hb⟩ := built_of_pub h.laid.pub
  obtain ⟨Y, hY, eY⟩ := k03_link_in h hb hl hy
  exact masks_of_built hb hY (lookAt_link hy) eY

/-- **hB AT THE 25 LOOKUPS ON THE CALLS.** -/
theorem k03_hB_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ l < 25, ∀ y, lookAt (At.X Zp) l false = some y →
      maskCallsB (h.toAtMg.𝔇 h.𝔇).sent
        (sigListCalls (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 y.link) y.link y.ns = true :=
  fun _ hl _ hy => maskCallsB_of_upTo (k03_masksUpTo h hl hy) _

/-- **hB AT THE 25 LOOKUPS ON THE DIGITS.** -/
theorem k03_hB_digits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ l < 25, ∀ y, lookAt (At.X Zp) l true = some y →
      maskB (h.toAtMg.𝔇 h.𝔇).sent (digList y (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad) y.link
        y.arrays.ns = true :=
  fun _ hl _ hy => digits_maskB_of_upTo (k03_masksUpTo h hl hy) (Nat.le_refl _) _

end P5J

#print axioms P5J.k03_slots_all
#print axioms P5J.k03_link_in
#print axioms P5J.k03_masksUpTo
#print axioms P5J.k03_hB_calls
#print axioms P5J.k03_hB_digits
