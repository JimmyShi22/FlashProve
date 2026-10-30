-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K6/StretchAtSwitch.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6): THE TEXT OF THE FIELD
stretch OF `K6HeadBelow` AT THE LETTERS OF THE CODE SWITCH INTO LINK 24: o := ⟨p.place, 0⟩,
base := `maskBase` … 2, p BEING THE WRITTEN SWITCH PLACE WITH LINK 24. No definition; one theorem.

  `k6_stretch_at_switch`   under h, hA, p ∈ placesW, p.link = 24

By. `k6_stretch_named` (AtFullSide/K6/StretchNamed.lean). OF THE CODE SWITCH's AUTHORS: `atLink24W`,
`atLink24_gives` (Johnson/Desc/ProofFile/Honest/K2/Law/Link24Written.lean): at a written place with
link 24 the place is ⟨1, some 24, 2, .K2⟩ and message 2's mask entries begin at element 439 of the
sending's elements of the extension field: BY AN EVALUATION IN LEAN's KERNEL. Just one written place
has that link (their `link24W_one`): so the two premises on p are met by one place.

What it is not.
  * hA IS A PREMISE.
  * THE NUMERALS BENEATH ARE TWO OTHER GROUPS' CLOSED FACTS: here they meet: nothing is evaluated.
  * At the written list of switch places, not at the list that the kind's maker makes of a ground:
    these are one under h and the maker's opening (the same authors' `places_at_head`).
  * All limits of AtFullSide/K6/StretchNamed.lean.
  * Nothing on any property.
-/
import AtFullSide.K6.StretchNamed
import Johnson.Desc.ProofFile.Honest.K2.Law.Link24Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Kinds (Head.parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf takesOf)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type}

/-- CONDITIONAL: h; hA; hp; hl. **THE TEXT OF THE FIELD stretch AT THE SENDER's OWN LETTERS.** -/
theorem k6_stretch_at_switch (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {p : K2.SwitchPlace} (hp : p ∈ K2.Law.placesW) (hl : p.link = 24)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) :
    oneStretch (rowEntries A.B IM.k6Place (headRow (X := X) wit
      (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place).length 0) =
      some (⟨p.place, 0⟩,
        K2.maskBase p.sizes.codes (K2.switchSent p.sizes p.others)
          (K2.switchFresh p.sizes p.others p.foldVars) 2 +
          OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs,
        takesOf (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))) := by
  have g := K2.Law.atLink24_gives (List.all_eq_true.1 K2.Law.atLink24W p hp) hl
  rw [g.1, g.2.2.2.2]
  exact k6_stretch_named (X := X) h hA wit

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_stretch_at_switch
