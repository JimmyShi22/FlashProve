--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/HandsBridgeK13.lean: THE BRIDGE OF
Johnson/Desc/AtSeats/HandsBridge.lean AT OUR HOUSE's WIDER FILLING `plus13 D d Mg`
(Johnson/Desc/K13/Law/BridgeK13.lean: the three struck layers laid over Mg again): `IM.Hands` at
its public test is `IM.HandsR Fk` at Mg's own. One statement with its proof; free of any kind of
sub-protocol. `handsR_plus13`: WHERE the test on the two doors accepts at borders k and k + 1, and
  the fence Fk gives
    `FactsK13` at every state without a mark.
So our terms at kind K13's batching, at W's commitment and at the first segment's opening
(`HandsAtE`), whose premises on the letters have members at the wider filling alone,
serve at the narrower one with the facts on the verifier's state in hand. What is not claimed.
That a fence gives `FactsK13`. Nothing on soundness.
-/
import Johnson.Desc.AtSeats.HandsBridge
import Johnson.Desc.K13.Law.BridgeK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning)
open VerifiableInference.Desc.Sound (doorsFitB)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K13.Law (DataK13 plus13 cA13 FactsK13 plus13_hand plus13_class)
open ProofFile (Cl)

/-- **The bridge at our house's wider filling.** -/
theorem handsR_plus13 {Pp W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (d : K12Data)
    (Mg : Meaning Pp W) (z : Pp) {Fk : ℕ → S → Prop} {N : Numbers} {links : List ModelPart}
    {ps : List Place} {ft k : ℕ} {b : Block S Cl}
    (hD : doorsFitB Mg.more (plus13 D d Mg).more cA13 links ps k = true)
    (hD' : doorsFitB Mg.more (plus13 D d Mg).more cA13 links ps (k + 1) = true)
    (hF : ∀ s, Fk k s → s.failed = none → FactsK13 D d Mg (z, s))
    (H : IM.Hands N links ps (EAt z (plus13 D d Mg) links ps) ft k b) :
    IM.HandsR Fk N links ps (EAt z Mg links ps) ft k b :=
  handsR_of_widen z Mg (plus13 D d Mg).more (plus13 D d Mg).pub (plus13 D d Mg).inOrder cA13 links
    ps (plus13_hand D d Mg) hD hD'
    (fun s f h0 q _ hc => plus13_class D d Mg _ (hF s f h0) q hc) H

end HashBuild
