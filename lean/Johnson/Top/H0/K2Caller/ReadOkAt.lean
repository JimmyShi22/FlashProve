-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/ReadOkAt.lean: what is owed by whoever lays the seven readings, the two
views and the two tests of work into the tie of the code switch's law (`ReadOK`,
Johnson/Top/H0/K2Hands/TieT.lean), paid at the values of LawAt.lean: `rdOf`, `vN`, `passOf`.

  readOK_at: the six clauses: where a round's test of work passes, the seed and the positions have
      readings; there the views that the typed side reads show the elements, the positions and the
      items that the kind is shown; the second view's items do not hang on the verifier's message
Limits: those of ReadingRd.lean and LawAt.lean. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.LawAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.First.K2Hands
open OnBytes.Tie.Pv.Row (rvOne)

set_option maxHeartbeats 1000000 in
/-- **The six clauses at the readings of ReadingRd.lean.** -/
theorem readOK_at {r : SwRow} {H : r.OK} (X : Letters r H)
    (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (w : K2Wr r d₁ d₂) :
    ReadOK (selR X) (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
      (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) (rdOf (X.withSel iJ iQ) d₁ d₂ ρ)
      (vN d₁) (vN d₂) (passOf d₁) (passOf d₂) where
  seed := fun m c hp => seed_some d₁ d₂ H w m c hp
  pos := fun m c hp => pos_some d₁ d₂ w m c hp
  elems := fun m c hp => by
    show (shownW d₁ voidE m c).drawn.elems = (rvOne d₁ m c).drawn.elems
    rw [shownW_pass d₁ voidE m c hp]
  poss := fun m c hp => by
    show (shownW d₂ (voidP (baseCount r.set .request r.g)) m c).drawn.poss =
      (rvOne d₂ m c).drawn.poss
    rw [shownW_pass d₂ _ m c hp]
  vals := fun _ _ _ => rfl
  viewOK := rdOf_viewOK (X.withSel iJ iQ) d₁ d₂ ρ

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.readOK_at
