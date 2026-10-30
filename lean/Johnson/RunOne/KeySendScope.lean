-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendScope.lean: THEOREMS. **IN THE GOALS' SCOPE THE LAW OF A SENDING HOLDS AT THE KEY FILE's THREE SENDINGS WITH NO TEST LEFT TO ASK**: the four tests (SendAsks) are theorems there, at K = 129 and the planner's
radii as closed numerals; so from the run's yes alone: send_seat's whole conclusion at the three seats.
OBJECT. parIdx X | parMsg X | parW X msg and the blocks at (Key.descriptionFromSource X N P).first.blocksInOrder[0]? | [1]? | W's place (KeySendAtDesc.lean), X the source of Key.madeAt's record at public files in scope, at ANY digest.
USER. Nobody yet: whoever calls below_send | cond_idx … | seat_idx … at these numbers in scope.
LETTERS. Zp: three public files in scope · Z under ReadOf Zp.pol Z · cfg: any digest · m · X · N · P; in seats_in_scope also x, the views, and SeatLaw's own letters (base, d₁, d₂ · F, W · fOf, fIn · On, On', R, R').
  asks_in_scope    the three SendAsks: KeySendFull.lean's layer B at the five equations (five_in_scope: Johnson/RunOne/Law/KeyInScope.lean)
  seats_in_scope   three_seats with its asks paid (a packaging at fixed rows: such a packaging RESTS: nothing is built on it toward the file's top; what other files call is asks_in_scope beside the parametric laws)
What is not claimed. That the radii at which the proximity tests' laws certify closeness are these. SeedRound, fOf | fIn | hf, hkeep | hback: SeatLaw's letters. One size. Nothing on soundness.

-/
import Johnson.RunOne.KeySendFull
import Johnson.RunOne.Law.KeyInScope

set_option autoImplicit false

namespace Johnson.RunOne.KeySendGood

open OnBytes OnBytes.Params
open OnBytes.Model.Verify (Public)
open Johnson.G.OfPlan (Made)
open VerifiableInference.Desc (Block Link FileDescription)
open VerifiableInference.Desc.Sound (Frame)
open VerifiableInference.Desc.Key
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)

variable {Zp : VerifierAndGoals.PublicFiles} {Z : Public} {cfg : ByteArray} {m : Made} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **The four tests are theorems in scope.** -/
theorem asks_in_scope (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (descriptionFromSource X N P).planOk = true) :
    SendAsks 129 (parIdx X) (fun _ => 6130) ∧ SendAsks 129 (parMsg X) (fun _ => 3131959) ∧
      ∀ msg, linMessageW X.Y.k.oneTime.lin = some msg → SendAsks 129 (parW X msg) (fun _ => 3138896) := by
  obtain ⟨-, hr, hl, hi, hc⟩ := five_in_scope hZ hP hm hX hp
  exact ⟨asks_idx hc hi, asks_msg hc hr, asks_w hc hl⟩

/-- **The law at the three seats, in scope, from the run's yes alone.** -/
theorem seats_in_scope {W : Type} {F : Frame} (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    {x : Xi} {v₁ v₂ v₃ : Fmt.View} (hy : (descriptionFromSource X N P).run x v₁ v₂ v₃ = true) :
    (∃ b, (descriptionFromSource X N P).first.blocksInOrder[0]? = some b ∧ SeatLaw W F (parIdx X) (fun _ => 6130) b) ∧
    (∃ b, (descriptionFromSource X N P).first.blocksInOrder[1]? = some b ∧ SeatLaw W F (parMsg X) (fun _ => 3131959) b) ∧
    ∀ bw : Block FirstState Claim, sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) (gW X) = some bw →
      ∃ b msg, (descriptionFromSource X N P).first.blocksInOrder[(descriptionFromSource X N P).first.front.length + ((descriptionFromSource X N P).first.links.flatMap Link.blocksInOrder).length + 3 + 1]? = some b ∧
        linMessageW X.Y.k.oneTime.lin = some msg ∧ SeatLaw W F (parW X msg) (fun _ => 3138896) b := by
  obtain ⟨aI, aM, aW⟩ := asks_in_scope hZ hP hm hX (FileDescription.planOk_of_run hy)
  exact three_seats hy 129 _ _ _ aI aM aW

end Johnson.RunOne.KeySendGood

#print axioms Johnson.RunOne.KeySendGood.asks_in_scope
#print axioms Johnson.RunOne.KeySendGood.seats_in_scope
