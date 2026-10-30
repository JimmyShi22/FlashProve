-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Ride.lean: a short masked sumcheck whose claimed sum is sent by the prover in the first
message, as an interactive oracle reduction with its knowledge soundness.

In the library's sumcheck (Cb/Ld/LdPsc.lean) the claimed sum is a part of the statement. In two
sumchecks of the layers' sub-proof it is hidden: the prover sends it, under a mask, in the first
message, before the sum of the hiding polynomial. What was to be shown of the true sum is from
then on claimed of the sent scalar.

Main names:
  `tsum Y st m`: the true masked sum: the sum of the summand plus the incoming masks' form.
  `rideR Y F stOf Ex`: the reduction, for any parameters Y of a sumcheck, picks F of the
    coefficients that are left out, and any type X of statements with the sumcheck's state read
    off it by stOf. Its rounds are `shapeR Y` (Cb/G6/Johnson/Layers/Ride.lean). Its verifier
    completes each short message and then is the library's verifier at the sent target. It puts
    out ((the statement, the sent scalar), the output claim).
  `ride_out`: where the picks are lawful the verifier refuses nothing: its output, written out.
  `rideE Y`: its errors. `rideE_list`: 1, the degrees of the variables, 0.
  `rideIn`, `rideOut`: the joints, for any claim Psi on the statement, a scalar and the entries,
    over what rides (A0): "Psi at the true masked sum"; "Psi at the sent scalar, and the
    sumcheck's output claims".
  `ride_knowAt`: knowledge soundness for each fixed tuple of messages, at every pick F. This is said
    under the hypotheses that stand in the statement itself, which this comment does not list; it is
    no claim that they hold.

Limits: where F is not lawful the verifier may refuse everything, and knowledge soundness then
says nothing. The errors are numbers of bad draws, round by round. The coefficient is drawn from
the whole field, each variable's challenge from that variable's own set (`PFmt.Ch`); for the
values of Cb/Pv/Lay/Sum.lean see there. Nothing is said on the honest prover, on completeness or
on zero knowledge. The sentences on what the programs do are by reading: nothing is compared with
the programs here. This reduction is not joined to the one before it or behind it in the
sub-proof: that the two joints agree is not shown in this folder.

-/
import Cb.G6.Carried
import Cb.G6.Value
import Cb.G6.Johnson.Door.Ride
import Cb.G6.Johnson.Layers.Ride

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR TWhole Johnson.L5.Layers Johnson.L5.Door

variable {E : Type} [Field E] [Fintype E] (Y : PscPar E)

def rRound0_point : (rRound0 E).IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => p.elim
  ofSyms_rd := fun _ => rfl
  zero := fun _ => ()

theorem noOrc_R : NoOrc (shapeR Y) :=
  ⟨inferInstanceAs (Subsingleton Unit),
    noOrc_s Y.fmt _ ⟨inferInstanceAs (Subsingleton Unit), trivial⟩⟩

/-- the true masked sum -/
def tsum (st : Y.St) (m : Y.J → E) : E := hSumAll (Y.vars st) (Y.sum st m) + Y.inc st m

omit [Fintype E] in
theorem tsum_holds (st : Y.St) (m : Y.J → E) : Y.SumHolds (tsum Y st m, st) m := rfl

section Term
variable (F : ∀ st, HFixs (Y.vars st)) {X : Type} (stOf : X → Y.St) (Ex : ExtSpec)

/-- the long transcript to which a short one with a sent sum is completed -/
noncomputable def full (x : X) (τ : Tr (shapeR Y)) : Tr (Y.psc Ex).shape :=
  (carryS Y (rTarget Y τ, stOf x) (F (stOf x)) Ex).tr (unride Y τ)

/-- The reduction. -/
noncomputable def rideR : IOR X Ex ((X × E) × Y.Out) Ex where
  shape := shapeR Y
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  out := fun x y τ =>
    ((Y.psc Ex).out (rTarget Y τ, stOf x) y (full Y F stOf Ex x τ)).map fun o =>
      ((x, rTarget Y τ), o)
  imp := fun y _ => y
  srcE := fun _ q => {q}
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

/-- Where the picks are lawful the verifier refuses nothing. -/
theorem ride_out (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) (x : X) (y : Ex.Str) (τ : Tr (shapeR Y)) :
    (rideR Y F stOf Ex).out x y τ =
      some ((x, rTarget Y τ), shortV Y F (rTarget Y τ, stOf x) (unride Y τ)) := by
  have h := short_out Y F Ex hF (rTarget Y τ, stOf x) y (unride Y τ)
  show ((shortR Y F Ex).out (rTarget Y τ, stOf x) y (unride Y τ)).map _ = _
  rw [h]
  rfl

/-- Its errors. -/
def rideE : Err (rideR Y F stOf Ex).shape := ((1, errS Y) : ℕ × Err _)

theorem rideE_list : TWhole.errList (rideE Y F stOf Ex) = 1 :: (Y.fmt.map PFmt.n ++ [0]) :=
  congrArg (1 :: ·) (errList_s Y Y.fmt)

variable {Wt Kc : Type} (msg : Wt → Y.J → E) (A0 : IOR.Rels Kc Y.St Ex Wt)
  (Psi : X → E → (Y.J → E) → Prop)

/-- The joints. -/
def rideIn : IOR.Rels Kc X Ex Wt :=
  Y.baseRels A0 msg stOf fun x m => Psi x (tsum Y (stOf x) m) m
def rideOut : IOR.Rels Kc ((X × E) × Y.Out) Ex Wt :=
  Y.baseRels A0 msg (fun b => stOf b.1.1) fun b m => Psi b.1.1 b.1.2 m ∧ Y.OutHolds b.2 m

end Term

/-- Knowledge soundness, for each fixed tuple of messages. -/
theorem ride_knowAt (F : ∀ st, HFixs (Y.vars st)) {X : Type} (stOf : X → Y.St) (Ex : ExtSpec)
    (M Wp Kc : Type) (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E)
    (Psi : X → E → (Y.J → E) → Prop) (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) :
    KnowAt (rideR Y F stOf Ex) (rideIn Y stOf Ex (fun w : M × Wp => msg w.1) A0 Psi)
      (rideOut Y stOf Ex (fun w : M × Wp => msg w.1) A0 Psi) (fun _ _ _ wp => wp)
      (rideE Y F stOf Ex) where
  point := ⟨(rRound0_point, sRounds_point Y.fmt _ (pRoundV_point Y.A, ()))⟩
  isLocal :=
    { out := fun x y y' τ τ' h1 h2 _ _ => by
        rw [tr_ext (noOrc_R Y) τ τ' h1 h2]
        show ((Y.psc Ex).out _ y _).map _ = ((Y.psc Ex).out _ y' _).map _
        rw [(psc_local E Y Ex).out _ y y' _ _ rfl rfl (fun p hp => absurd hp (by
          show p ∉ (Y.psc Ex).extReads _
          simp [PscPar.psc, IOR.seq, PscPar.core, PscPar.ends])) fun _ _ => rfl]
      imp := fun y y' _ _ q _ _ h _ => h q (Finset.mem_singleton_self q) }
  onOut := fun a τ b ha hb => by
    obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨o, _, rfl⟩ := Option.map_eq_some_iff.1 hxo
    exact ha
  know := fun m a _ => by
    refine Doomed.mono _ _ ?_
      (ride_doomed Y Ex hV hD hI (stOf a.1) (F (stOf a.1)) a.2 (msg m))
    intro τ hτ b wp hb hB
    obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hxo
    have hs : Y.SumHolds (rTarget Y τ, stOf a.1) (msg m) := by
      by_contra hn
      exact hτ hn o ho hB.2.2
    have hs' : tsum Y (stOf a.1) (msg m) = rTarget Y τ := hs
    refine ⟨hB.1, ?_⟩
    show Psi a.1 (tsum Y (stOf a.1) (msg m)) (msg m)
    rw [hs']
    exact hB.2.1

end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.ride_knowAt
#print axioms Cb.Pv.Lay.rideE_list
#print axioms Cb.Pv.Lay.ride_out
