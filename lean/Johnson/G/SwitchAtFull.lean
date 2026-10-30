-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/SwitchAtFull.lean: the condition of the caller `switchOf` of the code switch, at the 26
written lists of Johnson/G/LinkLit.lean and the written sendings of Johnson/G/PackLit.lean (the
full-size example): it is left with one premise, the laws of the choice of kept messages.

Johnson/Top/H/SwitchBehindFold.lean has the caller `switchOf` and its condition from three premises:
the test `allMeet` at the family that is sent, the laws of the kept messages (`GHeld.Laws`), and
that the group's joint radius implies each member's own (`Grp.Fits`). Johnson/G/PackLit.lean has the
first as a theorem at every sending of the seven plans; Johnson/G/BatAtFull.lean has, at each of the
26 written lists of a link's sampled messages, the test on each member from which
Johnson/Pack/Group.lean gives the third. Here they are laid in. Statements and proofs.
Main names:
  `fits_full`: `Grp.Fits` of `grpOf codesFull2 l mem logFull radFull`, at each of the 26 lists, for
    every choice of members.
  `switch_ok_full`: at each of the 26 lists, every choice of members, every shape of that group,
    every choice Hd of kept messages that has its laws, and every element x of `packFullLit`:
    `SendLocRide.OK` of `switchOf Hd .. x.1 x.2 ..`.
Limits: those of Johnson/G/PackLit.lean, Johnson/G/LinkLit.lean and Johnson/G/BatAtFull.lean: the
theorems speak of written lists and numbers; that these are the planner's is held by tests by
evaluation, or not at all (the three numbers of Johnson/G/BatAtFull.lean). Which list is the group
in front of which sending is not said: the statement holds at every pair. No shape and no choice
of kept messages is written here, and `GHeld.Laws` is shown of none. That a switch of the programs'
protocol is a value of `switchOf` is not said (Johnson/Top/H/SwitchBehindFold.lean, Limits). The
condition says nothing on the size of the errors. Nothing on the small example.

-/
import Johnson.Top.H.SwitchBehindFold
import Johnson.G.BatAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Slice Johnson.Pack Johnson.Top.H Cb Iop IOR

/-- The joint radius implies each member's own, at each of the 26 lists. -/
theorem fits_full (l : List (OracleShape × ℕ)) (hl : l ∈ linksFullLit)
    (mem : Fin l.length → Prop) [DecidablePred mem] :
    (grpOf codesFull2 l mem logFull radFull).Fits :=
  grp_fits codesFull2 l mem logFull radFull
    (fun i _ => (links_fit l hl (l.get i) (List.get_mem l i)).le)
    fun i _ => (links_fit l hl (l.get i) (List.get_mem l i)).near

instance (l : List (OracleShape × ℕ)) (mem : Fin l.length → Prop) [DecidablePred mem] :
    Nonempty (grpOf codesFull2 l mem logFull radFull).P := ⟨⟨0, Nat.two_pow_pos _⟩⟩

/-- The kind's condition, left with the kept messages' laws. -/
theorem switch_ok_full (l : List (OracleShape × ℕ)) (hl : l ∈ linksFullLit)
    (mem : Fin l.length → Prop) [DecidablePred mem]
    {Sh : GShape (grpOf codesFull2 l mem logFull radFull)}
    {kp : (sigOf codesFull2 l).O → Prop} [DecidablePred kp] (Hd : GHeld Sh kp) (hL : Hd.Laws)
    {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
    (sl : ∀ b, Slf GE (Sb b) (grpOf codesFull2 l mem logFull radFull).C.J)
    (Z : Evader GE ((grpOf codesFull2 l mem logFull radFull).Row B)) {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 l).sub kp).Msg × Wp))
    {x : Codes × List (OracleShape × ℕ)} (hx : x ∈ packFullLit)
    (cutN : (sigOf x.1 x.2).Msg → (Hd.foldD Sb sl Z A₀).Cf.N.Wit) (t : ℕ)
    (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw) :
    Cb.Pv.SendLocRide.OK (switchOf Hd Sb sl Z A₀ x.1 x.2 cutN t w₀ Cw) :=
  switchOf_ok Hd Sb sl Z A₀ x.1 x.2 cutN t w₀ Cw
    (List.all_eq_true.1 packFullLit_meets x hx) hL (fits_full l hl mem)

end Johnson.G

#print axioms Johnson.G.fits_full
#print axioms Johnson.G.switch_ok_full
