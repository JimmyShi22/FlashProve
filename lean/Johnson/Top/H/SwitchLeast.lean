-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchLeast.lean: the least caller of the code switch with kept messages: no old
message stays open beside the held ones, and the carried joint asks nothing.

The caller of Johnson/Top/H/SwitchKeptIs.lean has two letters that a law on the kept messages does
not need: kq, which old messages are read behind the bridge, and the carried joint A₀. The typed
relation behind the switch asks a decoding of every old message that stays open and is not held, and
A₀'s relation. Here both are brought to nothing by a choice of the two letters, and it is shown how
far kq can be brought down. Definitions, statements and proofs.
Main names:
  `keptOnly mem kp`: the choice of kq: just the kept members.
  `keptOnly_held`: at that choice every kept member is held.
  `keptSel_S0_empty`: where only kept members stand under kq, the switch's signature of old open
    messages has no message (`SendLoc.Size.S₀`, which is `LdFoldD.S₂`, Cb/Req1/LdSegKit.lean: the
    messages under kq that are not held).
  `heldPort_never`: THE CONTROL: where no message stands under kq, NO message is held: a held
    message is a message under kq (`GHeld.cl`, Cb/Ld/LdGroupSeg.lean; `Rows.held_cl`,
    Johnson/Top/H/GroupRowsHeld.lean). So at kq := never every statement "for each held message"
    says nothing.
  `keptSel_A1_free`, `keptSel_A1_on_free`: at the carried joint that asks nothing (`Cb.mjTriv`,
    Cb/Ld/LdLkpMaskAsmProofs.lean) the joint A₁ behind the switch holds of everything, relation and
    condition.
That the promise in front can be kept at that joint, at every kq: `keptSel_member_free`
(Johnson/Top/H/SwitchHonestAt.lean).
Near kin: `Rows.keptHeld_iff`, `Rows.keptHeld_all` (Johnson/Top/H/CallerHeld.lean): at the caller of
the round in front of a proximity test (`Rows.keptCaller`) the messages read behind the round are
ALL THAT ARE NO MEMBERS and the members marked keep (`Cb.Pv.Bat.Size.kp`); if every member marked
keep is kept, every MEMBER that is read behind is held. So that caller's kq is `keptOnly` just where
every old message is a member and the marked ones are the kept ones. `kqOf`, `Letters.plain`
(Johnson/Top/H0/K2Caller/Member.lean): at a record of a place's numbers, the choice "the messages
that stay open: the kept members" and a carried joint that claims nothing, laid as a member of the
letters' types; nothing is shown of them there.
Limits: kq and A₀ are letters of a typed caller: these are facts on a choice of them. With this
choice a law at the caller says NOTHING of the protocol's other old messages: neither that they stay
as they were nor that the switch leaves them alone. That these may be left out of the switch's law
and carried past it by another rule is said by nothing here. Where the switch is laid behind the
library's own caller of the round in front, kq is that caller's, not a free choice (see the kin).
Nothing on soundness.

-/
import Johnson.Top.H.SwitchKeptIs
import Cb.Ld.LdLkpMaskAsmProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack OnBytes.Tie.Pv.Switch

variable (cs : Codes) (l : List (OracleShape × ℕ)) (mem : Fin l.length → Prop)
  [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]
  (h1 : ∀ a, kp a → (l.get a.1).1.mainRows ≠ 0) (h0 : ∀ a, kp a → (l.get a.1).1.maskRows = 0)

/-- Just the kept members. -/
def keptOnly (i : Fin l.length) : Prop := ∃ h : mem i, kp ⟨i, h⟩

instance decKeptOnly : DecidablePred (keptOnly l mem kp) := fun i =>
  inferInstanceAs (Decidable (∃ h : mem i, kp ⟨i, h⟩))

/-- At that choice every kept member is held. -/
theorem keptOnly_held (a : {a // kp a}) :
    (heldPort cs l mem s e oM oZ hM hZ kp h1 h0 (keptOnly l mem kp)).cl
      ⟨a.1.1, ⟨a.1.2, a.2⟩⟩ := ⟨a.1.2, a.2⟩

variable (kq : Fin l.length → Prop)

set_option quotPrecheck false in
local notation "hP" => heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq

/-- THE CONTROL: where no old message stays open, no message is held. -/
theorem heldPort_never (hkq : ∀ i, ¬ kq i) : IsEmpty {a // (hP).cl a} :=
  ⟨fun k => hkq _ k.1.2⟩

variable [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsPort cs l mem s e oM oZ hM hZ).G.C.J)
  (Z : Evader GE ((rowsPort cs l mem s e oM oZ hM hZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs l).sub kq).Msg × Wp))
  (cs' : Codes) (l' : List (OracleShape × ℕ)) (W : SwitchFrame)
  (num : {a // kp a} → ℕ) (plOf : {a // kp a} → KeptPlace)
  (Ft : Fit cs' l' s W (slotNum cs l mem s e oM oZ hM hZ kp num)
    (slotRow cs l mem s e oM oZ hM hZ kp) (slotPl cs l mem s e oM oZ hM hZ kp plOf))
  (t : ℕ)
  (w₀ : ((heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq).foldD Sb sl Z A₀).tgt.W) {Pw : Type}
  (Cw : LdCode GE Pw)

set_option quotPrecheck false in
local notation "jS" => iJ s W (slotNum cs l mem s e oM oZ hM hZ kp num)
  (slotRow cs l mem s e oM oZ hM hZ kp) (slotPl cs l mem s e oM oZ hM hZ kp plOf) cs' l' Ft.nameJ
set_option quotPrecheck false in
local notation "qS" => iQ s W (slotNum cs l mem s e oM oZ hM hZ kp num)
  (slotRow cs l mem s e oM oZ hM hZ kp) cs' l' Ft.nameQ

/-- **Where only kept members stay open, no old message stays open beside the held ones.** -/
theorem keptSel_S0_empty (hkq : ∀ i, kq i → ∃ h : mem i, kp ⟨i, h⟩) :
    IsEmpty (switchSel (hP) Sb sl Z A₀ cs' l' (jS) (qS) t w₀ Cw).sw.S₀.O :=
  ⟨fun a => a.2 (hkq _ a.1.2)⟩

/-- **At the carried joint that asks nothing the joint behind the switch asks nothing**: its
relation. -/
theorem keptSel_A1_free
    (w₁ : ((hP).foldD Sb sl Z (mjTriv Unit extNone (((sigOf cs l).sub kq).Msg × Unit))).tgt.W) :
    ∀ x m, (closeSel (hP) Sb sl Z (mjTriv Unit extNone (((sigOf cs l).sub kq).Msg × Unit)) cs' l'
      (jS) (qS) t w₁).loc.A₁.relR x m := fun _ _ => trivial

/-- Its condition. -/
theorem keptSel_A1_on_free
    (w₁ : ((hP).foldD Sb sl Z (mjTriv Unit extNone (((sigOf cs l).sub kq).Msg × Unit))).tgt.W) :
    ∀ x, (closeSel (hP) Sb sl Z (mjTriv Unit extNone (((sigOf cs l).sub kq).Msg × Unit)) cs' l'
      (jS) (qS) t w₁).loc.A₁.on x := fun _ => trivial

end Johnson.Top.H

#print axioms Johnson.Top.H.keptOnly_held
#print axioms Johnson.Top.H.heldPort_never
#print axioms Johnson.Top.H.keptSel_S0_empty
#print axioms Johnson.Top.H.keptSel_A1_free
#print axioms Johnson.Top.H.keptSel_A1_on_free
