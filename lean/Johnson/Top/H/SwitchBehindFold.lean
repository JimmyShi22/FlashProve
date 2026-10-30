-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/SwitchBehindFold.lean: a caller of the code switch behind a group's fold, for any
group, shape and choice of kept messages, whose sent family is made of public data; its condition
from a test on numbers, the kept messages' laws and the group's radii.

A caller of the kind "SEND seed, LOC with a rider" is a size `Cb.Pv.SendLocRide.Size`
(Cb/Pv/Switch/SendLocRide.lean). `FoldSeam.sizeR D Q w₀ Cw` (Cb/Pv/Switch/FoldSeam.lean) makes one
from the data D of the fold in front and the data Q of the second half of the closing; the stage
before the switch is then the fold's target stage by definition. Here D is the library's record at
a choice of kept messages (`GHeld.foldD`, Cb/Ld/LdGroupSeg.lean), and Q sends the family of
Johnson/Pack/ (`sigOf`, `seedsOf`, `lOf`), whose four conditions follow from the test `allMeet`
(Johnson/Pack/Buys.lean). Definitions, statements and proofs.
Main names:
  `closeOf`: the second half of the closing: the family `sigOf cs l` under `seedsOf cs l`, the
    bounds `lOf`, t positions, and a sender of which nothing is asked.
  `switchOf`: the caller.
  `switchOf_stage`: the stage before the switch is the fold's target stage. By definition.
  `switchOf_ok`: `allMeet cs l = true → Hd.Laws → G.Fits → SendLocRide.OK (switchOf ..)`.
Limits: the group, its shape and its kept messages are letters: no value is written here. How the
folded word's message and randomness are read off the new messages (`cutN`), the carried joint A₀
and the rider's code are letters of which the condition asks nothing. The sender is made up:
nothing on an honest prover. That a switch of the programs' protocol is a value of `switchOf` is not
said. The condition says nothing on the size of the errors.

-/
import Cb.Ld.LdGroupSegProofs
import Cb.Pv.Switch.FoldSeam
import Johnson.Pack.Buys

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Iop IOR Johnson.Pack

variable {S : Sig GE} {G : Grp S} [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] (Hd : GHeld Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) G.C.J) (Z : Evader GE (G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (cutN : (sigOf cs l).Msg → (Hd.foldD Sb sl Z A₀).Cf.N.Wit) (t : ℕ)
  (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W)

/-- The second half of the closing: the family of public data; a sender of which nothing is
asked. -/
noncomputable def closeOf : LdCloseD (Hd.foldD Sb sl Z A₀) where
  N := sigOf cs l
  Sd := seedsOf cs l
  Wp' := Wp
  cutN := cutN
  bk₀ := fun _ w => w
  Sn :=
    { Nn := ⟨Unit, Unit, fun _ _ a => ((sigOf cs l).om a).sy0, fun _ => none⟩
      upM := fun _ _ _ => 0
      upR := fun _ _ _ => 0
      Mk := Unit
      put := fun _ _ => ()
      rest := fun w => (w.1, w.2.2)
      w0 := w₀ }
  L := fun i => lOf cs (l.get i).1 (l.get i).2
  tN := fun _ => 0
  t := t

variable {Pw : Type} (Cw : LdCode GE Pw)

/-- The caller of the code switch behind the group's fold. -/
noncomputable def switchOf : Cb.Pv.SendLocRide.Size GE :=
  Cb.Pv.FoldSeam.sizeR (Hd.foldD Sb sl Z A₀) (closeOf Hd Sb sl Z A₀ cs l cutN t w₀) w₀ Cw

/-- The stage before the switch is the fold's target stage. -/
theorem switchOf_stage :
    Cb.Pv.SendLoc.stage (switchOf Hd Sb sl Z A₀ cs l cutN t w₀ Cw).sw =
      (Hd.foldD Sb sl Z A₀).tgt := rfl

/-- The kind's condition. -/
theorem switchOf_ok (h : allMeet cs l = true) (hL : Hd.Laws) (hF : G.Fits) :
    Cb.Pv.SendLocRide.OK (switchOf Hd Sb sl Z A₀ cs l cutN t w₀ Cw) :=
  have Bu := allMeet_buys cs l h
  Cb.Pv.FoldSeam.ok_size _ _ _ ⟨Bu.laws, Bu.fair, Bu.list, Bu.evades⟩
    (ldGroup_seg_laws GE B Kc St₀ Wp S G Sh kp Hd Sb sl Z E₀ A₀ hL hF)

end Johnson.Top.H

#print axioms Johnson.Top.H.switchOf_stage
#print axioms Johnson.Top.H.switchOf_ok
