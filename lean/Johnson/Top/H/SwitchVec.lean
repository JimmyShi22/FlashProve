-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchVec.lean: the caller of the code switch behind a group's fold, with the claim on
the folded word stated by its vector of coefficients; the step without rounds that leads there from
the fold's own target stage; and its conditions, carried over from the caller `switchOf`.

The target stage of a fold (`LdFoldD.tgt`, Cb/Req1/LdSegKit.lean) states the claim on the folded
word as a target and a state of the fold's output form. At `GHeld.foldD` that state holds the
states of all rows in front, the coefficients' seed, the point and the factor. A verifier that
keeps the folded form as a vector cannot give that state back. The claim reads the state through
the form's vector alone (`Slf.Holds`, Cb/Ld/LdRel.lean). Here the state is replaced by the vector
(`Slf.idf`). Definitions, statements and proofs.
Main names:
  `vecD D`: the data D of a fold with the state of the output form := its vector.
  `toVec D`: a statement of D's target stage as one of `vecD D`'s: the target and all samples as
    they are; the state replaced by the form at it.
  `stepVec D`, `stepVec_ok`: the step without rounds (`KObj.StepD`, Johnson/E/KObj/RowS.lean)
    between the two stages' joints, and what a seam owes of it. Oracles and witnesses do not move.
  `closeVec Q`: the second half of a closing, at `vecD D`.
  `switchVec`: `FoldSeam.sizeR` at `vecD (Hd.foldD ..)` and `closeVec (closeOf ..)`.
  `switchVec_ok`: its condition, from the three premises of `switchOf_ok`. `switchVec_ok_of`: from
    the condition of `switchOf`.
  `switchVec_prices`, `switchVec_fits`: `SendLocPrices` and `SendLocFits` carry over from
    `switchOf`: they read the sent family, its seeds and bounds, the radius, the positions and the
    rider's code alone.
Limits: those of Johnson/Top/H/SwitchBehindFold.lean. Nothing says that a program's vector is the
form at a typed state.

-/
import Johnson.Top.H.SwitchPrices
import Johnson.E.KObj.RowS
import Ior.FrameProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Iop IOR Johnson.Pack OnBytes OnBytes.Params OnBytes.Plan
open OnBytes.Tie.Pv.Switch

section
variable {Kc : Type} (D : LdFoldD GE Kc)

/-- The data of a fold, the claim on the folded word stated by its vector. -/
@[reducible] def vecD : LdFoldD GE Kc := { D with Stf := D.Cf.J → GE, slf := Slf.idf }

/-- A statement of the fold's target stage, the state replaced by the form at it. -/
def toVec (x : D.tgt.X) : (vecD D).tgt.X :=
  ((((x.1.1.1.1, D.slf x.1.1.1.2), x.1.1.2), x.1.2), x.2)

/-- The step without rounds between the two stages' joints. -/
def stepVec : KObj.StepD (KObj.jOf (D.tgt.S.over D.tgt.A))
    (KObj.jOf ((vecD D).tgt.S.over (vecD D).tgt.A)) :=
  ⟨fun x => some (toVec D x), ExtMap.id _, fun _ w => w⟩

theorem stepVec_ok : (stepVec D).OK where
  isLocal := extMap_isLocal.1 _
  onOut := fun b x' hb hf => by
    obtain rfl := Option.some.inj hf
    exact hb
  know := fun b x' w _ hf hw => by
    obtain rfl := Option.some.inj hf
    exact hw

/-- The second half of a closing, at the vector's data. -/
def closeVec (Q : LdCloseD D) : LdCloseD (vecD D) :=
  { N := Q.N, Sd := Q.Sd, Wp' := Q.Wp', cutN := Q.cutN, bk₀ := Q.bk₀, Sn := Q.Sn, L := Q.L,
    tN := Q.tN, t := Q.t, neP := Q.neP }

end

variable {S : Sig GE} {G : Grp S} [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] (Hd : GHeld Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) G.C.J) (Z : Evader GE (G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (cutN : (sigOf cs l).Msg → (Hd.foldD Sb sl Z A₀).Cf.N.Wit) (t : ℕ)
  (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw)

/-- The caller, with the claim stated by its vector. -/
noncomputable def switchVec : Cb.Pv.SendLocRide.Size GE :=
  Cb.Pv.FoldSeam.sizeR (vecD (Hd.foldD Sb sl Z A₀))
    (closeVec _ (closeOf Hd Sb sl Z A₀ cs l cutN t w₀)) w₀ Cw

/-- The stage before the switch is the vector's target stage. -/
theorem switchVec_stage :
    Cb.Pv.SendLoc.stage (switchVec Hd Sb sl Z A₀ cs l cutN t w₀ Cw).sw =
      (vecD (Hd.foldD Sb sl Z A₀)).tgt := rfl

/-- The kind's condition. -/
theorem switchVec_ok (h : allMeet cs l = true) (hL : Hd.Laws) (hF : G.Fits) :
    Cb.Pv.SendLocRide.OK (switchVec Hd Sb sl Z A₀ cs l cutN t w₀ Cw) :=
  have Bu := allMeet_buys cs l h
  Cb.Pv.FoldSeam.ok_size _ _ _ ⟨Bu.laws, Bu.fair, Bu.list, Bu.evades⟩
    (ldGroup_seg_laws GE B Kc St₀ Wp S G Sh kp Hd Sb sl Z E₀ A₀ hL hF)

/-- The kind's condition carries over. -/
theorem switchVec_ok_of (h : Cb.Pv.SendLocRide.OK (switchOf Hd Sb sl Z A₀ cs l cutN t w₀ Cw)) :
    Cb.Pv.SendLocRide.OK (switchVec Hd Sb sl Z A₀ cs l cutN t w₀ Cw) :=
  Cb.Pv.FoldSeam.ok_size _ _ _ ⟨h.1.laws, h.1.fair, h.1.list, h.1.evades⟩ h.2.laws

/-- The conditions on the prices carry over. -/
theorem switchVec_prices {s : Setting} {o : List SampleSize} {g : GroupSize}
    {idx : Fin l.length ≃ Fin o.length}
    (h : SendLocPrices (switchOf Hd Sb sl Z A₀ cs l cutN t w₀ Cw) s o g idx) :
    SendLocPrices (switchVec Hd Sb sl Z A₀ cs l cutN t w₀ Cw) s o g idx :=
  ⟨h.field, h.marginals, h.clash, h.lists, h.rule, h.source, h.counted, h.radius⟩

/-- The conditions on the shape carry over. -/
theorem switchVec_fits {samples cube answers t' logN : ℕ}
    (h : SendLocFits (switchOf Hd Sb sl Z A₀ cs l cutN t w₀ Cw) samples cube answers t' logN) :
    SendLocFits (switchVec Hd Sb sl Z A₀ cs l cutN t w₀ Cw) samples cube answers t' logN :=
  ⟨h.seeds, h.place, h.answers, h.positions⟩

end Johnson.Top.H

#print axioms Johnson.Top.H.stepVec_ok
#print axioms Johnson.Top.H.switchVec_stage
#print axioms Johnson.Top.H.switchVec_ok
#print axioms Johnson.Top.H.switchVec_ok_of
#print axioms Johnson.Top.H.switchVec_prices
#print axioms Johnson.Top.H.switchVec_fits
