-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackPointAt.lean: two premises of seven_parts (Johnson/Road/K4/SevenParts.lean) in
its own letters, at the last statement made from the chain's data off a tape (tailT).

  `hpt_at`: the premise hpt: the batched sumcheck's typed end point reads as the verifier's
    challenges turned round: r4_at (Johnson/Road/K4/PointsAt.lean), with the stage's number of
    variables' rounds written kS P.D and the stage's letters written P.ip.inn's (the same by
    definition).
  `zt_at`: the clause zt of PointTies, where the letter zt is the token part of the lookup's point
    in the batched sumcheck's state and that point is z.
Limits. As r4_at. Identities on public numbers: nothing on a world, on a draw, on soundness or on
hiding.


-/
import Johnson.Road.K4.PointsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc
open Inst.Model (Scl)
open Inst.Model.FFSeg (zpos)
open OnBytes.Model (Fork Psc)
open OnBytes.Model.Layer (Pub Env Heard HeardStack)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Desc.First.K4 (hearStack engFl)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 tailT TailM TailR)

variable [scl : Scl] {M X : Type} (P : FullPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailF P) R)
  (k : Ks) (t : Tape) (nz : NzT (tailF P) k t) (a : Adds7 (tailF P)) (x : P.XT)

/-- The premise hpt of seven_parts. -/
theorem hpt_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d4 p) (hk : kS P.D = k.k4) {Pp : Pub}
    {v : Env} {H : Heard} {NCLp : ℕ} {F G : Fork} {u : Tape} {K : HeardStack}
    (h : hearStack engFl Pp v H k.k4 NCLp F (k.tc4 t) = some (K, G, u)) :
    ∀ j, j < kS P.D → Blocks.nat (P.ip.inn.Kp.outPt P.ip.inn.Mk
        ((tailF P).b4 ((tailT W' k t nz a).z7 x)).2) j =
      gl.val (K.rs.getD (kS P.D - 1 - j) zeroE) :=
  fun _ hj => r4_at P W' k t nz a x O hk h hj

/-- The clause zt of PointTies. -/
theorem zt_at {z : ℕ → Cb.Gl.E}
    (hz0 : ((tailF P).b4 ((tailT W' k t nz a).z7 x)).2.st.z = z) :
    ∀ j, j < P.D.lT → zpos P.D z j =
      zpos P.D ((tailF P).b4 ((tailT W' k t nz a).z7 x)).2.st.z j :=
  fun _ _ => by rw [hz0]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.hpt_at
#print axioms OnBytes.Road.K4.zt_at
