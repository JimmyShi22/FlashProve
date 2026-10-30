-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/RowSeamRide.lean: the seam between the end of a link's sub-proof and the closing of
the link, in the form in which the closing fold's mask was sent earlier. Definitions, statements and
proofs.

What it is for. Johnson/Top/H/RowSeam.lean lays a sub-proof's one form as one row of the link's
group and ends at the input joint of the batching round. In a proof file's first chain the fresh
mask of the fold that closes a link goes out with the link's FIRST message, so the block behind the
seam is the batching round and the fold with the mask riding (`Cb.Pv.Tower.batFoldRide`,
Cb/Pv/Tower/First.lean). Its input joint is the batching round's with one oracle more, F, kept
behind all others. Through the sub-proof that oracle stands among the further oracles. The seam sets
it in its place.

Main names:
  `rowSeamRide s F A0 msg A₀ lay`: from `jOver s.S (ledOutA A0 msg)`, where A0 is a joint over the
    further oracles `E₀.prod F`, to `jOf ((Cb.Pv.Bat.inJ s A₀).keepE F)`, where A₀ is a joint over
    E₀: the statement is laid by `lay`; the oracles are set anew by `Cb.Pv.Tower.setR`; the samples
    and the witness pass unchanged.
  `RowLayRide.OK`: what the seam owes, as three named conditions on the base joints: those of
    `RowLay.OK` (Johnson/Top/H/RowSeam.lean), A₀ read at the further oracles without F.
  `rowSeamRide_ok`: under `RowLayRide.OK`: `StepD.OK`.
Limits: those of Johnson/Top/H/RowSeam.lean. Nothing is claimed of the riding oracle: neither joint
reads it. The three conditions are hypotheses: they are shown of no link here.
-/
import Johnson.Top.H.RowSeam
import Cb.Pv.Tower.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR TWhole Cb.Pv.Att

section
variable {E : Type} [Field E] [Fintype E] (s : Cb.Pv.Bat.Size E) (F : ExtSpec)
  {Kc P St₀ Wp J : Type} [Fintype J] {E₀ : ExtSpec}
  (A0 : Rels Kc P (E₀.prod F) (s.S.Msg × Wp)) (msg : s.S.Msg → J → E)
  (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)) (lay : RowLay s P J St₀)

/-- The seam, the riding oracle set behind all others. -/
@[reducible] noncomputable def rowSeamRide :
    StepD (jOver s.S (ledOutA A0 msg)) (jOf ((Cb.Pv.Bat.inJ s A₀).keepE F)) :=
  ⟨fun x => some (lay x.1, x.2), Cb.Pv.Tower.setR E₀ F s.S.ext, fun _ w => w⟩

/-- What the seam owes, on the base joints. -/
structure RowLayRide.OK : Prop where
  /-- the condition is carried -/
  on : ∀ x (y : (E₀.prod F).Str), A0.on (x.1.1, y) → A₀.on ((lay x).2, y.1)
  /-- all open rows of the group give the sub-proof's one form -/
  form : ∀ x m, Slf.All s.sl (lay x).1 (s.G.msg m) → x.2.Holds (msg m)
  /-- all open rows and what is kept give what rode beside the sub-proof's claims -/
  ride : ∀ x (y : (E₀.prod F).Str) (w : s.S.Msg × Wp), A0.on (x.1.1, y) →
    Slf.All s.sl (lay x).1 (s.G.msg w.1) →
    A₀.relR ((lay x).2, y.1) (s.S.res (T := OMsg.Msg) s.kp w.1, w.2) → A0.relR (x.1.1, y) w

/-- The seam has what a seam owes. -/
theorem rowSeamRide_ok (h : RowLayRide.OK s F A0 msg A₀ lay) :
    (rowSeamRide s F A0 msg A₀ lay).OK where
  isLocal := Cb.Pv.Tower.setR_isLocal E₀ F s.S.ext
  onOut := fun b x' hb hx => by
    obtain rfl : (lay b.1.1, b.1.2) = x' := Option.some.inj hx
    exact ⟨hb.1, h.on _ _ hb.2⟩
  know := fun b x' w hb hx hw => by
    obtain rfl : (lay b.1.1, b.1.2) = x' := Option.some.inj hx
    exact ⟨hw.1, h.ride _ _ _ hb.2 hw.2.1 hw.2.2, h.form _ _ hw.2.1⟩

end

#print axioms VerifiableInference.OnPublicFiles.rowSeamRide_ok

end VerifiableInference.OnPublicFiles
