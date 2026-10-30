-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/RowSeam.lean: the seam between the end of a link's sub-proof and the closing of the
link: the sub-proof's one form becomes one row of the link's group of oracle messages. Definitions,
statements and proofs.

What it is for. In a proof file's first chain each link's sub-proof ends with a draw that batches
all its claims into one form in the entries of the committed messages (`kLedBatch`,
Johnson/Top/H/LedBatch.lean). The frame of the links then lays that form as ONE open row of the
link's group, beside the rows that the switch into the group has left, and closes the group: one
round batches all rows, a fold follows (`Cb.Pv.Bat`, Cb/Pv/Bat.lean). No round stands between the
two: the seam is a step without rounds (`KObj.StepD`, Johnson/E/KObj/RowS.lean).

Main names:
  `batBase s A₀`: the base joint of the batching round at the size s: all open rows hold of the
    group's message, beside a joint A₀ on the kept messages. `jOver_batBase`: over the signature it
    is the round's own input joint `Cb.Pv.Bat.inJ s A₀`, by definition.
  `RowLay s P J St₀`: how the statement behind the draw is laid as the round's statement: the
    targets and states of the open rows, and what is carried. Data alone.
  `rowSeam s A0 msg A₀ lay`: the seam, from `jOver s.S (ledOutA A0 msg)` to
    `jOver s.S (batBase s A₀)`: the statement is laid by `lay`; the samples, the oracles and the
    witness pass unchanged.
  `RowLay.OK`: what the seam owes, as three named conditions on the base joints:
    `on`: where A0's condition holds, A₀'s holds at what is carried;
    `form`: IF ALL OPEN ROWS HOLD OF THE GROUP'S MESSAGE, THE ONE FORM HOLDS OF THE ENTRIES;
    `ride`: if all open rows hold and A₀ holds of the kept messages, A0 holds: what rode beside the
      sub-proof's claims is paid by the other rows and by what is kept.
  `rowSeam_ok`: under `RowLay.OK`: `StepD.OK`.
  `RowLay.form_of_row`: `form` from one row b₀ alone: if that row's claim at the laid state is the
    form's claim.
Limits: the three conditions are hypotheses: they are shown of no link here. Nothing says that `lay`
is the programs' laying of an equation on named arrays as a row on the group's messages, that the
other rows are those which the switch into the group leaves, or that a row which a link leaves on
the committed table (a pending row) is accounted for: it is no row of the group and must ride in A0
and A₀. The fold's mask that was sent earlier is not treated: where it rides, the target joint is
this one with that oracle kept beside. A seam adds no round and no error. Nothing on an honest
prover.
-/
import Johnson.E.KObj.RowS
import Cb.Pv.Att.BatchRide
import Cb.Pv.Bat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR TWhole Cb.Pv.Att

section
variable {E : Type} [Field E] [Fintype E] (s : Cb.Pv.Bat.Size E)
  {Kc P St₀ Wp J : Type} [Fintype J] {Ex : ExtSpec}

/-- The base joint of the batching round: all open rows hold of the group's message, beside A₀ on
the kept messages. -/
@[reducible] def batBase (A₀ : Rels Kc St₀ Ex ((s.S.sub s.kp).Msg × Wp)) :
    Rels Kc (((s.B → E) × (∀ b, s.Sb b)) × St₀) Ex (s.S.Msg × Wp) :=
  claimRels (fun x m => Slf.All s.sl x (s.G.msg m))
    (onMsgRels (s.S.res (T := OMsg.Msg) s.kp) A₀)

/-- Over the signature it is the round's own input joint. -/
theorem jOver_batBase (A₀ : Rels Kc St₀ Ex ((s.S.sub s.kp).Msg × Wp)) :
    jOver s.S (batBase s A₀) = jOf (Cb.Pv.Bat.inJ s A₀) := rfl

/-- How the statement behind the batching draw of a sub-proof is laid as the statement of the
group's batching round. -/
abbrev RowLay (P J St₀ : Type) : Type :=
  (P × E) × Form E J → ((s.B → E) × (∀ b, s.Sb b)) × St₀

variable (A0 : Rels Kc P Ex (s.S.Msg × Wp)) (msg : s.S.Msg → J → E)
  (A₀ : Rels Kc St₀ Ex ((s.S.sub s.kp).Msg × Wp)) (lay : RowLay s P J St₀)

/-- The seam. -/
@[reducible] def rowSeam : StepD (jOver s.S (ledOutA A0 msg)) (jOver s.S (batBase s A₀)) :=
  ⟨fun x => some (lay x.1, x.2), ExtMap.id _, fun _ w => w⟩

/-- What the seam owes, on the base joints. -/
structure RowLay.OK : Prop where
  /-- the condition is carried -/
  on : ∀ x y, A0.on (x.1.1, y) → A₀.on ((lay x).2, y)
  /-- all open rows of the group give the sub-proof's one form -/
  form : ∀ x m, Slf.All s.sl (lay x).1 (s.G.msg m) → x.2.Holds (msg m)
  /-- all open rows and what is kept give what rode beside the sub-proof's claims -/
  ride : ∀ x y (w : s.S.Msg × Wp), A0.on (x.1.1, y) → Slf.All s.sl (lay x).1 (s.G.msg w.1) →
    A₀.relR ((lay x).2, y) (s.S.res (T := OMsg.Msg) s.kp w.1, w.2) → A0.relR (x.1.1, y) w

/-- The base joints' step: the target's relaxed relation gives the source's. -/
theorem RowLay.OK.base (h : RowLay.OK s A0 msg A₀ lay) (x : (P × E) × Form E J) (y : Ex.Str)
    (w : s.S.Msg × Wp) (ho : (ledOutA A0 msg).on (x, y))
    (hw : (batBase s A₀).relR (lay x, y) w) : (ledOutA A0 msg).relR (x, y) w :=
  ⟨h.ride x y w ho hw.1 hw.2, h.form x w.1 hw.1⟩

/-- `form` from one row alone. -/
theorem RowLay.form_of_row (b₀ : s.B)
    (h : ∀ x m, (s.sl b₀).Holds ((lay x).1.1 b₀, (lay x).1.2 b₀) (s.G.msg m) → x.2.Holds (msg m)) :
    ∀ x m, Slf.All s.sl (lay x).1 (s.G.msg m) → x.2.Holds (msg m) :=
  fun x m ha => h x m (ha b₀)

/-- The seam has what a seam owes. -/
theorem rowSeam_ok (h : RowLay.OK s A0 msg A₀ lay) : (rowSeam s A0 msg A₀ lay).OK where
  isLocal := fun _ _ q hq => hq q (Finset.mem_singleton_self q)
  onOut := fun b x' hb hx => by
    obtain rfl : (lay b.1.1, b.1.2) = x' := Option.some.inj hx
    exact ⟨hb.1, h.on _ _ hb.2⟩
  know := fun b x' w hb hx hw => by
    obtain rfl : (lay b.1.1, b.1.2) = x' := Option.some.inj hx
    exact ⟨hw.1, h.base s A0 msg A₀ lay _ _ _ hb.2 hw.2⟩

end

#print axioms VerifiableInference.OnPublicFiles.rowSeam_ok
#print axioms VerifiableInference.OnPublicFiles.jOver_batBase

end VerifiableInference.OnPublicFiles
