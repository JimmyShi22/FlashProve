-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseAt.lean: AT THE VALUE THAT READS ITS LETTERS OFF A SEAT (`Plan4K`,
Johnson/Road/K4/ValueSeat.lean): PARTS OF TWO FIELDS OF `Plan4L.Owes` (CloseK.lean) ARE NO DEBTS ANY
MORE. Two theorems, of a few lines: calls of ValueSeat.lean's own lemmas.

  `Plan4K.look_at`: where the first statement is the record itself (fa a = (a.1, …)) and the seat
  finds what the lookup returned: zOf, kTg and kIncS at the first statement are that return's: three
  of the five conjuncts of `Owes.look`.
  `Plan4K.readsAt`: `Plan4L.ReadsAt` at Mt := the value's own matrices of part w, from the true
  reads at these matrices alone: the clause on the cells is concluded (`Plan4K.cells_eq`), if the
  value's layout is the place's and the matrices read as 0 outside the bounds.

Limits. THE TRUE READS STAY A PREMISE; so do `LookLines` and that the lookup's end form names filled
slots. Nothing is said of a real plan.
-/
import Johnson.Road.K4.CloseK
import Johnson.Road.K4.ValueSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Forest.Heard)
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.P1 (gl)
open VerifiableInference.Desc.Plain.K04 (Sem)
open Inst.Model (Scl)

variable [scl : Scl] {Mm T Wt : Type} (QK : Plan4K Mm T)

/-- **What the lookup left, at the first statement**: three ties, by the value's own make. -/
theorem Plan4K.look_at {x : T} {fo : Forest.Heard} (h : QK.L.look x = some fo) :
    QK.toL.plan.full.zOf x = zAt fo ∧ QK.toL.plan.full.kTg x = kTgAt fo (QK.L.fork x) ∧
      ∀ s, QK.toL.plan.kIncS x s = kIncAt fo (QK.L.fork x) s :=
  ⟨QK.zOf_look h, QK.kTg_look h, fun s => congrFun (QK.kIncS_look h) s⟩

/-- **The matrices' reads are true and their cells are the message's**, from the true reads. -/
theorem Plan4K.readsAt {par : Par} {hS : OnBytes.Model.Layer.Shape} (Sm : Sem Wt)
    (part : Wt → Mm) (hy : QK.y = par.P.y) (s : T) (fo : Forest.Heard) (o : Own) (G : Fork)
    (w : Wt)
    (hz : ∀ a b c, ¬ (a < QK.nM ∧ b < QK.nR ∧ c < QK.nC) → QK.mats (part w) a b c = 0)
    (hR : ∀ (Xp : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape),
      PubAt Xp { par.P with tokv := QK.L.tokv s } par.hp fo o G2 t4 QK.toL.plan.full.D
        QK.toL.plan.full.tb hS →
      ∀ Fl, Fo.Later G Fl →
        Xp.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) (QK.mats (part w))) :
    Plan4L.ReadsAt QK.toL par hS QK.L Sm part s fo o G w (QK.mats (part w)) :=
  ⟨hR, hy ▸ (QK.cells_eq (part w) hz).symm⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4K.look_at
#print axioms OnBytes.Road.K4.Plan4K.readsAt
