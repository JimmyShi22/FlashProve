-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ValueSeatFirst.lean: THE FIRST GROUP's VALUE (Johnson/Road/K4/ValueSlotsFirst.lean)
AT A SEAT OF K4's TEXT: the letters of Johnson/Road/K4/ValueSeat.lean (`Plan4K`), the first group's
three numbers with their two conditions, AND THE TOKENS READ OFF THE SEAT. The twin of
ValueSeat.lean and of Johnson/Road/K4/CloseAt.lean. A record, a definition and four theorems, of a
few lines: calls of ValueSeat.lean's own lemmas, and one of its proofs typed again.

  `Plan4KF M T`: `Plan4K M T` with ls, nb, gB, nb ≤ 2 ^ gB, d = nb 2 ^ ls.
  `Plan4KF.toLF : Plan4LF Cb.Gl.E M T`: the value; its letter tok is
    tok x p := (L.tokv x).getD p 0: THE TOKENS THAT K4's HEARING READS AT THE RECORD x.
  `Plan4KF.tok_at`: that equation, by definition.
  `Plan4KF.look_atF`: where the seat finds what the lookup returned: zOf, kTg and kIncS at the first
    statement are that return's.
  `Plan4KF.cells_eqF`: if the matrices read as 0 outside the bounds, the value's cells are
    `cellsOf D (cellsAt y (mats m))`.
  `Plan4KF.readsAtF`: `Plan4LF.ReadsAtF` (CloseKFirst.lean) at Mt := the value's own matrices of
    part w, from the true reads at these matrices alone, if the value's layout is the place's and
    the matrices read as 0 outside the bounds.

WHICH READING OF THE TOKENS WAS FOLLOWED. K4's text lays the embedding's claim by `ClaimEnv.claimE`
(OnBytes/Model/LayerPanels.lean:494-503; called at OnBytes/Desc/First/K4/Hear.lean:189 with
P.tokv, which the block overwrites by the seat's tokv): it returns nothing unless tokv.size = y.T
(and `layout` lays T := 2 ^ lt, OnBytes/Model/LayerLayout.lean:484) and every token is below V; the
token of position t is tokv.getD t 0, for t below T. So at a hearing that returns in the first
group getD's default is never read at a position below 2 ^ lt. NO THEOREM HERE SAYS SO.

Limits. K04_law IS NOT PROVED BY THIS. Those of ValueSeat.lean: NOTHING HERE SAYS THAT THE LETTERS
ARE A PLAN's. THE TRUE READS STAY A PREMISE of `readsAtF`. That (J11) at these tokens is what the
statement's letter idn means is not said.
-/
import Johnson.Road.K4.ValueSeat
import Johnson.Road.K4.CloseKFirst

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

noncomputable section

/-- The letters that stay at a seat, in the first group. -/
structure Plan4KF (M T : Type) [scl : Scl] extends Plan4K M T where
  ls : ℕ
  nb : ℕ
  gB : ℕ
  hnb : nb ≤ 2 ^ gB
  hd : D.d = nb * 2 ^ ls

variable [scl : Scl] {Mm T Wt : Type} (QK : Plan4KF Mm T)

/-- The letters of ValueSlotsFirst.lean; the tokens are the seat's. -/
def Plan4KF.toLF : Plan4LF Cb.Gl.E Mm T where
  toPlan4L := QK.toPlan4K.toL
  ls := QK.ls
  nb := QK.nb
  gB := QK.gB
  hnb := QK.hnb
  hd := QK.hd
  tok := fun x p => (QK.L.tokv x).getD p 0

/-- The value's tokens at a record are those that K4's hearing reads there. -/
theorem Plan4KF.tok_at (x : T) (p : ℕ) : QK.toLF.planF.tok x p = (QK.L.tokv x).getD p 0 := rfl

/-- **What the lookup left, at the first statement**: three ties, by the value's own make, where the
seat finds the lookup's return. -/
theorem Plan4KF.look_atF {x : T} {fo : Forest.Heard} (h : QK.L.look x = some fo) :
    QK.toLF.planF.fullF.zOf x = zAt fo ∧
      QK.toLF.planF.fullF.kTg x = kTgAt fo (QK.L.fork x) ∧
      ∀ s, QK.toLF.planF.kIncS x s = kIncAt fo (QK.L.fork x) s :=
  ⟨QK.toPlan4K.zOf_look h, QK.toPlan4K.kTg_look h,
    fun s => congrFun (QK.toPlan4K.kIncS_look h) s⟩

/-- **The first group's value's cells are the Road's**, if the matrices read as 0 outside the
bounds: `Plan4K.cells_eq` (ValueSeat.lean) at this value, by its proof. -/
theorem Plan4KF.cells_eqF (m : Mm)
    (hz : ∀ a b c, ¬ (a < QK.nM ∧ b < QK.nR ∧ c < QK.nC) → QK.mats m a b c = 0) :
    QK.toLF.planF.fullF.rd (QK.toLF.planF.fullF.msg m) =
      cellsOf QK.toLF.planF.fullF.D (cellsAt QK.y (QK.mats m)) := by
  funext q
  show QK.toLF.planF.toPlan4.rd (QK.toLF.planF.toPlan4.msg m) q =
    cellsOf QK.D (cellsAt QK.y (QK.mats m)) q
  rw [cellsOf_addr]
  by_cases h : (addrOf QK.y QK.D q).1 < QK.nM ∧ (addrOf QK.y QK.D q).2.1 < QK.nR ∧
      (addrOf QK.y QK.D q).2.2 < QK.nC
  · have e : QK.toLF.planF.toPlan4.nameOf q = some (⟨_, h.1⟩, ⟨_, h.2.1⟩, ⟨_, h.2.2⟩) :=
      dif_pos h
    exact QK.toLF.planF.toPlan4.rd_valid (QK.toLF.planF.toPlan4.msg m) e
  · have e : QK.toLF.planF.toPlan4.nameOf q = none := dif_neg h
    rw [hz _ _ _ h]
    exact QK.toLF.planF.toPlan4.rd_invalid (QK.toLF.planF.toPlan4.msg m) e

/-- **The matrices' reads are true and their cells are the message's**, from the true reads, if the
value's layout is the place's and the matrices read as 0 outside the bounds. -/
theorem Plan4KF.readsAtF {par : Par} {hS : OnBytes.Model.Layer.Shape} (Sm : Sem Wt)
    (part : Wt → Mm) (hy : QK.y = par.P.y) (s : T) (fo : Forest.Heard) (o : Own) (G : Fork)
    (w : Wt)
    (hz : ∀ a b c, ¬ (a < QK.nM ∧ b < QK.nR ∧ c < QK.nC) → QK.mats (part w) a b c = 0)
    (hR : ∀ (Xp : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape),
      PubAt Xp { par.P with tokv := QK.L.tokv s } par.hp fo o G2 t4 QK.toLF.planF.fullF.D
        QK.toLF.planF.fullF.tb hS →
      ∀ Fl, Fo.Later G Fl →
        Xp.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) (QK.mats (part w))) :
    Plan4LF.ReadsAtF QK.toLF par hS QK.L Sm part s fo o G w (QK.mats (part w)) := by
  refine ⟨hR, ?_⟩
  rw [← hy]
  exact (QK.cells_eqF (part w) hz).symm

end
end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4KF.tok_at
#print axioms OnBytes.Road.K4.Plan4KF.look_atF
#print axioms OnBytes.Road.K4.Plan4KF.cells_eqF
#print axioms OnBytes.Road.K4.Plan4KF.readsAtF
