-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PendingLed.lean: THE PENDING ROW AT A HEARING. Under the record `Led7` of a hearing
of the layers' own rounds in a group that is not the first (Johnson/Road/K4/OwnLedgers.lean), at the
chain's data read off the hearing's tape with the states `addsOf`
(OnBytes/Desc/First/P1/TailAdds.lean): what the chain's end asks of its last statement beside the
ledger (`OkMore`, Cb/Pv/Lay/End/LayHEndAt.lean) holds exactly if the named sentence `WoSays`
(OwnPending.lean) holds of the hearing's own merge record o.wo, at the seventh state `aS7`. One
statement and its proof.

  `pending_of_led`: `OkMore P (fun _ _ => True) ((k4Tail W Pp hp t0 nz (addsOf W (ksOf Pp hp)
    (t0.drop 1) nz x g7)).z7 x) m ↔ WoSays P (aS7 W (ksOf Pp hp) (t0.drop 1) nz x g7) o.wo m`.

NO NEW ARGUMENT: `k4_pending` (OwnPending.lean) at `Led7.c7`; `out7` (StageOuts.lean) for `OutIs` at
the seventh stage; `merge_shown` (MergeShown.lean) with `Led7.sG4` for the shown value.

Limits. All letters are the caller's: nothing stands under "there are". PREMISES: `Led7`; hk (the
typed merge has as many variables as the program's); n7 (the seventh stage has no further scalar);
g7.t7 is the merge's record's target; hnum (the one end value's number is 0). THE STATE `aS7` IS
TYPED: that the row weights at it are what `o.wo.recs` spells is not said. A group that is not the
first. Nothing on soundness.
-/
import Johnson.Road.K4.StageOuts
import Johnson.Road.K4.OwnPending
import Johnson.Road.K4.MergeShown

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Fork Forest.Heard Level Tsc)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aS7 addsOf pscT)
open Inst.Model (Scl)

variable [scl : Scl] {M Xs : Type} (P : FullPar Cb.Gl.E M Xs) {R : TailR}
  (W : TailM P.own.toOwn.tail R) {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- **The pending row at a hearing is the named sentence of the hearing's own merge record.** -/
theorem pending_of_led (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (hk : P.own.toOwn.tail.s7.L.S.k = Pp.wsLay.lk) (n7 : P.own.toOwn.tail.s7.n = 0)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) (ht7 : g7.t7 = o.wo.p.target)
    (hnum : W.w7.num () = 0) (m : M) :
    OkMore P (fun _ _ => True)
        ((k4Tail W Pp hp t0 nz (addsOf W (ksOf Pp hp) (t0.drop 1) nz x g7)).z7 x) m ↔
      WoSays P (aS7 W (ksOf Pp hp) (t0.drop 1) nz x g7) o.wo m := by
  obtain ⟨cl, h7⟩ := Ld.c7
  have O7 := out7 P W Ld hk nz x g7 ht7
  have hfv : (k4Tail W Pp hp t0 nz (addsOf W (ksOf Pp hp) (t0.drop 1) nz x g7)).d7.v () =
      gl.val o.wo.fvp := by
    rw [merge_shown Ld.sG4 h7]
    show gl.val ((pscT _ _ (((ksOf Pp hp).tcW (t0.drop 1)).drop 1)).v.getD (W.w7.num ()) _) = _
    rw [hnum]
    rfl
  exact k4_pending P W h7 n7 nz (addsOf W (ksOf Pp hp) (t0.drop 1) nz x g7) x O7 hfv m

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pending_of_led
