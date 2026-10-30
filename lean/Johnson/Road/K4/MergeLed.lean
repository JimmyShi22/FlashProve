-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MergeLed.lean: THE MERGE's PART OF THE LIBRARY's LEDGER AT A HEARING. Under the
record `Led7` of a hearing in a group that is not the first (Johnson/Road/K4/OwnLedgers.lean), at
the chain's data read off the hearing's tape with the states `addsOf`: the form that K4's run "back"
makes as the merge's own claim (`ownClaim o.wo.p o.wo.fvp {}`, OnBytes/Desc/First/K4/Plain.lean:
`o.wo.p.rowForm o.wo.fvp {}`) is worth 0 exactly if the ledger `mergeLed`
(Cb/Pv/Lay/End/MergeShare.lean) holds at the output that stands in the chain's last statement. One
statement and its proof.

NO NEW ARGUMENT: `merge_row_stg` (OwnRowsStage.lean) at `Led7.c7` with `fits7` (StageFitsRest.lean);
`ledOf_holds`.

Limits. All letters are the caller's. PREMISES: `Led7`; hk; g7.t7 is the record's target; hnum;
(D1), (D2) at the state `aS7` in the world W. A group that is not the first. One world: no draw.
Nothing on the pending row (PendingLed.lean). Nothing on soundness.
-/
import Johnson.Road.K4.OwnRowsStage
import Johnson.Road.K4.StageOuts
import Cb.Pv.Lay.End.MergeShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Fork Forest.Heard Level Tsc World)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aS7 addsOf)
open Inst.Model (Scl)

variable [scl : Scl] {M Xs : Type} (P : FullPar Cb.Gl.E M Xs) {R : TailR}
  (W : TailM P.own.toOwn.tail R) {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork} {J₂ : Type} [Fintype J₂]

/-- **The merge's own claim is worth 0 exactly if the merge's part of the ledger holds.** -/
theorem merge_of_led (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (hk : P.own.toOwn.tail.s7.L.S.k = Pp.wsLay.lk)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) (ht7 : g7.t7 = o.wo.p.target)
    (hnum : W.w7.num () = 0) (Ex : ExtSpec) (y : Ex.Str) (Wd : World Cb.Gl.E)
    (m : P.wp0.J → Cb.Gl.E) (w : J₂ → Cb.Gl.E)
    (D1 : P.wp0.wt.L.toSum.T.par.W (aS7 W (ksOf Pp hp) (t0.drop 1) nz x g7) m =
      OnBytes.Road.Hd.place Wd.slot
        (P.wp0.wt.L.toSum.T.par.vars (aS7 W (ksOf Pp hp) (t0.drop 1) nz x g7)) o.wo.p.first)
    (D2 : P.wp0.wt.L.toSum.T.par.inc (aS7 W (ksOf Pp hp) (t0.drop 1) nz x g7) m =
      gl.val o.wo.p.target - o.wo.p.start.value gl Wd) :
    (o.wo.p.rowForm o.wo.fvp {}).value gl Wd = 0 ↔
      TWhole.Ledger.Holds
        (mergeLed (J₂ := J₂) P.wp0
          ((k4Tail W Pp hp t0 nz (addsOf W (ksOf Pp hp) (t0.drop 1) nz x g7)).z7 x).2)
        (Sum.elim m w) := by
  obtain ⟨cl, c7⟩ := Ld.c7
  have key := merge_row_stg (J₂ := J₂) W.w7.num c7 Ld.sG4 nz.b7
    (aS7 W (ksOf Pp hp) (t0.drop 1) nz x g7) g7.t7 rfl ht7 (fits7 P _ Pp.wsLay.lk hk)
    P.wp0.wt.L.pick_ok Ex y Wd m D1 D2
    (fun _ _ => Finset.sum_eq_zero fun b _ => (show Empty from b).elim) () hnum
    (fun z vals => by
      show ([(1 : Cb.Gl.E) * [vals ()].prod]).sum = _
      simp)
    (fun _ b => Empty.elim b) (fun _ _ b _ => Empty.elim b) w
  unfold mergeLed
  rw [ledOf_holds]
  exact key.trans ⟨fun h f hf => by rw [List.mem_singleton.1 hf]; exact h,
    fun h => h _ List.mem_cons_self⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.merge_of_led
