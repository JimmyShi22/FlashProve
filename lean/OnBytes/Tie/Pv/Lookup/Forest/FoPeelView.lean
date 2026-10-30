-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPeelView.lean.
The plain data of written rounds are the reading of the rounds that a view holds.

OnBytes/Tie/Pv/Lookup/Forest/FoPeelKit.lean reads a written transcript as plain data (`flWs`). The
byte-level routines take
rounds off a view (Fmt.RoundView), and their laws speak of these rounds read in the field (`Fo.rdRV`).
The view of a written transcript has the rounds `PQ.rvSL` (Run/PlanQS.lean). This file says that
the two readings are one list.

Main names.
 * `NoAns l`: no item of the message is an answer to a sample. (The byte-level reading of a round
   takes the plain field elements alone; `flW` takes answers too.)
 * `flWs_view`: (PQ.rvSL (ckP .two) ds τ).map (rdRV Reading.gl) = flWs ds τ.
 * `car_view`: the image of a written transcript, read back, is the view's rounds read in the field.
 * `Rd.one`, `Rd.one_tr`, `Rd.one_fits`: one round as `CarryS.one` (OnBytes/Flat/CarrySApp.lean).

Does not say: that a routine takes these rounds. Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelKit
import OnBytes.Flat.CarrySApp
import OnBytes.Tie.Pv.Lookup.Forest.FoEv

set_option autoImplicit false

namespace Fo.Peel
open Iop Prob Run OnBytes OnBytes.Model OnBytes.Slice OnBytes.Flat OnBytes.PscRun TwV

/-- No item of the message is an answer to a sample. -/
def NoAns (l : List Fmt.Item) : Prop := ∀ it ∈ l, it ≠ Fmt.Item.answer

theorem NoAns.tail {a : Fmt.Item} {l : List Fmt.Item} (h : NoAns (a :: l)) : NoAns l :=
  fun it hi => h it (List.mem_cons_of_mem _ hi)

theorem gots_read : ∀ (l : List Fmt.Item) (x : PQ.PlainOf l), NoAns l →
    ((PQ.PlainOf.gots l x).filterMap eOf).map Reading.gl.val =
      (PQ.PlainOf.gots l x).filterMap fun g =>
        match g with
        | .e x => some (toE x)
        | .answer x => some (toE x)
        | _ => none
  | [], _, _ => rfl
  | .root :: l, x, h => gots_read l x h.tail
  | .f :: l, (x : UInt64 × PQ.PlainOf l), h => gots_read l x.2 h.tail
  | .word :: l, (x : UInt64 × PQ.PlainOf l), h => gots_read l x.2 h.tail
  | .e :: l, (x : Fmt.Ext × PQ.PlainOf l), h => congrArg (toE x.1 :: ·) (gots_read l x.2 h.tail)
  | .answer :: _, _, h => absurd rfl (h _ List.mem_cons_self)

/-- One written round. -/
theorem flW_view (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal) (h : NoAns d.items) :
    rdRV Reading.gl ⟨PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
      (ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ = flW d m c := by
  refine Prod.ext (gots_read d.items _ h) ?_
  show (((rvOf d m c).els.map E.ofTriple).map Reading.gl.val) = elemsV _ (Slice.valsOf d c)
  rw [← rvOf_els d m c, List.map_map]
  rfl

/-- The view's rounds, read in the field, are the written transcript's plain data. -/
theorem flWs_view : ∀ (ds : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) ds)),
    (∀ d ∈ ds, NoAns d.items) → (PQ.rvSL (ckP .two) ds τ).map (rdRV Reading.gl) = flWs ds τ
  | [], _, _ => rfl
  | d :: ds, (m, c, τ), h =>
    congrArg₂ List.cons (flW_view d m c (h d List.mem_cons_self))
      (flWs_view ds τ fun d' hd => h d' (List.mem_cons_of_mem _ hd))

/-- The image of a written transcript, read back, is the view's rounds read in the field. -/
theorem car_view (ds : List PQ.RD) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (hM : List.Forall₂ Meets ds sp) (hA : ∀ d ∈ ds, NoAns d.items) (τ : Tr (PQ.uL (ckP .two) ds))
    (τ' : Tr s') (h : (car ds s' sp R hM.length_eq).tr τ = some τ') :
    outs s' sp R τ' = (PQ.rvSL (ckP .two) ds τ).map (rdRV Reading.gl) :=
  (car_read ds s' sp R hM τ τ' h).1.trans (flWs_view ds τ hA).symm

/-! ### one round -/

/-- One written round read as one typed round. -/
def Rd.one {r' : Round} {s : Tw.RSp} (R : Rd r' s) (d : PQ.RD) : CarryS [wRound d] [r'] :=
  CarryS.one (fun m => R.fm (ansOf d m)) fun _ => chalTo d fun v => R.g (elemsV _ v)

theorem Rd.one_tr {r' : Round} {s : Tw.RSp} (R : Rd r' s) (d : PQ.RD) (m : (wRound d).Msg)
    (c : (wRound d).Chal) : (R.one d).tr (m, c, ()) =
      if GChal.pass (b := d.entry.work) c = true then
        some (R.fm (flW d m c).1, R.g (flW d m c).2, ()) else none := by
  unfold Rd.one
  rw [CarryS.tr_one]
  unfold chalTo
  cases GChal.pass (b := d.entry.work) c <;> rfl

theorem Rd.one_fits {r' : Round} {s : Tw.RSp} (R : Rd r' s) {d : PQ.RD} (h : Meets d s) (e e' : ℕ)
    (he : e * (bsRound .two d.entry d.kind).w ≤ e') :
    (R.one d).Fits (s' := [r']) (e, ()) (e', ()) :=
  CarryS.fits_one _ _ _ e e' (fun _ c' => chalTo_fib d _ (R.vals_inj h) h.sd.logN c') he

end Fo.Peel
