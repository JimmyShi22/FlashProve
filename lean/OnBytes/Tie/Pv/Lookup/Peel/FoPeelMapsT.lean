-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Peel/FoPeelMapsT.lean.
The maps of OnBytes/Tie/Pv/Lookup/Forest/FoPeelKitT.lean are maps of the general make
(OnBytes/Flat/CarrySMaps.lean).

OnBytes/Flat/CarrySMaps.lean lays the maps from a stretch of a file's written rounds to a list of
typed rounds for all chains of a file: `RMap d r'`, `Maps ds s'`, `Maps.carry`, with the image, the
counts and the counts as shares. OnBytes/Tie/Pv/Lookup/Forest/FoPeelKit.lean has readers of typed
rounds from plain data
(`Rd`, `Rds`), OnBytes/Tie/Pv/Lookup/Forest/FoPeelKitT.lean a carry `carT` made of them. This file
says that `carT` is
`Maps.carry` of maps made of the readers, so that all that is proved of `Maps` holds of it.

Main names.
 * `Rd.rmapT R d`: a reader as an `RMap`; `Rd.rmapT_ok`: it is as asked where d meets the spec.
 * `mapsT ds s' sp R h : Maps ds s'`: steps alone. `carT_eq`: carT ds s' sp R h is its carry.
 * `mapsT_ok`, `mapsT_view` (the image is `img` of the plain data), `mapsT_pass` (its tests of work
   are `passT`), `mapsT_bears` (`Maps.err` meets `BearsT`, with equality).
 * `mapsT_read`: the image, read back, is the written transcript's plain data.

Does not say: anything on a verifier. Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelKitT
import OnBytes.Flat.CarrySMaps

set_option autoImplicit false

namespace Fo.Peel
open Iop Prob Run OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker TwV

/-- A reader as a map of one round. -/
def Rd.rmapT {r' : Round} {s : Tw.RSp} (R : Rd r' s) (d : RDT) : RMap d r' :=
  ⟨fun m => R.fm (ansOf (toRD d) (msgRD d m)), fun v => R.g (elemsV _ v)⟩

theorem Rd.rmapT_ok {r' : Round} {s : Tw.RSp} (R : Rd r' s) {d : RDT} (h : MeetsT d s) :
    (R.rmapT d).OK := ⟨R.vals_inj h, h.sd.logN⟩

/-- The readers of a typed shape as maps from the written rounds ds. -/
def mapsT : (ds : List RDT) → (s' : Shape) → (sp : List Tw.RSp) → Rds s' sp →
    ds.length = sp.length → Maps ds s'
  | [], [], [], _, _ => .nil
  | d :: ds, _ :: s', _ :: sp, R, h => .step (R.1.rmapT d) (mapsT ds s' sp R.2 (Nat.succ.inj h))
  | [], _ :: _, _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], [], _, h => absurd h (by simp)
  | _, [], _ :: _, R, _ => nomatch R
  | _, _ :: _, [], R, _ => nomatch R

/-- The kit's carry is the general make's. -/
theorem carT_eq : ∀ (ds : List RDT) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (h : ds.length = sp.length), carT ds s' sp R h = (mapsT ds s' sp R h).carry
  | [], [], [], _, _ => rfl
  | d :: ds, _ :: s', _ :: sp, R, h => by
    show CarryS.step (r := wT d) _ _ (fun _ _ => carT ds s' sp R.2 (Nat.succ.inj h)) =
      CarryS.step (r := wT d) _ _ (fun _ _ => (mapsT ds s' sp R.2 (Nat.succ.inj h)).carry)
    rw [carT_eq ds s' sp R.2 (Nat.succ.inj h)]
    rfl
  | [], _ :: _, _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], [], _, h => absurd h (by simp)
  | _, [], _ :: _, R, _ => nomatch R
  | _, _ :: _, [], R, _ => nomatch R

theorem mapsT_ok : ∀ (ds : List RDT) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (hM : List.Forall₂ MeetsT ds sp), (mapsT ds s' sp R hM.length_eq).OK
  | [], [], [], _, _ => trivial
  | _ :: ds, _ :: s', _ :: sp, R, .cons h1 h2 => ⟨R.1.rmapT_ok h1, mapsT_ok ds s' sp R.2 h2⟩
  | _, [], _ :: _, R, _ => nomatch R
  | _, _ :: _, [], R, _ => nomatch R

theorem mapsT_view : ∀ (ds : List RDT) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (h : ds.length = sp.length) (τ : Tr (uLT (ckP .two) ds)),
    (mapsT ds s' sp R h).view τ = img s' sp R (flWsT ds τ)
  | [], [], [], _, _, _ => rfl
  | d :: ds, _ :: s', _ :: sp, R, h, (m, c, τ) => by
    show (R.1.fm (ansOf (toRD d) (msgRD d m)), R.1.g (elemsV _ (OnBytes.Slice.valsOf (toRD d) c)),
      (mapsT ds s' sp R.2 (Nat.succ.inj h)).view τ) = (R.1.fm (ansOf (toRD d) (msgRD d m)),
        R.1.g (elemsV _ (OnBytes.Slice.valsOf (toRD d) c)), img s' sp R.2 (flWsT ds τ))
    rw [mapsT_view ds s' sp R.2 (Nat.succ.inj h) τ]
  | [], _ :: _, _ :: _, _, h, _ => absurd h (by simp)
  | _ :: _, [], [], _, h, _ => absurd h (by simp)
  | _, [], _ :: _, R, _, _ => nomatch R
  | _, _ :: _, [], R, _, _ => nomatch R

theorem mapsT_pass : ∀ (ds : List RDT) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (h : ds.length = sp.length) (τ : Tr (uLT (ckP .two) ds)),
    (mapsT ds s' sp R h).pass τ = passT (ckP .two) ds (Maker.rhoT (ckP .two) ds τ)
  | [], [], [], _, _, _ => rfl
  | d :: ds, _ :: s', _ :: sp, R, h, (_, c, τ) =>
    congrArg (GChal.pass (b := d.entry.work) c && ·) (mapsT_pass ds s' sp R.2 (Nat.succ.inj h) τ)
  | [], _ :: _, _ :: _, _, h, _ => absurd h (by simp)
  | _ :: _, [], [], _, h, _ => absurd h (by simp)
  | _, [], _ :: _, R, _, _ => nomatch R
  | _, _ :: _, [], R, _, _ => nomatch R

theorem mapsT_bears : ∀ (ds : List RDT) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (h : ds.length = sp.length) (ε : Err s'), BearsT ds s' ε ((mapsT ds s' sp R h).err ε)
  | [], [], [], _, _, _ => trivial
  | _ :: ds, _ :: s', _ :: sp, R, h, (_, ε) =>
    ⟨le_rfl, mapsT_bears ds s' sp R.2 (Nat.succ.inj h) ε⟩
  | [], _ :: _, _ :: _, _, h, _ => absurd h (by simp)
  | _ :: _, [], [], _, h, _ => absurd h (by simp)
  | _, [], _ :: _, R, _, _ => nomatch R
  | _, _ :: _, [], R, _, _ => nomatch R

/-- The image, read back, is the written transcript's plain data. -/
theorem mapsT_read (ds : List RDT) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (hM : List.Forall₂ MeetsT ds sp) (τ : Tr (uLT (ckP .two) ds)) :
    outs s' sp R ((mapsT ds s' sp R hM.length_eq).view τ) = flWsT ds τ := by
  rw [mapsT_view]
  exact outs_img s' sp R _ (flWsT_fit ds sp hM τ)

end Fo.Peel
