-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPeelKitT.lean.
The maps of OnBytes/Tie/Pv/Lookup/Forest/FoPeelKit.lean over the rounds of a file, where a round may
send several trees.

A file's chains have the rounds `uLT (ckP .two) ds`, ds : List RDT (OnBytes/Maker/Trees.lean).
OnBytes/Tie/Pv/Lookup/Forest/FoPeelKit.lean and OnBytes/Tie/Pv/Lookup/Forest/FoPeelView.lean speak
of `PQ.uL (ckP .two) ds`, ds : List PQ.RD. The two kinds of
round have the same plain messages and the same verifier's messages; their oracles differ. The maps
here read no oracle, so this file says the written side again over RDT, through `toRD`, `wT` and
`msgRD` of OnBytes/Flat/RoundsT.lean. The readers (`Rd`, `Rds`, `outs`, `img`) are
OnBytes/Tie/Pv/Lookup/Forest/FoPeelKit.lean's,
unturned.

Main names.
 * `flWsT ds τ`: a written transcript as plain data. `carT ds s' sp R h`: the maps.
 * `carT_tr`, `carT_read`, `carT_none`, `BearsT`, `carT_fits`: as `car_tr` .. `car_fits`; the tests
   of work are `passT`; the premise on the rounds is List.Forall₂ MeetsT ds sp, where
   `MeetsT d s` is Meets (toRD d) s.
 * `flWsT_view`, `carT_view`: the plain data are the view's rounds `rvT (ckP .two) ds τ`, read in
   the field.

Does not say: which rounds a given file has; anything on a verifier.
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelView
import OnBytes.Flat.RoundsT

set_option autoImplicit false

namespace Fo.Peel
open Iop Prob Run OnBytes OnBytes.Model OnBytes.Slice OnBytes.Flat OnBytes.Maker TwV

/-- The written round d meets the spec s. -/
abbrev MeetsT (d : RDT) (s : Tw.RSp) : Prop := Meets (toRD d) s

/-- A written transcript as plain data. -/
def flWsT : (ds : List RDT) → Tr (uLT (ckP .two) ds) → Rounds GE
  | [], _ => []
  | d :: ds, (m, c, τ) => flW (toRD d) (msgRD d m) c :: flWsT ds τ

/-- The maps from the written rounds ds to the typed shape. -/
def carT : (ds : List RDT) → (s' : Shape) → (sp : List Tw.RSp) → Rds s' sp →
    ds.length = sp.length → CarryS (uLT (ckP .two) ds) s'
  | [], [], [], _, _ => .nil
  | d :: ds, _ :: s', _ :: sp, R, h =>
    .step (r := wT d) (fun m => R.1.fm (ansOf (toRD d) (msgRD d m)))
      (fun _ c => chalTo (toRD d) (fun v => R.1.g (elemsV _ v)) c)
      fun _ _ => carT ds s' sp R.2 (Nat.succ.inj h)
  | [], _ :: _, _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], [], _, h => absurd h (by simp)
  | _, [], _ :: _, R, _ => nomatch R
  | _, _ :: _, [], R, _ => nomatch R

/-- A written transcript has an image if and only if every round's test of work passes; the image
is made of its plain data. -/
theorem carT_tr : ∀ (ds : List RDT) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (h : ds.length = sp.length) (τ : Tr (uLT (ckP .two) ds)), (carT ds s' sp R h).tr τ =
      if passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true then
        some (img s' sp R (flWsT ds τ)) else none
  | [], [], [], _, _, _ => rfl
  | d :: ds, _ :: s', _ :: sp, R, h, (m, c, τ) => by
    show (chalTo (toRD d) (fun v => R.1.g (elemsV _ v)) c).bind (fun c' =>
      ((carT ds s' sp R.2 (Nat.succ.inj h)).tr τ).map fun τ' =>
        (R.1.fm (ansOf (toRD d) (msgRD d m)), c', τ')) = _
    rw [carT_tr ds s' sp R.2 (Nat.succ.inj h) τ]
    show _ = if (GChal.pass (b := d.entry.work) c &&
        passT (ckP .two) ds (rhoT (ckP .two) ds τ)) = true then
      some (R.1.fm (ansOf (toRD d) (msgRD d m)), R.1.g (elemsV _ (Slice.valsOf (toRD d) c)),
        img s' sp R.2 (flWsT ds τ)) else none
    unfold chalTo
    show (if GChal.pass (b := d.entry.work) c = true then _ else none : Option _).bind _ = _
    cases GChal.pass (b := d.entry.work) c <;>
      cases passT (ckP .two) ds (rhoT (ckP .two) ds τ) <;> rfl
  | [], _ :: _, _ :: _, _, h, _ => absurd h (by simp)
  | _ :: _, [], [], _, h, _ => absurd h (by simp)
  | _, [], _ :: _, R, _, _ => nomatch R
  | _, _ :: _, [], R, _, _ => nomatch R

theorem flWsT_fit : ∀ (ds : List RDT) (sp : List Tw.RSp), List.Forall₂ MeetsT ds sp →
    ∀ τ : Tr (uLT (ckP .two) ds), List.Forall₂ Tw.RFit sp (flWsT ds τ)
  | [], [], .nil, _ => .nil
  | d :: ds, _ :: sp, .cons h1 h2, (m, c, τ) =>
    .cons (flW_fit h1 (msgRD d m) c) (flWsT_fit ds sp h2 τ)

/-- The image, read back, is the written transcript's plain data; these fit the spec; every test of
work has passed. -/
theorem carT_read (ds : List RDT) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (hM : List.Forall₂ MeetsT ds sp) (τ : Tr (uLT (ckP .two) ds)) (τ' : Tr s')
    (h : (carT ds s' sp R hM.length_eq).tr τ = some τ') :
    outs s' sp R τ' = flWsT ds τ ∧ List.Forall₂ Tw.RFit sp (flWsT ds τ) ∧
      passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true := by
  rw [carT_tr] at h
  split at h
  · next hp =>
    obtain rfl := Option.some.inj h
    exact ⟨outs_img s' sp R _ (flWsT_fit ds sp hM τ), flWsT_fit ds sp hM τ, hp⟩
  · cases h

/-- A written transcript without an image has failed a test of work. -/
theorem carT_none (ds : List RDT) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (h : ds.length = sp.length) (τ : Tr (uLT (ckP .two) ds))
    (h0 : (carT ds s' sp R h).tr τ = none) :
    passT (ckP .two) ds (rhoT (ckP .two) ds τ) = false := by
  rw [carT_tr] at h0
  split at h0
  · cases h0
  · next hp => exact Bool.eq_false_iff.2 hp

/-- Each written count is at least the typed count times the sampler's bound of its round. -/
def BearsT : (ds : List RDT) → (s' : Shape) → Err s' → Err (uLT (ckP .two) ds) → Prop
  | [], [], _, _ => True
  | d :: ds, _ :: s', ε, ε' =>
    ε.1 * (bsRound .two d.entry d.kind).w ≤ ε'.1 ∧ BearsT ds s' ε.2 ε'.2
  | [], _ :: _, _, _ => True
  | _ :: _, [], _, _ => True

theorem carT_fits : ∀ (ds : List RDT) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (hM : List.Forall₂ MeetsT ds sp) (ε : Err s') (ε' : Err (uLT (ckP .two) ds)),
    BearsT ds s' ε ε' → (carT ds s' sp R hM.length_eq).Fits ε ε'
  | [], [], [], _, _, _, _, _ => trivial
  | d :: ds, _ :: s', _ :: sp, R, .cons h1 h2, ε, ε', hB =>
    ⟨⟨_, fun _ c' => chalTo_fib (toRD d) _ (R.1.vals_inj h1) h1.sd.logN c', hB.1⟩,
      fun _ _ => carT_fits ds s' sp R.2 h2 ε.2 ε'.2 hB.2⟩
  | _, [], _ :: _, R, _, _, _, _ => nomatch R
  | _, _ :: _, [], R, _, _, _, _ => nomatch R

/-- The view's rounds, read in the field, are the written transcript's plain data. -/
theorem flWsT_view : ∀ (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)),
    (∀ d ∈ ds, NoAns d.items) → (rvT (ckP .two) ds τ).map (rdRV Reading.gl) = flWsT ds τ
  | [], _, _ => rfl
  | d :: ds, (m, c, τ), h =>
    congrArg₂ List.cons (flW_view (toRD d) (msgRD d m) c (h d List.mem_cons_self))
      (flWsT_view ds τ fun d' hd => h d' (List.mem_cons_of_mem _ hd))

/-- The image of a written transcript, read back, is the view's rounds read in the field. -/
theorem carT_view (ds : List RDT) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (hM : List.Forall₂ MeetsT ds sp) (hA : ∀ d ∈ ds, NoAns d.items) (τ : Tr (uLT (ckP .two) ds))
    (τ' : Tr s') (h : (carT ds s' sp R hM.length_eq).tr τ = some τ') :
    outs s' sp R τ' = (rvT (ckP .two) ds τ).map (rdRV Reading.gl) :=
  (carT_read ds s' sp R hM τ τ' h).1.trans (flWsT_view ds τ hA).symm

end Fo.Peel
