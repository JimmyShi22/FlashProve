-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/CarrySMaps.lean: the maps from a stretch of written rounds to a list of typed rounds,
given round by round, with their image, their counts, and the counts as shares.

A stretch of a file's chain is a list ds of written rounds (`uLT (ckP .two) ds`,
OnBytes/Maker/Trees.lean: a round may send the roots of several trees; OnBytes/Flat/RoundsT.lean).
A typed block has a list of rounds of its own. `Maps ds s'` says round by round how the first is
read as the second: a written round is read as the next typed round (`step`), or the typed list
lacks it (`skip`). From it come a `CarryS` (OnBytes/Flat/CarrySkip.lean) and all that a reading of a
whole file asks of it: what the image of a transcript is and when there is one; that the written
counts bear the typed ones; that the written counts are small as shares. So whoever lays a kind of
block gives, for each of its rounds, a map of prover messages and a map of typed values, and shows
that the second is one-to-one.

Main names:
  `RMap d r'`: fm, the map of prover messages; g, the map from the typed values that the format's
    sampler makes of the written verifier message. `RMap.OK`: g is one-to-one; the round's positions
    have at most 64 bits.
  `Maps ds s'`: `nil`, `step M rest`, `skip d rest`. `Maps.app`; `Maps.all`: one typed round r', as
    often as ds is long.
  `Maps.carry`: the `CarryS`. `Maps.view`: the image.
  `tr_of_pass`: where all tests of work of the stretch's read rounds pass (`Maps.pass`), the image
    is `view`; `tr_none`: else there is none.
  `Maps.err`: the written counts: at a step e · w, w the sampler's bound; at a skipped round 0.
  `Maps.fits`: they bear the typed counts (`CarryS.Fits`).
  `Maps.Held εs`, `Maps.below_err`: if at each step the typed count is a share of at most c of the
    round's typed values and (1 + 2^-128)^b · c / 2^work ≤ εs, the written counts are shares of at
    most εs: THE WORK IS COUNTED.

Limits: fm and g read their own round alone, and no statement: maps that read more are laid by
`CarryS.step` itself and joined by `CarryS.app` (OnBytes/Flat/CarrySApp.lean). A test of work in a
skipped round is not looked at. No protocol occurs here.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.CarrySkip
import OnBytes.Flat.RoundsT
import OnBytes.Slice.Rates

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob Run OnBytes.Maker OnBytes.Slice
open scoped ENNReal

/-- How one written round is read as one typed round. -/
structure RMap (d : RDT) (r' : Round) where
  /-- the prover's message -/
  fm : (wT d).Msg → r'.Msg
  /-- the typed values of the verifier's message -/
  g : Vals .two (Fmt.dsOf d.entry d.kind) → r'.Chal

/-- What is asked of it. -/
structure RMap.OK {d : RDT} {r' : Round} (M : RMap d r') : Prop where
  inj : Function.Injective M.g
  log : d.entry.logN ≤ 64

/-- How a stretch of written rounds is read as a list of typed rounds. -/
inductive Maps : List RDT → Shape → Type 1
  | nil : Maps [] []
  | step {d : RDT} {r' : Round} {ds : List RDT} {s' : Shape} (M : RMap d r')
      (rest : Maps ds s') : Maps (d :: ds) (r' :: s')
  | skip (d : RDT) {ds : List RDT} {s' : Shape} (rest : Maps ds s') : Maps (d :: ds) s'

namespace Maps

/-- Two stretches behind each other. -/
def app : {ds es : List RDT} → {s' t' : Shape} → Maps ds s' → Maps es t' →
    Maps (ds ++ es) (s' ++ t')
  | _, _, _, _, .nil, N => N
  | _, _, _, _, .step M rest, N => .step M (rest.app N)
  | _, _, _, _, .skip d rest, N => .skip d (rest.app N)

/-- Every written round is read as the typed round r'. -/
def all {r' : Round} (f : ∀ d : RDT, RMap d r') :
    (ds : List RDT) → Maps ds (List.replicate ds.length r')
  | [] => .nil
  | d :: ds => .step (f d) (all f ds)

/-- All rounds are skipped. -/
def skips : (ds : List RDT) → Maps ds []
  | [] => .nil
  | d :: ds => .skip d (skips ds)

/-- The maps as a `CarryS`. -/
def carry : {ds : List RDT} → {s' : Shape} → Maps ds s' → CarryS (uLT (ckP .two) ds) s'
  | _, _, .nil => .nil
  | _, _, .step (d := d) M rest => .step M.fm (fun _ => chalTo (toRD d) M.g) fun _ _ => rest.carry
  | _, _, .skip _ rest => .skip fun _ _ => rest.carry

/-- The image of a written transcript. -/
def view : {ds : List RDT} → {s' : Shape} → Maps ds s' → Tr (uLT (ckP .two) ds) → Tr s'
  | _, _, .nil, _ => ()
  | _, _, .step (d := d) M rest, (m, c, τ) => (M.fm m, M.g (valsOf (toRD d) c), rest.view τ)
  | _, _, .skip _ rest, (_, _, τ) => rest.view τ

/-- All tests of work of the rounds that are read pass. -/
def pass : {ds : List RDT} → {s' : Shape} → Maps ds s' → Tr (uLT (ckP .two) ds) → Bool
  | _, _, .nil, _ => true
  | _, _, .step (d := d) _ rest, (_, c, τ) => GChal.pass (b := d.entry.work) c && rest.pass τ
  | _, _, .skip _ rest, (_, _, τ) => rest.pass τ

/-- Where they pass, the image is `view`. -/
theorem tr_of_pass : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s')
    (τ : Tr (uLT (ckP .two) ds)), M.pass τ = true → M.carry.tr τ = some (M.view τ)
  | _, _, .nil, _, _ => rfl
  | _, _, .step (d := d) M rest, (m, c, τ), h => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
      show (chalTo (toRD d) M.g c).bind
        (fun c' => (rest.carry.tr τ).map fun τ' => (M.fm m, c', τ')) = _
      unfold chalTo
      rw [if_pos h1, tr_of_pass rest τ h2]
      rfl
  | _, _, .skip _ rest, (_, _, τ), h => tr_of_pass rest τ h

/-- Where one fails there is no image. -/
theorem tr_none : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s')
    (τ : Tr (uLT (ckP .two) ds)), M.pass τ = false → M.carry.tr τ = none
  | _, _, .nil, _, h => nomatch h
  | _, _, .step (d := d) M rest, (m, c, τ), h => by
      show (chalTo (toRD d) M.g c).bind
        (fun c' => (rest.carry.tr τ).map fun τ' => (M.fm m, c', τ')) = _
      unfold chalTo
      cases h1 : GChal.pass (b := d.entry.work) c with
      | false => rfl
      | true =>
        have h2 : rest.pass τ = false := by
          have h' : (GChal.pass (b := d.entry.work) c && rest.pass τ) = false := h
          rw [h1, Bool.true_and] at h'
          exact h'
        rw [if_pos rfl, tr_none rest τ h2]
        rfl
  | _, _, .skip _ rest, (_, _, τ), h => tr_none rest τ h

/-- Every step's map is as asked. -/
def OK : {ds : List RDT} → {s' : Shape} → Maps ds s' → Prop
  | _, _, .nil => True
  | _, _, .step M rest => M.OK ∧ rest.OK
  | _, _, .skip _ rest => rest.OK

/-- The written counts. -/
def err : {ds : List RDT} → {s' : Shape} → Maps ds s' → Err s' → Err (uLT (ckP .two) ds)
  | _, _, .nil, _ => ()
  | _, _, .step (d := d) _ rest, (e, ε) => (e * (bsRound .two d.entry d.kind).w, rest.err ε)
  | _, _, .skip _ rest, ε => (0, rest.err ε)

/-- The written counts bear the typed ones. -/
theorem fits : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s'), M.OK → ∀ ε : Err s',
    M.carry.Fits ε (M.err ε)
  | _, _, .nil, _, _ => trivial
  | _, _, .step (d := d) M rest, h, (_, ε) =>
      ⟨⟨(bsRound .two d.entry d.kind).w,
          fun _ c' => chalTo_fib (toRD d) M.g h.1.inj h.1.log c', le_rfl⟩,
        fun _ _ => fits rest h.2 ε⟩
  | _, _, .skip _ rest, h, ε => fun _ _ => fits rest h ε

/-- At each step the typed count is a share of at most c of the round's typed values, and c, with
the sampler's bias and the gain from the test bits, is at most εs. -/
def Held (εs : ℝ≥0∞) : {ds : List RDT} → {s' : Shape} → Maps ds s' → Err s' → Prop
  | _, _, .nil, _ => True
  | _, _, .step (d := d) _ rest, (e, ε) =>
      (∃ c : ℝ≥0∞, (e : ℝ≥0∞) ≤ c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞) ∧
        kapSl 128 ^ (bsRound .two d.entry d.kind).b * (c / 2 ^ d.entry.work) ≤ εs) ∧
      rest.Held εs ε
  | _, _, .skip _ rest, ε => rest.Held εs ε

/-- Then the written counts are shares of at most εs. -/
theorem below_err {εs : ℝ≥0∞} : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s'), M.OK →
    ∀ ε : Err s', M.Held εs ε → Err.Below (M.err ε) εs
  | _, _, .nil, _, _, _ => trivial
  | _, _, .step (d := d) _ rest, h, (e, ε), hh => by
      obtain ⟨⟨c, h1, h2⟩, h3⟩ := hh
      exact ⟨(below_round_div (toRD d) h.1.log e c h1).trans (mul_le_mul' h2 le_rfl),
        below_err rest h.2 ε h3⟩
  | _, _, .skip _ rest, h, ε, hh =>
      ⟨by rw [Nat.cast_zero]; exact zero_le _, below_err rest h ε hh⟩

theorem OK.app : ∀ {ds es : List RDT} {s' t' : Shape} {M : Maps ds s'} {N : Maps es t'},
    M.OK → N.OK → (M.app N).OK
  | _, _, _, _, .nil, _, _, hN => hN
  | _, _, _, _, .step _ rest, _, hM, hN => ⟨hM.1, OK.app (M := rest) hM.2 hN⟩
  | _, _, _, _, .skip _ rest, _, hM, hN => OK.app (M := rest) hM hN

theorem Held.app {εs : ℝ≥0∞} : ∀ {ds es : List RDT} {s' t' : Shape} {M : Maps ds s'}
    {N : Maps es t'} {ε : Err s'} {δ : Err t'}, M.Held εs ε → N.Held εs δ →
    (M.app N).Held εs (Err.app ε δ)
  | _, _, _, _, .nil, _, _, _, _, hN => hN
  | _, _, _, _, .step _ rest, _, (_, _), _, hM, hN => ⟨hM.1, Held.app (M := rest) hM.2 hN⟩
  | _, _, _, _, .skip _ rest, _, _, _, hM, hN => Held.app (M := rest) hM hN

theorem ok_all {r' : Round} (f : ∀ d : RDT, RMap d r') :
    ∀ ds : List RDT, (∀ d ∈ ds, (f d).OK) → (all f ds).OK
  | [], _ => trivial
  | d :: ds, h =>
      ⟨h d List.mem_cons_self, ok_all f ds fun d' hd' => h d' (List.mem_cons_of_mem _ hd')⟩

theorem ok_skips : ∀ ds : List RDT, (skips ds).OK
  | [] => trivial
  | _ :: ds => ok_skips ds

theorem held_skips (εs : ℝ≥0∞) : ∀ ds : List RDT, (skips ds).Held εs ()
  | [] => trivial
  | _ :: ds => held_skips εs ds

end Maps

end OnBytes.Flat

#print axioms OnBytes.Flat.Maps.tr_of_pass
#print axioms OnBytes.Flat.Maps.tr_none
#print axioms OnBytes.Flat.Maps.fits
#print axioms OnBytes.Flat.Maps.below_err
#print axioms OnBytes.Flat.Maps.OK.app
#print axioms OnBytes.Flat.Maps.Held.app
#print axioms OnBytes.Flat.Maps.ok_all
