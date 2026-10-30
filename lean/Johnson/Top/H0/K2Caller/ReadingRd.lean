-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/ReadingRd.lean: the seven readings of the code switch's two written rounds
(`Rd`, Johnson/Top/H/LocPlace.lean), written out at the caller of Row.lean, so that the work is
counted: the place's map `Rd.carS` at them bears the typed block's errors at the written counts of
Reading.lean, which are shares of at most 2⁻¹ ^ target.

A written verifier's message is a string of hash blocks and, where the round has work, of test bits
(`GChal`, Iop/Grind.lean). What the verifier is shown of a round (`rvOne`,
OnBytes/Tie/Pv/Row/ViewT.lean) is made of the blocks alone, and `Rd.carS` reads a record of draws
(`Fmt.Drawn`), which has no mark of the test bits. At the bare views each typed value would have
2 ^ work times as many written messages over it. So here a view is what the verifier is shown where
the round's test of work passes; where it fails, the items are kept and the record of draws is a
void one, at which the readings say "none". Definitions, and theorems with their proofs.

Main names:
  `seedOfD c D`: c coordinates, in their order, and then the factor, off the elements of a record of
    draws; "none" unless it has just c + 1 elements. `posOfD a t D`: t positions below 2 ^ a off its
    positions; "none" unless it has just t.
  `shownW d void m c`: the view with the test of work. `shownW_pass`: where the test passes it is
    `rvOne d m c`.
  `seed_read`, `pos_read`: the readings at these views are the library's `chalTo` at `gSeed` and
    `gPos`.
  `rdOf X d₁ d₂ ρ`: the seven readings. The members' words and the rider's word stay the two
    letters of Reading.lean (`WordsOf`).
  `elems_len`, `poss_len`: what the verifier is shown of the two rounds has just the seed's
    elements, and just the plan's number of positions: so there the readings are not "none".
  `rdOf_viewOK`: `Rd.ViewOK`. `rdOf_fits`: `Rd.carS` bears the typed errors at `(switchMaps …).err`.
  `K02Rd`, `k02Rd`: these two and the bound of Reading.lean as one closed proposition; its proof.

Limits: those of Reading.lean. That a text's yes gives the two tests of work is not said here:
whoever lays a text over the two rounds owes it. The answers are read off the items of the sort
"answer" alone, as `Rd.answ` has it. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.Reading
import Johnson.Top.H.LocPlace
import OnBytes.Tie.Pv.Row.ViewT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Prob
open Johnson.Pack OnBytes.Tie.Pv.Switch
open OnBytes.Tie.Pv.Row (rvOne)
open _root_.Run (bsRound)
open scoped ENNReal

/-! ### Readings of a record of draws -/

/-- c coordinates and the factor. -/
noncomputable def seedOfD (c : ℕ) (D : Fmt.Drawn) : Option ((Fin c → GE) × GEˣ) :=
  if (D.elems.map toE).length = c + 1 then
    some (fun i => (D.elems.map toE).getD i.val 0, unitOf ((D.elems.map toE).getD c 0))
  else none

/-- t positions below 2 ^ a, off a list of numbers. -/
def posOfL (a t : ℕ) (L : List ℕ) : Option (Fin t → Fin (2 ^ a)) :=
  if L.length = t then some fun i => ⟨L.getD i.val 0 % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos a)⟩
  else none

/-- t positions below 2 ^ a. -/
def posOfD (a t : ℕ) (D : Fmt.Drawn) : Option (Fin t → Fin (2 ^ a)) := posOfL a t D.poss

/-- A record of draws without an element. -/
def voidE : Fmt.Drawn := ⟨[], [], [], none⟩

/-- A record of draws with one position too many. -/
def voidP (t : ℕ) : Fmt.Drawn := ⟨[], List.replicate (t + 1) 0, [], none⟩

/-- **The view with the test of work.** -/
def shownW (d : RDT) (void : Fmt.Drawn) (m : (wT d).Msg) (c : (wT d).Chal) : Fmt.RoundView :=
  ⟨(rvOne d m c).vals,
    if GChal.pass (b := d.entry.work) (c : (wRound (toRD d)).Chal) = true then (rvOne d m c).drawn
    else void⟩

theorem shownW_pass (d : RDT) (void : Fmt.Drawn) (m : (wT d).Msg) (c : (wT d).Chal)
    (h : GChal.pass (b := d.entry.work) (c : (wRound (toRD d)).Chal) = true) :
    shownW d void m c = rvOne d m c := by
  unfold shownW
  rw [if_pos h]

/-- The view's items do not hang on the verifier's message. -/
theorem shownW_vals (d : RDT) (void : Fmt.Drawn) (m : (wT d).Msg) (c c' : (wT d).Chal) :
    (shownW d void m c).vals = (shownW d void m c').vals := rfl

/-- The elements that the round's record of draws holds, read, are the typed values' elements. -/
theorem rvOne_elems (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) :
    (rvOne d m c).drawn.elems.map toE = elemsV _ (valsOf (toRD d) c) :=
  collect_elems _ _

/-- The positions that the round's record of draws holds are the typed values' positions. -/
theorem rvOne_poss (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) :
    (rvOne d m c).drawn.poss = possV _ (valsOf (toRD d) c) :=
  collect_poss _ _

theorem seed_read (d : RDT) (c₀ : ℕ) (hE : nE (Fmt.dsOf d.entry d.kind) = c₀ + 1)
    (m : (wT d).Msg) (c : (wT d).Chal) :
    seedOfD c₀ (shownW d voidE m c).drawn = chalTo (toRD d) (gSeed c₀ _) c := by
  unfold shownW chalTo
  by_cases hp : GChal.pass (b := d.entry.work) (c : (wRound (toRD d)).Chal) = true
  · rw [if_pos hp, if_pos hp]
    unfold seedOfD
    rw [rvOne_elems, if_pos ((elemsV_length _ _).trans hE)]
    rfl
  · rw [if_neg hp, if_neg hp]
    rfl

theorem pos_read (d : RDT) (a t : ℕ) (hP : nP (Fmt.dsOf d.entry d.kind) = t)
    (m : (wT d).Msg) (c : (wT d).Chal) :
    posOfD a t (shownW d (voidP t) m c).drawn = chalTo (toRD d) (gPos a t _) c := by
  unfold shownW chalTo
  by_cases hp : GChal.pass (b := d.entry.work) (c : (wRound (toRD d)).Chal) = true
  · rw [if_pos hp, if_pos hp]
    show posOfL a t (rvOne d m c).drawn.poss = _
    rw [rvOne_poss]
    unfold posOfL
    rw [if_pos ((possV_length _ _).trans hP)]
    rfl
  · rw [if_neg hp, if_neg hp]
    show posOfL a t (List.replicate (t + 1) 0) = none
    unfold posOfL
    rw [if_neg (by simp)]

/-! ### The seven readings -/

section
variable {r : SwRow} {H : r.OK} (X : Letters r H) (d₁ d₂ : RDT) (ρ : WordsOf X.caller d₁)

/-- **The seven readings.** -/
noncomputable def rdOf : Rd X.caller (wT d₁) (wT d₂) where
  view₁ := shownW d₁ voidE
  view₂ := shownW d₂ (voidP (baseCount r.set .request r.g))
  words := ρ.words
  mask := ρ.mask
  rdSeed := seedOfD (bMax r.cs r.l)
  rdAns := fun L => (eA r.cs r.l).symm fun i => toE (L.getD i.val zeroE).triple
  rdPos := posOfD r.g.main.logN (baseCount r.set .request r.g)

theorem K2Wr.nE₁ (H : r.OK) (w : K2Wr r d₁ d₂) :
    nE (Fmt.dsOf d₁.entry d₁.kind) = bMax r.cs r.l + 1 := by
  have hE : d₁.entry.drawE = bMax r.cs r.l + 1 := by
    rw [w.e₁]
    show r.set.samples * (largestCube r.o + 1) = _
    rw [H.samples, H.cube, Nat.one_mul]
  have hZ : d₁.entry.drawNZ = 1 := by
    rw [w.e₁]
    exact H.samples
  rw [w.kind₁, nE_dsOf_seed _ hZ (by omega)]
  exact hE

theorem K2Wr.nP₂ (w : K2Wr r d₁ d₂) :
    nP (Fmt.dsOf d₂.entry d₂.kind) = baseCount r.set .request r.g := by
  rw [nP_dsOf, w.e₂]
  rfl

/-- What the verifier is shown of the first round has just the seed's elements. -/
theorem elems_len (H : r.OK) (w : K2Wr r d₁ d₂) (m : (wT d₁).Msg) (c : (wT d₁).Chal) :
    ((rvOne d₁ m c).drawn.elems.map toE).length = bMax r.cs r.l + 1 := by
  rw [rvOne_elems, elemsV_length]
  exact K2Wr.nE₁ d₁ d₂ H w

/-- What the verifier is shown of the second round has just the plan's number of positions. -/
theorem poss_len (w : K2Wr r d₁ d₂) (m : (wT d₂).Msg) (c : (wT d₂).Chal) :
    (rvOne d₂ m c).drawn.poss.length = baseCount r.set .request r.g := by
  rw [rvOne_poss, possV_length]
  exact K2Wr.nP₂ d₁ d₂ w

/-- The items of the second round's view do not hang on the verifier's message. -/
theorem rdOf_viewOK : (rdOf X d₁ d₂ ρ).ViewOK := fun m c c' =>
  shownW_vals d₂ (voidP (baseCount r.set .request r.g)) m c c'

set_option maxHeartbeats 1000000 in
/-- **The place's map at these readings bears the typed errors at the written counts.** -/
theorem rdOf_fits (w : K2Wr r d₁ d₂) (hl : r.g.main.logN ≤ 64) :
    (rdOf X d₁ d₂ ρ).carS.Fits (Cb.Pv.SendLocRide.eps X.caller)
      ((switchMaps X d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps X.caller)) := by
  have ok := switchMaps_ok X d₁ d₂ ρ w hl
  refine ⟨⟨(bsRound .two d₁.entry d₁.kind).w, fun m c' => ?_, le_rfl⟩, fun _ _ =>
    ⟨⟨(bsRound .two d₂.entry d₂.kind).w, fun m c' => ?_, le_rfl⟩, fun _ _ => trivial⟩⟩
  · refine le_trans (le_of_eq (congrArg cnt (funext fun c => ?_)))
      (chalTo_fib (toRD d₁) _ ok.1.inj ok.1.log c')
    exact congrArg (· = some c') (seed_read d₁ _ (K2Wr.nE₁ d₁ d₂ H w) m c)
  · refine le_trans (le_of_eq (congrArg cnt (funext fun c => ?_)))
      (chalTo_fib (toRD d₂) _ ok.2.1.inj ok.2.1.log c')
    exact congrArg (· = some c') (pos_read d₂ _ _ (K2Wr.nP₂ d₁ d₂ w) m c)

end

/-- **As one closed proposition**: at every record at which both tests say yes. -/
def K02Rd : Prop :=
  ∀ (r : SwRow) (h : r.ok = true), r.writtenOK = true →
    ∀ (X : Letters r (r.ok_says h)) (d₁ d₂ : RDT) (ρ : WordsOf X.caller d₁), K2Wr r d₁ d₂ →
      (rdOf X d₁ d₂ ρ).ViewOK ∧
      (rdOf X d₁ d₂ ρ).carS.Fits (Cb.Pv.SendLocRide.eps X.caller)
        ((switchMaps X d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps X.caller)) ∧
      Err.Below ((switchMaps X d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps X.caller))
        ((2 : ℝ≥0∞)⁻¹ ^ r.set.target)

theorem k02Rd : K02Rd := fun _ h hW X d₁ d₂ ρ w =>
  ⟨rdOf_viewOK X d₁ d₂ ρ, rdOf_fits X d₁ d₂ ρ w (logN_of_written hW),
    switch_written h hW X d₁ d₂ ρ w⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.seed_read
#print axioms VerifiableInference.Desc.First.K2Caller.pos_read
#print axioms VerifiableInference.Desc.First.K2Caller.rdOf_viewOK
#print axioms VerifiableInference.Desc.First.K2Caller.rdOf_fits
#print axioms VerifiableInference.Desc.First.K2Caller.k02Rd
