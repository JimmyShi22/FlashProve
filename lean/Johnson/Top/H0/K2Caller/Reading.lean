-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/Reading.lean: how the code switch's two WRITTEN rounds are read as the two
typed rounds of the proved block, at the caller of Row.lean: a term of the library's `Maps`
(OnBytes/Flat/CarrySMaps.lean) that is in order; so the written counts bear the typed ones, and they
are shares of at most 2⁻¹ ^ target.

WrittenMaps.lean bounds `M.err ε` for every reading M that skips no round; there M is a letter. Here
one is written.
  The verifier's messages. "SEND seed": the sampler's typed values are read by the library's `gSeed`
    as c coordinates and a factor other than 0, c the sending's number of coordinates (`bMax`): that
    IS the block's joint seed, in this order (Johnson/Pack/PortS.lean: `seedsOf`;
    Johnson/Pack/SeedDraw.lean: `eS`). "LOC": by the library's `gPos` as t positions below 2 ^ logN:
    that IS the block's tuple of long positions.
  The prover's messages. "LOC": member i's answer is element number i that the written message
    sends (`sentT`; `eA`). "SEND seed": the members' words and the rider's word are read off the
    written message by two letters (`WordsOf`).

Main names:
  `K2Wr r d₁ d₂`: what is asked of the two written rounds: they have the plan's two entries, and
    each has the kind of its entry's name, as the format has it (`Fmt.kindOf`).
  `K2Wr.kind₁`, `K2Wr.kind₂`: so the kinds are seeds and positions.
  `WordsOf`: the two letters.
  `switchMaps`: the reading. `switchMaps_ok`: it is in order. `switchMaps_marks`: it skips no round.
  `switch_fits`: the written counts bear the typed ones (`Maps.fits`).
  `switch_written`: `Err.Below ((switchMaps …).err (the caller's errors)) (2⁻¹ ^ target)`.
  `K02Reading`, `k02Reading`: the last three as one closed proposition; its proof.

Limits: those of WrittenMaps.lean, WrittenMeets.lean and Row.lean. The two written rounds are
letters under `K2Wr`: none is taken from a file's chain. `WordsOf` stays a letter: nothing says that
the words read are what the trees of the written message commit to. That the block's decision on the
image is the programs' decision on the written rounds is not said. It is no soundness of the
protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.WrittenMaps
import OnBytes.Flat.CarrySForms
import OnBytes.Flat.CarrySProx
import Decl.Declared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.G4 OnBytes.Flat OnBytes.Maker Iop
open Johnson.Pack OnBytes.Tie.Pv.Switch
open scoped ENNReal

/-- **What is asked of the two written rounds.** -/
structure K2Wr (r : SwRow) (d₁ d₂ : RDT) : Prop where
  e₁ : d₁.entry = ((sendSeed r.set r.o r.roots).round r.set .request).entry
  k₁ : Fmt.kindOf d₁.entry.name = some d₁.kind
  e₂ : d₂.entry = ((locRound r.set .request r.g (24 * (r.set.samples * r.o.length)) 0
    (r.set.samples * r.o.length)).round r.set .request).entry
  k₂ : Fmt.kindOf d₂.entry.name = some d₂.kind

theorem K2Wr.kind₁ {r : SwRow} {d₁ d₂ : RDT} (w : K2Wr r d₁ d₂) : d₁.kind = .seeds := by
  have h := w.k₁
  rw [w.e₁] at h
  have h' : Fmt.kindOf "SEND seed" = some d₁.kind := h
  have e : Fmt.kindOf "SEND seed" = some Fmt.Kind.seeds := by decide
  rw [e] at h'
  exact (Option.some.inj h').symm

theorem K2Wr.kind₂ {r : SwRow} {d₁ d₂ : RDT} (w : K2Wr r d₁ d₂) : d₂.kind = .positions := by
  have h := w.k₂
  rw [w.e₂] at h
  have h' : Fmt.kindOf "LOC" = some d₂.kind := h
  have e : Fmt.kindOf "LOC" = some Fmt.Kind.positions := by decide
  rw [e] at h'
  exact (Option.some.inj h').symm

/-- So the two written rounds are as MeetsOfCovered.lean asks. -/
theorem K2Wr.writtenAs {r : SwRow} {d₁ d₂ : RDT} (w : K2Wr r d₁ d₂) :
    WrittenAs r.set .request ([d₁, d₂].map toRD) r.specs :=
  .cons ⟨w.e₁, by show d₁.kind ≠ .sealed; rw [w.kind₁]; decide⟩
    (.cons ⟨w.e₂, by show d₂.kind ≠ .sealed; rw [w.kind₂]; decide⟩ .nil)

/-- The two letters: the members' words and the rider's word, off the first written prover's
message. -/
structure WordsOf (z : Cb.Pv.SendLocRide.Size GE) (d₁ : RDT) where
  words : (wT d₁).Msg → z.sw.d.N.ext.Str
  mask : (wT d₁).Msg → z.Cw.Word

section
variable {r : SwRow} {H : r.OK} (X : Letters r H) (d₁ d₂ : RDT) (ρ : WordsOf X.caller d₁)

/-- **The reading.** -/
noncomputable def switchMaps : Maps [d₁, d₂] (Cb.Pv.SendLocRide.R X.caller).shape :=
  .step (RMap.seed (fun m => ((ρ.mask m, ρ.words m), ((), ()))) (bMax r.cs r.l) id)
    (.step (RMap.pos (fun m => (((), ()), ((eA r.cs r.l).symm fun i => sentT d₂ m i.val, ())))
      r.g.main.logN (baseCount r.set .request r.g) id) .nil)

theorem switchMaps_marks : (switchMaps X d₁ d₂ ρ).marks = allRead ([d₁, d₂].map toRD) := rfl

/-- **It is in order.** -/
theorem switchMaps_ok (w : K2Wr r d₁ d₂) (hl : r.g.main.logN ≤ 64) :
    (switchMaps X d₁ d₂ ρ).OK := by
  have hE : d₁.entry.drawE = bMax r.cs r.l + 1 := by
    rw [w.e₁]
    show r.set.samples * (largestCube r.o + 1) = _
    rw [H.samples, H.cube, Nat.one_mul]
  have hZ : d₁.entry.drawNZ = 1 := by
    rw [w.e₁]
    exact H.samples
  have hT : d₁.entry.trits = 0 := by rw [w.e₁]; rfl
  have hP : d₁.entry.poss = 0 := by rw [w.e₁]; rfl
  have hL : d₁.entry.logN ≤ 64 := by rw [w.e₁]; exact Nat.zero_le 64
  have s2 : SendsDraws (toRD d₂) (nS d₂.items) 0 (baseCount r.set .request r.g) r.g.main.logN := by
    have a1 : d₂.entry.drawE = 0 := by rw [w.e₂]; rfl
    have a2 : d₂.entry.drawNZ = 0 := by rw [w.e₂]; rfl
    have a3 : d₂.entry.poss = baseCount r.set .request r.g := by rw [w.e₂]; rfl
    have a4 : d₂.entry.logN = r.g.main.logN := by rw [w.e₂]; rfl
    have a5 : d₂.entry.trits = 0 := by rw [w.e₂]; rfl
    have k : d₂.kind = .positions := w.kind₂
    have k1 : d₂.kind ≠ .sealed := by rw [k]; decide
    have k2 : d₂.kind ≠ .seeds := by rw [k]; decide
    have z : d₂.entry.drawNZ ≤ d₂.entry.drawE := by omega
    have l4 : d₂.entry.logN ≤ 64 := by omega
    refine ⟨rfl, plain_dsOf _ _ a5 k1, ?_, ?_, ?_, l4⟩
    · exact (nE_dsOf _ _ z k2).trans a1
    · exact (nP_dsOf _ _).trans a3
    · rw [← a4]
      exact allPos_dsOf _ _
  refine ⟨RMap.seed_ok _ ?_ ?_ ?_ ?_ hL Function.injective_id,
    RMap.pos_ok _ s2 Function.injective_id, trivial⟩
  · exact plain_dsOf _ _ hT (by rw [w.kind₁]; decide)
  · rw [w.kind₁, nE_dsOf_seed _ hZ (by omega)]
    exact hE
  · exact (nP_dsOf _ _).trans hP
  · have h := isNZ_dsOf_seed d₁.entry hZ
    rw [hE, Nat.add_sub_cancel] at h
    rw [w.kind₁]
    exact h

end

/-- **The written counts bear the typed ones.** -/
theorem switch_fits {r : SwRow} {H : r.OK} (X : Letters r H) (d₁ d₂ : RDT)
    (ρ : WordsOf X.caller d₁) (w : K2Wr r d₁ d₂) (hl : r.g.main.logN ≤ 64) :
    (switchMaps X d₁ d₂ ρ).carry.Fits (Cb.Pv.SendLocRide.eps X.caller)
      ((switchMaps X d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps X.caller)) :=
  Maps.fits _ (switchMaps_ok X d₁ d₂ ρ w hl) _

/-- **The written counts are shares of at most 2⁻¹ ^ target.** -/
theorem switch_written {r : SwRow} (h : r.ok = true) (hW : r.writtenOK = true)
    (X : Letters r (r.ok_says h)) (d₁ d₂ : RDT) (ρ : WordsOf X.caller d₁) (w : K2Wr r d₁ d₂) :
    Err.Below ((switchMaps X d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps X.caller))
      ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) :=
  Letters.mapsBelow h hW X _ (switchMaps_marks X d₁ d₂ ρ) w.writtenAs

/-- The positions have at most 64 bits, off the second test. -/
theorem logN_of_written {r : SwRow} (hW : r.writtenOK = true) : r.g.main.logN ≤ 64 := by
  unfold SwRow.writtenOK at hW
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hW
  exact (fine_of (hW.1 _ (List.mem_cons_of_mem _ List.mem_cons_self))).log

/-- **As one closed proposition.** -/
def K02Reading : Prop :=
  ∀ (r : SwRow) (h : r.ok = true), r.writtenOK = true →
    ∀ (X : Letters r (r.ok_says h)) (d₁ d₂ : RDT) (ρ : WordsOf X.caller d₁), K2Wr r d₁ d₂ →
      (switchMaps X d₁ d₂ ρ).OK ∧
      (switchMaps X d₁ d₂ ρ).carry.Fits (Cb.Pv.SendLocRide.eps X.caller)
        ((switchMaps X d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps X.caller)) ∧
      Err.Below ((switchMaps X d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps X.caller))
        ((2 : ℝ≥0∞)⁻¹ ^ r.set.target)

theorem k02Reading : K02Reading := fun _ h hW X d₁ d₂ ρ w =>
  ⟨switchMaps_ok X d₁ d₂ ρ w (logN_of_written hW), switch_fits X d₁ d₂ ρ w (logN_of_written hW),
    switch_written h hW X d₁ d₂ ρ w⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.switchMaps_ok
#print axioms VerifiableInference.Desc.First.K2Caller.switch_fits
#print axioms VerifiableInference.Desc.First.K2Caller.switch_written
#print axioms VerifiableInference.Desc.First.K2Caller.k02Reading
