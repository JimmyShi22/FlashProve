-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/MeetsOfCovered.lean: from typed rounds that a plan's rounds cover to the
WRITTEN rounds: if a block's typed rounds have the shape of the plan's entries, each typed count is
covered by the plan's round, and each of these rounds holds in the planner's reckoning, then each
count, times the sampler's weight, is a share of at most 2⁻¹ ^ target of the written round's
verifier messages, test bits among them.

The road is the library's: `held_round` (OnBytes/Slice/HeldRound.lean) for one round: there the
planner's own term for the distance from uniform of the drawn elements pays for the sampler's bias,
and the round's bits of work are counted as the written round counts them; and
`Held.cnts_below_held` (OnBytes/Flat/CountsHeld.lean) along a list of rounds, under two premises:
`Held` of each pair of a planned and a written round, and `Held.CountsL`: each typed count is at
most the planner's number times the number of the WRITTEN round's typed values.
OnBytes/Flat/CarrySBelow.lean has the same along a reading of a file's rounds (`Maps.below_held`).
What is added here: both premises follow from what a tie of a typed block to the planner has in hand
(`ShapeIsAll`, OnBytes/G4/RoundIsAll.lean; `Covered`, OnBytes/Tie/Pv/PortKit.lean), because the
number of a typed round's values IS the number of typed values of a written round with the same
entry, whatever its kind but a sealing. General in the block. Definitions, and theorems with their
proofs.

Main names:
  `nVals_dsOf_seeds`, `nVals_any`: the number of typed values of a written round, from its entry's
    numbers of draws, also at the kind seeds (OnBytes/Slice/HeldCounts.lean has the other kinds).
  `Fine σ c y`, `fineB`, `fine_of`: what `held_round` asks of a planned round beside the count:
    positions of at most 64 bits; work + 66 ≤ target if an element is drawn; the planner's
    `roundHolds`. As a test that can be evaluated.
  `WrittenAs σ c ds ys`: the written rounds ds have the entries of the planned rounds ys, one by
    one, and none is a sealing.
  `count_one`, `held_one`: one round: the clause of `CountsL`; `Held`.
  `premises_of_covered`: both premises of `Held.cnts_below_held`, along a list of rounds.
  `written_below`: `Err.Below` of the library's written counts (`Held.cnts`, every round read, at
    the sampler's weights) at 2⁻¹ ^ target.

Limits: those of OnBytes/Slice/HeldRound.lean and OnBytes/Flat/CountsHeld.lean. A share is a count
among all strings of hash blocks and test bits: nothing on the hash function, and nothing on what
work is worth against a prover who tries many times. The written rounds are letters with the plan's
entries. That the written counts bear the typed ones along maps of messages is `Held.fits_cnts`,
under `Follows`: not called here. A bound on each round, not on a sum over rounds. That a typed
count bounds a prover's chance is the block's own law. Nothing on soundness of a protocol. On hiding
nothing.

-/
import OnBytes.Slice.HeldCounts
import OnBytes.Flat.CountsHeld
import OnBytes.G4.RoundIsAll
import OnBytes.Tie.Pv.PortKit
import OnBytes.Slice.RatesToy
import Ior.KnowCollRulesChainErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.G4 Iop
open _root_.Run (PQ.RD ckP)
open _root_.Run.PQ (uL)
open scoped ENNReal

/-! ### The number of typed values of a written round -/

theorem nVals_flatten (L : List Fmt.Draw) : ∀ s : ℕ,
    nVals (List.replicate s L).flatten = nVals L ^ s
  | 0 => rfl
  | s + 1 => by
      rw [List.replicate_succ, List.flatten_cons, nVals_append, nVals_flatten L s, pow_succ,
        Nat.mul_comm]

theorem nVals_seedOne (v : ℕ) :
    nVals (List.replicate v Fmt.Draw.elem ++ [Fmt.Draw.elemNZ]) =
      (Fmt.Fld.two.p ^ 3) ^ v * (Fmt.Fld.two.p ^ 3 - 1) := by
  rw [nVals_append, nVals_replicate]
  simp [nVals]

/-- The kind seeds: the same number as at the other kinds. -/
theorem nVals_dsOf_seeds (e : Fmt.Entry) :
    nVals (Fmt.dsOf e .seeds) =
      (2 ^ e.logN) ^ e.poss * ((Fmt.Fld.two.p ^ 3) ^ (e.drawE - e.drawNZ) *
        ((Fmt.Fld.two.p ^ 3 - 1) ^ e.drawNZ * 4 ^ e.trits)) := by
  unfold Fmt.dsOf Fmt.dsElems Fmt.dsSeeds
  rw [if_pos rfl, if_neg (by decide), nVals_append, nVals_append, nVals_append, nVals_replicate,
    nVals_flatten, nVals_seedOne, nVals_replicate]
  simp only [nVals, mul_one]
  generalize Fmt.Fld.two.p ^ 3 - 1 = Q
  generalize Fmt.Fld.two.p ^ 3 = P
  generalize e.drawE - e.drawNZ = D
  conv_rhs => rw [← Nat.div_add_mod' D e.drawNZ]
  ring

/-- **The number of typed values of a written round**, at every kind but a sealing. -/
theorem nVals_any (e : Fmt.Entry) (k : Fmt.Kind) (hk : k ≠ .sealed) :
    nVals (Fmt.dsOf e k) = (2 ^ e.logN) ^ e.poss * ((Fmt.Fld.two.p ^ 3) ^ (e.drawE - e.drawNZ) *
      ((Fmt.Fld.two.p ^ 3 - 1) ^ e.drawNZ * 4 ^ e.trits)) := by
  by_cases h : k = .seeds
  · rw [h]
    exact nVals_dsOf_seeds e
  · exact nVals_dsOf e k h hk

/-! ### One round -/

/-- What `held_round` asks of a planned round beside the count. -/
structure Fine (σ : Setting) (c : Scope) (y : RoundSpec) : Prop where
  log : (y.round σ c).entry.logN ≤ 64
  work : (y.round σ c).entry.drawE ≠ 0 → (y.round σ c).entry.work + 66 ≤ σ.target
  holds : roundHolds σ (capped σ) (y.round σ c) = true

/-- The same as a test. -/
def fineB (σ : Setting) (c : Scope) (y : RoundSpec) : Bool :=
  decide ((y.round σ c).entry.logN ≤ 64) &&
    decide ((y.round σ c).entry.drawE ≠ 0 → (y.round σ c).entry.work + 66 ≤ σ.target) &&
    roundHolds σ (capped σ) (y.round σ c)

theorem fine_of {σ : Setting} {c : Scope} {y : RoundSpec} (h : fineB σ c y = true) :
    Fine σ c y := by
  unfold fineB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **One round: the count.** A typed round with the entry's shape, covered by a planned round; a
written round with that entry. -/
theorem count_one (σ : Setting) (c : Scope) (F : Type) {r : Round} {e : ℕ} {y : RoundSpec}
    {d : PQ.RD} (hE : EntryIsAll GE F r (y.round σ c).entry)
    (hC : Cb.Pv.Covered σ c (e, Fintype.card r.Chal) y) (h1 : d.entry = (y.round σ c).entry)
    (hk : d.kind ≠ .sealed) :
    (e : ℚ) ≤ (y.round σ c).error.val * (nVals (Fmt.dsOf d.entry d.kind) : ℚ) := by
  have hN : Fintype.card r.Chal = nVals (Fmt.dsOf d.entry d.kind) := by
    rw [← Nat.card_eq_fintype_card, hE.card_chal, nVals_any _ _ hk, h1, Nat.card_eq_fintype_card,
      card_GE]
    ring
  have hpos : (0 : ℝ) < (Fintype.card r.Chal : ℝ) := by exact_mod_cast Fintype.card_pos
  have hC' : (e : ℝ) / (Fintype.card r.Chal : ℝ) ≤ (((y.round σ c).error.val : ℚ) : ℝ) := hC
  have hc' : (e : ℝ) ≤ (((y.round σ c).error.val : ℚ) : ℝ) * (Fintype.card r.Chal : ℝ) :=
    (div_le_iff₀ hpos).1 hC'
  rw [← hN]
  exact_mod_cast hc'

/-- **One round: the planner's yes.** -/
theorem held_one (σ : Setting) (c : Scope) (F : Type) (hp : σ.p = 2 ^ 64 - 2 ^ 32 + 1)
    (hd : σ.degree = 3) {r : Round} {y : RoundSpec} {d : PQ.RD}
    (hE : EntryIsAll GE F r (y.round σ c).entry) (h1 : d.entry = (y.round σ c).entry)
    (hF : Fine σ c y) : Held σ (y.round σ c) d :=
  ⟨hp, hd, h1, hF.log, hE.2.1, hF.work, hF.holds⟩

/-! ### A list of rounds -/

/-- The written rounds have the planned rounds' entries, one by one, and none is a sealing. -/
def WrittenAs (σ : Setting) (c : Scope) (ds : List PQ.RD) (ys : List RoundSpec) : Prop :=
  List.Forall₂ (fun (d : PQ.RD) (y : RoundSpec) =>
    d.entry = (y.round σ c).entry ∧ d.kind ≠ .sealed) ds ys

/-- Every round is read. -/
def allRead (ds : List PQ.RD) : List Bool := ds.map fun _ => true

/-- **The library's premise on the counts**, and `Held` pair by pair. -/
theorem premises_of_covered (σ : Setting) (c : Scope) (F : Type) (hp : σ.p = 2 ^ 64 - 2 ^ 32 + 1)
    (hd : σ.degree = 3) : ∀ (s : Shape) (ε : Err s) (ys : List RoundSpec) (ds : List PQ.RD),
    ShapeIsAll GE F s (ys.map fun y => (y.round σ c).entry) →
    List.Forall₂ (Cb.Pv.Covered σ c) (ε.toList.zip s.chalList) ys → WrittenAs σ c ds ys →
    (∀ y ∈ ys, Fine σ c y) →
    List.Forall₂ (fun d r => Held σ r d) ds (ys.map fun y => y.round σ c) ∧
      OnBytes.Flat.Held.CountsL ds (ys.map fun y => y.round σ c) (allRead ds) s ε := by
  intro s
  induction s with
  | nil =>
    intro ε ys ds hS _ hD _
    cases ys with
    | nil =>
      cases hD
      exact ⟨.nil, trivial⟩
    | cons y ys =>
      rw [List.map_cons] at hS
      cases hS
  | cons r s ih =>
    intro ε ys ds hS hC hD hF
    obtain ⟨e, ε⟩ := ε
    cases ys with
    | nil => cases hS
    | cons y ys =>
      rw [List.map_cons] at hS
      cases hD with
      | cons c1 c2 =>
        cases hS with
        | cons a1 a2 =>
          have hC' : List.Forall₂ (Cb.Pv.Covered σ c)
              ((e, Fintype.card r.Chal) :: ε.toList.zip (Shape.chalList s)) (y :: ys) := hC
          cases hC' with
          | cons b1 b2 =>
            obtain ⟨i1, i2⟩ := ih ε ys _ a2 b2 c2 fun z hz => hF z (List.mem_cons_of_mem _ hz)
            exact ⟨.cons (held_one σ c F hp hd a1 c1.1 (hF y List.mem_cons_self)) i1,
              count_one σ c F a1 b1 c1.1 c1.2, i2⟩

/-- **The written counts are shares of at most 2⁻¹ ^ target.** -/
theorem written_below (σ : Setting) (c : Scope) (F : Type) (hp : σ.p = 2 ^ 64 - 2 ^ 32 + 1)
    (hd : σ.degree = 3) (s : Shape) (ε : Err s) (ys : List RoundSpec) (ds : List PQ.RD)
    (hS : ShapeIsAll GE F s (ys.map fun y => (y.round σ c).entry))
    (hC : List.Forall₂ (Cb.Pv.Covered σ c) (ε.toList.zip s.chalList) ys)
    (hD : WrittenAs σ c ds ys) (hF : ∀ y ∈ ys, Fine σ c y) :
    Err.Below (OnBytes.Flat.Held.cnts (uL (ckP .two) ds)
      (OnBytes.Flat.Held.wsOf ds (allRead ds)) s ε) ((2 : ℝ≥0∞)⁻¹ ^ σ.target) :=
  OnBytes.Flat.Held.cnts_below_held σ ds _ _ s ε
    (premises_of_covered σ c F hp hd s ε ys ds hS hC hD hF).1
    (premises_of_covered σ c F hp hd s ε ys ds hS hC hD hF).2

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.nVals_any
#print axioms VerifiableInference.Desc.First.K2Caller.count_one
#print axioms VerifiableInference.Desc.First.K2Caller.premises_of_covered
#print axioms VerifiableInference.Desc.First.K2Caller.written_below
