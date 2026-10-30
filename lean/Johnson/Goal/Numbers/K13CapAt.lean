-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K13CapAt.lean: the kind K13's batching AT THE CAP: the errors that the law's
piece bears (errK rows k: rows - 1 at the draw, 1 at the sum's round, 2 at each variable's, as
written counts) are, round by round, at most the cap (Iop/ErrCap.lean: Err.cap 128: the written
round's challenges divided by 2 ^ 128, rounded down), at the written rounds of a proof file's and of
a key file's batching.

IT IS SAID OF THE LIST OF WRITTEN COUNTS ITSELF, (mapsOf dZ d0 ds).err (errK rows k), WITHOUT A
PIECE: pieceM3 stands over the proof file's first chain's record and cannot, by type, be spent at a
key file's place; pieceAt (K13/Law/GoodAny.lean), which can, bears the same list by make.
  maps_below_pow: Err.Below of the list, from the comparisons of
      Johnson/Goal/Numbers/K13RoundsAt.lean
  K13AtCap, k13_at_cap: Declared, Err.Below at 2^-128 and Err.le against the cap
  k13_at_cap_real: in a proof file: 13 rows
  k13_at_cap_key: in a key file: 24 rows (the pile's count), kCol = 18
  k13_at_cap_key_at_scope: at the planner's own numbers, at every three public files in the scope of
      the goals, from a planner that returns

  key_batt, real_batt: the written stretch's entries and kinds are those of the rounds that the kind
      itself declares (K13/Kind.lean: battRounds) at these numbers
  key_pending, key_pending_loop: the key file's pile has 24 rows: the sum of the lookups' parts (as
      List.sum and as the loop sumT); kCol = 18

What is not claimed. What the head of Johnson/Goal/Numbers/K13RoundsAt.lean does not claim. Nothing
on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K13RoundsAt
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Run
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Params (Rounds LinSized)
open OnBytes.Params.Prices (AtRecord)
open Johnson.G (dryProofFull dryKeyFull codesFull2)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.K1 (realSized)
open _root_.Desc.K14.Law (roundB)
open scoped ENNReal
open Lk6.AtPlan (keyFull key_eq_at_scope)

/-- **The list of written counts itself**, without a piece: pieceM3 (K13/Law/Good.lean) and pieceAt
(K13/Law/GoodAny.lean: the piece at any state and block, as a key file's description wants it) both
bear this very list as their err, by make. -/
theorem maps_below_pow (P : Where) (dZ d0 : RDT) (ds : List RDT) (hD : Declared P dZ d0 ds) (k : ℕ)
    (hZ : roundB dZ.entry dZ.kind (P.rows - 1) k = true)
    (h0 : roundB d0.entry d0.kind 1 k = true)
    (hs : ∀ d ∈ ds, roundB d.entry d.kind 2 k = true) :
    Err.Below ((mapsOf dZ d0 ds).err (errK P.rows ds.length)) ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  obtain ⟨nZ, aZ, gZ⟩ := sends_of_entry (d := dZ) (by rw [hD.sigma.1]; rfl)
    (by rw [hD.sigma.1]; rfl) (by rw [hD.sigma.1]; rfl) (by rw [hD.sigma.1]; exact Nat.zero_le 1)
    (by rw [hD.sigma.1]; exact Nat.zero_le 64) hD.sigma.2.1 hD.sigma.2.2
  obtain ⟨n0, a0, g0⟩ := sends_of_entry (d := d0) (by rw [hD.eps.1]; rfl) (by rw [hD.eps.1]; rfl)
    (by rw [hD.eps.1]; rfl) (by rw [hD.eps.1]; exact Nat.zero_le 1)
    (by rw [hD.eps.1]; exact Nat.zero_le 64) hD.eps.2.1 hD.eps.2.2
  refine Maps.below_err _ (mapsOf_ok gZ g0 fun d hd => ?_) _
    (Maps.held_of_nat _ _ (maps_heldN k P.rows dZ d0 ds hZ h0 hs))
  obtain ⟨he, hk⟩ := hD.vars d hd
  exact sends_of_entry (by rw [he]; rfl) (by rw [he]; rfl) (by rw [he]; rfl)
    (by rw [he]; exact Nat.zero_le 1) (by rw [he]; exact Nat.zero_le 64) hk.1 hk.2

/-- **At the cap**: at every stretch with the written entries and kinds: the rounds are declared,
and the list of written counts is below 2^-128 and, round by round, at most the cap. -/
def K13AtCap (P : Where) (Wr : Rounds) (i : ℕ) : Prop :=
  ∀ (dZ d0 : RDT) (ds : List RDT),
    (dZ :: d0 :: ds).map (fun d => (d.entry, d.kind)) = stretch Wr i (2 + P.lin.kCol) →
      Declared P dZ d0 ds ∧
      Err.Below ((mapsOf dZ d0 ds).err (errK P.rows ds.length)) ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      Err.le ((mapsOf dZ d0 ds).err (errK P.rows ds.length))
        (Err.cap 128 (uLT (ckP .two) (dZ :: d0 :: ds)))

theorem k13_at_cap {P : Where} {codes : Codes} {Wr : Rounds} {i : ℕ}
    {msg : Option (List OracleNotice)} (hc : K13Cond P codes Wr i msg)
    (h : k13RB P.rows (stretch Wr i (2 + P.lin.kCol)) = true) : K13AtCap P Wr i := by
  intro dZ d0 ds hd
  rw [← hd] at h
  simp only [k13RB, List.map_cons, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := h
  have hB := maps_below_pow P dZ d0 ds (hc.declared dZ d0 ds hd) 128 h1 h2 fun d hm =>
    h3 (d.entry, d.kind) (List.mem_map_of_mem (f := fun d : RDT => (d.entry, d.kind)) hm)
  exact ⟨hc.declared dZ d0 ds hd, hB, Err.le_cap_of_below_inv 128 _ hB⟩

/-- **In a proof file.** -/
theorem k13_at_cap_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    ∀ P : Where, P.rows = 13 → P.lin = x.shape → P.work = (0, 0, 0) →
      K13AtCap P dryProofFull.1 48270 := by
  obtain ⟨x, a1, a2, a3⟩ := k13_real
  refine ⟨x, a1, a2, fun P h1 h2 h3 => k13_at_cap (a3 P h1 h2 h3).1 ?_⟩
  have h := real_testR13
  rw [a1] at h
  rw [h1, h2]
  exact h

/-- **In a key file.** -/
theorem k13_at_cap_key (P : Where) (h1 : P.rows = keyFull.ranges.pending)
    (h2 : P.lin = keyFull.once.shape) (h3 : P.work = (0, 0, 0)) :
    K13AtCap P dryKeyFull.1 18828 := by
  refine k13_at_cap (k13_key P h1 h2 h3).1 ?_
  rw [h1, h2]
  exact key_testR13

/-- **In a key file, at the planner's own numbers.** -/
theorem k13_at_cap_key_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p)
    (P : Where) (h1 : P.rows = p.chains.made.sized.key.ranges.pending)
    (h2 : P.lin = p.chains.made.sized.key.once.shape) (h3 : P.work = (0, 0, 0)) :
    K13AtCap P dryKeyFull.1 18828 := by
  rw [key_eq_at_scope hZ hp] at h1 h2
  exact k13_at_cap_key P h1 h2 h3

/-! ## The written stretch is the kind's own declared rounds -/

/-- **In a key file: the written stretch's entries and kinds are those of the rounds that the kind
declares** (K13/Kind.lean: battRounds), each kind read off the entry's name. -/
theorem key_batt (P : Where) (h1 : P.rows = keyFull.ranges.pending)
    (h2 : P.lin = keyFull.once.shape) (h3 : P.work = (0, 0, 0)) :
    (stretch dryKeyFull.1 18828 20).map (fun x => (x.1, some x.2)) =
      (battRounds P).map (fun r => (r.entry, Fmt.kindOf r.entry.name)) := by
  simp only [battRounds, sigmaEntry, epsEntry, roundEntry, h1, h2, h3]
  decide +kernel

/-- The like in a proof file. -/
theorem real_batt : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    ∀ P : Where, P.rows = 13 → P.lin = x.shape → P.work = (0, 0, 0) →
      (stretch dryProofFull.1 48270 20).map (fun x => (x.1, some x.2)) =
        (battRounds P).map (fun r => (r.entry, Fmt.kindOf r.entry.name)) := by
  obtain ⟨x, a1, -, -⟩ := k13_real
  have h : (realSized.any fun p => decide (p.1.shape.kCol = 18)) = true := by decide +kernel
  rw [a1, Option.any_some] at h
  have hk : x.shape.kCol = 18 := of_decide_eq_true h
  refine ⟨x, a1, fun P h1 h2 h3 => ?_⟩
  simp only [battRounds, sigmaEntry, epsEntry, roundEntry, h1, h2, h3, hk]
  decide +kernel

/-- The pile's count in a key file: 24: a row for each part of each lookup of the ranges' proof. -/
theorem key_pending : keyFull.ranges.pending = 24 ∧
    (keyFull.ranges.x.lookups.map fun l => l.parts.length).sum = 24 ∧
    keyFull.once.shape.kCol = 18 := by
  decide +kernel

/-- The same count in the form in which a key file's description writes it (a loop). -/
theorem key_pending_loop :
    OnBytes.sumT (keyFull.ranges.x.lookups.map (·.parts.length)) = keyFull.ranges.pending := by
  decide +kernel

end VerifiableInference.Desc.K13.Law
