-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K13RoundsAt.lean: the written errors of the kind K13's batching (BAT-sigma, PSC
epsilon, a PSC round for each column variable) are shares of at most 2^-128 of each round's written
challenges, at the kind's own counts, from ONE comparison of natural numbers a round, which Lean's
kernel evaluates at the written rounds of a proof file's and of a key file's first chain.

The kind's law (K13/Law/PinA.lean: atM3_goodInA) is stated of the piece pieceM3, which bears the
typed errors errK rows k: rows - 1 at the draw, 1 at the sum's round, 2 at each variable's.
K13/Law/Data.lean has pieceM3_below from the library's condition Maps.Held, "tried nowhere". Here
that condition is had at 2^-128 by the library's rule at natural numbers
(OnBytes/Flat/CarrySNum.lean: Maps.HeldN, held_of_nat), with the comparison roundB of
Johnson/Goal/Numbers/K14RoundsAt.lean.
  held_one, short_heldN, maps_heldN: from a yes of the comparison at each round: Maps.HeldN
  pieceM3_pow: so Err.Below of the piece's errors at 2^-k
  k13RB: the test with code, on the entries and kinds of a stretch of written rounds
  K13Rounds P W i: every stretch of written rounds with the entries and kinds of W's 2 + kCol rounds
      from place i on is Declared, bears no work, and the piece at it has Err.Below at 2^-128
  real_testR13, key_testR13: the test says yes: evaluations in Lean's kernel (decide +kernel)
  k13_rounds_real, k13_rounds_key: in a proof file (13 rows), in a key file (24 rows)
  K13RoundsStatement, k13RoundsStatement: K13Rounds in a proof file and in a key file, as one closed
      proposition
  teeth13: the comparison says no at a count of 2 ^ 65 at the draw's written round of both files

HOW MANY BITS ARE WORK: no work: the kind has no round of positions.

What is not claimed. That the typed numbers are the parameters at a description's own places. One
count a round. From Err.Below to the cap: the user's step. The law's premises on letters. What the
heads of Johnson/Goal/Numbers/K13CondAt.lean and Johnson/Goal/Numbers/K14RoundsAt.lean do not claim.
Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K13CondAt
import Johnson.Goal.Numbers.K14RoundsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Run
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Params (Rounds LinSized recordSet)
open OnBytes.Params.Prices (AtRecord)
open Johnson.G (dryProofFull dryKeyFull codesFull2)
open Johnson.L5.Layers (rd sRound sRounds errTo)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.K1 (realSized)
open _root_.Desc.K14.Law (roundB)
open Lk6.AtPlan (keyFull)
open scoped ENNReal

/-- What a yes of the comparison gives at one round. -/
theorem held_one {en : Fmt.Entry} {kd : Fmt.Kind} {e k : ℕ} (h : roundB en kd e k = true) :
    ∃ n D : ℕ, 0 < D ∧ e * D ≤ n * nVals (Fmt.dsOf en kd) ∧
      (2 ^ 128 + 1) ^ (bsRound .two en kd).b * n * 2 ^ k ≤
        (2 ^ 128) ^ (bsRound .two en kd).b * D * 2 ^ en.work := by
  unfold roundB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨e, nVals (Fmt.dsOf en kd), h.1, Nat.le_refl _, h.2⟩

/-- The variables' rounds. -/
theorem short_heldN (k : ℕ) : ∀ ds : List RDT, (∀ d ∈ ds, roundB d.entry d.kind 2 k = true) →
    (shortMaps (pfCube GE 2) mapK ds).HeldN k
      (errTo (sRounds (fmtOf GE ds.length)) (pRounds (fmtOf GE ds.length))
        (pErr (fmtOf GE ds.length)))
  | [], _ => trivial
  | d :: ds, h => ⟨held_one (h d List.mem_cons_self),
      short_heldN k ds fun d' hd' => h d' (List.mem_cons_of_mem _ hd')⟩

/-- All rounds. -/
theorem maps_heldN (k rows : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hZ : roundB dZ.entry dZ.kind (rows - 1) k = true) (h0 : roundB d0.entry d0.kind 1 k = true)
    (hs : ∀ d ∈ ds, roundB d.entry d.kind 2 k = true) :
    (mapsOf dZ d0 ds).HeldN k (errK rows ds.length) :=
  ⟨held_one hZ, held_one h0, short_heldN k ds hs⟩

variable {Cl W : Type}

/-- **The piece's errors are shares of at most 2^-k.** -/
theorem pieceM3_pow (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (k : ℕ)
    (hZ : roundB dZ.entry dZ.kind (P.rows - 1) k = true)
    (h0 : roundB d0.entry d0.kind 1 k = true)
    (hs : ∀ d ∈ ds, roundB d.entry d.kind 2 k = true) :
    Err.Below (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).err ((2 : ℝ≥0∞)⁻¹ ^ k) :=
  pieceM3_below F P base dZ d0 ds hD
    (Maps.held_of_nat _ _ (maps_heldN k P.rows dZ d0 ds hZ h0 hs))

/-- The test with code, on a stretch's entries and kinds. -/
def k13RB (rows : ℕ) (l : List (Fmt.Entry × Fmt.Kind)) : Bool :=
  match l with
  | z :: o :: t => roundB z.1 z.2 (rows - 1) 128 && roundB o.1 o.2 1 128 &&
      (t.all fun x => roundB x.1 x.2 2 128) && l.all fun x => decide (x.1.work = 0)
  | _ => false

/-- **The kind's rounds at exact integers.** -/
def K13Rounds (P : Where) (Wr : Rounds) (i : ℕ) : Prop :=
  ∀ (dZ d0 : RDT) (ds : List RDT),
    (dZ :: d0 :: ds).map (fun d => (d.entry, d.kind)) = stretch Wr i (2 + P.lin.kCol) →
      Declared P dZ d0 ds ∧ (∀ d ∈ dZ :: d0 :: ds, d.entry.work = 0) ∧
      ∀ (Cl W : Type) (F : Frame) (base : ℕ),
        Err.Below (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).err ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem k13Rounds_of {P : Where} {codes : Codes} {Wr : Rounds} {i : ℕ}
    {msg : Option (List OracleNotice)} (hc : K13Cond P codes Wr i msg)
    (h : k13RB P.rows (stretch Wr i (2 + P.lin.kCol)) = true) : K13Rounds P Wr i := by
  intro dZ d0 ds hd
  rw [← hd] at h
  simp only [k13RB, List.map_cons, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨hc.declared dZ d0 ds hd, fun d hm => ?_, fun Cl W F base => ?_⟩
  · exact h4 (d.entry, d.kind)
      (List.mem_map_of_mem (f := fun d : RDT => (d.entry, d.kind)) hm)
  · exact pieceM3_pow F P base dZ d0 ds (hc.declared dZ d0 ds hd) 128 h1 h2
      fun d hm => h3 (d.entry, d.kind)
        (List.mem_map_of_mem (f := fun d : RDT => (d.entry, d.kind)) hm)

/-! ## A proof file, a key file -/

theorem real_testR13 : (realSized.any fun p =>
    k13RB 13 (stretch dryProofFull.1 48270 (2 + p.1.shape.kCol))) = true := by
  decide +kernel

theorem key_testR13 : k13RB keyFull.ranges.pending
    (stretch dryKeyFull.1 18828 (2 + keyFull.once.shape.kCol)) = true := by
  decide +kernel

/-- **In a proof file.** -/
theorem k13_rounds_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    ∀ P : Where, P.rows = 13 → P.lin = x.shape → P.work = (0, 0, 0) →
      K13Rounds P dryProofFull.1 48270 := by
  obtain ⟨x, a1, a2, a3⟩ := k13_real
  refine ⟨x, a1, a2, fun P h1 h2 h3 => k13Rounds_of (a3 P h1 h2 h3).1 ?_⟩
  have h := real_testR13
  rw [a1] at h
  rw [h1, h2]
  exact h

/-- **In a key file.** -/
theorem k13_rounds_key (P : Where) (h1 : P.rows = keyFull.ranges.pending)
    (h2 : P.lin = keyFull.once.shape) (h3 : P.work = (0, 0, 0)) :
    K13Rounds P dryKeyFull.1 18828 := by
  refine k13Rounds_of (k13_key P h1 h2 h3).1 ?_
  rw [h1, h2]
  exact key_testR13

/-- **K13Rounds (its last clause: Err.Below at 2⁻¹ ^ 128 at its own stretch)**, at the batching's
twenty written rounds of both files. The step to the cap is one application of
Err.le_cap_of_below_inv (Iop/ErrCap.lean). -/
def K13RoundsStatement : Prop :=
  (∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    ∀ P : Where, P.rows = 13 → P.lin = x.shape → P.work = (0, 0, 0) →
      K13Rounds P dryProofFull.1 48270) ∧
  ∀ P : Where, P.rows = keyFull.ranges.pending → P.lin = keyFull.once.shape →
    P.work = (0, 0, 0) → K13Rounds P dryKeyFull.1 18828

theorem k13RoundsStatement : K13RoundsStatement := ⟨k13_rounds_real, k13_rounds_key⟩

/-- The comparison can say no. -/
theorem teeth13 : ((stretch dryProofFull.1 48270 1 ++ stretch dryKeyFull.1 18828 1).all fun x =>
    !roundB x.1 x.2 (2 ^ 65) 128) = true := by
  decide +kernel

end VerifiableInference.Desc.K13.Law
