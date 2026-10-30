-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Answers.lean: under three public premises, the instance's answer (oracle message
k, answer i, coordinate s) at dataOf data and readC c is coordinate s of the honest sender's answer
divided by its seed's factor.
Terms: Johnson/SendSim/At/Sim.lean; sender, readC, dataOf, wOf, name, the instance's answers,
RidesZero: Johnson/SendSim/At/Bridge.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves. Finite sums and coordinates; no distribution is named.
  ans_tie     If the job fits its place (sendFits), RidesZero (a table that is sent along has
              entries 0 in its 2 ^ h rows if its coins are all 0) holds and the challenge consists
              of exactly the seeds (seedsFit), then the instance's ansAt at the weights wOf, at
              dataOf data and readC c, at the name (k, i, s), is crd s (bInv i * yAt k i).
  yAt, bInv   the sender's answer i of oracle message k: the left-hand side of the answer's equation
              K1.sampleRow at the held words of rowsR data c; the inverse of the factor of seed i.
  msg_eq      If the job fits its place and RidesZero holds, the instance's messages at dataOf data
              and readC c are the entries of the sender's rows rowsR data c.
  form_rows   K1's closed form K1.Msg.form on an oracle message's entries, as a sum over rows and
              entries. No premise.
  form_at     The instance's linear form at an answer's weights reads only the rows of the answer's
              own oracle message. No premise.
  main_part, mask_part   If the job fits its place: what an oracle message's main rows, and its mask
              rows, contribute to the instance's answer.
  Wg, wOf_main, wOf_mask, wOf_ne   K1's weight of an entry at seed i; the weights wOf written out.
  crd_cell, cell_main, cell_mask, crd_mul_sum2   Tools on a coordinate of a product and of a sum.

Limits. RidesZero is a premise here; it holds for every ride (ridesZero,
Johnson/SendSim/At/RideLay.lean).

How it fits. Johnson/SendSim/At/Shown.lean uses ans_tie for shownTie, which serves rowsExact
(Johnson/SendSim/At/RowsExact.lean) and rowsFresh (Johnson/SendSim/At/RowsFresh.lean).
Johnson/SendSim/At/FormOne.lean and Johnson/SendSim/At/PadsOf.lean use form_rows, form_at, main_part
and mask_part. The proofs rest on value_stAt (Johnson/SendSim/At/Stat.lean), entry_split
(Johnson/SendSim/At/Split.lean), crd_mul (Johnson/SendSim/Tie/Coord.lean) and table_sum
(Johnson/SendSim/Tie/Sums.lean). K1.sampleRow is defined in Johnson/Desc/K1/Own.lean, K1.Msg.form in
Johnson/Desc/K1/Law/Law.lean, the held words (held) in Johnson/Prover/Send/Core.lean.

Notes. ans_tie does not require that a factor is not 0: at a factor 0 both sides are 0.
-/
import Johnson.Prover.Send.Held
import Johnson.SendSim.Tie.Sums
import Johnson.SendSim.At.Stat
import Johnson.SendSim.At.Seeds
import Johnson.SendSim.At.Symbols

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt held)

/-- K1's closed form K1.Msg.form on the entries of one oracle message (V.word s), as a sum over its
main rows and their entries plus a sum over its mask rows and their entries, each entry times K1's
weight at its index. -/
theorem form_rows (codes : Codes) (s : OracleShape) (V : Rows) (z : ℕ → GE) (β : GE) (i : ℕ) :
    (K1.Msg.of codes s).form z β i (V.word s) =
      (∑ r ∈ Finset.range s.mainRows,
        ∑ j ∈ Finset.range (2 ^ (codes.base.getD s.code default).logEll),
          (K1.Msg.of codes s).weight z β i .main (r + j * 2 ^ K1.clog s.mainRows) *
            V.main (s.mainDeg == 3) r j) +
      ∑ r ∈ Finset.range s.maskRows,
        ∑ j ∈ Finset.range (2 ^ (codes.mask.getD s.maskCode default).logEll),
          (K1.Msg.of codes s).weight z β i .mask (r + j * 2 ^ K1.clog s.maskRows) *
            V.mask r j := by
  unfold K1.Msg.form
  congr 1
  · by_cases h0 : s.mainRows = 0
    · have : (K1.Msg.of codes s).has .main = false := by
        show (s.mainRows != 0) = false
        simp [h0]
      rw [this, h0]
      simp
    · have h1 : (K1.Msg.of codes s).has .main = true := by
        show (s.mainRows != 0) = true
        simp [h0]
      have h2 : (K1.Msg.of codes s).bits .main =
          K1.clog s.mainRows + (codes.base.getD s.code default).logEll := by
        show (if (s.mainRows == 0) = true then 0 else
          K1.clog s.mainRows + (codes.base.getD s.code default).logEll) = _
        rw [if_neg (by simpa using h0)]
      rw [h1, if_pos rfl, h2, pow_add]
      exact table_sum s.mainRows (K1.clog s.mainRows) _ (K1.le_two_pow_clog' _) _ _
  · by_cases h0 : s.maskRows = 0
    · have : (K1.Msg.of codes s).has .mask = false := by
        show (s.maskRows != 0) = false
        simp [h0]
      rw [this, h0]
      simp
    · have h1 : (K1.Msg.of codes s).has .mask = true := by
        show (s.maskRows != 0) = true
        simp [h0]
      have h2 : (K1.Msg.of codes s).bits .mask =
          K1.clog s.maskRows + (codes.mask.getD s.maskCode default).logEll := by
        show (if (s.maskRows == 0) = true then 0 else
          K1.clog s.maskRows + (codes.mask.getD s.maskCode default).logEll) = _
        rw [if_neg (by simpa using h0)]
      rw [h1, if_pos rfl, h2, pow_add]
      exact table_sum s.maskRows (K1.clog s.maskRows) _ (K1.le_two_pow_clog' _) _ _

variable (P : K1.Par) (ride : Nat → Option Ride) (ds : List Fmt.Drawn)

/-- The inverse of the factor of the seed of answer number i (0 if the factor is 0). -/
def bInv (i : ℕ) : GE := (readE (seedAt P ds i).2)⁻¹

/-- K1's weight (K1.Msg.weight) of the entry with the index idx of oracle message k, in answer i, at
the seed of answer i. -/
def Wg (k i : ℕ) (part : Part) (idx : ℕ) : GE :=
  (K1.Msg.of P.codes (shapeAt P k)).weight (readL (seedAt P ds i).1) (readE (seedAt P ds i).2) i
    part idx

theorem wOf_main (k : Fin P.sent.size) (i : Fin (shapeAt P k).answers) (s : Fin 3)
    (r : Fin (shapeAt P k).mainRows) (t : Fin (dg P k)) (j : ℕ) :
    wOf P ds ⟨k, (i, s)⟩ ⟨k, .inl (r, t)⟩ j =
      crd s (bInv P ds i * (Wg P ds k i .main (r.val + j * 2 ^ K1.clog (shapeAt P k).mainRows) *
        readE (thetaE t.val))) := if_pos rfl

theorem wOf_mask (k : Fin P.sent.size) (i : Fin (shapeAt P k).answers) (s : Fin 3)
    (r : Fin (shapeAt P k).maskRows) (t : Fin 3) (j : ℕ) :
    wOf P ds ⟨k, (i, s)⟩ ⟨k, .inr (r, t)⟩ j =
      crd s (bInv P ds i * (Wg P ds k i .mask (r.val + j * 2 ^ K1.clog (shapeAt P k).maskRows) *
        readE (thetaE t.val))) := if_pos rfl

theorem wOf_ne (a : AnsN P) (ρ : RowN P) (j : ℕ) (h : ρ.1 ≠ a.1) : wOf P ds a ρ j = 0 := if_neg h

/-- Coordinate s of b * (W * y), as a sum over the three coordinates of y. -/
theorem crd_cell (s : Fin 3) (b W y : GE) :
    ∑ t : Fin 3, crd s (b * (W * readE (thetaE t.val))) * crd t y = crd s (b * (W * y)) := by
  rw [← mul_assoc b W y, crd_mul]
  exact Finset.sum_congr rfl fun t _ => by rw [mul_assoc]

theorem cell_mask (V : ℕ → Rows) (k : Fin P.sent.size) (r : Fin (shapeAt P k).maskRows) (j : ℕ)
    (s : Fin 3) (b W : GE) :
    ∑ t : Fin 3, crd s (b * (W * readE (thetaE t.val))) * entry P V ⟨k, .inr (r, t)⟩ j =
      crd s (b * (W * (V k).mask r.val j)) := crd_cell s b W _

theorem cell_main (V : ℕ → Rows) (k : Fin P.sent.size) (r : Fin (shapeAt P k).mainRows) (j : ℕ)
    (s : Fin 3) (b W : GE) :
    ∑ t : Fin (dg P k), crd s (b * (W * readE (thetaE t.val))) * entry P V ⟨k, .inl (r, t)⟩ j =
      crd s (b * (W * (V k).main ((shapeAt P k).mainDeg == 3) r.val j)) := by
  by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
  · obtain ⟨F, hF⟩ : ∃ F : ℕ → GF, F = fun t => crd s (b * (W * readE (thetaE t))) *
        crd (co t) ((V k).mainE r.val j) := ⟨_, rfl⟩
    have e : ∀ t : Fin (dg P k), crd s (b * (W * readE (thetaE t.val))) *
        entry P V ⟨k, .inl (r, t)⟩ j = F t.val := fun t => by
      rw [hF]
      show _ * (if (shapeAt P k).mainDeg == 3 then _ else _) = _
      rw [if_pos h3]
    rw [Finset.sum_congr rfl fun t _ => e t, Fin.sum_univ_eq_sum_range F (dg P k),
      dg_three P h3, ← Fin.sum_univ_eq_sum_range F 3, hF]
    simp only [co_fin]
    rw [crd_cell]
    unfold Rows.main
    rw [if_pos h3]
  · obtain ⟨F, hF⟩ : ∃ F : ℕ → GF, F = fun t => crd s (b * (W * readE (thetaE t))) *
        (V k).mainF r.val j := ⟨_, rfl⟩
    have e : ∀ t : Fin (dg P k), crd s (b * (W * readE (thetaE t.val))) *
        entry P V ⟨k, .inl (r, t)⟩ j = F t.val := fun t => by
      rw [hF]
      show _ * (if (shapeAt P k).mainDeg == 3 then _ else _) = _
      rw [if_neg h3]
    rw [Finset.sum_congr rfl fun t _ => e t, Fin.sum_univ_eq_sum_range F (dg P k),
      dg_one P h3, Finset.sum_range_one, hF]
    simp only [readE_theta_zero, mul_one]
    unfold Rows.main
    rw [if_neg h3, ← mul_assoc, mul_comm (b * W), crd_cast_mul, mul_comm]

/-- The instance's linear form at the weights of the answer a is a sum over the rows of a's own
oracle message and no others. -/
theorem form_at (a : AnsN P) (g : RowN P → ℕ → GF) :
    (sender P ride).form (wOf P ds a) g =
      ∑ v, ∑ j ∈ Finset.range (codeAt P ⟨a.1, v⟩).l, wOf P ds a ⟨a.1, v⟩ j * g ⟨a.1, v⟩ j := by
  unfold Sender.form
  show (∑ ρ : RowN P, ∑ j ∈ Finset.range (codeAt P ρ).l, wOf P ds a ρ j * g ρ j) = _
  rw [Fintype.sum_sigma, Finset.sum_eq_single a.1]
  · intro k' _ hne
    refine Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun j _ => ?_
    rw [wOf_ne P ds a ⟨k', v⟩ j hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem crd_mul_sum2 (s : Fin 3) (b : GE) (A B : Finset ℕ) (f : ℕ → ℕ → GE) :
    crd s (b * ∑ r ∈ A, ∑ j ∈ B, f r j) = ∑ r ∈ A, ∑ j ∈ B, crd s (b * f r j) := by
  rw [Finset.mul_sum, crd_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum, crd_sum]

/-- If the job fits its place (sendFits): what the main rows of oracle message k contribute to the
instance's answer (k, i, s), for any family of rows V, is coordinate s of bInv i times the sum of
K1's weights Wg times the entries of V k's main rows. -/
theorem main_part (hf : sendFits P ride = true) (V : ℕ → Rows) (k : Fin P.sent.size)
    (i : Fin (shapeAt P k).answers) (s : Fin 3) :
    ∑ x : Fin (shapeAt P k).mainRows × Fin (dg P k),
        ∑ j ∈ Finset.range (codeAt P ⟨k, .inl x⟩).l,
          wOf P ds ⟨k, (i, s)⟩ ⟨k, .inl x⟩ j * entry P V ⟨k, .inl x⟩ j =
      crd s (bInv P ds i * ∑ r ∈ Finset.range (shapeAt P k).mainRows,
        ∑ j ∈ Finset.range (2 ^ (P.codes.base.getD (shapeAt P k).code default).logEll),
          Wg P ds k i .main (r + j * 2 ^ K1.clog (shapeAt P k).mainRows) *
            (V k).main ((shapeAt P k).mainDeg == 3) r j) := by
  rw [crd_mul_sum2, Fintype.sum_prod_type, Finset.sum_range]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hm : (shapeAt P k).mainRows ≠ 0 := fun h0 => by
    have := r.isLt
    omega
  rw [two_logEll_base P.codes _ (fits_lengths P ride hf) (fits_code P ride k hf k.isLt hm)]
  show ∑ t : Fin (dg P k), ∑ j ∈ Finset.range (P.codes.base.getD (shapeAt P k).code default).ell,
    wOf P ds ⟨k, (i, s)⟩ ⟨k, .inl (r, t)⟩ j * entry P V ⟨k, .inl (r, t)⟩ j = _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [wOf_main]
  exact cell_main P V k r j s _ _

/-- The same for the mask rows of oracle message k. -/
theorem mask_part (hf : sendFits P ride = true) (V : ℕ → Rows) (k : Fin P.sent.size)
    (i : Fin (shapeAt P k).answers) (s : Fin 3) :
    ∑ x : Fin (shapeAt P k).maskRows × Fin 3,
        ∑ j ∈ Finset.range (codeAt P ⟨k, .inr x⟩).l,
          wOf P ds ⟨k, (i, s)⟩ ⟨k, .inr x⟩ j * entry P V ⟨k, .inr x⟩ j =
      crd s (bInv P ds i * ∑ r ∈ Finset.range (shapeAt P k).maskRows,
        ∑ j ∈ Finset.range (2 ^ (P.codes.mask.getD (shapeAt P k).maskCode default).logEll),
          Wg P ds k i .mask (r + j * 2 ^ K1.clog (shapeAt P k).maskRows) * (V k).mask r j) := by
  rw [crd_mul_sum2, Fintype.sum_prod_type, Finset.sum_range]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hm : (shapeAt P k).maskRows ≠ 0 := fun h0 => by
    have := r.isLt
    omega
  rw [two_logEll_mask P.codes _ (fits_lengths P ride hf) (fits_maskCode P ride k hf k.isLt hm)]
  show ∑ t : Fin 3, ∑ j ∈ Finset.range (P.codes.mask.getD (shapeAt P k).maskCode default).ell,
    wOf P ds ⟨k, (i, s)⟩ ⟨k, .inr (r, t)⟩ j * entry P V ⟨k, .inr (r, t)⟩ j = _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [wOf_mask]
  exact cell_mask P V k r j s _ _

variable (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c : Cs (dueR P ride))

/-- If the job fits its place (sendFits) and RidesZero holds, the instance's messages at dataOf data
and readC c are the entries of the sender's rows rowsR data c. -/
theorem msg_eq (hf : sendFits P ride = true) (hR : RidesZero ride) :
    (sender P ride).msg (dataOf P ride data) (readC P ride c) =
      entry P (rowsR P ride data c) :=
  funext fun ρ => funext fun j => (entry_split P ride c data hf hR ρ j).symm

/-- The honest sender's answer i of oracle message k: the left-hand side of the answer's equation
K1.sampleRow, at the statement stAt P first and the held words of the rows rowsR data c. -/
def yAt (first k i : ℕ) : GE :=
  Means.value rdE (stAt P first)
    (K1.sampleRow (K1.Msg.of P.codes (shapeAt P k)) (first + k) (seedAt P ds i).1
      (seedAt P ds i).2 i zeroE)
    (held (fun _ _ _ => 0) first P (rowsR P ride data c))

/-- If the job fits its place (sendFits), RidesZero holds and the challenge consists of exactly the
seeds (seedsFit), the instance's answer with the name (k, i, s), at dataOf data and readC c, is
coordinate s of the sender's answer yAt times the inverse of its seed's factor. -/
theorem ans_tie (hf : sendFits P ride = true) (hR : RidesZero ride) (hs : seedsFit P ds = true)
    (first : ℕ) (k : Fin P.sent.size) (i : Fin (shapeAt P k).answers) (s : Fin 3) :
    (sender P ride).ansAt (wOf P ds) (dataOf P ride data) (readC P ride c) ⟨k, (i, s)⟩ =
      crd s (bInv P ds i * yAt P ride ds data c first k i) := by
  unfold Sender.ansAt yAt
  rw [msg_eq P ride data c hf hR, form_at, Fintype.sum_sum_type,
    main_part P ride ds hf _ k i s, mask_part P ride ds hf _ k i s,
    value_stAt P first k k.isLt _ _ _ _ _ (has_table P ride hf k k.isLt)
      (v_le_len P ds hs k i k.isLt i.isLt)]
  have hw : held (fun _ _ _ => 0) first P (rowsR P ride data c) (first + k) =
      (rowsR P ride data c k).word (shapeAt P k) :=
    funext fun part => funext fun idx => Johnson.Prover.Send.held_new _ first P _ k k.isLt part idx
  rw [hw, form_rows, mul_add, crd_add]
  rfl

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.form_rows
#print axioms OnBytes.SendSim.At.ans_tie
