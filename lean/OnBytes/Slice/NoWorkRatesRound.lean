-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/NoWorkRatesRound.lean: what the bounds at the exponent 128 ask of a written round that
has no test bits.

The written link is the link between two stored tables as an interactive protocol in the format's
types (OnBytes/Slice/README.md has the vocabulary). The files OnBytes/Slice/NoWorkRates….lean bound
the error count of a round.
They are stated for a round that is a variable.
This file gathers in one record what they ask of such a round, so that a description's round meets
them by four small evaluations. A round's challenge values are its written verifier messages
(`(wRound d).Chal`): for a round without test bits, all strings of its hash blocks.

Main definition.
 `NwRound d ds B`   the written round d draws the list ds, has B hash blocks and no test bit, and
                  its positions have at most 64 bits.
Main theorems.
 `NwRound.of_plan`  the number of hash blocks may be given as the format's plan counts it.
 `nVals_repE`, `nVals_elems`   the typed values of a run of n elements: q^n, for q the size of the
                  extension field.
 `nw_entry`         the written round's count e * w is at most 2^-128 as a share of the round's
                  challenge values, from a share n / D that bounds e among the typed values and one
                  comparison of natural numbers.

What this file does not claim: it claims no number, and not that any description has such rounds.
The bound speaks of one round: it is no bound on the chance of a false proof.
-/
import OnBytes.Slice.RatesNum
import OnBytes.Slice.RatesToy

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Run
open scoped ENNReal

/-- What the bounds ask of a written round d: it draws the list ds, it has B hash blocks and no
test bit, and its positions have at most 64 bits. -/
structure NwRound (d : PQ.RD) (ds : List Fmt.Draw) (B : ℕ) : Prop where
  /-- The round's positions have at most 64 bits. -/
  log : d.entry.logN ≤ 64
  /-- What the round draws. -/
  draws : Fmt.dsOf d.entry d.kind = ds
  /-- The round's number of hash blocks. -/
  blocks : (bsRound .two d.entry d.kind).b = B
  /-- The round has no test bit. -/
  noWork : d.entry.work = 0

/-- The same, with the number of hash blocks as the format's plan counts it from the entry. -/
theorem NwRound.of_plan (d : PQ.RD) (ds : List Fmt.Draw) (B : ℕ) (hlog : d.entry.logN ≤ 64)
    (hds : Fmt.dsOf d.entry d.kind = ds)
    (hB : Fmt.blocksFor (Fmt.wordsAtMost d.entry d.kind) = B) (hw : d.entry.work = 0) :
    NwRound d ds B :=
  ⟨hlog, hds, (planDraws_law .two d.entry d.kind hlog).2.trans hB, hw⟩

/-- The typed values of a run of n elements, and of what is drawn after them. -/
theorem nVals_repE (n : ℕ) (rest : List Fmt.Draw) :
    nVals (List.replicate n Fmt.Draw.elem ++ rest) = (Fmt.Fld.two.p ^ 3) ^ n * nVals rest := by
  induction n with
  | zero => rw [pow_zero, one_mul]; rfl
  | succ n ih =>
      show Fmt.Fld.two.p ^ 3 * nVals (List.replicate n Fmt.Draw.elem ++ rest) = _
      rw [ih]
      generalize Fmt.Fld.two.p ^ 3 = P
      rw [pow_succ, mul_comm (P ^ n) P, mul_assoc]

/-- A run of n elements, then an empty draw of matrix entries: q^n typed values. -/
theorem nVals_elems (n : ℕ) :
    nVals (List.replicate n Fmt.Draw.elem ++ [.trits 0]) = Fintype.card GE ^ n := by
  rw [nVals_repE, nVals_end, mul_one, card_GE]

/-- The clause on the error count e of a round without test bits, at 2^-128: e * w is at most 2^-128
times the number of the round's challenge values (w: the sampler's bound on how many challenge
values go to one typed value). n / D: a share that bounds e among the typed values. -/
theorem nw_entry {d : PQ.RD} {ds : List Fmt.Draw} {B : ℕ} (hd : NwRound d ds B) (e n D : ℕ)
    (hD : 0 < D) (h : e * D ≤ n * nVals ds)
    (hnum : (2 ^ 128 + 1) ^ B * n * 2 ^ 128 ≤ (2 ^ 128) ^ B * D * 2 ^ 0) :
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 128 * (Fintype.card (wRound d).Chal : ℝ≥0∞) :=
  entry_pow d hd.log e n D B 0 128 hd.blocks hd.noWork hD (hd.draws.symm ▸ h) hnum

end OnBytes.Slice

#print axioms OnBytes.Slice.NwRound.of_plan
#print axioms OnBytes.Slice.nVals_repE
#print axioms OnBytes.Slice.nVals_elems
#print axioms OnBytes.Slice.nw_entry
