-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRng2Alg.lean: the approximate range check with packing and reads, with a number of digits of
one width and one table: its plain mathematics, without any protocol.

This file states the count of the approximate range check in which each entry of each random
combination, plus D, is written in nd digits of wd bits, all in one table [0, 2^wd).

Definitions and statements (Cb.Spec.rng2_*); the proofs are in Cb/Ld/LdRng2AlgProofs.lean.
Cb/Ld/LdRngAlg.lean has two digits of two kinds for each combination (low below q, high below H,
q H = 2 D). In a write-up of ours that is not in this repository (lean/CREDITS.md; the later of its
two forms of the digits) a combination is written in a number nd of digits of one width wd:
    2 D = 2^(wd · nd);
    what the digits stand for: ∑_{i < nd} 2^(wd · i) · digit_i - D;
    one table: [0, 2^wd).
Neither form is a case of the other. All that does not mention digits in Cb/Ld/LdRngAlg.lean holds
here unchanged and is not defined anew: `PackBy`, `ReadBy`, `Rng`, `cells`, `Uniq`, `Writes`,
`GoodCol`, `CanPass`, and the count `rngPk_cnt_pass`.
In that file's words: A cell is an integer. The cells form a matrix Y with rows (i, l), i a packed
row (Rp), l < P a lane, and columns C.
  `pack ϱ y i`: the P lanes of the packed row i in one element: ∑_l ϱ^l · y (i, l).
  `PackBy b ϱ Y mpk`: all cells have absolute value below b, and mpk, a matrix over E with rows Rp,
    is the packing of Y.
  `ReadBy W Y mrd`: mrd, a matrix over E with rows Rd (the reads), is W · Y. W: one weight vector
    over E on the rows of cells for each read; any weight vectors.
  `RngBy b ϱ W Y mpk mrd`, `Rng b ϱ W mpk mrd`: the predicate, on two components (mpk, mrd):
    `PackBy` and `ReadBy` for the same integer matrix Y; with Y named, and "there is Y".
  The verifier draws Θ: |U| vectors of |C| coefficients in {-1, 0, 1}, independent, 0 with
    probability 1/2 and each sign with probability 1/4 (`Prob.Coef`: two uniform bits).

Main names:
  `Dig2 E Rp P U nd`: the digits: one for each row of cells, each combination and each i < nd.
  `Rows2`, `Out2`: the rows (linear in the packed matrix, the reads and the digits, with public
    targets); what holds after the test.
  `Spec.rng2_lt`: digits below 2^wd: their value is below 2^(wd · nd).
  `Spec.rng2_digits`: a natural number below 2^(wd · nd) is the value of its nd digits; each digit
    is below 2^wd.
  `Spec.rng2_cnt_out`: soundness of the draw: for 2 D = 2^(wd · nd), if the predicate `Rng` fails at
    2 D, digits with `Out2` exist for at most the fraction 2^(-|U|) of the challenges. The relaxed
    bound is 2 D = 2^(wd · nd).
  `Spec.rng2_honest`: for 2 D = 2^(wd · nd) and `RngBy b ϱ W Y mpk mrd`, the honest digits satisfy
    `Out2` outside the window event (an entry of some combination leaves [-D, D)).

Limits: this file says nothing on oracles, codes, decoding. It says nothing on the lookup that
checks the digits. That lookup's keys are all digits, padded with 0 to a power of two; 0 is in the
table.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRngAlg

set_option autoImplicit false

namespace Cb.RngPk
open Prob Finset Cb.Rng

section
variable {E Rp Rd C U : Type} [CommRing E] [Fintype Rp] {P nd : ℕ}

/-- the digits -/
abbrev Dig2 (E Rp : Type) (P : ℕ) (U : Type) (nd : ℕ) : Type := Rp × Fin P → U → Fin nd → E

/-- what the digits stand for -/
def psi2 (D : ℤ) (wd : ℕ) (d : Dig2 E Rp P U nd) (r : Rp × Fin P) (u : U) : E :=
  ∑ i : Fin nd, ((2 ^ (wd * (i : ℕ)) : ℕ) : E) * d r u i - (D : E)

/-- All digits are in the table. -/
def InTabs2 (wd : ℕ) (d : Dig2 E Rp P U nd) : Prop := ∀ r u i, InTab (2 ^ wd) (d r u i)

/-- The rows. -/
def Rows2 [Fintype C] (D ϱ : ℤ) (wd : ℕ) (W : Rd → Rp × Fin P → E) (Θ : U → C → Coef)
    (mpk : Rp → C → E) (mrd : Rd → C → E) (d : Dig2 E Rp P U nd) : Prop :=
  (∀ i u, ∑ c, (((Θ u c).val : ℤ) : E) * mpk i c = pack ϱ (fun r => psi2 D wd d r u) i) ∧
  ∀ k u, ∑ c, (((Θ u c).val : ℤ) : E) * mrd k c = ∑ r, W k r * psi2 D wd d r u

/-- What holds after the test. -/
def Out2 [Fintype C] (D ϱ : ℤ) (wd : ℕ) (W : Rd → Rp × Fin P → E) (Θ : U → C → Coef)
    (mpk : Rp → C → E) (mrd : Rd → C → E) (d : Dig2 E Rp P U nd) : Prop :=
  InTabs2 wd d ∧ Rows2 D ϱ wd W Θ mpk mrd d

/-- the i-th digit at the radix 2^wd -/
def dig2 (wd i n : ℕ) : ℕ := n / 2 ^ (wd * i) % 2 ^ wd

/-- The honest digits. -/
def hdig2 [Fintype C] (D : ℤ) (wd : ℕ) (Y : Rp × Fin P → C → ℤ) (Θ : U → C → Coef) :
    Dig2 E Rp P U nd :=
  fun r u i => ((dig2 wd i (comb (Y r) (Θ u) + D).toNat : ℕ) : E)

end
end Cb.RngPk

namespace Cb.Spec
open Prob Finset Cb.Rng Cb.RngPk

def rng2_lt : Prop :=
  ∀ (wd nd : ℕ) (a : Fin nd → ℕ),
    (∀ i, a i < 2 ^ wd) → ∑ i : Fin nd, 2 ^ (wd * (i : ℕ)) * a i < 2 ^ (wd * nd)

def rng2_digits : Prop :=
  ∀ (wd nd n : ℕ), n < 2 ^ (wd * nd) →
    (∑ i : Fin nd, 2 ^ (wd * (i : ℕ)) * dig2 wd i n = n) ∧ ∀ i, dig2 wd i n < 2 ^ wd

/-- For 2 D = 2^(wd · nd): digits in the table that satisfy the rows: every combination can pass.
Error 0. -/
def rng2_pass_of_out : Prop :=
  ∀ (E : Type) [CommRing E] (Rp Rd C U : Type) [Fintype Rp] [Fintype C] (P nd : ℕ) (D ϱ : ℤ)
      (wd : ℕ) (W : Rd → Rp × Fin P → E) (Θ : U → C → Coef) (mpk : Rp → C → E)
      (mrd : Rd → C → E) (d : Dig2 E Rp P U nd),
    2 * D = ((2 ^ (wd * nd) : ℕ) : ℤ) → Out2 D ϱ wd W Θ mpk mrd d →
    ∀ u, CanPass D ϱ W mpk mrd fun c => (Θ u c).val

/-- Soundness of the draw. -/
def rng2_cnt_out : Prop :=
  ∀ (E : Type) [CommRing E] (Rp Rd C U : Type) [Fintype Rp] [Fintype C] [DecidableEq C]
      [Fintype U] [DecidableEq U] (P nd : ℕ) (D ϱ : ℤ) (wd : ℕ) (W : Rd → Rp × Fin P → E)
      (mpk : Rp → C → E) (mrd : Rd → C → E),
    2 * D = ((2 ^ (wd * nd) : ℕ) : ℤ) → ¬ Rng (2 * D) ϱ W mpk mrd →
    cnt (fun Θ : U → C → Coef => ∃ d : Dig2 E Rp P U nd, Out2 D ϱ wd W Θ mpk mrd d) *
        2 ^ Fintype.card U ≤
      Fintype.card (U → C → Coef)

/-- The honest digits, outside the window event.
(not all hypotheses are named here: see the statement below) -/
def rng2_honest : Prop :=
  ∀ (E : Type) [CommRing E] (Rp Rd C U : Type) [Fintype Rp] [Fintype C] (P nd : ℕ) (b D ϱ : ℤ)
      (wd : ℕ) (W : Rd → Rp × Fin P → E) (Y : Rp × Fin P → C → ℤ) (Θ : U → C → Coef)
      (mpk : Rp → C → E) (mrd : Rd → C → E),
    2 * D = ((2 ^ (wd * nd) : ℕ) : ℤ) → RngBy b ϱ W Y mpk mrd → ¬ Event D Y Θ →
    Out2 D ϱ wd W Θ mpk mrd (hdig2 (nd := nd) D wd Y Θ)

end Cb.Spec
