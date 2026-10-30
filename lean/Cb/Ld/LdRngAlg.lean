-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRngAlg.lean: the approximate range check with packing and reads: its plain mathematics,
without any protocol.

This file has the counting argument of an approximate range proof: a test, by |U| random
combinations with coefficients in {-1, 0, 1}, that the entries of a matrix over a ring pack integers
of small absolute value, and that a second matrix is W times these integers, for weight vectors W
that are a parameter.

Definitions and statements (Cb.Spec.rngPk_*); the proofs are in Cb/Ld/LdRngAlgProofs.lean.
It generalizes Cb/Gen/RngAlg.lean (one cell an element, no reads) and Alg/Range.lean (three cells an
element): the number P of rows that are packed into one and the radix ϱ are parameters.

The objects. E: a commutative ring of characteristic p. A cell is an integer. The cells form a
matrix Y with rows (i, l), i a packed row (Rp), l < P a lane, and columns C.
  `pack ϱ y i`: the P lanes of the packed row i in one element: ∑_l ϱ^l · y (i, l).
  `PackBy b ϱ Y mpk`: all cells have absolute value below b, and mpk, a matrix over E with rows Rp,
    is the packing of Y.
  `ReadBy W Y mrd`: mrd, a matrix over E with rows Rd (the reads), is W · Y. W: one weight vector
    over E on the rows of cells for each read; any weight vectors.
  `RngBy b ϱ W Y mpk mrd`, `Rng b ϱ W mpk mrd`: the predicate, on two components (mpk, mrd):
    `PackBy` and `ReadBy` for the same integer matrix Y; with Y named, and "there is Y".
  `cells P b ϱ mpk`: the virtual matrix of cells: the Y with `PackBy b ϱ Y mpk` (a choice; it is
    unique under the two conditions `Uniq b ϱ P p`), the matrix 0 if there is none. Nobody sends it.

The test. The verifier draws Θ: |U| vectors of |C| coefficients in {-1, 0, 1}, independent, 0 with
probability 1/2 and each sign with probability 1/4 (`Prob.Coef`: two uniform bits). The prover
names, for every row of cells and every u, two digits at the radix q (low below q, high below H,
q H = 2 D).
  `psi D q d r u`: low + q · high - D: what the digits stand for.
  `Rows ..`: mpk · Θ_u = pack (psi · u) for every packed row, and mrd · Θ_u = W · (psi · u) for
    every read. (Packing and reads act on rows, Θ on columns.) (|Rp| + |Rd|) · |U| equations, linear
    in mpk, mrd and the digits, with public targets.
  `Out ..`: `InTabs` (all digits are in their tables) and `Rows`: what holds after the test.

Main names:
Soundness goes by joint columns of (mpk; mrd).
  `Writes ϱ W y sym tab`: the integers y are behind the joint column (sym; tab): sym is their
    packing, tab their reads.
  `GoodCol b ..`: some y of absolute values below b is behind the column. `CanPass D .. cf`: some z
    in the window [-D, D) is behind the combination of the columns with the coefficients cf.
  `Spec.rngPk_good_of_two`: if a combination can pass with 0 at a column and also with +1 or -1
    there, the other coefficients being the same, then that column is good at the bound 2 D: the
    difference of the two z, up to the sign, is behind it.
  `Spec.rngPk_cnt_out`: for q H = 2 D, if `Rng (2 D)` fails, then for at most the fraction 2^(-|U|)
    of the Θ there are digits with `Out`. One error for the range, the packing and the tie of the
    reads to the cells. No condition on ϱ, P, p, W.
  `Spec.rngPk_tight`: the bound is met with equality by an example, for every |U|.
The honest side. `hdig D q Y Θ`: the digits of the integer combinations Y · Θ_u.
`Spec.rngPk_honest`: for 0 < q, q H = 2 D and `RngBy b ϱ W Y mpk mrd`, outside the window event
(`Cb.Rng.Event`: an entry of some combination leaves [-D, D)) they satisfy `Out`. The probability of
the event: Cb/Gen/RngAlg.lean's `pr_event_le` and `event_empty`, unchanged, with the rows of cells
as rows.
Virtual cells.
  `Spec.rngPk_unique`: under `Uniq`: two integer columns of absolute values below b with the same
    packing in E are equal.

Limits: this file says nothing on oracles, codes, decoding. It says nothing on the lookup that
checks the digits. A number of rows of cells that is no multiple of P is filled up: the last lanes
are cells like the others. The digits are not packed.
That a relaxed Y times Θ equals psi over the integers is not claimed and is false in general: the
combination of a relaxed Y may overflow the radix. The proof does not go that way.
The test is the field's approximate range proof with ternary coefficients; packing, reads and the
proof by joint columns follow this protocol's technical report, which follows the paper that this
protocol builds on and advice (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.RngAlg
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.RngPk
open Prob Finset Cb.Rng

/-- P lanes in one element, at the radix ϱ. -/
def pack {A Rp : Type} [CommRing A] {P : ℕ} (ϱ : ℤ) (y : Rp × Fin P → A) (i : Rp) : A :=
  ∑ l : Fin P, (ϱ : A) ^ (l : ℕ) * y (i, l)

/-- The two conditions under which the packing determines the cells. -/
def Uniq (b ϱ : ℤ) (P p : ℕ) : Prop := 2 * b - 2 < ϱ ∧ (2 * b - 2) * ∑ l ∈ range P, ϱ ^ l < p

section
variable {E Rp Rd C U : Type} [CommRing E] [Fintype Rp] {P : ℕ}

/-- All cells are below b in absolute value, and mpk is their packing. -/
def PackBy (b ϱ : ℤ) (Y : Rp × Fin P → C → ℤ) (mpk : Rp → C → E) : Prop :=
  (∀ r c, |Y r c| < b) ∧ ∀ i c, mpk i c = pack ϱ (fun r => ((Y r c : ℤ) : E)) i

/-- The reads are the weight vectors times the cells. -/
def ReadBy (W : Rd → Rp × Fin P → E) (Y : Rp × Fin P → C → ℤ) (mrd : Rd → C → E) : Prop :=
  ∀ k c, mrd k c = ∑ r, W k r * ((Y r c : ℤ) : E)

/-- The predicate, with the integer matrix named. -/
def RngBy (b ϱ : ℤ) (W : Rd → Rp × Fin P → E) (Y : Rp × Fin P → C → ℤ)
    (mpk : Rp → C → E) (mrd : Rd → C → E) : Prop :=
  PackBy b ϱ Y mpk ∧ ReadBy W Y mrd

/-- The predicate on the two components. -/
def Rng (b ϱ : ℤ) (W : Rd → Rp × Fin P → E) (mpk : Rp → C → E) (mrd : Rd → C → E) : Prop :=
  ∃ Y, RngBy b ϱ W Y mpk mrd

/-- The predicate without reads. -/
def Packed (P : ℕ) (b ϱ : ℤ) (mpk : Rp → C → E) : Prop := ∃ Y : Rp × Fin P → C → ℤ, PackBy b ϱ Y mpk

open Classical in
/-- The virtual matrix of cells. -/
def cells (P : ℕ) (b ϱ : ℤ) (mpk : Rp → C → E) : Rp × Fin P → C → ℤ :=
  if h : Packed P b ϱ mpk then h.choose else fun _ _ => 0

/-- The integers y are behind the joint column (sym; tab). -/
def Writes (ϱ : ℤ) (W : Rd → Rp × Fin P → E) (y : Rp × Fin P → ℤ) (sym : Rp → E) (tab : Rd → E) :
    Prop :=
  (∀ i, sym i = pack ϱ (fun r => ((y r : ℤ) : E)) i) ∧ ∀ k, tab k = ∑ r, W k r * ((y r : ℤ) : E)

/-- A good joint column. -/
def GoodCol (b ϱ : ℤ) (W : Rd → Rp × Fin P → E) (sym : Rp → E) (tab : Rd → E) : Prop :=
  ∃ y, (∀ r, |y r| < b) ∧ Writes ϱ W y sym tab

/-- A combination of the joint columns can pass. -/
def CanPass [Fintype C] (D ϱ : ℤ) (W : Rd → Rp × Fin P → E) (mpk : Rp → C → E)
    (mrd : Rd → C → E) (cf : C → ℤ) : Prop :=
  ∃ z,
    (∀ r, -D ≤ z r ∧ z r < D) ∧
    Writes ϱ W z (fun i => ∑ c, (cf c : E) * mpk i c) (fun k => ∑ c, (cf c : E) * mrd k c)

/-- the digits: low, high; one pair for each row of cells and each combination -/
abbrev Dig (E Rp : Type) (P : ℕ) (U : Type) : Type := (Rp × Fin P → U → E) × (Rp × Fin P → U → E)

/-- what the digits stand for -/
def psi (D : ℤ) (q : ℕ) (d : Dig E Rp P U) (r : Rp × Fin P) (u : U) : E :=
  d.1 r u + (q : E) * d.2 r u - (D : E)

/-- All digits are in their tables. -/
def InTabs (q H : ℕ) (d : Dig E Rp P U) : Prop :=
  (∀ r u, InTab q (d.1 r u)) ∧ ∀ r u, InTab H (d.2 r u)

/-- The rows. -/
def Rows [Fintype C] (D ϱ : ℤ) (q : ℕ) (W : Rd → Rp × Fin P → E) (Θ : U → C → Coef)
    (mpk : Rp → C → E) (mrd : Rd → C → E) (d : Dig E Rp P U) : Prop :=
  (∀ i u, ∑ c, (((Θ u c).val : ℤ) : E) * mpk i c = pack ϱ (fun r => psi D q d r u) i) ∧
  ∀ k u, ∑ c, (((Θ u c).val : ℤ) : E) * mrd k c = ∑ r, W k r * psi D q d r u

/-- What holds after the test. -/
def Out [Fintype C] (D ϱ : ℤ) (q H : ℕ) (W : Rd → Rp × Fin P → E) (Θ : U → C → Coef)
    (mpk : Rp → C → E) (mrd : Rd → C → E) (d : Dig E Rp P U) : Prop :=
  InTabs q H d ∧ Rows D ϱ q W Θ mpk mrd d

/-- The honest digits. -/
def hdig [Fintype C] (D : ℤ) (q : ℕ) (Y : Rp × Fin P → C → ℤ) (Θ : U → C → Coef) : Dig E Rp P U :=
  (fun r u => ((lo D q (comb (Y r) (Θ u)) : ℕ) : E),
    fun r u => ((hi D q (comb (Y r) (Θ u)) : ℕ) : E))

end
end Cb.RngPk

namespace Cb.Spec
open Prob Finset Cb.Rng Cb.RngPk

/-- Unique packing. -/
def rngPk_unique : Prop :=
  ∀ (E : Type) [CommRing E] (p : ℕ) [CharP E p] (Rp : Type) (P : ℕ)
      (b ϱ : ℤ) (y y' : Rp × Fin P → ℤ),
    Uniq b ϱ P p → (∀ r, |y r| < b) → (∀ r, |y' r| < b) →
    (∀ i, pack ϱ (fun r => ((y r : ℤ) : E)) i = pack ϱ (fun r => ((y' r : ℤ) : E)) i) → y = y'

/-- For E of characteristic p, under the two conditions (`Uniq b ϱ P p`) the virtual matrix is the
matrix that was packed, at any bound b' ≤ b. -/
def rngPk_cells : Prop :=
  ∀ (E : Type) [CommRing E] (p : ℕ) [CharP E p] (Rp C : Type) [Fintype Rp] (P : ℕ) (b b' ϱ : ℤ)
      (Y : Rp × Fin P → C → ℤ) (mpk : Rp → C → E),
    Uniq b ϱ P p → b' ≤ b → PackBy b' ϱ Y mpk → cells P b ϱ mpk = Y

/-- For E of characteristic p, under the two conditions (`Uniq b ϱ P p`) the predicate speaks of the
virtual matrix. -/
def rngPk_iff_cells : Prop :=
  ∀ (E : Type) [CommRing E] (p : ℕ) [CharP E p] (Rp Rd C : Type) [Fintype Rp] (P : ℕ) (b ϱ : ℤ)
      (W : Rd → Rp × Fin P → E) (mpk : Rp → C → E) (mrd : Rd → C → E),
    Uniq b ϱ P p → (Rng b ϱ W mpk mrd ↔ Packed P b ϱ mpk ∧ ReadBy W (cells P b ϱ mpk) mrd)

/-- A larger bound is a weaker predicate. -/
def rngPk_mono : Prop :=
  ∀ (E : Type) [CommRing E] (Rp Rd C : Type) [Fintype Rp] (P : ℕ) (b b' ϱ : ℤ)
      (W : Rd → Rp × Fin P → E) (Y : Rp × Fin P → C → ℤ) (mpk : Rp → C → E) (mrd : Rd → C → E),
    b' ≤ b → RngBy b' ϱ W Y mpk mrd → RngBy b ϱ W Y mpk mrd

/-- The plain case: one lane, no reads. -/
def rngPk_plain : Prop :=
  ∀ (E : Type) [CommRing E] (Rp C : Type) [Fintype Rp] (b ϱ : ℤ) (W : Empty → Rp × Fin 1 → E)
      (mpk : Rp → C → E) (mrd : Empty → C → E),
    Rng b ϱ W mpk mrd ↔ ∀ i c, Short b (mpk i c)

/-- The predicate holds if and only if every joint column is good. -/
def rngPk_iff_cols : Prop :=
  ∀ (E : Type) [CommRing E] (Rp Rd C : Type) [Fintype Rp] (P : ℕ) (b ϱ : ℤ)
      (W : Rd → Rp × Fin P → E) (mpk : Rp → C → E) (mrd : Rd → C → E),
    Rng b ϱ W mpk mrd ↔ ∀ c, GoodCol b ϱ W (fun i => mpk i c) (fun k => mrd k c)

/-- One joint column, two coefficients. -/
def rngPk_good_of_two : Prop :=
  ∀ (E : Type) [CommRing E] (Rp Rd C : Type) [Fintype Rp] [Fintype C] [DecidableEq C]
      (P : ℕ) (D ϱ : ℤ) (W : Rd → Rp × Fin P → E) (mpk : Rp → C → E) (mrd : Rd → C → E)
      (cf : C → ℤ) (c₀ : C) (e : ℤ),
    e = 1 ∨ e = -1 → CanPass D ϱ W mpk mrd (Function.update cf c₀ 0) →
    CanPass D ϱ W mpk mrd (Function.update cf c₀ e) →
    GoodCol (2 * D) ϱ W (fun i => mpk i c₀) (fun k => mrd k c₀)

/-- If the predicate fails at 2 D, all combinations can pass for at most the fraction 2^(-|U|) of
the challenges. -/
def rngPk_cnt_pass : Prop :=
  ∀ (E : Type) [CommRing E] (Rp Rd C U : Type) [Fintype Rp] [Fintype C] [DecidableEq C]
      [Fintype U] [DecidableEq U] (P : ℕ) (D ϱ : ℤ) (W : Rd → Rp × Fin P → E)
      (mpk : Rp → C → E) (mrd : Rd → C → E),
    ¬ Rng (2 * D) ϱ W mpk mrd →
    cnt (fun Θ : U → C → Coef => ∀ u, CanPass D ϱ W mpk mrd fun c => (Θ u c).val) *
        2 ^ Fintype.card U ≤
      Fintype.card (U → C → Coef)

/-- For q H = 2 D: digits in their tables that satisfy the rows: every combination can pass. Error
0. -/
def rngPk_pass_of_out : Prop :=
  ∀ (E : Type) [CommRing E] (Rp Rd C U : Type) [Fintype Rp] [Fintype C] (P : ℕ) (D ϱ : ℤ)
      (q H : ℕ) (W : Rd → Rp × Fin P → E) (Θ : U → C → Coef) (mpk : Rp → C → E)
      (mrd : Rd → C → E) (d : Dig E Rp P U),
    (q : ℤ) * H = 2 * D → Out D ϱ q H W Θ mpk mrd d →
    ∀ u, CanPass D ϱ W mpk mrd fun c => (Θ u c).val

/-- Soundness of the draw: for q H = 2 D, if the predicate fails at 2 D, digits with `Out` exist for
at most the fraction 2^(-|U|) of the challenges. -/
def rngPk_cnt_out : Prop :=
  ∀ (E : Type) [CommRing E] (Rp Rd C U : Type) [Fintype Rp] [Fintype C] [DecidableEq C]
      [Fintype U] [DecidableEq U] (P : ℕ) (D ϱ : ℤ) (q H : ℕ) (W : Rd → Rp × Fin P → E)
      (mpk : Rp → C → E) (mrd : Rd → C → E),
    (q : ℤ) * H = 2 * D → ¬ Rng (2 * D) ϱ W mpk mrd →
    cnt (fun Θ : U → C → Coef => ∃ d, Out D ϱ q H W Θ mpk mrd d) * 2 ^ Fintype.card U ≤
      Fintype.card (U → C → Coef)

/-- The bound is met with equality: over the integers, one cell with the value 2, D = 1. -/
def rngPk_tight : Prop :=
  ∀ (U : Type) [Fintype U] [DecidableEq U],
    ¬ Rng (E := ℤ) (Rp := Unit) (Rd := Empty) (C := Unit) (P := 1) (2 * 1) 1 (fun k => k.elim)
      (fun _ _ => 2) (fun k => k.elim) ∧
    cnt (fun Θ : U → Unit → Coef =>
          ∃ d, Out (E := ℤ) (Rp := Unit) (Rd := Empty) (P := 1) 1 1 2 1 (fun k => k.elim) Θ
            (fun _ _ => 2) (fun k => k.elim) d) *
        2 ^ Fintype.card U =
      Fintype.card (U → Unit → Coef)

/-- The honest digits, outside the window event.
(not all hypotheses are named here: see the statement below) -/
def rngPk_honest : Prop :=
  ∀ (E : Type) [CommRing E] (Rp Rd C U : Type) [Fintype Rp] [Fintype C] (P : ℕ) (b D ϱ : ℤ)
      (q H : ℕ) (W : Rd → Rp × Fin P → E) (Y : Rp × Fin P → C → ℤ) (Θ : U → C → Coef)
      (mpk : Rp → C → E) (mrd : Rd → C → E),
    0 < q → (q : ℤ) * H = 2 * D → RngBy b ϱ W Y mpk mrd →
    ¬ Event D Y Θ → Out D ϱ q H W Θ mpk mrd (hdig D q Y Θ)

end Cb.Spec
