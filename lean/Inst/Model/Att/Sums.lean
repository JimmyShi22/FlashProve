-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Att/Sums.lean: the eight sumchecks of an attention segment: hypercubes, summands,
  public weights. Definitions, and one theorem on the numbers at the reference parameters
  (`ref_steps`).

  The steps are those of a table that is not shown in this file. (At1), (At2) are the identities
  `Idn.at1`, `Idn.at2` of Inst/Model/Att/Trace.lean. The public weights are coefficients that the
  verifier computes from the challenges.
  * `Step`: the seven batched sumchecks. `Step.g`: the number of variables. A point ξ is a function
    on ℕ, most significant bit first.
  All of it is defined for t : Raw → E, any content of the cells, and any values of the challenges.

  Notation:
    `D`: `Dim` (Inst/Model/Att/Index.lean): the sizes of an attention segment
    g, P, n (doc comments of `Dim.nG`, `Dim.hP`, `Dim.ch`, there): natural numbers: key/value heads
      g; rows P of region M; channels n
    I, J, s (`Dim.nBlk`, there): natural numbers: blocks I, J of positions; s also runs below nBlk
    i', j'; i, j (`Dim.B`, `Dim.T`, there): natural numbers: positions i', j' in a block; positions
      i, j
    b (`Dim.nb`, there): natural numbers: pairs b = na λ + a of a layer λ of the segment and the
      number a of a query head among those of its key/value head
    `Reg.M`, `Reg.D`: the two regions (Inst/Model/Att/Trace.lean; told in the head of
      Inst/Model/Att/Index.lean)
    `C`: `Calls` (Inst/Model/Att/Trace.lean): the numbers of the main lookup argument: call c has
      2^(a c) indices (a call: the head of that file)
    `wp u b`: an element of E (Inst/Model/Att/Points.lean): the weight of the piece (u, b)
    `uM`, `uD`, `uW`: `ℕ → E` (there): u^M = (z_g | z_P | z_s | z_i' | z_j'), the inner point of
      1M; u^D = (z̄_g | z̄_I | z_i' | z_j'), of 1D (what is not shown of both: their doc comments
      there); (z_χ | y_g | y_i | y_n), of 3W; y_i = (y_I | y_i')
    `sel` (Inst/Model/Att/Trace.lean): an element of E: sel_b[g, i, n] = ∑_j key_λ[g, j, n] ∏_k
    eq1(ib_(b,k)[g, i], bit_k(j))
-/
import Inst.Model.Att.Points
import Blocks.LookupRel

set_option autoImplicit false

namespace Inst.Model.AttSeg

open Finset Blocks

variable {E : Type} [Field E]

/-- eq(u, ξ) for two points of n coordinates -/
def eqPt (n : ℕ) (u ξ : ℕ → E) : E := ∏ k ∈ range n, eq1 (u k) (ξ k)

/-- the point (u | v), u of n coordinates -/
def cat (n : ℕ) (u v : ℕ → E) : ℕ → E := fun t => if t < n then u t else v (t - n)

/-- the number of bits of the index k of a bit of a position, in step 21 (4 at the reference
parameters) -/
def Dim.lK (D : Dim) : ℕ := Nat.clog 2 D.lT

/-- The challenges on which the summands depend. -/
structure Pub (E : Type) where
  /-- the end point of the product tree over the looked-up values of the main lookup argument -/
  z : ℕ → E
  /-- step 9: ϑ -/
  th : E
  /-- step 13: t_g, t_i test (At2); t̄_i, t̄_g, t_k test (At1) -/
  tg : ℕ → E
  ti : ℕ → E
  tbi : ℕ → E
  tbg : ℕ → E
  tk : ℕ → E
  /-- steps 15, 17, 20: o_b, o'_b, o''_b -/
  o : ℕ → E
  o' : ℕ → E
  o'' : ℕ → E
  /-- the end point (f_i | f_g | f_n) of step 16 -/
  fi : ℕ → E
  fg : ℕ → E
  fn : ℕ → E

/-- the seven batched sumchecks -/
inductive Step
  | s6b
  | s6d
  | s8
  | s11
  | s12
  | s16
  | s21
  deriving DecidableEq

section Summands
variable (D : Dim) (C : Calls) (p : Pub E) (t : Raw → E)

/-- the number of variables (at the reference parameters: 17, 14, 13, 16, 13, 20, 17) -/
def Step.g : Step → ℕ
  | .s6b => D.lg + D.lP + (D.lP + 1) + D.ln
  | .s6d => D.lg + (D.lP + 1) + D.ln
  | .s8 => D.lg + D.lT
  | .s11 => D.lg + D.lP + (D.lP + 1) + D.lB
  | .s12 => D.lg + (D.lP + 1) + D.lB
  | .s16 => D.lT + D.lg + D.ln
  | .s21 => D.lT + D.lg + D.lK

/-- ∑_n eq(v, n) a[n] over the channels -/
def conN (v : ℕ → E) (a : ℕ → E) : E := ∑ n ∈ range D.ch, eqN D.ln 0 v n * a n
/-- ∑_i' eq(v, i') a[i'] over the positions of a block -/
def conB (v : ℕ → E) (a : ℕ → E) : E := ∑ i' ∈ range D.B, eqN D.lB 0 v i' * a i'

/-- A_b on the hypercube, at the vertex X. -/
def Acube : Step → ℕ → ℕ → E
  | .s6b, b, X =>   -- (g | P | s | n)
      if X / D.ch % D.nBlk < D.nBlk - 1 then
        conB D (zi' D C p.z) fun i' =>
          qryV t b (X / D.ch / D.nBlk / D.hP)
            (D.B * D.rowBlk (X / D.ch / D.nBlk % D.hP) (X / D.ch % D.nBlk) + i') (X % D.ch)
      else 0
  | .s6d, b, X =>   -- (g | I | n)
      conB D (zi' D C p.z) fun i' =>
        qryV t b (X / D.ch / D.nBlk) (D.B * (X / D.ch % D.nBlk) + i') (X % D.ch)
  | .s8, b, X =>    -- (g | i)
      denV t b (X / D.T) (X % D.T)
  | .s11, b, X =>   -- (g | P | s | j')
      conB D (yi' D C p.z) fun i' =>
        wtV t .M b
          (D.codeM (X / D.B / D.nBlk / D.hP) (X / D.B / D.nBlk % D.hP)
            (X / D.B % D.nBlk) i' (X % D.B))
  | .s12, b, X =>   -- (g | I | j')
      conB D (yi' D C p.z) fun i' =>
        wtV t .D b (D.codeD (X / D.B / D.nBlk) (X / D.B % D.nBlk) i' (X % D.B))
  | .s16, b, X =>   -- (i | g | n)
      qryV t b (X / D.ch % D.nG) (X / D.ch / D.nG) (X % D.ch)
  | .s21, b, X =>   -- (i | g | k)
      if X % 2 ^ D.lK < D.lT then ibV t (X % 2 ^ D.lK) b (X / 2 ^ D.lK % D.nG) (X / 2 ^ D.lK / D.nG)
      else 0

/-- B_b on the hypercube, at the vertex X. -/
def Bcube : Step → ℕ → ℕ → E
  | .s6b, b, X =>
      if X / D.ch % D.nBlk < D.nBlk - 1 then
        conB D (zj' D C p.z) fun j' =>
          keyV t (D.lamOf b) (X / D.ch / D.nBlk / D.hP)
            (D.B * D.colBlk (X / D.ch / D.nBlk % D.hP) (X / D.ch % D.nBlk) + j') (X % D.ch)
      else 0
  | .s6d, b, X =>
      conB D (zj' D C p.z) fun j' =>
        keyV t (D.lamOf b) (X / D.ch / D.nBlk) (D.B * (X / D.ch % D.nBlk) + j') (X % D.ch)
  | .s8, b, X =>
      conN D (yn D C p.z) fun n => outV t b (X / D.T) (X % D.T) n
  | .s11, b, X =>
      if X / D.B % D.nBlk < D.nBlk - 1 then
        p.th + conN D (yn D C p.z) fun n =>
            valV t (D.lamOf b) (X / D.B / D.nBlk / D.hP)
              (D.B * D.colBlk (X / D.B / D.nBlk % D.hP) (X / D.B % D.nBlk) + X % D.B) n
      else p.th
  | .s12, b, X =>
      p.th + conN D (yn D C p.z) fun n =>
          valV t (D.lamOf b) (X / D.B / D.nBlk) (D.B * (X / D.B % D.nBlk) + X % D.B) n
  | .s16, b, X =>
      sel D t b (X / D.ch % D.nG) (X / D.ch / D.nG) (X % D.ch)
  | .s21, b, X =>
      Acube D C p t .s21 b X - 1

/-- The public weight W_b, a multilinear polynomial in ξ; it is constant in the variables that its
formula does not name. -/
def Wb : Step → ℕ → (ℕ → E) → E
  | .s6b, b, ξ =>   -- ξ = (ξ_g | ξ_P | ξ_s | ξ_n)
      wp D C p.z .m1 b * eqPt D.lg (zg D C p.z) ξ * eqPt D.lP (zP D C p.z) (sh ξ D.lg) *
        (eqPt (D.lP + 1) (zs D C p.z) (sh ξ (D.lg + D.lP)) -
          ones (D.lP + 1) (zs D C p.z) * ones (D.lP + 1) (sh ξ (D.lg + D.lP)))
  | .s6d, b, ξ =>   -- (ξ_g | ξ_I | ξ_n)
      wp D C p.z .d1 b * eqPt D.lg (zgD D C p.z) ξ * eqPt (D.lP + 1) (zID D C p.z) (sh ξ D.lg)
  | .s8, b, ξ =>    -- (ξ_g | ξ_i)
      wp D C p.z .w3 b * eqPt D.lg (yg D C p.z) ξ * eqPt D.lT (yi D C p.z) (sh ξ D.lg)
  | .s11, b, ξ =>   -- (ξ_g | ξ_P | ξ_s | ξ_j)
      wp D C p.z .w3 b * eqPt D.lg (yg D C p.z) ξ *
        ∑ P ∈ range D.hP, ∑ s ∈ range (D.nBlk - 1), eqN D.lP 0 (sh ξ D.lg) P *
          eqN (D.lP + 1) 0 (sh ξ (D.lg + D.lP)) s * eqN (D.lP + 1) 0 (yI D C p.z) (D.rowBlk P s)
  | .s12, b, ξ =>   -- (ξ_g | ξ_I | ξ_j)
      wp D C p.z .w3 b * eqPt D.lg (yg D C p.z) ξ * eqPt (D.lP + 1) (yI D C p.z) (sh ξ D.lg)
  | .s16, b, ξ =>   -- (ξ_i | ξ_g | ξ_n)
      p.o b * eqPt D.lg p.tg (sh ξ D.lT) * eqPt D.lT p.ti ξ
  | .s21, b, ξ =>   -- (ξ_i | ξ_g | ξ_k)
      p.o'' b * eqPt D.lT p.tbi ξ * eqPt D.lg p.tbg (sh ξ D.lT) *
        eqPt D.lK p.tk (sh ξ (D.lT + D.lg))

/-- ~A_b(ξ), the multilinear extension of A_b -/
def Aext (s : Step) (b : ℕ) (ξ : ℕ → E) : E := ext (s.g D) (Acube D C p t s b) ξ
/-- ~B_b(ξ), the multilinear extension of B_b -/
def Bext (s : Step) (b : ℕ) (ξ : ℕ → E) : E := ext (s.g D) (Bcube D C p t s b) ξ

/-- The summand Φ_s(ξ) = ∑_b W_b(ξ) ~A_b(ξ) ~B_b(ξ). -/
def Phi (s : Step) (ξ : ℕ → E) : E :=
  ∑ b ∈ range D.nb, Wb D C p s b ξ * Aext D C p t s b ξ * Bext D C p t s b ξ

/-- the sum of the summand over its hypercube -/
def sumPhi (s : Step) : E := ∑ X ∈ range (2 ^ s.g D), Phi D C p t s (cubePt (s.g D) X)

/-! ### Step 18 -/

/-- kc_λ[g, j] = ∑_n eq(f_n, n) key_λ[g, j, n], at the index (g | j) -/
def kc (lam X : ℕ) : E := conN D p.fn fun n => keyV t lam (X / D.T) (X % D.T) n

/-- The summand of step 18, at ξ = (X_j | X_g | X_i):
eq(f_i, X_i) eq(f_g, X_g) ∑_b o'_b ~kc_λ(b)(X_g, X_j) ∏_k eq1(~ib_(b,k)(X_g, X_i), X_(j,k)), where
X_(j,k) is the variable of X_j that belongs to the bit of weight 2^k. -/
def Phi18 (ξ : ℕ → E) : E :=
  eqPt D.lT p.fi (sh ξ (D.lT + D.lg)) * eqPt D.lg p.fg (sh ξ D.lT) *
    ∑ b ∈ range D.nb, p.o' b * ext (D.lg + D.lT) (kc D p t (D.lamOf b)) (cat D.lg (sh ξ D.lT) ξ) *
      ∏ k ∈ range D.lT, eq1
        (ext (D.lg + D.lT) (fun X => ibV t k b (X / D.T) (X % D.T)) (sh ξ D.lT)) (ξ (D.lT - 1 - k))

/-- the number of variables of step 18 -/
def g18 : ℕ := D.lT + D.lg + D.lT

/-! ### Functions of an entry and of a row -/

/-- sp_b(x): the score at an entry of M, 0 at an empty entry; sp^D_b(x): at an entry of D -/
def sp : Reg → ℕ → ℕ → E
  | .M, b, x => if D.EmptyM x then 0 else scV D t b (D.mG x) (D.iM x) (D.jM x)
  | .D, b, x => scV D t b (D.dG x) (D.iD x) (D.jD x)

/-- qs_b[g, i] = ∑_n qry_b[g, i, n] sel_b[g, i, n], at the index (g | i) -/
def qs (b X : ℕ) : E :=
  ∑ n ∈ range D.ch, qryV t b (X / D.T) (X % D.T) n * sel D t b (X / D.T) (X % D.T) n

/-! ### Contractions of arrays: what a read represents -/

/-- ∑_(g, i) eq(v_g, g) Ψ[i] a[g, i] -/
def rd2 (vg Ψ : ℕ → E) (a : ℕ → ℕ → E) : E :=
  ∑ g ∈ range D.nG, ∑ i ∈ range D.T, eqN D.lg 0 vg g * Ψ i * a g i
/-- ∑_(g, i, n) eq(v_g, g) Ψ[i] eq(v_n, n) a[g, i, n] -/
def rd3 (vg Ψ vn : ℕ → E) (a : ℕ → ℕ → ℕ → E) : E :=
  ∑ g ∈ range D.nG,
    ∑ i ∈ range D.T, ∑ n ∈ range D.ch, eqN D.lg 0 vg g * Ψ i * eqN D.ln 0 vn n * a g i n
/-- the equality vector of a point over the positions -/
def eqT (v : ℕ → E) : ℕ → E := eqN D.lT 0 v

end Summands

theorem ref_steps :
    ([Step.s6b, .s6d, .s8, .s11, .s12, .s16, .s21].map fun s => s.g Dim.ref) =
      [17, 14, 13, 16, 13, 20, 17] ∧
    g18 Dim.ref = 23 ∧ Dim.ref.lK = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end Inst.Model.AttSeg
