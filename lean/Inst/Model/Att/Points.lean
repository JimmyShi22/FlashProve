-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Att/Points.lean: the evaluation points of an attention segment and its public weights
  (coefficients that the verifier computes from the challenges; not the model's weights).
  Definitions, and two theorems on the numbers at the reference parameters (`ref_fam`, `ref_deep`).

  Numbering. A point is a function on ℕ, and coordinate 0 belongs to the most significant bit
  (`eqN`, Blocks/Basic.lean; `ext`, Blocks/Ext.lean). In the main lookup argument the product tree
  over the looked-up values (keys in Lean names) ends at z = (z_in | z_tr): the coordinates 0, ..,
  `C.Dk` - 1 of z are z_in, the coordinates `C.Dk`, .., `C.Dk` + σ - 1 are z_tr
  (Blocks/LookupCalls.lean); σ is `C.sg`. Calls, trees, families and pieces of looked-up values are
  defined in Inst/Model/Att/Trace.lean.
  * `Fam`: the seven families of looked-up values, each with its call, the number of bits of its
    inner index and the number of the block at which its first piece starts. `wp`: the weight of the
    piece (u, b).
  * `ones`, `idP`, `LE`: the multilinear extensions of [x = 2^g - 1], of x ↦ x and of [x ≤ y]
    (that they are: `ones_eq`, as the equality weight of the last index, `ext_id`, `ext_le`:
    Cube.lean, Tools.lean, LessEq.lean in Inst/Model/Att/KeyFormsExt/).
  * `psiRow`, `psiCol`: the weights on the positions that come from a point on the pairs (P, s).
    They are not equality vectors.
  * z̄g, z̄I are `zgD`, `zID` in the code.

  Notation:
    1M, 1D, 2M, 2D, 3W, 3X, 4: the families `Fam.m1`, `Fam.d1`, `Fam.m2`, `Fam.d2`, `Fam.w3`,
      `Fam.x3`, `Fam.f4`; the digit is the family's call, counted from 1; `Fam.call` counts from 0;
    `C.a c`, a_c (`Calls`, Inst/Model/Att/Trace.lean): a natural number: call c has 2^(a c) indices;
    `C.trees c`, `C.first c` (Inst/Model/Att/Trace.lean): natural numbers: the number of trees of a
      call, and its first tree;
    ℓ, `Fam.l`: a natural number: a piece of the family has 2^ℓ keys; `Fam.nu0`: a natural number:
      piece b of the family is block number nu0 + b (the ν of `wp`), in blocks of 2^ℓ keys, of its
      call;
    `D.lg`, `D.lP`, `D.lB` (`Dim`, Inst/Model/Att/Index.lean): numbers of bits: 2^lg key/value
      heads; 2^lP rows P of region M; 2^lB positions in a block;
    P, s (Inst/Model/Att/Index.lean): natural numbers: rows P of region M (`Dim.hP`); s also runs
      below nBlk (`Dim.nBlk`: blocks I, J of positions).
-/
import Inst.Model.Att.Trace
import Blocks.Ext

set_option autoImplicit false

namespace Inst.Model.AttSeg

open Finset Blocks

variable {E : Type} [Field E]

/-- the part of a point from the coordinate off on -/
def sh (u : ℕ → E) (off : ℕ) : ℕ → E := fun t => u (off + t)

namespace Calls
variable (C : Calls)

/-- call c has 2^e trees -/
def e (c : Fin 4) : ℕ := C.a c - C.Dk
/-- their numbers are pre 2^e + τ, τ < 2^e, if 2^e divides `C.first c` (`Calls.OK.aligned`) -/
def pre (c : Fin 4) : ℕ := C.first c / C.trees c

/-- the key point of call c: z_c = (the last e coordinates of z_tr | z_in), a_c coordinates -/
def zC (c : Fin 4) (z : ℕ → E) (t : ℕ) : E :=
  if t < C.e c then z (C.Dk + (C.sg - C.e c) + t) else z (t - C.e c)

/-- the weight of call c: w_c = eq(the first σ - e coordinates of z_tr, pre) -/
def wC (c : Fin 4) (z : ℕ → E) : E := eqN (C.sg - C.e c) C.Dk z (C.pre c)

end Calls

/-- The seven families of looked-up values. -/
inductive Fam
  | m1
  | d1
  | m2
  | d2
  | w3
  | x3
  | f4
  deriving DecidableEq

namespace Fam
variable (D : Dim)

/-- the call of a family -/
def call : Fam → Fin 4
  | .m1 => 0
  | .d1 => 0
  | .m2 => 1
  | .d2 => 1
  | .w3 => 2
  | .x3 => 2
  | .f4 => 3

/-- ℓ: a piece of the family has 2^ℓ keys -/
def l : Fam → ℕ
  | .m1 => D.lM
  | .d1 => D.lD
  | .m2 => D.lM
  | .d2 => D.lD
  | .w3 => D.lW
  | .x3 => D.lX
  | .f4 => D.l4

/-- piece b of the family is block number nu0 + b, in blocks of 2^ℓ keys, of its call (at the
reference parameters: 0, 160, 0, 160, 0, 5,120, 0) -/
def nu0 : Fam → ℕ
  | .m1 => 0
  | .d1 => D.nb * 2 ^ (D.lM - D.lD)
  | .m2 => 0
  | .d2 => D.nb * 2 ^ (D.lM - D.lD)
  | .w3 => 0
  | .x3 => D.nb * 2 ^ (D.lW - D.lX)
  | .f4 => 0

end Fam

section Pieces
variable (D : Dim) (C : Calls) (z : ℕ → E)

/-- The weight of the piece (u, b): eq(the first a_c - ℓ coordinates of z_c, ν) -/
def wp (u : Fam) (b : ℕ) : E := eqN (C.a u.call - u.l D) 0 (C.zC u.call z) (u.nu0 D + b)

/-- The inner point of a family: the last ℓ coordinates of z_c -/
def inn (u : Fam) : ℕ → E := sh (C.zC u.call z) (C.a u.call - u.l D)

/-- L^u = ∑_b wp^u_b -/
def LL (u : Fam) : E := ∑ b ∈ range D.nb, wp D C z u b

/-! ### The parts of the inner points -/

/-- u^M = (z_g | z_P | z_s | z_i' | z_j'), the inner point of 1M; that it is also that of 2M is not
shown in this file -/
def uM : ℕ → E := inn D C z .m1
def zg : ℕ → E := sh (uM D C z) 0
def zP : ℕ → E := sh (uM D C z) D.lg
def zs : ℕ → E := sh (uM D C z) (D.lg + D.lP)
def zi' : ℕ → E := sh (uM D C z) (D.lg + D.lP + (D.lP + 1))
def zj' : ℕ → E := sh (uM D C z) (D.lg + D.lP + (D.lP + 1) + D.lB)
/-- u^D = (z̄_g | z̄_I | z_i' | z_j'), the inner point of 1D; that it is also that of 2D is not
proved in this library; that its last coordinates are z_i', z_j' (`zi'`, `zj'` are cut from u^M) is
not shown in this file -/
def uD : ℕ → E := inn D C z .d1
def zgD : ℕ → E := sh (uD D C z) 0
def zID : ℕ → E := sh (uD D C z) D.lg
/-- (z_χ | y_g | y_i | y_n), the inner point of 3W; y_i = (y_I | y_i') -/
def uW : ℕ → E := inn D C z .w3
def zChi : E := uW D C z 0
def yg : ℕ → E := sh (uW D C z) 1
def yi : ℕ → E := sh (uW D C z) (1 + D.lg)
def yI : ℕ → E := sh (uW D C z) (1 + D.lg)
def yi' : ℕ → E := sh (uW D C z) (1 + D.lg + (D.lP + 1))
def yn : ℕ → E := sh (uW D C z) (1 + D.lg + D.lT)
/-- (x_g | x_i), the inner point of 3X -/
def uX : ℕ → E := inn D C z .x3
def xg : ℕ → E := sh (uX D C z) 0
def xi : ℕ → E := sh (uX D C z) D.lg
/-- the inner point of 4; that it is (y_g | y_i | y_n) is not proved in this library -/
def u4 : ℕ → E := inn D C z .f4

end Pieces

/-! ### Three functions of points -/

/-- ones(u) = ∏_k u_k, the extension of [x = 2^g - 1] -/
def ones (g : ℕ) (u : ℕ → E) : E := ∏ k ∈ range g, u k
/-- id(u) = ∑_k 2^(g-k) u_k (k from 1), the extension of x ↦ x -/
def idP (g : ℕ) (u : ℕ → E) : E := ∑ k ∈ range g, 2 ^ (g - 1 - k) * u k
/-- LE(u, v), the multilinear extension in all 2 g variables of [x ≤ y]: LE_(g+1) = 1 and LE_k = (1
- u_k) v_k + eq1(u_k, v_k) LE_(k+1) -/
def LE : ℕ → (ℕ → E) → (ℕ → E) → E
  | 0, _, _ => 1
  | g + 1, u, v => (1 - u 0) * v 0 + eq1 (u 0) (v 0) * LE g (sh u 1) (sh v 1)

/-! ### Position weights from blocks -/

section Psi
variable (D : Dim) (vP vs v : ℕ → E)

/-- the weight of the block I as a row block: ∑ over the pairs (P, s), s < 2 hP - 1, with I(P, s) =
I, of eq(v_P, P) eq(v_s, s) -/
def blkRow (I : ℕ) : E :=
  ∑ P ∈ range D.hP, ∑ s ∈ range (D.nBlk - 1), if D.rowBlk P s = I then
    eqN D.lP 0 vP P * eqN (D.lP + 1) 0 vs s
  else 0
/-- `blkRow` for the block J as a column block -/
def blkCol (J : ℕ) : E :=
  ∑ P ∈ range D.hP, ∑ s ∈ range (D.nBlk - 1), if D.colBlk P s = J then
    eqN D.lP 0 vP P * eqN (D.lP + 1) 0 vs s
  else 0
/-- Ψ_row[v_P, v_s; v][B I + i'] = eq(v, i') · (the weight of I as a row block) -/
def psiRow (i : ℕ) : E := eqN D.lB 0 v (i % D.B) * blkRow D vP vs (i / D.B)
/-- Ψ_col[v_P, v_s; v][B J + j'] = eq(v, j') · (the weight of J as a column block) -/
def psiCol (j : ℕ) : E := eqN D.lB 0 v (j % D.B) * blkCol D vP vs (j / D.B)

end Psi

/-! ## The numbers at the reference parameters -/

theorem ref_fam :
    (Fam.l Dim.ref .m1, Fam.l Dim.ref .d1, Fam.l Dim.ref .w3,
        Fam.l Dim.ref .x3, Fam.l Dim.ref .f4) =
      (22, 19, 21, 13, 20) ∧
    (Fam.nu0 Dim.ref .d1, Fam.nu0 Dim.ref .x3) = (160, 5120) ∧
    ((List.finRange 4).map fun c => (Calls.ref.e c, Calls.ref.pre c)) =
      [(2, 0), (2, 1), (1, 4), (0, 10)] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- At the reference parameters an inner index is not longer than the index in a tree, calls 1 and 2
have the same size, and a piece of M fits into call 1. -/
theorem ref_deep :
    (∀ u : Fam, u.l Dim.ref ≤ Calls.ref.Dk) ∧
    Calls.ref.a 0 = Calls.ref.a 1 ∧
    Dim.ref.lM ≤ Calls.ref.a 0 := by
  refine ⟨fun u => ?_, ?_, ?_⟩
  · cases u <;> decide +kernel
  · decide +kernel
  · decide +kernel

end Inst.Model.AttSeg
