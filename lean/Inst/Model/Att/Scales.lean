-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Att/Scales.lean: an attention segment whose layers have their own scales and tables, at
  any valid input shift of the exponential.

  Why. The statement `Spec.honest` (Inst/Model/Att/Trace.lean) is at the reference sizes, with one
  set of tables, and at `ppref` with the scales in scope (`refP`); it is proved for scales that are
  valid for attention: one shift in the segment, 2,307 live rows. A model whose scales are fitted to
  its weights has a scale of each kind for each layer (Inst/Model/Program.lean: `LayerScale`,
  `Params.at`), among them the input shift sh of the exponential, which the implementation allows
  in 4 .. 12. Here the statements on the segment are given for every size D within the reference
  sizes, every valid pair (D.sh, D.u0), and parameters and tables that may differ from layer to
  layer of the segment:
  * `SizeOK D`: at most 128 channels, at most 1,024 positions; the shift and the live rows are valid
    (`ExpOK`).
  * `ExpTab D tb`: (Tab8) for the segment's table: 1 ≤ Exp[u] ≤ 2^12 for u < u0, Exp[0] = 2^12.
  * `noWrapK` (Inst/Model/Bound/AttK.lean): from the field relation to the program, one layer: the
    layer's parameters P fit D (sizes, P.sh = D.sh, P.expRows = D.u0); the layer's tables have the
    segment's exponential. `outBoundK` (same file): the bound on the output. (not all hypotheses are
    named here: see `noWrapK`, `outBoundK`)
  * `honK`, `honestK`: the honest trace from the program run with the layers' own parameters and
    tables satisfies the relation over the integers, with cells of at most 128, under `SizeOK`,
    `ExpTab`, hF, hX.
  * `D5`, `scl5`, `sizeOK_5`, `calls_ok_5`: guards: the conditions on the sizes have an instance
    other than the reference: at the reference sizes with sh = 5 and 1,000 live rows `SizeOK` holds,
    and so do the conditions on the calls of the lookup argument. These two numbers are made up;
    they are fitted to nothing. (A synthetic table Exp and the statements on the relation at this
    instance: not in this library.) `sizeOK_ref`: `SizeOK` at the reference sizes, for all valid
    scales.
  Notation:
    `D.u0` (`Dim`, Inst/Model/Att/Index.lean): a natural number: the number of live rows of the
      table Exp;
    `D.sh` (Inst/Model/Att/Index.lean): a natural number: the input shift of the exponential;
    b, g, i, j, n, lam (Inst/Model/Att/Index.lean): natural numbers: pairs b = na λ + a of a layer λ
      of the segment and the number a of a query head among those of its key/value head (`Dim.nb`);
      key/value heads g (`Dim.nG`); positions i, j (`Dim.T`); channels n (`Dim.ch`); lam: a layer of
      the segment (`Dim.nl`);
    `Scl` (Inst/Model/Scl.lean): a class: the scales of one segment, and the final normalisation;
    `Lawful` (Inst/Model/Att/Trace.lean): a proposition: the scales of the segment are valid for
      attention;
    `ExpOK sh u0` (Inst/Model/Tables.lean): a proposition: the valid shifts and numbers of rows in
      use;
    `NW2.Fit D P` (Inst/Model/Att/NoWrap2.lean), `Hon.Fit D P` (Inst/Model/Att/Honest.lean):
      propositions: ch and na (positive), the number of live rows and the shift are those of P;
    `Adm` (Inst/Model/Att/HonestGen.lean): a proposition: what is asked of the inputs, the sizes and
      the table.
  Limits. Nothing on a segment whose layers have different shifts (the implementation then makes one
  call for each value; this folder has four calls). Nothing on the chain: the closed chain is at
  `Dim.ref` and `tbRef`.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Att.NoWrap2
import Inst.Model.Att.Honest

set_option autoImplicit false

namespace Inst.Model.AttSeg

open Finset

/-- at most 128 channels and 1,024 positions, and the shift and the live rows of the exponential are
valid -/
structure SizeOK [scl : Scl] (D : Dim) : Prop where
  ch : D.ch ≤ 128
  lT : D.lT ≤ 10
  T : D.T ≤ 1024
  ex : ExpOK D.sh D.u0

/-- (Tab8) for the table of the segment -/
structure ExpTab (D : Dim) (tb : Tables) : Prop where
  rng : ∀ u : ℕ, u < D.u0 → 1 ≤ tb.Exp u ∧ tb.Exp u ≤ 2 ^ 12
  zero : tb.Exp 0 = 2 ^ 12

/-! ## The honest trace -/

namespace Hon

variable (D : Dim) (Ps : ℕ → Params) (tbs : ℕ → Tables) (tb : Tables) (w : ℕ → LayerW) (L0 : ℕ) (x : ℕ → ℕ → Vec)

/-- the program's q, kx, v, o at the indices of the segment; layer lam of the segment runs at Ps lam
and tbs lam -/
def QpK (b g i n : ℕ) : ℤ :=
  Att.q (Ps (D.lamOf b)) (tbs (D.lamOf b)) (w (D.lamOf b)) (L0 + D.lamOf b) (x (D.lamOf b))
    i (D.ch * D.head g b + n)
def KpK (lam g j n : ℕ) : ℤ := Att.kx (Ps lam) (tbs lam) (w lam) (L0 + lam) (x lam) j (D.ch * g + n)
def VpK (lam g j n : ℕ) : ℤ := Att.v (Ps lam) (w lam) (x lam) j (D.ch * g + n)
def OpK (b g i n : ℕ) : ℤ :=
  Att.o (Ps (D.lamOf b)) (tbs (D.lamOf b)) (w (D.lamOf b)) (L0 + D.lamOf b) (x (D.lamOf b))
    i (D.ch * D.head g b + n)

/-- The honest trace, from the program run with the layers' own parameters and tables. tb: the
tables of the segment's lookup argument. -/
def honK [scl : Scl] : Raw → ℤ :=
  honG D tb (QpK D Ps tbs w L0 x) (KpK D Ps tbs w L0 x) (VpK D Ps w x) (OpK D Ps tbs w L0 x)

variable {D Ps tbs tb}

section Link
variable [scl : Scl]
variable (hF : ∀ lam, Fit D (Ps lam)) (hX : ∀ lam, (tbs lam).Exp = tb.Exp)
include hF

local notation "Q'" => QpK D Ps tbs w L0 x
local notation "K'" => KpK D Ps tbs w L0 x
local notation "V'" => VpK D Ps w x
local notation "O'" => OpK D Ps tbs w L0 x

theorem scK_eq (b g i : ℕ) :
    Att.sc (Ps (D.lamOf b)) (tbs (D.lamOf b)) (w (D.lamOf b)) (L0 + D.lamOf b)
        (x (D.lamOf b)) (D.head g b) i =
      scP D Q' K' b g i := by
  funext j
  unfold Att.sc scP QpK KpK
  rw [(hF _).kvOf, (hF _).ch]

theorem mxK_eq (b g i : ℕ) :
    Att.mx (Ps (D.lamOf b)) (tbs (D.lamOf b)) (w (D.lamOf b)) (L0 + D.lamOf b)
        (x (D.lamOf b)) (D.head g b) i =
      mxP D Q' K' b g i := by
  unfold Att.mx mxP
  rw [scK_eq w L0 x hF b g i]

include hX in
theorem wtK_eq (b g i j : ℕ) :
    Att.wt (Ps (D.lamOf b)) (tbs (D.lamOf b)) (w (D.lamOf b)) (L0 + D.lamOf b)
        (x (D.lamOf b)) (D.head g b) i j =
      wtP D tb Q' K' b g i j := by
  unfold Att.wt Att.u wtP
  rw [mxK_eq w L0 x hF b g i, congrFun (scK_eq w L0 x hF b g i) j, (hF _).rows,
    (hF _).sh, hX, wOf_eq_wt]

include hX in
theorem denK_eq (b g i : ℕ) :
    Att.den (Ps (D.lamOf b)) (tbs (D.lamOf b)) (w (D.lamOf b)) (L0 + D.lamOf b)
        (x (D.lamOf b)) (D.head g b) i =
      denP D tb Q' K' b g i := by
  unfold Att.den denP
  exact sum_congr rfl fun j _ => wtK_eq w L0 x hF hX b g i j

include hX in
theorem acK_eq (b g i n : ℕ) :
    Att.ac (Ps (D.lamOf b)) (tbs (D.lamOf b)) (w (D.lamOf b)) (L0 + D.lamOf b)
        (x (D.lamOf b)) (D.head g b) i n =
      acP D tb Q' K' V' b g i n := by
  unfold Att.ac acP
  refine sum_congr rfl fun j _ => ?_
  rw [wtK_eq w L0 x hF hX b g i j, (hF _).kvOf, (hF _).ch]
  rfl

include hX in
/-- (PA7) at a channel of a head -/
theorem outK_eq (b g i : ℕ) {n : ℕ} (hn : n < D.ch) :
    O' b g i n =
      (2 * acP D tb Q' K' V' b g i n + denP D tb Q' K' b g i) / (2 * denP D tb Q' K' b g i) := by
  have hpos : 0 < D.ch := Nat.two_pow_pos _
  have e1 : (D.ch * D.head g b + n) / D.ch = D.head g b := by
    rw [Nat.mul_comm]
    exact (Dim.div_step hpos hn).1
  have e2 : (D.ch * D.head g b + n) % D.ch = n := by
    rw [Nat.mul_comm]
    exact (Dim.div_step hpos hn).2
  rw [← acK_eq w L0 x hF hX, ← denK_eq w L0 x hF hX]
  unfold OpK Att.o
  rw [(hF _).ch, e1, e2]

include hX in
theorem admK (hD : SizeOK D) (hT : ExpTab D tb) : Adm D tb Q' K' V' O' where
  q := fun _ _ _ _ => abs_clamp_le (by norm_num) _
  k := fun _ _ _ _ => abs_clamp_le (by norm_num) _
  v := fun _ _ _ _ => abs_clamp_le (by norm_num) _
  o := fun b g i _ hn => outK_eq w L0 x hF hX b g i hn
  ch := by
    have : (D.ch : ℤ) ≤ 128 := by exact_mod_cast hD.ch
    unfold Smax
    nlinarith
  T := hD.T
  ex := hD.ex
  exp := hT.rng
  exp0 := hT.zero

include hX in
/-- Under `SizeOK`, `ExpTab`, hF, hX: the honest trace satisfies the relation, over the integers,
with cells of absolute value at most 128. -/
theorem honestK (hD : SizeOK D) (hT : ExpTab D tb) :
    RFraw D tb ℤ (honK D Ps tbs tb w L0 x) ∧
    ∀ c : Raw, c.Valid D → |honK D Ps tbs tb w L0 x c| ≤ 128 :=
  ⟨rfraw_hon (admK w L0 x hF hX hD hT), abs_hon_le (admK w L0 x hF hX hD hT)⟩

end Link

/-- The honest trace holds the program's inputs. -/
theorem honK_inputs [scl : Scl] (lam : ℕ) :
    InputsAre D (Ps lam) (tbs lam) (w lam) (L0 + lam) (x lam) lam (honK D Ps tbs tb w L0 x) := by
  refine ⟨fun b _ hb g _ i _ n _ => ?_, fun g _ j _ n _ => ⟨?_, ?_⟩⟩
  · subst hb
    exact qryV_hon D tb _ _ _ _ b g i n
  · exact keyV_hon D tb _ _ _ _ lam g j n
  · exact valV_hon D tb _ _ _ _ lam g j n

/-- The honest trace holds the program's output. -/
theorem honK_output [scl : Scl] (lam : ℕ) :
    OutputIs D (Ps lam) (tbs lam) (w lam) (L0 + lam) (x lam) lam (honK D Ps tbs tb w L0 x) := by
  intro b _ hb g _ i _ n _
  subst hb
  exact outV_hon D tb _ _ _ _ b g i n

/-- If the layers' parameters fit D, then with one tb in all layers it is the honest trace of
Inst/Model/Att/Trace.lean. -/
theorem honK_const [scl : Scl] (hF : ∀ lam, Fit D (Ps lam)) :
    honK D Ps (fun _ => tb) tb w L0 x = hon D Ps tb w L0 x :=
  (hon_eq tb w L0 x hF).symm

end Hon

/-! ## Guards: another instance. The numbers 5 and 1,000 are made up -/

/-- the reference sizes with 1,000 live rows (the shift 5 is that of `scl5`) -/
def D5 : Dim := { Dim.ref with u0 := 1000 }
/-- the reference scales with two synthetic numbers: the shift 5 and 1,000 live rows in every
layer -/
@[reducible] def scl5 : Scl := ⟨fun _ => { ppref.scale with sh := 5, expRows := 1000 }, ppref.nf⟩

theorem sizeOK_ref [scl : Scl] [law : Lawful] : SizeOK Dim.ref :=
  ⟨by decide, by decide, by decide, law.ex⟩

/- from here on the scales in scope are `scl5` -/
attribute [local instance] scl5

theorem sizeOK_5 : SizeOK D5 := ⟨by decide, by decide, by decide, expOK_5⟩
/-- the numbers of the lookup argument fit as at the reference -/
theorem calls_ok_5 : Calls.ref.OK D5 where
  fits := by decide +kernel
  le := by decide +kernel
  nt := by decide +kernel
  aligned := by decide +kernel
  ten := by decide +kernel
  ex := expOK_5

end Inst.Model.AttSeg
