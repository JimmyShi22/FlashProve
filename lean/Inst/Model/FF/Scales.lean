-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/Scales.lean: a feed-forward segment for every lawful table of quantization scales,
  with the table written out.

  The files of Inst/Model/FF take the table of scales of the segment (for each layer ten shifts, the
  constants of two normalisations, and attention's `sh` and `expRows`) as the instance argument
  `[scl : Scl]` (Inst/Model/Scl.lean), and what needs a lawful table takes `[Lawful]`
  (Inst/Model/FF/Lawful.lean; other files of this folder say "valid scales"). Here the conclusions
  on the integer side are stated once more with the table as an explicit argument: κ l are the words
  of layer l of the segment (its numbers in the table: `LayerScale`, Inst/Model/Program.lean), nf
  the constants of the final normalisation (which no feed-forward segment reads), and the instance
  is the written term ⟨κ, nf⟩. No statement of this file leaves a table to be found by Lean. The
  sizes are the reference sizes `Dim.ref`, whose scales of a layer `Dim.Pl` replaces by κ l
  (`Params.at`, Inst/Model/Program.lean).

  Main names:
    `lawful_of`: from "∀ l, LawfulW (κ l)" the class `Lawful` at ⟨κ, nf⟩.
    `qkOne_K`, `admN_K`, `admP_K`, `admS_K`, `szR_K`, `par_K`: the size conditions of the files
      whose sizes are not fixed.
    `SettingK`: `Spec.Setting` at ⟨κ, nf⟩.
    `honestK`: `Spec.honest`, here with the read-out at all indices (Inst/Model/FF/Trace.lean):
      under the hypotheses of its statement, the honest trace of the program at the parameters
      ppref.at (κ l) satisfies the relation over the integers. `noWrap1K`, `noWrap2K`, `noWrap3K`
      (Cm/TargetInstFFK.lean): under the hypotheses of each statement, the relation of the trace
      gives `Part1`, `Part2`, `Part3` of the program's layer at those parameters.
    Guards: tables with some synthetic entries (a lawful one with shifts below 16 in one layer; the
      ends of the intervals of `lawfulW_iff`; unlawful words); the reference table.

  Limits: what `LawfulW` is, against the programs' tests, that is the tests of the implementation's
  verifier (definitions: Inst/Model/FF/ScalesDef.lean; closed form: `lawfulW_iff`,
  Inst/Model/FF/Lawful.lean). That `LawfulW` says what the programs test is a reading
  (Inst/Model/ProgTests.lean's header says of what), and no theorem.
  * Of the tests of the programs' verifier on a layer's words and of the no-overflow conditions of
    its layer sub-proof (verifier/src/cp_verify.cpp: the rejections "KL-..", "policy-norm" and, in
    q9, "no-wrap-..") `LawfulW` has every one that reads a layer's word of the table of scales,
    eps_1 or eps_2: the range of each shift by the digit form of its class [KL-shift-range], "kq =
    kk unless both are >= 16" [KL-kq-kk], the ranges of M and K [KL-norm] and of eps [policy-norm,
    no-wrap-ledger-eps], the conditions (U-name) and (W-name) of the eight rounding sites and
    (guard-radix-clamp). The other conditions of q9 read sizes, and one the final normalisation's
    eps. The tests on the final normalisation and on the policy ("policy-norm-F", "no-wrap-H-..")
    are not in `LawfulW`: `HeadTests`, `PolTests`, Inst/Model/ProgTests.lean.
  * The proofs need no more than `LawfulW`, the rendering of the programs' tests. They need less:
    the programs bound a key by 2^60, the proofs by 2^61 − 1 less the table's size, and
    none needs a condition (U-name) or the lower limit 1 ≤ k (the proofs take ko, kd ≤ 19 from the
    closed ranges, where these come from (U-o), (U-down); 20 would do for them). The inequalities of
    the proofs alone (`AdmS.o`, `AdmS.d`) would also admit ko = 20 and kd = 9, 20, which `LawfulW`
    rejects (the guards on unlawful words below): it renders the programs' list, and by that reading
    the programs refuse them too.
  * The sizes (d = dq = 5,120, f = 16,384) and the digit forms (2 for queries and keys and for the
    normalisations, 1 for the six other classes) are those of the reference parameter file: they fix
    shapes, and they are no part of the table.
  * Departures. (a) In the programs' table only a layer with experts has the words kr, kgR, kuR
    (here kr, kg', ku'); here every layer's word has them, and `LawfulW` tests them in every layer,
    though nothing reads them in a dense one.
    (b) In the programs eps_1 and eps_2 are two numbers of the parameter file; here each layer's
        word has its own.
    (c) The flag rp of the programs' table (a layer without rotation) is no word here: it is a
        property of the tables C and S.
    (d) The words `sh` and `expRows` of a `LayerScale` are attention's (Inst/Model/Att/Scales.lean);
        `LawfulW` does not read them.
  No claim is made that a table of this file suits the weights of any real model (where the
  reference table's numbers come from: lean/CREDITS.md, section 8): the file speaks of every lawful
  table, and in its guards the entries that are not those of `ppref` are made up. The lemmas take "∀
  l, LawfulW (κ l)", for all natural numbers l, because the records of the files whose sizes are not
  fixed quantify over all l; the relation of the trace and `Part1` to `Part3` read only l < 4. One
  segment has one set of tables tb for its four layers.
  Notation:
    `LawfulW s`: a proposition on a `LayerScale`: "The scales of one layer are valid: this library's
      rendering of the checks of the implementation's verifier that read them"
      (Inst/Model/FF/ScalesDef.lean).
    `Spec.Setting tb W L0 tok`: "The setting of the statements on the integer model"
      (Inst/Model/FF/Trace.lean; what it asks: its fields).
    `tb`, `W`, `L0`, `tok`, `first`, `t`: a `Tables` ("The five table functions that the program
      reads."); a `Mat`, the matrix W; "L0 the first layer of the segment" (`trace`); the prompt,
      `ℕ → ℕ` ("the instance is the prompt"); a `Bool` (whether the segment is the first: (J11)); a
      trace on the valid names of cells, with integer values. (Inst/Model/FF/Trace.lean)
    `rd D t`: "a trace that is given on the valid names, as a function on all names with values in a
      ring R: the integer of a valid name, mapped into R; 0 at a name that is not valid".
      (Inst/Model/FF/Trace.lean)
    `Layout.kRef`, `Layout.hRef`: "rows and columns of W: h; 2^k" (h is `hRef`, k is `kRef`;
      Inst/Model/Layout.lean); `ppref`: "The reference parameters." (Inst/Model/Program.lean).
    a term of three numbers in the place of a `NormPar`: its fields M, K, eps, in this order:
      "exponent of the reciprocal; shift; constant" (Inst/Model/Program.lean).
  Terms: lean/GLOSSARY.md.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.FF.NoWrap
import Inst.Model.FF.Honest
import Inst.Model.FF.Objects

set_option autoImplicit false

/- the default table of scales is no instance in this file: what reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

open Finset Scales

/-! ## 1. The size conditions of the files whose sizes are not fixed -/

/-- From `LawfulW` at every layer, the class `Lawful` at the table ⟨κ, nf⟩. -/
theorem lawful_of {κ : ℕ → LayerScale} {nf : NormPar} (hκ : ∀ l, LawfulW (κ l)) :
    Lawful (scl := ⟨κ, nf⟩) :=
  Lawful.mk (scl := ⟨κ, nf⟩) hκ

/-- The setting of the statements on the program (`Spec.Setting`) at the table ⟨κ, nf⟩: the ranges
of the tables are required at the words of the segment's first layer (only Exp's number of rows is
read of them, and no feed-forward segment reads Exp). -/
abbrev SettingK (κ : ℕ → LayerScale) (nf : NormPar) (tb : Tables) (W : Mat)
    (L0 : ℕ) (tok : ℕ → ℕ) : Prop :=
  Spec.Setting (scl := ⟨κ, nf⟩) tb W L0 tok

section Records
variable {κ : ℕ → LayerScale} {nf : NormPar} (hκ : ∀ l, LawfulW (κ l))
include hκ

theorem qkOne_K : Dim.QKOne (scl := ⟨κ, nf⟩) Dim.ref := @ref_qkOne ⟨κ, nf⟩ (lawful_of hκ)

theorem admN_K : AdmN (scl := ⟨κ, nf⟩) (2 ^ 61 - 1) Dim.ref := @admN_ref ⟨κ, nf⟩ (lawful_of hκ)

theorem szR_K : NWR.SzR (scl := ⟨κ, nf⟩) Dim.ref := @NWA.szR_ref ⟨κ, nf⟩ (lawful_of hκ)

theorem par_K {L0 : ℕ} (hL : L0 % 2 = 0) : Hon.Par (scl := ⟨κ, nf⟩) Dim.ref L0 :=
  @Hon.par_ref ⟨κ, nf⟩ (lawful_of hκ) L0 hL

variable {tb : Tables} {W : Mat} {L0 : ℕ} {tok : ℕ → ℕ} (S : SettingK κ nf tb W L0 tok)
include S

theorem admP_K :
    AdmP (scl := ⟨κ, nf⟩) (2 ^ 61 - 1) Dim.ref tb L0 fun l =>
      Layout.layerOf ppref Layout.kRef W (L0 + l) :=
  @admP_ref ⟨κ, nf⟩ (lawful_of hκ) tb W L0 tok S

theorem admS_K :
    AdmS (scl := ⟨κ, nf⟩) (2 ^ 61 - 1) Dim.ref L0 fun l =>
      Layout.layerOf ppref Layout.kRef W (L0 + l) :=
  @admS_ref ⟨κ, nf⟩ (lawful_of hκ) tb W L0 tok S

end Records

/-! ## 2. The segment for every lawful table -/

section Main
variable {κ : ℕ → LayerScale} {nf : NormPar} (hκ : ∀ l, LawfulW (κ l))
include hκ

/-- The honest trace (`Spec.honest`, here with the read-out at all indices), under the hypotheses
below: if the program's four layers run at the parameters ppref.at (κ l), the honest trace has small
cells, reads out the honest values, has every key in its table and meets the identities ((J11) if x
0 is the embedding of the prompt), over the integers. -/
theorem honestK {tb : Tables} {W : Mat} {L0 : ℕ} {tok : ℕ → ℕ}
    (hS : SettingK κ nf tb W L0 tok) (x : ℕ → ℕ → Vec) (o : ℕ → ℕ → Vec)
    (R : Runs (scl := ⟨κ, nf⟩) Dim.ref tb
      (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 x o) :
    (∀ c : Cell, c.Valid Dim.ref →
      |hon (scl := ⟨κ, nf⟩) Dim.ref tb
          (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 x o c| ≤ 128) ∧
    (∀ (X : Arr) (n j i : ℕ),
      val (hon (scl := ⟨κ, nf⟩) Dim.ref tb
            (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 x o)
          X n j i =
        hv (scl := ⟨κ, nf⟩) Dim.ref tb
          (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 x o X n j i) ∧
    (∀ q : KeyName Dim.ref,
      key (scl := ⟨κ, nf⟩) Dim.ref
          (hon (scl := ⟨κ, nf⟩) Dim.ref tb
            (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 x o)
          tb L0 (fun l => LW.ofInt ℤ (Layout.layerOf ppref Layout.kRef W (L0 + l)))
          q.val.1 q.val.2.1 q.val.2.2.1 q.val.2.2.2 ∈
        lutSet (R := ℤ) (lut tb (call q.val.1))) ∧
    ∀ first : Bool,
      (first = true →
        ∀ i < Dim.ref.T,
          ∀ j < Dim.ref.d, x 0 i j = (Layout.weightsOf ppref Layout.kRef W).Emb (tok i) j) →
      ∀ j : Idn, j.Valid Dim.ref first →
        idnVal (scl := ⟨κ, nf⟩) Dim.ref
            (hon (scl := ⟨κ, nf⟩) Dim.ref tb
              (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 x o)
            (Layout.weightsOf ppref Layout.kRef W).Emb tok j = 0 := by
  letI : Scl := ⟨κ, nf⟩
  exact Hon.honest_gen (par_K hκ hS.even) (Unit.TabOK.of_ok hS.tab) R
    (Layout.weightsOf ppref Layout.kRef W).Emb tok

end Main

/-! ## 3. Guards, at tables with some synthetic entries, and at the reference table -/

namespace Scales

/-- a synthetic word with nine shifts below 16 and other constants of the normalisations (`expRows`
and `sh` are those of `ppref.scale`) -/
def wLow : LayerScale :=
  { ppref.scale with
    kq := 7, kk := 7, kv := 3, ko := 9, kg := 1, ku := 12, kd := 10, kr := 8, kg' := 15, ku' := 24,
    n1 := ⟨24, 17, 1⟩, n2 := ⟨46, 32, 2 ^ 48 - 1⟩ }

/-- a synthetic table: that word in layer 1, the reference words elsewhere -/
def kLow (l : ℕ) : LayerScale := if l = 1 then wLow else ppref.scale

example : LawfulW wLow := by decide +kernel
example : LawfulFF kLow := by decide +kernel
theorem kLow_lawful : ∀ l, LawfulW (kLow l) := fun l => by
  unfold kLow
  split_ifs
  · decide +kernel
  · exact lawfulW_ref

/-- the theorems of Sections 1 and 2 apply to it -/
example : AdmN (scl := ⟨kLow, ppref.nf⟩) (2 ^ 61 - 1) Dim.ref := admN_K kLow_lawful
example :
    (Dim.ref.Pl (scl := ⟨kLow, ppref.nf⟩) 1).ko = 9 ∧
    (Dim.ref.Pl (scl := ⟨kLow, ppref.nf⟩) 0).ko = 17 ∧
    (Dim.ref.Pl (scl := ⟨kLow, ppref.nf⟩) 1).d = 5120 := ⟨rfl, rfl, rfl⟩

/-! unlawful words: a shift 0; queries and keys with different shifts, one or both below 16 (and a
lawful pair from 16 on); a shift above its digit form; a no-overflow condition broken from below
(down, queries, router) and from above (down, o); eps out of its range; M above K + 14 -/
example : ¬ LawfulW { ppref.scale with kv := 0 } := by decide +kernel
example : ¬ LawfulW { ppref.scale with kq := 9, kk := 10 } := by decide +kernel
example : ¬ LawfulW { ppref.scale with kq := 9, kk := 16 } := by decide +kernel
example : LawfulW { ppref.scale with kq := 16, kk := 32 } := by decide +kernel
example : ¬ LawfulW { ppref.scale with kv := 25 } := by decide +kernel
example : ¬ LawfulW { ppref.scale with kd := 9 } := by decide +kernel
example : ¬ LawfulW { ppref.scale with kq := 4, kk := 4 } := by decide +kernel
example : ¬ LawfulW { ppref.scale with kr := 7 } := by decide +kernel
example : ¬ LawfulW { ppref.scale with kd := 20 } := by decide +kernel
example : ¬ LawfulW { ppref.scale with ko := 20 } := by decide +kernel
example : ¬ LawfulW { ppref.scale with n1 := ⟨44, 30, 0⟩ } := by decide +kernel
example : ¬ LawfulW { ppref.scale with n2 := ⟨44, 30, 2 ^ 48⟩ } := by decide +kernel
example : ¬ LawfulW { ppref.scale with n1 := ⟨32, 17, 5⟩ } := by decide +kernel
example : ¬ LawfulW { ppref.scale with n1 := ⟨47, 32, 5⟩ } := by decide +kernel

/-! the ends of the intervals of `lawfulW_iff`: lawful at the end, unlawful one step beyond; for M
the highest lawful value is 46, not the 47 of `NormPar.OK`, since M ≤ K + 14 and K ≤ 32; of the
normalisations the lower ends at n1, the upper at n2 -/
example :
    LawfulW { ppref.scale with kq := 5, kk := 5 } ∧
    ¬ LawfulW { ppref.scale with kq := 4, kk := 4 } := by decide +kernel
example :
    LawfulW { ppref.scale with kq := 32, kk := 32 } ∧
    ¬ LawfulW { ppref.scale with kq := 33 } ∧
    ¬ LawfulW { ppref.scale with kk := 33 } := by decide +kernel
example :
    LawfulW { ppref.scale with kq := 15, kk := 15 } ∧
    ¬ LawfulW { ppref.scale with kq := 15, kk := 16 } ∧
    ¬ LawfulW { ppref.scale with kq := 16, kk := 15 } ∧
    LawfulW { ppref.scale with kq := 16, kk := 17 } := by decide +kernel
example :
    LawfulW { ppref.scale with kv := 1 } ∧
    ¬ LawfulW { ppref.scale with kv := 0 } ∧
    LawfulW { ppref.scale with kv := 24 } ∧
    ¬ LawfulW { ppref.scale with kv := 25 } := by decide +kernel
example :
    LawfulW { ppref.scale with ko := 1 } ∧
    ¬ LawfulW { ppref.scale with ko := 0 } ∧
    LawfulW { ppref.scale with ko := 19 } ∧
    ¬ LawfulW { ppref.scale with ko := 20 } := by decide +kernel
example :
    LawfulW { ppref.scale with kg := 1 } ∧
    ¬ LawfulW { ppref.scale with kg := 0 } ∧
    LawfulW { ppref.scale with kg := 24 } ∧
    ¬ LawfulW { ppref.scale with kg := 25 } := by decide +kernel
example :
    LawfulW { ppref.scale with kg' := 1 } ∧
    ¬ LawfulW { ppref.scale with kg' := 0 } ∧
    LawfulW { ppref.scale with kg' := 24 } ∧
    ¬ LawfulW { ppref.scale with kg' := 25 } := by decide +kernel
example :
    LawfulW { ppref.scale with ku := 1 } ∧
    ¬ LawfulW { ppref.scale with ku := 0 } ∧
    LawfulW { ppref.scale with ku := 24 } ∧
    ¬ LawfulW { ppref.scale with ku := 25 } := by decide +kernel
example :
    LawfulW { ppref.scale with ku' := 1 } ∧
    ¬ LawfulW { ppref.scale with ku' := 0 } ∧
    LawfulW { ppref.scale with ku' := 24 } ∧
    ¬ LawfulW { ppref.scale with ku' := 25 } := by decide +kernel
example :
    LawfulW { ppref.scale with kd := 10 } ∧
    ¬ LawfulW { ppref.scale with kd := 9 } ∧
    LawfulW { ppref.scale with kd := 19 } ∧
    ¬ LawfulW { ppref.scale with kd := 20 } := by decide +kernel
example :
    LawfulW { ppref.scale with kr := 8 } ∧
    ¬ LawfulW { ppref.scale with kr := 7 } ∧
    LawfulW { ppref.scale with kr := 24 } ∧
    ¬ LawfulW { ppref.scale with kr := 25 } := by decide +kernel
example :
    LawfulW { ppref.scale with n1 := ⟨24, 17, 1⟩ } ∧
    ¬ LawfulW { ppref.scale with n1 := ⟨23, 17, 1⟩ } ∧
    ¬ LawfulW { ppref.scale with n1 := ⟨24, 16, 1⟩ } ∧
    ¬ LawfulW { ppref.scale with n1 := ⟨24, 17, 0⟩ } := by decide +kernel
example :
    LawfulW { ppref.scale with n2 := ⟨46, 32, 2 ^ 48 - 1⟩ } ∧
    ¬ LawfulW { ppref.scale with n2 := ⟨47, 32, 1⟩ } ∧
    ¬ LawfulW { ppref.scale with n2 := ⟨46, 33, 1⟩ } ∧
    ¬ LawfulW { ppref.scale with n2 := ⟨46, 32, 2 ^ 48⟩ } := by decide +kernel
example :
    LawfulW { ppref.scale with n1 := ⟨31, 17, 1⟩ } ∧
    ¬ LawfulW { ppref.scale with n1 := ⟨32, 17, 1⟩ } := by decide +kernel

/-! the inequalities of the proofs alone (`AdmS.o` at ko = 20, `AdmS.d` at kd = 9 and 20) hold at
three words that `LawfulW` rejects (above) -/
example :
    (2 : ℤ) ^ Site.dn 20 * ((5120 : ℤ) * (2047 * 2 ^ 12) + 2 ^ (20 - 1) + 2 ^ 20 * 2 ^ 40) +
        2 ^ 16 * (2 ^ 18 + 128) + 2 ^ 16 ≤ 2 ^ 61 - 1 := by
  norm_num [Site.dn]
example :
    (2 : ℤ) ^ Site.dn 9 * ((16384 : ℤ) * (4095 * 2 ^ 15 * 2 ^ 12) + 2 ^ (9 - 1) + 2 ^ 9 * 2 ^ 40) +
        2 ^ 16 * (2 ^ 18 + 128) + 2 ^ 16 ≤ 2 ^ 61 - 1 := by
  norm_num [Site.dn]
example :
    (2 : ℤ) ^ Site.dn 20 *
          ((16384 : ℤ) * (4095 * 2 ^ 15 * 2 ^ 12) + 2 ^ (20 - 1) + 2 ^ 20 * 2 ^ 40) +
        2 ^ 16 * (2 ^ 18 + 128) + 2 ^ 16 ≤ 2 ^ 61 - 1 := by
  norm_num [Site.dn]

/-! the sizes that are written as numerals in Inst/Model/FF/ScalesDef.lean are those of `ppref` -/
example : Scales.acc = ppref.d * BC * BW := rfl
example : (5120 : ℕ) = ppref.d ∧ (5120 : ℕ) = ppref.nq * ppref.ch ∧ (16384 : ℕ) = ppref.f :=
  ⟨rfl, rfl, rfl⟩

/-- the reference table -/
example : LawfulFF fun _ => ppref.scale := by decide +kernel
example (l : ℕ) : Dim.ref.Pl (scl := Scl.ref) l = ppref := rfl
example (l : ℕ) : Dim.ref.Pl (scl := ⟨fun _ => ppref.scale, ppref.nf⟩) l = ppref := rfl

end Scales

end Inst.Model.FFSeg
