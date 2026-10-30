-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/ScalesGuard.lean: sanity checks on the settings and on the definitions that take scales
as arguments. Another file (Inst/Model/ScalesSanity.lean) uses `put` and `one`; nothing else here is
used by another file.

Part 1. At the reference numbers the definitions that take scales as arguments unfold to terms with
fixed numerals. So that the scales can vary, definitions on which the theorems at the reference
settings rest take them as arguments:
  * `Params` has a field `sh` and (PA3) divides by 2 ^ P.sh (Inst/Model/Program.lean);
  * the cut-off C, the step st, the number nd of unused rows and the tables τ1, τ2 take the shift,
    and C and τ2 the number of rows in use too, as arguments (Inst/Model/Tables.lean);
  * the files of a segment read the scales of its layers from the instance argument `[scl : Scl]`
    (Inst/Model/Scl.lean), and `AttSeg.Dim` has the number `u0` of rows in use.
Here the terms with fixed numerals are written out (`Old.*`), and each is shown equal to the general
term at the reference numbers.
Of the integer program only the line (PA3) is compared (`u_old`).

Terms inside the verifier read the scales too: in Inst/Model/FF/Objects.lean ten panel weights have
the factor `Site.scl`, and in Inst/Model/FF/Trace.lean the keys are `Site.ssite`, `Site.shigh`;
Inst/Model/Att/KeyForms.lean reads `D.cutC`, `Om D`, 2 ^ D.sh.

Limit of Part 1:
That at each of the ten reference shifts the terms of the verifier's affine forms with a branch on
16 ≤ k are those without it, and the factor is 1,
and that each affine form is its term with fixed numerals family by family,
is not proved in this library (proved for the functions `scl`, `ssite` and `shigh` on a ring, and
for `SSITE` and `SHIGH` on affine forms, for every 16 ≤ k: Inst/Model/Common/Site.lean: `scl_of_le`,
`ssite_of_le`, `shigh_of_le`, `SSITE_of_le`, `SHIGH_of_le`).

The definition of Inst/Model/All/ without an argument for scales (`honT`) takes the reference
scales: Part 2.

Part 2. `Inf.R` (Inst/Model/Inf/Spec.lean) is `RinfPP0 ppRef`.
Both are the relation on a request without `Head3`, the clause that the request is well-formed (the
comment at the top of Inst/Model/ProgramR.lean), `RinfR0` at the policy of exact match, and `Inf.R`
is written as such, so this part compares `RinfR0` with `RinfR0` (`kap_ref` and unfolding).
The tie to R_inf is shown only on the requests "the next token" and is in
Inst/Model/RequestGuards.lean: `infR_next`. Of that tie this file has: `RinfK` at `ppref`'s scales
in all layers, `ppref.nf` and `tbRef` is `Rinf` (the example with `RinfK_const`).

Part 3. Settings with some synthetic entries, decided by the kernel: valid ones (`ppMade`); invalid
ones (`unlawful`); and both ends of every interval of `Lawful`: valid at the end (of M: at 46: the
doc comment of `ends`), invalid one step beyond; the same for the clause K ≤ M (`km_nf_ends`,
`km_layer_ends`) and the policy's three numbers (`pol_ends`).
Part 3's settings are the reference settings with scales, a normalisation or the policy changed.

Notation: from Inst/Model/All/TraceK.lean: `SFK κ nf g`: the table of one segment
(Inst/Model/Scl.lean) for group g; from Inst/Model/All/Honest.lean: `honT`: the honest trace; `xs g
s`: the program's stream at index s of group g; `os g l`: the program's output of attention in layer
l of group g; from Inst/Model/All/NoWrap.lean: `wOf W g l`: the weights of layer l of group g.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Scales
import Inst.Model.Inf.Spec
import Inst.Model.Att.KeyForms
import Inst.Model.All.HonestK
import Inst.Model.All.Honest

set_option autoImplicit false

namespace Inst.Model.ScalesGuard

/-! ## Part 1. The terms with fixed numerals -/

namespace Old

def cutC : ℤ := 2 ^ 8 * 2307
def stp : ℤ := 2 ^ 16 - 2 ^ 8
def nd : ℕ := 32865
def tau1 : Lut :=
  ⟨2 ^ 16, fun ι => (ι % 256 : ℕ) + 2 ^ 20 * (ι / 256 : ℕ) + (if 2 ^ 8 ≤ ι then 2 ^ 40 else 0), 0⟩
def tau2 (tb : Tables) : Lut :=
  ⟨2 ^ 16, fun ι =>
    if ι < 2307 then 2 ^ 8 * ι + 2 ^ 33 * tb.Exp ι
    else if ι < 2307 + nd then cutC - 2 ^ 8 + stp * (ι - 2307) + 2 ^ 32
    else cutC - 2 ^ 8 + stp * (ι - (2307 + nd : ℕ)) + stp / 2 + 2 ^ 32,
    cutC - 2 ^ 8 + 2 ^ 32⟩
/-- (PA3) u_ij = ⌊(mx_i − sc_ij) / 2^8⌋ -/
def u (P : Params) (tb : Tables) (w : LayerW) (L : ℕ) (x : ℕ → Vec) (h i j : ℕ) : ℤ :=
  (Att.mx P tb w L x h i - Att.sc P tb w L x h i j) / 2 ^ 8

end Old

theorem cutC_old : cutC 8 2307 = Old.cutC := rfl
theorem stp_old : stp 8 = Old.stp := rfl
theorem nd_old : nd 8 = Old.nd := by decide +kernel
theorem tau1_old : tau1 8 = Old.tau1 := rfl
theorem tau2_old (tb : Tables) : tau2 8 2307 tb = Old.tau2 tb := by
  unfold tau2 Old.tau2
  rw [nd_old]
  rfl
theorem u_old : Att.u ppref = Old.u ppref := rfl

example (tb : Tables) (w : LayerW) (L : ℕ) (x : ℕ → Vec) (h i j : ℕ) :
    Att.u ppref tb w L x h i j =
      (Att.mx ppref tb w L x h i - Att.sc ppref tb w L x h i j) / 2 ^ 8 := rfl
example (l : ℕ) : FFSeg.Dim.ref.Pl l = ppref := rfl
example (l : ℕ) : FFSeg.Dim.Pl (scl := ⟨fun _ => ppref.scale, ppref.nf⟩) FFSeg.Dim.ref l = ppref :=
  rfl
example : AttSeg.Dim.refK 2307 = AttSeg.Dim.ref := rfl
example : AttSeg.Dim.ref.sh = 8 ∧ AttSeg.Dim.ref.u0 = 2307 := ⟨rfl, rfl⟩
example : ppref.at ppref.scale = ppref := rfl
example : ppref.sh = 8 ∧ ppref.expRows = 2307 := ⟨rfl, rfl⟩

example : AttSeg.Dim.ref.cutC = 2 ^ 8 * 2307 := rfl
example : AttSeg.Om AttSeg.Dim.ref = 2 * Smax + 2 ^ 8 * 2307 := rfl

/-! the numerals of the checks are the sizes of `ppref` -/

example : FFSeg.Scales.acc = ppref.d * FFSeg.Scales.BC * FFSeg.Scales.BW := rfl
example : (5120 : ℕ) = Att.dq ppref ∧ (16384 : ℕ) = ppref.f ∧ (5120 : ℕ) = ppref.d :=
  ⟨rfl, rfl, rfl⟩
example : Smax = (ppref.ch : ℤ) * 2047 ^ 2 := rfl

/-! no two fields are swapped where a record is written by position: synthetic numbers that all
differ -/

example :
    (⟨1, 2, 3, 4, 5, 6, 7, 8, 9, 10, ⟨11, 12, 13⟩, ⟨14, 15, 16⟩, 17⟩ : Words).scale =
      { kq := 1, kk := 2, kv := 3, ko := 4, kg := 5, ku := 6, kd := 7, kr := 8, kg' := 9, ku' := 10,
        n1 := { M := 11, K := 12, eps := 13 }, n2 := { M := 14, K := 15, eps := 16 },
        expRows := 2307, sh := 17 } := rfl
example :
    (⟨1, 2, 3, 4, 5, 6, 7, 8, 9, 10, ⟨11, 12, 13⟩, ⟨14, 15, 16⟩, 17⟩ : Words) =
      { kq := 1, kk := 2, kv := 3, ko := 4, kg := 5, ku := 6, kd := 7, kr := 8, kg' := 9, ku' := 10,
        n1 := { M := 11, K := 12, eps := 13 }, n2 := { M := 14, K := 15, eps := 16 }, sh := 17 } :=
  rfl
example (P : Params) :
    P.scale = { kq := P.kq, kk := P.kk, kv := P.kv, ko := P.ko, kg := P.kg, ku := P.ku, kd := P.kd,
                kr := P.kr, kg' := P.kg', ku' := P.ku', n1 := P.n1, n2 := P.n2,
                expRows := P.expRows, sh := P.sh } := rfl
example :
    wRef = { kq := ppref.kq, kk := ppref.kk, kv := ppref.kv, ko := ppref.ko, kg := ppref.kg,
             ku := ppref.ku, kd := ppref.kd, kr := ppref.kr, kg' := ppref.kg', ku' := ppref.ku',
             n1 := ppref.n1, n2 := ppref.n2, sh := ppref.sh } := rfl

/-! ## Part 2. The relation at the reference settings -/

example : RinfK ppref (fun _ => ppref.scale) ppref.nf (fun _ => tbRef) = Rinf ppref tbRef :=
  RinfK_const ppref tbRef

/-- `Inf.R` written out: the relation with a policy, without `Head3`, at the policy of exact match,
at the same scales in all layers; and what that says. -/
example :
    Inf.R =
      fun i x => RinfR0 ppref (fun _ => ppref.scale) ppref.nf (fun _ => tbRef) AcceptancePolicy.exact i x := rfl
example (i : Index ppref) (x : Instance ppref) :
    Inf.R i x ↔ RinfS0 ppref (fun _ => ppref.scale) ppref.nf (fun _ => tbRef) i x :=
  (RinfS0_iff_exact ppref (by decide) _ _ _ i x).symm

/-- `Inf.R` is the relation without `Head3` at the reference settings. -/
theorem infR_eq : Inf.R = RinfPP0 ppRef := rinfPP_ref.symm

/-! the definitions of Inst/Model/All/ without an argument for scales take `Scl.ref`, and no other
-/

section All
open All Layout
variable (tb : Tables) (W : Mat) (y : Head.Req) (prompt : Fin ppref.T → Fin ppref.V) (g : ℕ)

example : SFK (fun _ => ppref.scale) ppref.nf g = Scl.ref := rfl
example :
    (honT tb W prompt y).ff g =
      FFSeg.hon (scl := Scl.ref) FFSeg.Dim.ref tb (wOf W g) (4 * g)
        (xs tb W prompt g) (os tb W prompt g) := rfl
example :
    (honT tb W prompt y).att g =
      AttSeg.hon (scl := Scl.ref) AttSeg.Dim.ref (fun _ => ppref) tb (wOf W g) (4 * g)
        fun lam => xs tb W prompt g (2 * lam) := rfl

end All

/-! ## Part 3. Settings with synthetic entries -/

/-- the settings pp (default: `ppRef`) with the scales w in the layers of the set S -/
def put (S : Fin 48 → Bool) (w : Words) (pp : ScalesAndPolicy := ppRef) : ScalesAndPolicy :=
  ⟨fun L => if S L then w else pp.w L, pp.nf, pp.pol⟩
/-- one layer; one group of four layers; every fourth layer -/
def one (L₀ : ℕ) : Fin 48 → Bool := fun L => L.val == L₀
def grp (g : ℕ) : Fin 48 → Bool := fun L => L.val / 4 == g
def fourth : Fin 48 → Bool := fun L => L.val % 4 == 3

/-- synthetic scales with shifts below 16 (`sh` is that of `wRef`) -/
def wLow : Words :=
  { wRef with
    kq := 7, kk := 7, kv := 3, ko := 9, kg := 1, ku := 12, kd := 10, kr := 8, kg' := 15, ku' := 24,
    n1 := ⟨24, 17, 1⟩, n2 := ⟨46, 32, 2 ^ 48 - 1⟩ }
/-- the reference scales (`wRef`) with nine entries replaced by synthetic ones -/
def wAlt : Words :=
  { wRef with
    kq := 30, kk := 21, kv := 18, ko := 16, kg := 17, ku := 19, kd := 18,
    kr := 16, n1 := ⟨40, 28, 1000⟩ }

/-- Valid settings with synthetic entries: `wLow` in layer 13, `wAlt` in every fourth layer, sh = 5
in group 7, all else in the layers as in `ppRef`; a
separate final normalisation and a separate policy, (300, 257, 3), which is not exact match. -/
def ppMade : ScalesAndPolicy :=
  let p1 := put fourth wAlt
  let p2 := put (one 13) wLow p1
  ⟨fun L => if grp 7 L then { p2.w L with sh := 5 } else p2.w L, ⟨30, 20, 77⟩, ⟨300, 257, 3⟩⟩

set_option maxRecDepth 100000 in
theorem ppMade_lawful : Lawful ppMade := by decide +kernel

theorem ppMade_tests : ProgTests ppMade := (lawful_iff _).1 ppMade_lawful

theorem ppMade_ne : ppMade ≠ ppRef := by decide +kernel

set_option maxRecDepth 100000 in
/-- Invalid settings with synthetic entries, all else as in `ppRef`: a shift 0; kq ≠ kk below 16;
a no-overflow condition violated (the
rounding site "down" at kd = 9; the rounding site "o" at ko = 20); two values of sh in a group; a
final normalisation out of range. -/
theorem unlawful :
    ¬ Lawful (put (one 0) { wRef with kv := 0 }) ∧
    ¬ Lawful (put (one 47) { wRef with kq := 9, kk := 10 }) ∧
    ¬ Lawful (put (one 20) { wRef with kd := 9 }) ∧
    ¬ Lawful (put (one 20) { wRef with ko := 20 }) ∧
    ¬ Lawful (put (one 5) { wRef with sh := 9 }) ∧
    ¬ Lawful { ppRef with nf := ⟨48, 30, 1⟩ } := by decide +kernel

/-- the policy's three numbers: both ends, and one step beyond: valid: (0, 0, 0), (2^32 − 1,
2^32 − 1, 1,024); not valid: C = 2^32; θ = C + 1; cap = 1,025 -/
theorem pol_ends :
    Lawful { ppRef with pol := ⟨0, 0, 0⟩ } ∧
    Lawful { ppRef with pol := ⟨2 ^ 32 - 1, 2 ^ 32 - 1, 1024⟩ } ∧
    ¬ Lawful { ppRef with pol := ⟨2 ^ 32, 2 ^ 8, 0⟩ } ∧
    ¬ Lawful { ppRef with pol := ⟨2 ^ 8, 2 ^ 8 + 1, 0⟩ } ∧
    ¬ Lawful { ppRef with pol := ⟨2 ^ 8, 2 ^ 8, 1025⟩ } := by decide +kernel

/-- the violated conditions themselves, as the implementation writes them -/
example :
    ¬ FFSeg.Scales.SiteW 1 (16384 * 2 ^ 12 * FFSeg.Scales.Bu * FFSeg.Scales.BW) (2 ^ 40) 9 := by
  decide +kernel
example : ¬ FFSeg.Scales.SiteU (2 ^ 41) 20 := by decide +kernel

/-- the ends of the intervals: scales that are valid. (M = 47 is inside the range of M, but M ≤ K +
14 and K ≤ 32 leave M ≤ 46.) -/
def ends : List Words :=
  [{ wRef with kq := 5, kk := 5 }, { wRef with kq := 32, kk := 32 },
    { wRef with kq := 16, kk := 32 }, { wRef with kv := 1 }, { wRef with kv := 24 },
    { wRef with ko := 1 }, { wRef with ko := 19 }, { wRef with kg := 1 }, { wRef with kg := 24 },
    { wRef with kg' := 1 }, { wRef with kg' := 24 }, { wRef with ku := 1 }, { wRef with ku := 24 },
    { wRef with ku' := 1 }, { wRef with ku' := 24 }, { wRef with kd := 10 }, { wRef with kd := 19 },
    { wRef with kr := 8 }, { wRef with kr := 24 }, { wRef with n1 := ⟨24, 17, 1⟩ },
    { wRef with n1 := ⟨46, 32, 2 ^ 48 - 1⟩ }, { wRef with n1 := ⟨31, 17, 1⟩ },
    { wRef with n2 := ⟨24, 17, 1⟩ }, { wRef with n2 := ⟨46, 32, 2 ^ 48 - 1⟩ },
    { wRef with n2 := ⟨31, 17, 1⟩ }, { wRef with sh := 4 }, { wRef with sh := 12 }]

/-- one step beyond: scales that are not valid -/
def beyond : List Words :=
  [{ wRef with kq := 4, kk := 4 }, { wRef with kq := 33, kk := 33 },
    { wRef with kq := 15, kk := 32 }, { wRef with kv := 0 }, { wRef with kv := 25 },
    { wRef with ko := 0 }, { wRef with ko := 20 }, { wRef with kg := 0 }, { wRef with kg := 25 },
    { wRef with kg' := 0 }, { wRef with kg' := 25 }, { wRef with ku := 0 }, { wRef with ku := 25 },
    { wRef with ku' := 0 }, { wRef with ku' := 25 }, { wRef with kd := 9 }, { wRef with kd := 20 },
    { wRef with kr := 7 }, { wRef with kr := 25 }, { wRef with n1 := ⟨23, 17, 1⟩ },
    { wRef with n1 := ⟨47, 32, 1⟩ }, { wRef with n1 := ⟨48, 34, 1⟩ },
    { wRef with n1 := ⟨32, 17, 1⟩ }, { wRef with n1 := ⟨24, 16, 1⟩ },
    { wRef with n1 := ⟨44, 33, 1⟩ }, { wRef with n1 := ⟨44, 30, 0⟩ },
    { wRef with n1 := ⟨44, 30, 2 ^ 48⟩ }, { wRef with n2 := ⟨23, 17, 1⟩ },
    { wRef with n2 := ⟨47, 32, 1⟩ }, { wRef with n2 := ⟨48, 34, 1⟩ },
    { wRef with n2 := ⟨32, 17, 1⟩ }, { wRef with n2 := ⟨24, 16, 1⟩ },
    { wRef with n2 := ⟨44, 33, 1⟩ }, { wRef with n2 := ⟨44, 30, 0⟩ },
    { wRef with n2 := ⟨44, 30, 2 ^ 48⟩ }, { wRef with sh := 3 }, { wRef with sh := 13 }]

set_option maxRecDepth 100000 in
/-- Both ends of every interval (of M: 46: the doc comment of `ends`), in a whole group of four
layers (so that sh has one value there). -/
theorem ends_lawful : ∀ w ∈ ends, Lawful (put (grp 11) w) := by decide +kernel

set_option maxRecDepth 100000 in
theorem beyond_unlawful : ∀ w ∈ beyond, ¬ Lawful (put (grp 11) w) := by decide +kernel

set_option maxRecDepth 100000 in
/-- the final normalisation: ends, and one step beyond -/
theorem nf_ends :
    (∀ n ∈ [(⟨24, 17, 1⟩ : NormPar), ⟨46, 32, 2 ^ 48 - 1⟩, ⟨31, 17, 1⟩],
      Lawful { ppRef with nf := n }) ∧
    ∀ n ∈ [(⟨23, 17, 1⟩ : NormPar), ⟨47, 32, 1⟩, ⟨48, 34, 1⟩, ⟨32, 17, 1⟩, ⟨24, 16, 1⟩, ⟨44, 33, 1⟩,
          ⟨44, 30, 0⟩, ⟨44, 30, 2 ^ 48⟩],
      ¬ Lawful { ppRef with nf := n } := by decide +kernel

set_option maxRecDepth 100000 in
/-- the clause K ≤ M: valid at K = M, invalid one step beyond, in the final normalisation -/
theorem km_nf_ends :
    (∀ n ∈ [(⟨24, 24, 1⟩ : NormPar), ⟨32, 32, 1⟩], Lawful { ppRef with nf := n }) ∧
    ∀ n ∈ [(⟨24, 25, 1⟩ : NormPar), ⟨31, 32, 1⟩], ¬ Lawful { ppRef with nf := n } := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- and in each of a layer's two normalisations; the invalid ones are within all the intervals
(`LawfulBut`): it is the clause K ≤ M that excludes them -/
theorem km_layer_ends :
    (∀ w ∈ [{ wRef with n1 := ⟨24, 24, 1⟩ }, { wRef with n1 := ⟨32, 32, 1⟩ },
            { wRef with n2 := ⟨24, 24, 1⟩ }, { wRef with n2 := ⟨32, 32, 1⟩ }],
        Lawful (put (grp 11) w)) ∧
    ∀ w ∈ [{ wRef with n1 := ⟨24, 25, 1⟩ }, { wRef with n1 := ⟨31, 32, 1⟩ },
          { wRef with n2 := ⟨24, 25, 1⟩ }, { wRef with n2 := ⟨31, 32, 1⟩ }],
      ¬ Lawful (put (grp 11) w) ∧ LawfulBut (put (grp 11) w) := by decide +kernel

/-- the shift of the exponential's lookup key, against the library's own condition and this
library's rendering of the implementation's checks (`AttTests` of Inst/Model/ProgTests.lean;
that it says what the implementation checks is a reading, and no theorem) -/
example : ¬ ExpOK 3 2307 ∧ ¬ ExpOK 13 2307 ∧ ¬ AttTests 3 ∧ ¬ AttTests 13 := by decide +kernel
example : ∀ sh ∈ List.range' 4 9, ExpOK sh 2307 ∧ AttTests sh := by decide +kernel

end Inst.Model.ScalesGuard
