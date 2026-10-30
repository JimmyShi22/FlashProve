-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/ProgTests.lean: the settings (the parameter table `ScalesAndPolicy`), and this library's rendering of
the tests that the implementation's verifier makes on them.

`ScalesAndPolicy` holds the scales of the 48 layers (`Words`: ten shifts, two normalisations, and the shift sh of
the key of attention's exponential), the final normalisation, and the three numbers C, theta, cap of
the acceptance policy. `ProgTests pp` lists what the implementation's verifier tests on these
numbers under the reference parameter file (`LayerTests`, `AttTests`, `HeadTests`, `PolTests`), with
two conditions of its standard parameter form: one value of sh in a group of four layers (the
condition one-shift), and K ≤ M in every normalisation (the condition norm-shifts). `KLFile` is
the implementation's own public input (the file of scales and eight lines of the parameter file);
`ofKL` gives the settings that it encodes, or `none` if its rotary flags are not the reference
pattern. The file has definitions only.

A theorem "for all settings pp" is worth as much as the set of settings at which its relation is not
empty. For the relation `Lawful pp` together with `RinfPP pp`, that set is `Lawful pp`, and
`lawful_iff : Lawful pp ↔ ProgTests pp` (both in Inst/Model/Scales.lean) compares two definitions
of this library. Read against the implementation it says: the library's theorems for valid settings
are for all settings that pass the tests of the implementation's verifier under the reference
parameter file, meet the conditions one-shift and norm-shifts and have the reference rotary
pattern; the numbers kr,
kg', ku' of a dense layer, which the implementation does not have, may be any valid numbers.

Error names in square brackets are those of the implementation's verifier
(verifier/src/cp_verify.cpp, verifier/src/vf_attention_shape.h); at a test, words in quotation
marks state it in the implementation's symbols. The tests one by one, under these names, are in
docs/format/FORMAT.md, section 13.8; the standard parameter form, with its conditions by name, in
section 13.7 there. Every test is evaluated at the sizes,
digit forms and table lines of the reference parameter file (d = 5,120, f = 16,384, dh = 128,
T = 1,024, kFD = 16, S = 12, rx = 8, so u0 = 2,307 rows of the exponential's table are in use; digit
form 2 for queries and keys, 1 for the six other classes).

Limits:
- That `ProgTests` says what the implementation tests is a reading of its verifier's source, which
  is outside lean/, and no theorem. Every clause was compared with the source line by line, and the
  accepted sets were recomputed from the C++ text; they agree with the intervals of
  Inst/Model/Scales.lean and with 4 ≤ sh ≤ 12. No program of the implementation was run for it.
- The conditions one-shift and norm-shifts are not tests that reject. Without them a run of the
implementation ends as
  "not a verification"; a planning call, which ends as "plan only" either way, does not show the
  difference, and an accepting run does.
- Three tests have no clause of their name. [KL-length], the file of scales has exactly 13 L + 3 L /
  2 little-endian 32-bit words: of this the type of `KLFile` has the counts only, not the width.
  [policy-norm], 1 ≤ eps1, eps2 < 2^59, is the only origin of the lower bound on ϵ in `n1.OK`,
  `n2.OK` (Inst/Model/FF/ScalesDef.lean). [policy-norm-F] has two lines, and `HeadTests` renders
  both.
- Narrower than the implementation: the five lookup tables are the fixed `tbRef` (the conditions
  table-digests, no-range-words, softmax-table and rotary-table of the standard parameter form fix
  them in every run that can end in a verification, but for theta0's two values and the flags rp).
- Narrower: the rotary flag rp of a layer, which the implementation tests to be 0 or 1 [KL-rp], is
  here the fixed pattern "off in the layers L with L mod 4 = 3". No test of the implementation says
  that a file has this pattern, and the rotary table's digest does not depend on rp.
- Narrower: the digit forms, the sizes and all other lines of the parameter file are the reference
  file's. Of its policy lines, C, theta, cap are free within `PolTests`; F = 24, sh = 8 (the policy
  line sh, not the shift sh of `Words`) and sT = sh − 4 (the step table, under which the cost of a
  position is its logit gap plus 2^8: `costOf`, Inst/Model/ProgramR.lean) are fixed. The
  implementation also takes sh = 7 and the exponential tables sT = sh + 4 .. sh + 10; nothing here
  is about those. The line s is printed and is in no equation.
- The intervals depend on these lines of the reference file, which no "YES" of the implementation
  fixes: L, ll, d, f, H, dh, the seven digit forms, kFD. The rest of what the clauses assume (five
  limbs, both clamps, S = 12, rx = 8, no eg, no smax, routed experts, profile 4) every accepting run
  has, by the standard parameter form.
- Wider than the implementation: each layer has its own regularizers (the implementation: one eps1
  and one eps2 for the model), and every layer has kr, kg', ku' (the implementation: layers with
  experts only); they are tested in every layer.
- Nothing here checks a fitted set of parameters, and no settings are written out in this file.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.FF.ScalesDef
import Inst.Model.Tables
import Inst.Model.ProgramR

set_option autoImplicit false

namespace Inst.Model

deriving instance DecidableEq for NormPar
deriving instance DecidableEq for LayerScale

/-- The scales of one layer in the settings. In the implementation's file of scales a layer's record
is kq kk kv ko kg ku kd M_1 K_1 M_2 K_2 sh rp, and a layer with experts has kr kgR kuR besides
(docs/format/FORMAT.md, section 13.4, step 2; docs/model.md, section 3). -/
structure Words where
  kq : ℕ
  kk : ℕ
  kv : ℕ
  ko : ℕ
  kg : ℕ
  ku : ℕ
  kd : ℕ
  kr : ℕ
  kg' : ℕ
  ku' : ℕ
  n1 : NormPar
  n2 : NormPar
  sh : ℕ
deriving DecidableEq

/-- the scales as the integer program reads them; 2,307 rows of the exponential's table are in use
-/
def Words.scale (w : Words) : LayerScale :=
  ⟨w.kq, w.kk, w.kv, w.ko, w.kg, w.ku, w.kd, w.kr, w.kg', w.ku', w.n1, w.n2, 2307, w.sh⟩

deriving instance DecidableEq for AcceptancePolicy

/-- The settings: the scales of the 48 layers, the final normalisation, and the three numbers of
the acceptance policy. -/
structure ScalesAndPolicy where
  w : Fin 48 → Words
  nf : NormPar
  /-- the clip C, the bound theta on the mean cost, the limit cap on the number of positions above
  the clip -/
  pol : AcceptancePolicy
deriving DecidableEq

/-- the scales of layer L, as the integer program reads them; beyond the last layer, which nothing
reads, the reference scales -/
def ScalesAndPolicy.kap (pp : ScalesAndPolicy) : ℕ → LayerScale := fun L =>
  if h : L < 48 then (pp.w ⟨L, h⟩).scale else ppref.scale

/-- The rendering of the tests on a layer's shifts and normalisations. -/
abbrev LayerTests (w : Words) : Prop := FFSeg.LawfulW w.scale

/-- The rendering of the tests that read the shift sh of the key of the exponential
(docs/format/FORMAT.md, section 13.8, from af-policy-kF on), at u0 = 2,307 and kFD = 16. "C = 2^sh
u0,
rho = 2^16 − 2^sh, nHD = ceil((4 Smax + 1) / rho)" are cutC, stp, nd of Inst/Model/Tables.lean;
Smax = dh QM² = 128 · 2,047². -/
structure AttTests (sh : ℕ) : Prop where
  /-- the range of the shift: "4 .. 12" [af-shape-sh, af-policy-sh] -/
  rng : 4 ≤ sh ∧ sh ≤ 12
  /-- "for every shift value, u0 + nHD <= 2^kFD and 2^kFD − u0 − nHD <= nHD"
  [af-policy-kF] -/
  room : 2307 + nd sh ≤ 2 ^ 16
  fill : 2 ^ 16 - 2307 - nd sh ≤ nd sh
  /-- "C + 2^16 <= 2^24" [af-policy-C] -/
  cut : cutC sh 2307 + 2 ^ 16 ≤ 2 ^ 24
  /-- [af-no-wrap-N3]: "6 Smax + 2 C + 3 x 2^16 + 2^32 + 2^33 (Ty_2 + 128 + 2^S) < p",
  Ty_2 = 257 · 2^18, S = 12, p = 2^61 − 1 -/
  n3 : 6 * Smax + 2 * cutC sh 2307 + 3 * 2 ^ 16 + 2 ^ 32 + 2 ^ 33 * (257 * 2 ^ 18 + 128 + 2 ^ 12) <
    2 ^ 61 - 1
  /-- [af-no-wrap-N4]: "6 Smax + 2 C + 3 x 2^16 < 2^32" -/
  n4 : 6 * Smax + 2 * cutC sh 2307 + 3 * 2 ^ 16 < 2 ^ 32

/-- The rendering of the tests on the final normalisation (docs/format/FORMAT.md, section 13.8,
policy-norm-F). -/
structure HeadTests (nf : NormPar) : Prop where
  /-- "24 <= MF <= 47; MF <= KF + 14; 17 <= KF <= 32" [policy-norm-F] -/
  M : 24 ≤ nf.M ∧ nf.M ≤ 47
  MK : nf.M ≤ nf.K + 14
  K : 17 ≤ nf.K ∧ nf.K ≤ 32
  /-- "1 <= epsF < 2^59, and with five limbs epsF < 2^48" [policy-norm-F, no-wrap-ledger-eps] -/
  eps : 1 ≤ nf.eps ∧ nf.eps < 2 ^ 48
  /-- "2^16 2^KF <= 2^60" [no-wrap-H-U-NF] -/
  U : 2 ^ 16 * 2 ^ nf.K ≤ 2 ^ 60
  /-- "2^MF + 2^38 + 2^(KF−1) + 2^15 2^KF + 2^16 (257 Ty + 32,896) < 2^60" [no-wrap-H-W-NF], Ty =
  2^18 -/
  W : 2 ^ nf.M + 2 ^ 38 + 2 ^ (nf.K - 1) + 2 ^ 15 * 2 ^ nf.K + 2 ^ 16 * (257 * 2 ^ 18 + 32896) <
    2 ^ 60

/-- The rendering of the tests on the three policy lines C, theta, cap
(docs/format/FORMAT.md, section 12.5, policy-gap-words; the no-overflow checks on the output
head's
claims on the hidden numbers), at T = 1,024. The head's other
no-overflow conditions name none of the three numbers ([no-wrap-H-three-digits] uses C < 2^32
through the numeral 2^32). -/
structure PolTests (pol : AcceptancePolicy) : Prop where
  /-- docs/format/08-parameters.md, section 8.6: a value line of the parameter file has a name and
a value
  below 2^32 [policy-line-<i>] -/
  lineC : pol.C < 2 ^ 32
  lineTheta : pol.theta < 2 ^ 32
  lineCap : pol.cap < 2 ^ 32
  /-- "theta <= C" [policy-gap-words] -/
  mean : pol.theta ≤ pol.C
  /-- "cap <= T (greater values would give the same statement)" [policy-gap-words] -/
  capT : pol.cap ≤ 1024
  /-- "cap < 2^16 (z has two digits)" [policy-gap-words] -/
  cap16 : pol.cap < 2 ^ 16
  /-- "T (2^40 + 2^8 C + 2^40) + theta T < 2^60" [no-wrap-H-E2] -/
  E2 : 1024 * (2 ^ 40 + 2 ^ 8 * pol.C + 2 ^ 40) + pol.theta * 1024 < 2 ^ 60
  /-- "T (2^8 + 2^16) + cap < 2^60" [no-wrap-H-E3] -/
  E3 : 1024 * (2 ^ 8 + 2 ^ 16) + pol.cap < 2 ^ 60
  /-- "2^40 + 2^40 + C < 2^60" [no-wrap-H-E4] -/
  E4 : 2 ^ 40 + 2 ^ 40 + pol.C < 2 ^ 60

/-- This library's rendering of the tests of the implementation's verifier on the settings, under
the reference parameter file, with two conditions of its standard parameter form (the fields one and
shifts). That it says what the implementation tests is a reading, and no theorem. -/
structure ProgTests (pp : ScalesAndPolicy) : Prop where
  layer : ∀ L : Fin 48, LayerTests (pp.w L)
  att : ∀ L : Fin 48, AttTests (pp.w L).sh
  /-- a condition of the standard parameter form (docs/format/FORMAT.md, section 13.7): in each
  layer group the softmax key shift has one value [one-shift]. A group has four layers. -/
  one : ∀ g : Fin 12, ∀ l : Fin 4, (pp.kap (4 * g + l)).sh = (pp.kap (4 * g)).sh
  head : HeadTests pp.nf
  /-- the tests on the policy's three numbers -/
  pol : PolTests pp.pol
  /-- a condition of the standard parameter form (docs/format/FORMAT.md, section 13.7): K <= M in
  every norm: in KL for the two norms of each layer, and KF <= MF in the lines KF and MF of the
  parameter file [norm-shifts]. In the C++ verifier's source: normShifts = KF <= MF, and for every
  layer K1 <= M1 && K2 <= M2 (verifier/src/cp_verify.cpp). There it is a condition of the standard
  form and no rejection: a file with K above M is still read, planned and judged, and the call ends
  at best NOT-A-VERIFICATION; a plain YES needs the condition. In `Spec.ledger_lang`
  (Policy/Rel/LedgerRelLaws.lean), which names `RinfPP`, valid settings are a hypothesis
  (`LedgerRel.TableOK pp`, which `Lawful pp` gives: `tableOK_of_lawful`).
  The implementation's committer, at the threshold of bits, asks the verifier's planning call first
  and makes no commitment under files that miss a condition of the standard form
  [cp-commit-not-standard]; its own parsers of the files, the
  prover's and the reference's do not know the rule. All this on the implementation is a reading of
  its source (not held against these sources' cp_verify.cpp); no Lean statement of this
  file is about the implementation. -/
  shifts : (∀ L : Fin 48, (pp.w L).n1.K ≤ (pp.w L).n1.M ∧ (pp.w L).n2.K ≤ (pp.w L).n2.M) ∧
    pp.nf.K ≤ pp.nf.M

/-! ## The implementation's own public input -/

/-- The implementation's public numbers: the file of scales, 13 little-endian 32-bit words per layer
in the order kq kk kv ko kg ku kd M1 K1 M2 K2 sh rp; then, after the last layer's 13 words, 3 words
kr kgR kuR for each mixture-of-experts layer, in increasing order of the layer number
(docs/model.md, section 3), and the lines eps1, eps2, MF, KF, epsF, C, theta, cap of the parameter
file. -/
structure KLFile where
  lay : Fin 48 → Fin 13 → ℕ
  moe : Fin 24 → Fin 3 → ℕ
  eps1 : ℕ
  eps2 : ℕ
  MF : ℕ
  KF : ℕ
  epsF : ℕ
  C : ℕ
  theta : ℕ
  cap : ℕ

/-- the rotary flags are the reference pattern: 1 in every layer but each fourth (L mod 4 = 3) -/
def KLFile.rpRef (f : KLFile) : Prop := ∀ L : Fin 48, f.lay L 12 = if L.val % 4 = 3 then 0 else 1

instance (f : KLFile) : Decidable f.rpRef := by unfold KLFile.rpRef; infer_instance

/-- the scales of layer L. If NE > 0, "the odd layers are mixture-of-experts layers and the even
layers are dense" (docs/model.md, section 2; hasExperts of Inst/Model/Program.lean); so layer
2 e + 1 has the record e. A dense layer, which has no numbers kr, kgR, kuR, gets the reference's 17,
16, 20. -/
def KLFile.words (f : KLFile) (L : Fin 48) : Words where
  kq := f.lay L 0
  kk := f.lay L 1
  kv := f.lay L 2
  ko := f.lay L 3
  kg := f.lay L 4
  ku := f.lay L 5
  kd := f.lay L 6
  kr := if L.val % 2 = 1 then f.moe ⟨L.val / 2, by omega⟩ 0 else 17
  kg' := if L.val % 2 = 1 then f.moe ⟨L.val / 2, by omega⟩ 1 else 16
  ku' := if L.val % 2 = 1 then f.moe ⟨L.val / 2, by omega⟩ 2 else 20
  n1 := ⟨f.lay L 7, f.lay L 8, f.eps1⟩
  n2 := ⟨f.lay L 9, f.lay L 10, f.eps2⟩
  sh := f.lay L 11

/-- The settings that the implementation's public numbers encode; `none` if the rotary flags are not
the reference pattern. -/
def ofKL (f : KLFile) : Option ScalesAndPolicy :=
  if f.rpRef then some ⟨f.words, ⟨f.MF, f.KF, f.epsF⟩, ⟨f.C, f.theta, f.cap⟩⟩ else none

end Inst.Model
