-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Scales.lean: which settings are valid (`Lawful`), and the relation on a request at given
settings (`RinfPP`).

The settings (the parameter table `ScalesAndPolicy`, Inst/Model/ProgTests.lean) hold scales for each of the 48
layers, the final normalisation and the acceptance policy: a model whose scales are fitted to its
weights has its own in every layer, while the reference parameters have one set for all. `Lawful pp`
is a list of inequalities between numbers of pp, hence decidable. For every layer: 5 ≤ kq, kk ≤ 32,
equal unless both are 16 or more; 1 ≤ kv, kg, kg', ku, ku' ≤ 24; 1 ≤ ko ≤ 19; 10 ≤ kd ≤ 19; 8 ≤ kr ≤
24. For the three kinds of normalisation: 24 ≤ M ≤ 47, 17 ≤ K ≤ 32, M ≤ K + 14, 1 ≤ ϵ < 2^48.
Further 4 ≤ sh ≤ 12, with one value in a group of four layers, and for the policy C < 2^32, θ ≤ C,
cap ≤ 1,024. So far this is `LawfulBut pp`; `Lawful` adds K ≤ M in every normalisation (the field
`km`; what it is for: its doc comment).

`RinfPP pp` is the relation at the settings pp: `RinfR` (Inst/Model/ProgramR.lean) with layer L at
the scales of layer L, the output head at pp's final normalisation, the lookup tables `tbRef`, and
pp's own policy. `RinfPP0 pp` is the same without the request's form: `RinfPP_iff` says `RinfPP` ↔
`Head3` ∧ `RinfPP0`. If the policy is `AcceptancePolicy.exact`, `RinfPP0` says that the program runs and every
covered token is the least token of largest logit (`rinfPP0_iff`).

  `lawful_iff`   `Lawful pp ↔ ProgTests pp`; its parts are `FFSeg.lawfulW_iff`, `attTests_iff`,
      `headTests_iff`, `polTests_iff`
  `ppRef`, `lawful_ref`, `rinfPP_ref`   the reference settings, with the scales of `ppref` in all
      layers and the policy `AcceptancePolicy.exact`; they are valid; at them `RinfPP0` is `RinfR0` at
      `ppref.scale` in all layers, `ppref.nf` and `tbRef`, under `AcceptancePolicy.exact`
  `clip`   pp if it is valid, the reference settings otherwise
  `LawfulK`, `lawfulK_of`   validity for functions κ, nf and one set of tables for each group of
      four layers, the more general form in which Inst/Model/All/NoWrapK.lean and
      Inst/Model/All/HonestK.lean are stated; valid settings satisfy it, with `tbRef` in every group
      (by `expOK_iff`, among others)

To audit the relation, read `Lawful`, `LawfulBut`, `LawfulK`, `RinfPP`, `RinfPP0`, `ppRef`, `clip`,
and the definitions into which `RinfPP0` and `RinfPP` unfold, in Inst/Model/ProgramR.lean,
Inst/Model/ProgramRPol.lean (`ModelR`, `RinfR0`), Inst/Model/Program.lean (`Instance`),
Inst/Model/ProgTests.lean (`ScalesAndPolicy`, `Words.scale`, `ScalesAndPolicy.kap`), Inst/Model/TablesRef.lean (`tbRef`; its
numbers: Inst/Model/TablesData.lean; `rotaryOff`: Inst/Model/Tables.lean) and, for `Lawful`,
Inst/Model/FF/ScalesDef.lean (`FFSeg.Ranges`).

Notation: `kq`, `kk`, `kv`, `ko`, `kg`, `ku`, `kd`, `kr`, `kg'`, `ku'`: natural numbers, the ten
shifts of a layer (`Params`, Inst/Model/Program.lean); `M`, `K`, ϵ (`eps`): "exponent of the
reciprocal; shift; constant" of a normalisation (`NormPar`, Inst/Model/Program.lean); `sh`: the
shift applied to mx − sc before the look-up in Exp, step (PA3) (`Params`); the policy line sh = 8 of
the first limit is another number (the comment at the top of Inst/Model/ProgramR.lean); `C`, θ
(`theta`), `cap`: the three numbers of the acceptance policy: the clip, the bound on the mean cost,
the limit on the number of positions above the clip (`AcceptancePolicy`, Inst/Model/ProgramR.lean); T, y, r, e:
an instance is a request: T tokens, the announced token y, and the two numbers r, e that bound the
covered positions: r ≤ t < e (`Instance`, Inst/Model/Program.lean).

Limits:
- `lawful_iff` compares two definitions of this library. Read against the implementation (a reading
  of its document and its verifier's source, no theorem), the theorems for valid settings are for
  all settings that pass the tests of the implementation's verifier under the reference parameter
  file (with their own lines C, theta, cap, which are numbers of the settings; the other policy
  lines are fixed: F = 24, sh = 8, sT = 4, the step table), meet condition 12 and the condition
  norm-shifts of the standard parameter form, and have the reference rotary pattern. The numbers kr,
  kg', ku' of a dense layer, which the implementation does not have, may be any valid numbers
  (Inst/Model/ProgTests.lean).
- No claim is made that settings of this file suit the weights of any real model (where the
reference settings' scales come from: lean/CREDITS.md, section 8). "For all valid settings" covers
fitted ones only if
  they are valid in the sense of this file and are used with the reference parameter file's sizes,
  digit forms, tables and rotary pattern (Inst/Model/ProgTests.lean lists what the settings do not
  hold). Several values of sh inside one group, which the implementation serves by one call for each
  value, are not valid here.
- Without the request's form, `RinfPP0` says less than it seems to (the comment at the top of
  Inst/Model/ProgramR.lean; Inst/Model/RequestGuards.lean).
- The reference settings are related to `Rinf ppref tbRef` on the request "the next token" only:
  `infR_next` (Inst/Model/RequestGuards.lean).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.ProgTests
import Inst.Model.ProgramK
import Inst.Model.ProgramR
import Inst.Model.ProgramRPol
import Inst.Model.ProgramRExact
import Inst.Model.FF.Scales
import Inst.Model.Att.Scales
import Inst.Model.TablesRef

set_option autoImplicit false

namespace Inst.Model

/-! ## 1. Validity, as intervals -/

/-- The settings are valid but for the clause K ≤ M: the intervals. The clause K ≤ M
is not among them (`Lawful` adds it). -/
structure LawfulBut (pp : ScalesAndPolicy) : Prop where
  /-- the shifts and the two normalisations of every layer: the closed intervals -/
  ff : ∀ L : Fin 48, FFSeg.Ranges (pp.w L).scale
  /-- the shift of the key of the exponential -/
  sh : ∀ L : Fin 48, 4 ≤ (pp.w L).sh ∧ (pp.w L).sh ≤ 12
  /-- one value in a group of four layers -/
  one : ∀ g : Fin 12, ∀ l : Fin 4, (pp.kap (4 * g + l)).sh = (pp.kap (4 * g)).sh
  /-- the final normalisation -/
  nf : pp.nf.OK
  /-- the three numbers of the policy -/
  pol : pp.pol.C < 2 ^ 32 ∧ pp.pol.theta ≤ pp.pol.C ∧ pp.pol.cap ≤ 1024

/-- The settings are valid: the intervals of `LawfulBut`, and K ≤ M in every normalisation. -/
structure Lawful (pp : ScalesAndPolicy) : Prop extends LawfulBut pp where
  /-- no normalisation shifts right by more bits than its reciprocal is scaled by: K ≤ M, in the two
  normalisations of every layer and in the final one. (From K = M + 3 on a normalisation's output is
  0 for every input: this is neither stated nor proved in this library.) -/
  km : (∀ L : Fin 48, (pp.w L).n1.K ≤ (pp.w L).n1.M ∧ (pp.w L).n2.K ≤ (pp.w L).n2.M) ∧
    pp.nf.K ≤ pp.nf.M

instance (pp : ScalesAndPolicy) : Decidable (LawfulBut pp) :=
  decidable_of_iff ((∀ L : Fin 48, FFSeg.Ranges (pp.w L).scale) ∧
      (∀ L : Fin 48, 4 ≤ (pp.w L).sh ∧ (pp.w L).sh ≤ 12) ∧
      (∀ g : Fin 12, ∀ l : Fin 4, (pp.kap (4 * g + l)).sh = (pp.kap (4 * g)).sh) ∧
      pp.nf.OK ∧
      (pp.pol.C < 2 ^ 32 ∧ pp.pol.theta ≤ pp.pol.C ∧ pp.pol.cap ≤ 1024))
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun h => ⟨h.ff, h.sh, h.one, h.nf, h.pol⟩⟩

instance (pp : ScalesAndPolicy) : Decidable (Lawful pp) :=
  decidable_of_iff ((∀ L : Fin 48, FFSeg.Ranges (pp.w L).scale) ∧
      (∀ L : Fin 48, 4 ≤ (pp.w L).sh ∧ (pp.w L).sh ≤ 12) ∧
      (∀ g : Fin 12, ∀ l : Fin 4, (pp.kap (4 * g + l)).sh = (pp.kap (4 * g)).sh) ∧
      pp.nf.OK ∧
      (pp.pol.C < 2 ^ 32 ∧ pp.pol.theta ≤ pp.pol.C ∧ pp.pol.cap ≤ 1024) ∧
      ((∀ L : Fin 48, (pp.w L).n1.K ≤ (pp.w L).n1.M ∧ (pp.w L).n2.K ≤ (pp.w L).n2.M) ∧
        pp.nf.K ≤ pp.nf.M))
    ⟨fun ⟨a, b, c, d, p, e⟩ => ⟨⟨a, b, c, d, p⟩, e⟩,
      fun h => ⟨h.ff, h.sh, h.one, h.nf, h.pol, h.km⟩⟩

/-! ## 2. It is `ProgTests`, this library's rendering of what the implementation tests -/

instance (sh : ℕ) : Decidable (AttTests sh) :=
  decidable_of_iff ((4 ≤ sh ∧ sh ≤ 12) ∧
      2307 + nd sh ≤ 2 ^ 16 ∧
      2 ^ 16 - 2307 - nd sh ≤ nd sh ∧
      cutC sh 2307 + 2 ^ 16 ≤ 2 ^ 24 ∧
      6 * Smax + 2 * cutC sh 2307 + 3 * 2 ^ 16 + 2 ^ 32 + 2 ^ 33 * (257 * 2 ^ 18 + 128 + 2 ^ 12) <
        2 ^ 61 - 1 ∧
      6 * Smax + 2 * cutC sh 2307 + 3 * 2 ^ 16 < 2 ^ 32)
    ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩,
      fun h => ⟨h.rng, h.room, h.fill, h.cut, h.n3, h.n4⟩⟩

/-- in the range 4 .. 12 all clauses of AttTests hold, and so does ExpOK at 2,307 rows in use -/
theorem att_in : ∀ sh ≤ 12, 4 ≤ sh → AttTests sh ∧ ExpOK sh 2307 := by decide +kernel

/-- `AttTests`, this library's rendering of the implementation's tests on sh, holds exactly for
sh = 4, .., 12. -/
theorem attTests_iff (sh : ℕ) : AttTests sh ↔ 4 ≤ sh ∧ sh ≤ 12 :=
  ⟨fun h => h.rng, fun h => (att_in sh h.2 h.1).1⟩

/-- At 2,307 rows in use the shift satisfies the library's `ExpOK` exactly for sh = 4, .., 12. -/
theorem expOK_iff (sh : ℕ) : ExpOK sh 2307 ↔ 4 ≤ sh ∧ sh ≤ 12 :=
  ⟨fun h => ⟨h.lo, h.hi⟩, fun h => (att_in sh h.2 h.1).2⟩

/-- the two no-overflow lines of the head's rounding hold on the whole range of M and K -/
theorem head_in :
    ∀ M ≤ 47, ∀ K ≤ 32,
      2 ^ 16 * 2 ^ K ≤ 2 ^ 60 ∧
      2 ^ M + 2 ^ 38 + 2 ^ (K - 1) + 2 ^ 15 * 2 ^ K + 2 ^ 16 * (257 * 2 ^ 18 + 32896) < 2 ^ 60 := by
  decide +kernel

/-- `HeadTests`, this library's rendering of the implementation's tests on the final normalisation,
is `NormPar.OK`. -/
theorem headTests_iff (nf : NormPar) : HeadTests nf ↔ nf.OK := by
  unfold NormPar.OK
  constructor
  · intro h
    exact ⟨h.eps.1, h.eps.2, h.M.1, h.M.2, h.K.1, h.K.2, by have := h.MK; omega⟩
  · rintro ⟨e1, e2, m1, m2, k1, k2, mk⟩
    exact ⟨⟨m1, m2⟩, by omega, ⟨k1, k2⟩, ⟨e1, e2⟩, (head_in _ m2 _ k2).1, (head_in _ m2 _ k2).2⟩

/-- `PolTests`, this library's rendering of the implementation's tests on the three policy lines, is
C < 2^32, θ ≤ C, cap ≤ 1,024: the other clauses follow. -/
theorem polTests_iff (pol : AcceptancePolicy) :
    PolTests pol ↔ pol.C < 2 ^ 32 ∧ pol.theta ≤ pol.C ∧ pol.cap ≤ 1024 :=
  ⟨fun h => ⟨h.lineC, h.mean, h.capT⟩,
    fun ⟨a, b, c⟩ => ⟨a, by omega, by omega, b, c, by omega, by omega, by omega, by omega⟩⟩

/-- Lawful pp holds if and only if ProgTests pp holds. The theorem compares two definitions of this
library. ProgTests (Inst/Model/ProgTests.lean) is this library's rendering, clause by clause, of the
tests of the implementation's verifier under the reference parameter file, with two conditions of
its standard parameter form. That it says what the implementation tests is a reading of its document
and its verifier's source, and no theorem. -/
theorem lawful_iff (pp : ScalesAndPolicy) : Lawful pp ↔ ProgTests pp :=
  ⟨fun h =>
      ⟨fun L => (FFSeg.lawfulW_iff _).2 (h.ff L), fun L => (attTests_iff _).2 (h.sh L), h.one,
        (headTests_iff _).2 h.nf, (polTests_iff _).2 h.pol, h.km⟩,
    fun h =>
      ⟨⟨fun L => (FFSeg.lawfulW_iff _).1 (h.layer L),
          fun L => (attTests_iff _).1 (h.att L),
          h.one,
          (headTests_iff _).1 h.head,
          (polTests_iff _).1 h.pol⟩,
        h.shifts⟩⟩

/-- Under `LawfulBut`, the policy is as the head's theorems require: C, θ < 2^40, cap < 2^16. -/
theorem LawfulBut.polOK {pp : ScalesAndPolicy} (h : LawfulBut pp) : pp.pol.OK :=
  ⟨by have := h.pol; omega, by have := h.pol; omega, by have := h.pol; omega⟩
theorem Lawful.polOK {pp : ScalesAndPolicy} (h : Lawful pp) : pp.pol.OK := h.toLawfulBut.polOK

instance (pp : ScalesAndPolicy) : Decidable (ProgTests pp) := decidable_of_iff _ (lawful_iff pp)

/-! ## 3. The relation at given settings -/

/-- R_inf at the settings pp, the inner relation: the integer program that runs layer L at the
scales of layer L, the head at pp's final normalisation, with the tables tbRef, runs on the
request's tokens, and the three clauses of pp's own policy pp.pol hold of its logits
(Inst/Model/ProgramR.lean: PolOK: (a) the mean of the clipped costs of the counted positions is at
most θ, (b) at most cap of them lie above the clip C, (c) if the last position is covered, y is the
least token of largest logit there); y is read where e = T only. Nothing on the request's form: at
e ≤ r it says "the program runs". On the request "the next token" it says: y is the next token,
whatever the policy. It renders "the model at these scales" for valid settings:
then no division by 0 is reached (Inst/Model/ScalesSanity.lean). -/
def RinfPP0 (pp : ScalesAndPolicy) : Index ppref → Instance ppref → Prop :=
  RinfR0 ppref pp.kap pp.nf (fun _ => tbRef) pp.pol

/-- R_inf at the settings pp, with the request's form: r < e ≤ T, y = 0 if e < T (Head3), no range
condition fails, and the clauses of pp's own policy hold. `RinfPP0` above is the inner relation,
without the request's form. That a verifier first checks the form of the instance is neither
stated nor proved in this file. -/
def RinfPP (pp : ScalesAndPolicy) : Index ppref → Instance ppref → Prop :=
  RinfR ppref pp.kap pp.nf (fun _ => tbRef) pp.pol
/-- At settings whose policy is exact match the inner relation says: the program runs, and every
covered token is the least token of largest logit at its position -/
theorem rinfPP0_iff {pp : ScalesAndPolicy} (h : pp.pol = AcceptancePolicy.exact) (i : Index ppref) (x : Instance ppref) :
    RinfPP0 pp i x ↔ RinfS0 ppref pp.kap pp.nf (fun _ => tbRef) i x := by
  unfold RinfPP0
  rw [h]
  exact (RinfS0_iff_exact ppref (by decide) _ _ _ i x).symm
theorem RinfPP_iff (pp : ScalesAndPolicy) (i : Index ppref) (x : Instance ppref) :
    RinfPP pp i x ↔ Head3 x ∧ RinfPP0 pp i x :=
  RinfR_iff0 _ _ _ _ _ i x

/-- the scales of the reference parameters -/
def wRef : Words := ⟨29, 29, 17, 17, 16, 20, 19, 17, 16, 20, ⟨44, 30, 53687⟩, ⟨44, 30, 53687⟩, 8⟩

theorem wRef_scale : wRef.scale = ppref.scale := rfl

/-- the reference settings: the scales of ppref in all layers; the policy of exact match -/
def ppRef : ScalesAndPolicy := ⟨fun _ => wRef, ppref.nf, AcceptancePolicy.exact⟩

theorem kap_ref : ppRef.kap = fun _ => ppref.scale := by
  funext L
  unfold ScalesAndPolicy.kap
  split <;> rfl

theorem lawful_ref : Lawful ppRef :=
  ⟨⟨fun _ => (by decide : FFSeg.Ranges wRef.scale),
      fun _ => (by decide : 4 ≤ wRef.sh ∧ wRef.sh ≤ 12),
      fun _ _ => by rw [kap_ref],
      by unfold NormPar.OK; decide,
      by decide⟩,
    ⟨fun _ => (by decide : wRef.n1.K ≤ wRef.n1.M ∧ wRef.n2.K ≤ wRef.n2.M),
      (by decide : ppref.nf.K ≤ ppref.nf.M)⟩⟩

/-- At the reference settings the inner relation is RinfR0 at ppref.scale for all layers,
ppref.nf and tbRef, under AcceptancePolicy.exact. (How it relates to R_inf, on next-token requests: `infR_next`,
Inst/Model/RequestGuards.lean.) -/
theorem rinfPP_ref :
    RinfPP0 ppRef = RinfR0 ppref (fun _ => ppref.scale) ppref.nf (fun _ => tbRef) AcceptancePolicy.exact := by
  unfold RinfPP0
  rw [kap_ref]
  rfl

/-- pp if it is valid, the reference settings otherwise -/
def clip (pp : ScalesAndPolicy) : ScalesAndPolicy := if Lawful pp then pp else ppRef

theorem clip_lawful (pp : ScalesAndPolicy) : Lawful (clip pp) := by
  unfold clip
  split
  · assumption
  · exact lawful_ref

theorem clip_of {pp : ScalesAndPolicy} (h : Lawful pp) : clip pp = pp := if_pos h

/-! ## 4. Validity in the form that the proofs use: functions -/

/-- the reference sizes of an attention segment, with u0 rows of the exponential's table in use -/
def AttSeg.Dim.refK (u0 : ℕ) : AttSeg.Dim := { AttSeg.Dim.ref with u0 := u0 }

theorem AttSeg.refK_ref : AttSeg.Dim.refK 2307 = AttSeg.Dim.ref := rfl

/-- If s and P have the same number of rows of the exponential's table in use, `Tables.OK` at
`P.at s` is `Tables.OK` at P. -/
theorem Tables.OK_at {P : Params} {s : LayerScale} {tb : Tables} (h : s.expRows = P.expRows) :
    tb.OK (P.at s) ↔ tb.OK P := by
  have e : (P.at s).expRows = P.expRows := h
  unfold Tables.OK
  rw [e]
  exact Iff.rfl

/-- the tables of layer L, when each group of four layers has one set -/
def tbsOf (tbG : ℕ → Tables) : ℕ → Tables := fun L => tbG (L / 4)

/-- The scales (κ, nf), with the lookup tables tbG of the 12 groups, are valid. -/
structure LawfulK (κ : ℕ → LayerScale) (nf : NormPar) (tbG : ℕ → Tables) : Prop where
  /-- the shifts and the two normalisations of every layer -/
  ff : ∀ L < 48, FFSeg.LawfulW (κ L)
  /-- the final normalisation -/
  nf : nf.OK
  /-- one shift of the key of the exponential, and one number of rows in use, in a group -/
  one : ∀ g < 12, ∀ l < 4, (κ (4 * g + l)).sh = (κ (4 * g)).sh
  rows : ∀ g < 12, ∀ l < 4, (κ (4 * g + l)).expRows = (κ (4 * g)).expRows
  /-- the pair satisfies `ExpOK` -/
  ex : ∀ g < 12, ExpOK (κ (4 * g)).sh (κ (4 * g)).expRows.toNat
  /-- the ranges of the tables of a group -/
  tab : ∀ g < 12, (tbG g).OK (ppref.at (κ (4 * g)))

theorem ScalesAndPolicy.kap_lt (pp : ScalesAndPolicy) {L : ℕ} (h : L < 48) : pp.kap L = (pp.w ⟨L, h⟩).scale := dif_pos h

/-- Valid settings satisfy `LawfulK`, with tbRef in every group. -/
theorem lawfulK_of {pp : ScalesAndPolicy} (h : Lawful pp) : LawfulK pp.kap pp.nf fun _ => tbRef where
  ff := fun L hL => by
    rw [pp.kap_lt hL]
    exact (FFSeg.lawfulW_iff _).2 (h.ff _)
  nf := h.nf
  one := fun g hg l hl => h.one ⟨g, hg⟩ ⟨l, hl⟩
  rows := fun g hg l hl => by
    rw [pp.kap_lt (show 4 * g + l < 48 by omega), pp.kap_lt (show 4 * g < 48 by omega)]
    rfl
  ex := fun g hg => by
    rw [pp.kap_lt (show 4 * g < 48 by omega)]
    exact (expOK_iff _).2 (h.sh _)
  tab := fun g hg => (Tables.OK_at (by rw [pp.kap_lt (show 4 * g < 48 by omega)]; rfl)).2 tbRef_ok

end Inst.Model
