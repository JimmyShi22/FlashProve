-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartPsc.lean: from a sum of terms over maps to the parameters of a zero-knowledge
sumcheck (`PscOur` of Cb/Ld/LdPsc.lean), with its four conditions from degrees, and its claims
written out.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Part/LdPartPscProofs.lean.

Why: the reference request's front requires, of each of its sumchecks T : `PscOur E`, four
conditions (`VarsOK`, `ValInj`, `DegX`, `DegY`),
and whoever connects the blocks has to say what T's input claim and output rows say. Every sumcheck
that is built from a model's conditions has one form; so the four conditions and the claims are
stated once, here.
Degrees are counted as in a write-up of ours (lean/CREDITS.md; by inspection): for one
variable and one product, the maps in which the variable occurs (here: da a i, so a map of higher
degree can be counted too),
and the coefficient's degree in it; the forms add nothing. n i is the largest degree of a round
polynomial; the write-up bounds degrees strictly from above, so its number is one more. DY
is another number: the summand's degree in its revealed maps.

The form: k cube variables; finitely many maps a ∈ A, each a function F_a of (state, entries,
point); a list of terms, each a public coefficient (a function of state and point) and a list of
maps (with repeats). The summand at a point z is Σ over the terms t of coef_t(st, z) · Π over a in
t of F_a(st, m, z).
The incoming form `slS` is a linear form in the entries that the input claim adds to the sum
(`PscOur.SumHolds`, Cb/Ld/LdPsc.lean). An output row is a claim that the sumcheck leaves at the
verifier's point (`PscPar.UHolds`, `PscPar.EHolds`).

Main names:
  `LdPartTm`, `LdPartSm`: a term; the sum of terms over states St and entries J (parameters).
  `S.pol st z v`, `S.val st m z`: the summand: see their docstring.
  `LdPartMk S`: what the sumcheck adds: a degree n i for each variable; the degree DY in the dummy
    variable; the form slS of the masks that come in with the claim; the places wAt, cAt of its own
    masks.
  `S.our M : PscOur E`: all maps are revealed (B is empty); points are read as functions on the
    variables.
  `S.OK M da`: the conditions, for degrees da a i of the map a in the variable i.
    `map`: F_a has degree at most da a i in the i-th variable, at all states and all entries.
    `fit`: each term's coefficient has degrees dc with dc i + Σ over a in t (with repeats) of
      da a i ≤ n i for every variable i.
    `plain`: a variable under the plain form has 1 ≤ n i (`S.w st i = none`; why:
      `Spec.ldPartVars_ok`, Cb/Part/LdPartVars.lean).
    `dy`: no term has more than DY maps (with repeats).
  `Spec.ldPartPsc_ok`: `S.OK M da` ⇒ `VarsOK`, `ValInj`, `DegX`, `DegY` of `S.our M`.
  `Spec.ldPartPsc_sum`: the input claim (τ, st) of `S.our M` says: Σ over the corners b of
    (Π_i weight of the i-th form (`S.w st i`) at b i) · S.val st m (corner b) + Σ_j slS st j · m j
    = τ.
  `Spec.ldPartPsc_val`: the output row on the map a says: F_a(st, m, γ) + m (cAt a) · β = v_a, with
    γ, β the verifier's point read by `ldPartIni`, `ldPartLast`.
  `Spec.ldPartPsc_s0`: the public part of the output row on the hiding polynomial's coefficients:
    S0 at the verifier's point and the revealed values is S.pol st γ v; there is no other term (B
    is empty).

Limits: For arbitrary parameters: no family of conditions, no partition, no reading of cells here
(the family and the reading are put in by Cb/Part/LdPartPscFam.lean). This file does not say that
the maps are extensions of anything; what the entries are; where masks lie (wAt, cAt are letters;
that they are injective and apart is asked where zero knowledge is proved). n and DY are free above
the bounds (`S.OK`: `fit`, `plain`, `dy`): a larger number gives another protocol, with longer
messages and larger errors; that they are the least ones is not asked. This file says nothing on any
instance.
This form cannot say the following (by inspection, against the write-up; all four are
options there, and cost, not soundness, is what they change). Unrevealed maps (B is empty; the
write-up may leave maps in which the summand is affine unrevealed: they then stand in the
first output row;
each map that could have stayed costs here one scalar, one mask entry, one output claim, and may
raise DY). A sumcheck that reveals nothing (there: no dummy variable, no last round; here both still
run when A is empty). A first variable over a domain. An outer variable replaced by the point's
coordinate.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Part.LdPartVars

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

/-- A term: a public coefficient, a function of state and point; the maps whose product it
multiplies. -/
structure LdPartTm (E St A : Type) (k : ℕ) where
  coef : St → (Fin k → E) → E
  atoms : List A

/-- A sum of terms over maps: the data. St: the states (all that is public); J: the entries that
the maps read. Both are parameters, so that many sums of terms can be in one chain over one type of
states and one of entries. -/
structure LdPartSm (E St J : Type) where
  /-- the number of variables -/
  k : ℕ
  /-- the names of the maps -/
  A : Type
  [finA : Fintype A]
  F : St → (J → E) → A → (Fin k → E) → E
  terms : List (LdPartTm E St A k)
  /-- the form of each variable: the equality form at a scalar, or the plain form
  (Cb/Part/LdPartVars.lean) -/
  w : St → Fin k → Option E

attribute [instance] LdPartSm.finA

namespace LdPartSm
variable {E St J : Type} [Field E] (S : LdPartSm E St J)

/-- The summand, as a function of the point and of the maps' values; at the maps' own values. -/
def pol (st : St) (z : Fin S.k → E) (v : S.A → E) : E :=
  (S.terms.map fun t => t.coef st z * (t.atoms.map v).prod).sum
def val (st : St) (m : J → E) (z : Fin S.k → E) : E := S.pol st z fun a => S.F st m a z

end LdPartSm

/-- What the sumcheck adds: degrees, the incoming form, the places of its own masks. -/
structure LdPartMk {E St J : Type} [Field E] [Fintype E] (S : LdPartSm E St J) where
  n : Fin S.k → ℕ
  DY : ℕ
  slS : Slf E St J
  wAt : PIdx (ldPartFmt E S.k n ++ [pDummy E DY]) → J
  cAt : S.A → J

namespace LdPartSm
variable {E St J : Type} [Field E] [Fintype E] [Fintype J] (S : LdPartSm E St J) (M : LdPartMk S)

/-- a point of the sumcheck, as a function on the variables -/
abbrev fn (st : St) (X : HPt (pVars (ldPartFmt E S.k M.n) (ldPartDat E S.k M.n (S.w st)))) :
    Fin S.k → E :=
  ldPartFn S.k M.n (ldPartDat E S.k M.n (S.w st)) X

/-- The sumcheck. -/
@[reducible] def our : PscOur E where
  St := St
  J := J
  fmt := ldPartFmt E S.k M.n
  dat := fun st => ldPartDat E S.k M.n (S.w st)
  A := S.A
  B := Empty
  F := fun st m a X => S.F st m a (S.fn M st X)
  Fb := fun _ _ b _ => b.elim
  S0 := fun st X v => S.pol st (S.fn M st X) v
  S1 := fun _ _ _ b => b.elim
  DY := M.DY
  slS := M.slS
  wAt := M.wAt
  cAt := M.cAt

/-- The conditions, for degrees da of the maps. -/
structure OK (da : S.A → Fin S.k → ℕ) : Prop where
  map   : ∀ st m a, Alg.DegLE (da a) (S.F st m a)
  fit   : ∀ t ∈ S.terms, ∃ dc : Fin S.k → ℕ,
    (∀ st, Alg.DegLE dc (t.coef st)) ∧ ∀ i, dc i + (t.atoms.map fun a => da a i).sum ≤ M.n i
  plain : ∀ st i, S.w st i = none → 1 ≤ M.n i
  dy    : ∀ t ∈ S.terms, t.atoms.length ≤ M.DY

/-- the verifier's point, read off an output claim: the k coordinates; the dummy variable's
challenge -/
def outPt (o : (S.our M).par.Out) : Fin S.k → E := ldPartIni S.k M.n (pDummy E M.DY) o.pt
def outB (o : (S.our M).par.Out) : E := ldPartLast S.k M.n (pDummy E M.DY) o.pt

end LdPartSm

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

/-- The four conditions of the sumcheck. -/
def ldPartPsc_ok : Prop :=
  ∀ (St J : Type) [Fintype J] (S : LdPartSm E St J) (M : LdPartMk S) (da : S.A → Fin S.k → ℕ),
    S.OK M da → (S.our M).VarsOK ∧ (S.our M).ValInj ∧ (S.our M).DegX ∧ (S.our M).DegY

/-- What the input claim says. -/
def ldPartPsc_sum : Prop :=
  ∀ (St J : Type) [Fintype J] (S : LdPartSm E St J) (M : LdPartMk S) (τ : E) (st : St) (m : J → E),
    (S.our M).SumHolds (τ, st) m ↔
    ∑ b : Fin S.k → Bool, (∏ i, ldPartWt (S.w st i) (b i)) * S.val st m (Alg.corner b) +
        ∑ j, M.slS st j * m j = τ

/-- What the output row on a map's value says. -/
def ldPartPsc_val : Prop :=
  ∀ (St J : Type) [Fintype J] (S : LdPartSm E St J) (M : LdPartMk S)
      (o : (S.our M).par.Out) (m : J → E) (a : S.A),
    (S.our M).par.EHolds o m a ↔ S.F o.st m a (S.outPt M o) + m (M.cAt a) * S.outB M o = o.vals a

/-- The public part of the output row on the hiding polynomial's coefficients. -/
def ldPartPsc_s0 : Prop :=
  ∀ (St J : Type) [Fintype J] (S : LdPartSm E St J) (M : LdPartMk S) (o : (S.our M).par.Out),
    (S.our M).par.S0 o.st ((S.our M).par.hp o.st o.pt) o.vals = S.pol o.st (S.outPt M o) o.vals

end
end Spec
end
end Cb
