-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBatt.lean: the batching of tensor rows on one matrix at several points into one tensor row.

A batching step of an interactive oracle proof. Several linear claims on one matrix, each on the
value at a point of the multilinear extension of a combination of its rows, are reduced to one claim
of that kind: by a random linear combination, then a sumcheck over the columns.
The parameters, the term, the honest side, the joints (`IOR.Rels`, Ior/Chain.lean), the letters of
its zero-knowledge item (`B.maskData`; the item: `Honest.MM`, Ior/Masked.lean; both are told below),
and the statements. Proofs: Cb/Ld/LdBattProofs.lean.
At the base: between joints without a signature, in which the tuple of messages is a part of the
witness (`baseIn`, `baseOut`).

Among the entries m : J → E of the statement's messages lie those of a matrix M with rows named by
Rw and columns on the cube of k variables (`mAt`). A tensor row is < v ⊗ eq(z, ·), M > = the
multilinear extension, at the point z, of the vector vᵀM on the columns (`ten v z m`). Input: for
each name q in a finite set Q a claim with public target:
    < g_q ⊗ eq(ψ_q, ·), M > + < incoming mask form q, m > = τ_q.
(Such claims are left by earlier sumchecks that reveal a masked value of g_qᵀM at their last point:
the incoming form reads that value's mask.)

The protocol is a corollary of the sumcheck for a polynomial summand (Cb/Ld/LdPsc.lean), used with
no revealed map: no dummy variable, no last round, no value in the clear.
  Round 1: the prover sends nothing; the verifier sends the seed of a zero-evader (`Cb.Evader`) with
    one coefficient χ_q for each claim. The claims become one: ∑_q χ_q (left side q) = ∑_q χ_q τ_q
    (`Spec.batt_sum`).
  Then the rounds of that sumcheck (`PscPar.core` at the parameters `B.par`): the sum of a hiding
    polynomial; the coefficient ε; one round for each column variable. The summand is affine in its
    maps, none is revealed.
  Output: one row with public target (`Spec.batt_row`, if 1 ≤ n):
    ε < ( ∑_q χ_q eq(ψ_q, γ) g_q ) ⊗ eq(γ, ·), M >
      + (hiding polynomial's form at γ, on the own masks)
      + ε γ_1 .. γ_k ∑_q χ_q < form q, m > = the last value.
Rounds: 1 + 1 + k; nothing is merged. Errors, as counts: the evader's number; 1 of |E|; n for each
column variable (n ≥ 2 is the degree of the round polynomials). No query, no oracle. Extractor: the
identity. Completeness is perfect. (Errors, extractor, completeness: `Spec.batt_goodAt`, under its
hypotheses.)

`Cb.GoodAt` asks, of a reduction with its honest side between two joints whose witnesses pair a
value of one type M with a further witness, the clauses of `GoodB` with two differences: a further
clause `same` asks that, on every run, the honest prover's output witness carries the M-part of its
input witness unchanged; and the clause `know`, in place of `GoodB`'s, asks, for each fixed m of
type M, round-by-round knowledge soundness (`Know`) on the input joint's set of statements and at
the numbers' list of errors, as `GoodB`'s does, but between the relaxed relations at (m, ·) and with
the extractor `ext m`. `GoodB` is `IOR.GoodT` without its clause on zero knowledge. `IOR.GoodT`
(likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its honest side,
between two joints, at given numbers; among its clauses: completeness between the honest relations,
outside sets of verifier randomness whose probabilities further clauses bound by the numbers;
round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input joint's set
of statements, with a given extractor, at the numbers' list of errors; and one on honest-verifier
zero knowledge. `MaskData R Wi` is a structure: a type `Kc` with `kc : Wi → Kc`; a type `Xp` with
`pub : Xi → Xp`; a finite, non-empty type `Mk` with `put : Mk → Kc → Kc`; a predicate `Cl` on `Xp`
and `Kc`; `msg`, from `Kc`, `Xp` and the verifier's randomness ρ to plain parts; and `sim`, from
`Xp` and ρ to distributions on plain parts. `H.MM D` asks five things: the block sends no oracle;
`H.withheld w x` is always empty; the honest prover's plain parts are `D.msg` at `D.kc w`, `D.pub x`
and ρ; `D.Cl` is kept under `D.put`; and where `D.Cl xp k` holds, `D.msg (D.put M k) xp ρ` over
uniform M has the distribution `D.sim xp ρ`. `GoodM` is `GoodB` (`GoodT` without the clause `exact`)
with `H.MM D`, and the clause that every (x, y, w) in the honest relation meets
`D.Cl (D.pub x) (D.kc w)`. In this file `GoodAt` is the conclusion of `Spec.batt_goodAt`, `MM` that
of `Spec.batt_mm`, and `GoodM` that of `Spec.batt_goodM_sig`.

Zero knowledge. Under the hypotheses of `Spec.batt_mm`, the draw sends nothing, so "draw, then the
rounds" is one masked block (Ior/MaskedDraw.lean). Own masks: the k n + 1 coefficients of the hiding
polynomial, at `wAt`. Its item "masked messages" has the letters `B.maskData`; the simulator reads
the targets, the state and the verifier's messages. Conditions (2 ≤ `B.n`; `B.OwnOK Rd`): the own
entries lie at different places, none is an entry of the matrix, no incoming form reads one; the
block reads the entries in Rd only.

Main names:
  `Spec.batt_goodAt`: if 2 ≤ `B.n` and `B.Z.OK`: at the base, for each fixed tuple of messages
    (`GoodAt`, Cb/Ld/LdSigLift.lean; told above): complete; round-by-round knowledge sound, the
    identity extracts, the errors above.
  `Spec.batt_mm`: the item at the base (under the conditions above: 2 ≤ `B.n`; `B.OwnOK Rd`).
  `Spec.batt_goodM_sig`: if 2 ≤ `B.n`, `B.Z.OK` and `B.OwnOK Rd`: over a signature S: the bundle
    `GoodM` (Ior/Masked.lean).

Why at the base: in the protocols that we follow the matrix is always an encoded index: an oracle
that is no oracle message of a signature, but is decoded by the statement; the masks lie in an
oracle message of the instance. So what is used there are `batt_goodAt` and `batt_mm`, for a type M
of tuples that holds the index's message beside the messages of S, through a lifting rule for claims
that read such a further oracle.

Limits: `batt_goodM_sig`, with the matrix among the messages of S, is the plain case of the rule of
Cb/Ld/LdSigLift.lean, and renders no use of those protocols. The item's law fixes all entries but
the own masks, the matrix's too. This file does not say in which oracle matrix and masks lie (J
names all entries). It does not say that lifting rule (for claims that read a further oracle). It
says nothing on running times or succinct forms.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdPscGood
import Cb.Ld.LdPscVars
import Cb.Gen.BatEvader
import Ior.MaskedDraw

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

/-- The parameters. -/
structure BattPar (E : Type) [Field E] [Fintype E] where
  /-- states: all that is public but the targets -/
  St : Type
  /-- the entries of all messages, masks included -/
  J : Type
  [finJ : Fintype J]
  /-- the rows of the matrix; its columns are the cube of k variables; where its entries lie -/
  Rw : Type
  [finRw : Fintype Rw]
  k : ℕ
  mAt : Rw × (Fin k → Bool) → J
  /-- the names of the claims; their row vectors, points and incoming mask forms -/
  Q : Type
  [finQ : Fintype Q]
  g : St → Q → Rw → E
  pt : St → Q → Fin k → E
  slM : Q → Slf E St J
  /-- the coefficients -/
  Z : Evader E Q
  /-- the largest degree of a round polynomial -/
  n : ℕ
  /-- where the coefficients of the hiding polynomial lie -/
  wAt : PIdx (List.replicate k (pfCube E n)) → J

attribute [instance] BattPar.finJ BattPar.finRw BattPar.finQ

namespace BattPar
variable {E : Type} [Field E] [Fintype E] (B : BattPar E)

/-- vᵀM, a vector on the columns; the tensor row < v ⊗ eq(z, ·), M > -/
def col (m : B.J → E) (v : B.Rw → E) : (Fin B.k → Bool) → E := fun c => ∑ r, v r * m (B.mAt (r, c))
def ten (v : B.Rw → E) (z : Fin B.k → E) (m : B.J → E) : E := Alg.mle (B.col m v) z

/-- the left side of the claim q -/
def lhs (st : B.St) (q : B.Q) (m : B.J → E) : E :=
  B.ten (B.g st q) (B.pt st q) m + ∑ j, B.slM q st j * m j

/-- The claims of the input statement x = (targets, state). -/
def InHolds (x : (B.Q → E) × B.St) (m : B.J → E) : Prop := ∀ q, B.lhs x.2 q m = x.1 q

abbrev fmt : List (PFmt E) := List.replicate B.k (pfCube E B.n)
/-- a point as a function of the column variable -/
abbrev fn (X : HPt (pVars B.fmt (pdPlains E B.n B.k))) : Fin B.k → E :=
  hFnOf (pfCube E B.n) B.k (pdPlains E B.n B.k) X

/-- The parameters of the sumcheck: plain weights on the cube of the columns; no revealed map; one
map for each claim. -/
def par : PscPar E where
  St := B.St × B.Z.D
  J := B.J
  fmt := B.fmt
  dat := fun _ => pdPlains E B.n B.k
  A := Empty
  B := B.Q
  G := fun _ _ a _ => a.elim
  Gb := fun st m q X => Alg.mle (B.col m (B.g st.1 q)) (B.fn X)
  S0 := fun _ _ _ => 0
  S1 := fun st X _ q => B.Z.ze st.2 q * Alg.eqPt (B.pt st.1 q) (B.fn X)
  slS := fun st j => ∑ q, B.Z.ze st.2 q * B.slM q st.1 j
  wAt := B.wAt

/-- the one claim after the draw: the combination of the targets; the seed joins the state -/
def nx (x : (B.Q → E) × B.St) (ρ : B.Z.D) : E × B.par.St := (∑ q, B.Z.ze ρ q * x.1 q, (x.2, ρ))

variable (Ex : ExtSpec)

/-- The block. -/
def batt : IOR ((B.Q → E) × B.St) Ex B.par.Mid Ex := (IOR.draw B.Z.D B.nx Ex).seq (B.par.core Ex)

/-- The honest side: no coins; nothing is withheld; the witness stays. -/
def hon {Wt : Type} (msg : Wt → B.J → E) : (B.batt Ex).Honest Wt Wt :=
  (IOR.Honest.draw B.Z.D B.nx Ex Wt).seq (B.par.honC Ex msg)

/-- The numbers. -/
def nums (Kc : Type) : IOR.Nums Kc (B.batt Ex) :=
  (IOR.Nums.draw Kc B.Z.D B.nx Ex B.Z.err).seq (B.par.numsC Ex Kc)

/-- the point of the output claim, as a function of the column variable; the coefficients -/
def outPt (z : B.par.Mid) : Fin B.k → E := B.fn (B.par.hp z.st z.pt)
def chi (z : B.par.Mid) (q : B.Q) : E := B.Z.ze z.st.2 q

/-- The output claim as one row. -/
def RowHolds (z : B.par.Mid) (m : B.J → E) : Prop :=
  z.eps * B.ten (fun r => ∑ q, B.chi z q * Alg.eqPt (B.pt z.st.1 q) (B.outPt z) * B.g z.st.1 q r)
          (B.outPt z) m +
      ∑ i, hSl (B.par.vars z.st) (B.par.hp z.st z.pt) i *
        m (B.wAt (pIx B.fmt (pdPlains E B.n B.k) i)) +
      z.eps * (∏ i, B.outPt z i) * ∑ q, B.chi z q * ∑ j, B.slM q z.st.1 j * m j = z.fin

/-- The joints at the base: A0, any joint on (state, oracles, witness), is carried along unchanged
beside the claims. -/
def baseIn {Kc Wt : Type} (A0 : IOR.Rels Kc B.St Ex Wt) (msg : Wt → B.J → E) :
    IOR.Rels Kc ((B.Q → E) × B.St) Ex Wt where
  rel := fun x y w => A0.rel x.2 y w ∧ B.InHolds x (msg w)
  relR := fun a w => A0.relR (a.1.2, a.2) w ∧ B.InHolds a.1 (msg w)
  on := fun a => A0.on (a.1.2, a.2)
  core := A0.core
def baseOut {Kc Wt : Type} (A0 : IOR.Rels Kc B.St Ex Wt) (msg : Wt → B.J → E) :
    IOR.Rels Kc B.par.Mid Ex Wt :=
  B.par.baseMid (A0.keepX B.Z.D) msg

/-- The conditions on the own entries. -/
structure OwnOK (Rd : B.J → Prop) : Prop where
  inj  : Function.Injective B.wAt
  own  : ∀ i, Rd (B.wAt i)
  rdM  : ∀ a, Rd (B.mAt a)
  rdS  : ∀ q st j, ¬ Rd j → B.slM q st j = 0
  /-- no own entry is an entry of the matrix; no incoming form reads one -/
  wM   : ∀ i a, B.wAt i ≠ B.mAt a
  wS   : ∀ q st i, B.slM q st (B.wAt i) = 0

/-- The letters of the item "masked messages", at the base and over a signature. -/
def maskData {Wt : Type} (msg : Wt → B.J → E) (Rd : B.J → Prop) : IOR.MaskData (B.batt Ex) Wt :=
  (B.par.maskDataC Ex msg Rd).afterDraw B.Z.D B.nx B.InHolds
def maskSig (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (msg : S.Msg → B.J → E) (Rd : B.J → Prop) :
    IOR.MaskData ((B.batt E₀).keep S.Smp S.ext) (S.Wit × Wp) :=
  ((B.maskData E₀ (fun w : S.Msg × Wp => msg w.1) Rd).keep S.Smp S.ext).mapW fun w =>
    (S.msgs w.1, w.2)

end BattPar

/-! ## The statements -/

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

/-- The one claim after the draw is a sum claim: over the cube of the columns, with plain
weights. -/
def batt_sum : Prop :=
  ∀ (B : BattPar E) (x : (B.Q → E) × B.St) (ρ : B.Z.D) (m : B.J → E),
    B.par.SumHolds (B.nx x ρ) m ↔ ∑ q, B.Z.ze ρ q * B.lhs x.2 q m = ∑ q, B.Z.ze ρ q * x.1 q

/-- All claims hold: then the sum claim holds, at every seed. -/
def batt_fwd : Prop :=
  ∀ (B : BattPar E) (x : (B.Q → E) × B.St) (ρ : B.Z.D) (m : B.J → E),
    B.InHolds x m → B.par.SumHolds (B.nx x ρ) m

/-- If `B.Z.OK`: for fixed entries of which not all claims hold, the sum claim holds at no more
seeds than the evader's number. -/
def batt_cnt : Prop :=
  ∀ (B : BattPar E), B.Z.OK →
    ∀ (x : (B.Q → E) × B.St) (m : B.J → E),
      ¬ B.InHolds x m → cnt (fun ρ : B.Z.D => B.par.SumHolds (B.nx x ρ) m) ≤ B.Z.err

/-- If 2 ≤ `B.n`: the conditions of the sumcheck: φ(ψ) = 1 (`VarsOK`); degree 2 in each column
variable, so at most `B.n` (`DegOK`); challenges are their values, so different challenges have
different values (`ValInj`). -/
def batt_ok : Prop := ∀ B : BattPar E, 2 ≤ B.n → B.par.VarsOK ∧ B.par.DegOK ∧ B.par.ValInj

/-- If 1 ≤ `B.n`: the output claim (`MidHolds`) is one tensor row, with masks, and a public target
(`RowHolds`). -/
def batt_row : Prop :=
  ∀ (B : BattPar E), 1 ≤ B.n → ∀ (z : B.par.Mid) (m : B.J → E), B.par.MidHolds z m ↔ B.RowHolds z m

/-- The conditions on the own entries give those of the sumcheck. -/
def batt_own : Prop := ∀ (B : BattPar E) (Rd : B.J → Prop), B.OwnOK Rd → B.par.OwnW Rd

/-- At the base, for each fixed tuple of messages. -/
def batt_goodAt : Prop :=
  ∀ (B : BattPar E) (Ex : ExtSpec) (M Wp Kc : Type)
      (A0 : Rels Kc B.St Ex (M × Wp)) (msg : M → B.J → E),
    2 ≤ B.n → B.Z.OK →
    GoodAt (B.batt Ex) (B.hon Ex fun w => msg w.1) (B.baseIn Ex A0 fun w => msg w.1)
      (B.baseOut Ex A0 fun w => msg w.1) (fun _ _ _ wp => wp) (B.nums Ex Kc)

/-- The item "masked messages". -/
def batt_mm : Prop :=
  ∀ (B : BattPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → B.J → E) (Rd : B.J → Prop),
    2 ≤ B.n → B.OwnOK Rd → (B.hon Ex msg).MM (B.maskData Ex msg Rd)

/-- Over a signature: a masked block. -/
def batt_goodM_sig : Prop :=
  ∀ (S : Sig E) (B : BattPar E) (E₀ : ExtSpec) (Wp Kc : Type) (A0 : Rels Kc B.St E₀ (S.Msg × Wp))
      (msg : S.Msg → B.J → E) (Rd : B.J → Prop),
    2 ≤ B.n → B.Z.OK → B.OwnOK Rd →
    GoodM ((B.batt E₀).keep S.Smp S.ext) (S.liftH (B.hon E₀ fun w => msg w.1))
      (S.over (B.baseIn E₀ A0 fun w => msg w.1)) (S.over (B.baseOut E₀ A0 fun w => msg w.1))
      (fun _ _ w => w) ((B.nums E₀ Kc).keep S.Smp S.ext) (B.maskSig S E₀ Wp msg Rd)

/-- The number of rounds, and of own mask entries. -/
def batt_len : Prop := ∀ (B : BattPar E) (Ex : ExtSpec), (B.batt Ex).shape.length = B.k + 2
def batt_own_card : Prop := ∀ B : BattPar E, Fintype.card (PIdx B.fmt) = B.k * B.n + 1

end Spec
end
end Cb
