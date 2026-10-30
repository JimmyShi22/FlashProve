-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBattV.lean: tensor rows on one matrix into one tensor row at a point, by a sumcheck in which
the value of the batched map is shown.

A batching step of an interactive oracle proof, in a second form. Several linear claims on one
matrix, each with a vector on the rows and a vector on the columns, are reduced by a random linear
combination and a sumcheck over the columns with one more variable, at whose end the prover sends
one scalar. Two linear claims come out.

The parameters, the term, the honest side, the joints, the two rows that come out, the letters of
its zero-knowledge item (`B.maskData`; the item: `Honest.MM`, Ior/Masked.lean; both are told below),
and the statements. Proofs: Cb/Ld/LdBattVProofs.lean.
The first form (Cb/Ld/LdBatt.lean) shows no value and leaves one row, which reads the matrix, the
block's own masks and the incoming masks together. This form leaves two rows: one that does not read
the matrix (if `B.OwnOK Rd` and `B.FormsOff`), and one that reads the matrix and, of all other
entries, one.
"At the base" means without a signature: the joints are `baseIn` and `baseOut`, over any joint A0,
and the witness is read through msg.
A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and of
witness: the honest relation; a second relation, called relaxed, of which round-by-round knowledge
soundness speaks; the set of statements of which that soundness speaks; and a map from a witness to
its core. The fields, in this order: `rel`, `relR`, `on`, `core`.

Among the entries m : J → E of the statement's messages lie those of a matrix M with rows named by
Rw and columns on the cube of k variables (`mAt`). A tensor form is < v ⊗ c, M > = ∑ over the
columns b of c(b) (vᵀM)(b) (`tenForm`): v a vector on the rows, c any vector on the columns. Input:
for each name q in a finite set Q a claim with public target:
    < g_q ⊗ c_q, M > + < incoming mask form q, m > = τ_q.

The protocol is a draw, then the sumcheck for a polynomial summand in its instance with a dummy last
variable (`PscOur`, Cb/Ld/LdPsc.lean), with one revealed map, no other map, and the summand "the
value of that map".
  Round 1: the prover sends nothing; the verifier sends the seed of a zero-evader (`Cb.Evader`) with
    one coefficient χ_q for each claim. The claims become one: ∑_q χ_q (left side q) = ∑_q χ_q τ_q.
    This is a sum claim over the cube of the columns, with plain weights, for the batched map F(X) =
    ∑_q χ_q C_q(X) · (extension of g_qᵀM)(X) (C_q: the extension of c_q), with the incoming form ∑_q
    χ_q (form q) (`Spec.battV_sum`).
  Round 2: the prover sends the sum of a hiding polynomial U in k + 1 variables; the verifier a
    coefficient ε from all of E.
  Rounds 3 .. k+2: one for each column variable: a round polynomial of degree at most n (n ≥ 2), a
    challenge γ_i from all of E.
  Round k+3: the dummy variable Y ("sum" = the value at 0; public polynomial 1): a round polynomial
    of degree at most 1, a challenge β from E without 0. The masked map is F(X) + c Y, with c =
    m(cAt) the one inner mask entry.
  Round k+4: the prover sends, in the clear, one scalar u = F(γ) + β c; the verifier's message is
    empty.
  The polynomial of the sumcheck: H = U + ε ( F(X) + c Y + (∑_q χ_q < form q, m >) X_1 .. X_k ).
Output: two rows with public targets (`Spec.battV_rows`, if 1 ≤ n):
  `B.RowA`: < value form of U at (γ, β), the hiding coefficients >
      + ε γ_1 .. γ_k ∑_q χ_q < form q, m > = (last round polynomial at β) - ε u.
    It reads the hiding coefficients and what the incoming forms read (`Spec.battV_rowA_reads`). Not
      the matrix, not c, if no incoming form reads them and no hiding coefficient lies there
      (`Spec.battV_rowA_off`, stated under `B.OwnOK Rd` and `B.FormsOff`). That no incoming form
      reads c is a clause of `B.OwnOK`; that none reads an entry of the matrix is a condition of its
      own, `B.FormsOff`, which the zero-knowledge item does not need (J names the matrix's entries
      too).
  `B.RowB`: < ( ∑_q χ_q C_q(γ) g_q ) ⊗ eq(γ, ·), M > + β c = u.
    A tensor form at the point γ (`tenAt`); beside the matrix it reads c alone
      (`Spec.battV_rowB_reads`). No factor ε stands in its row vector.
Rounds: k + 4, the last with an empty verifier message; nothing is merged (`Spec.battV_len`).
Errors, as counts, in this order: the evader's number (of its seeds); 1 of |E|; n of |E| for each
column variable; 1 of |E| - 1; 0 (`Spec.battV_err`). No query, no oracle. Extractor: the identity.
Completeness is perfect. (Errors, extractor, completeness: `Spec.battV_goodAt`, under its
hypotheses.)

`Cb.GoodAt` asks, of a reduction with its honest side between two joints whose witnesses pair a
value of one type M with a further witness, the clauses of `GoodB` with two differences: a further
clause `same` asks that, on every run, the honest prover's output witness carries the M-part of its
input witness unchanged; and the clause `know`, in place of `GoodB`'s, asks, for each fixed m of
type M, round-by-round knowledge soundness (`Know`) on the input joint's set of statements and at
the numbers' list of errors, as `GoodB`'s does, but between the relaxed relations at (m, ·) and with
the extractor `ext m`. (`GoodB`, `IOR.GoodT`: told in the head of Cb/Ld/LdBatt.lean.)
`MaskData R Wi` is a structure: a type `Kc` with `kc : Wi → Kc`; a type `Xp` with `pub : Xi → Xp`; a
finite, non-empty type `Mk` with `put : Mk → Kc → Kc`; a predicate `Cl` on `Xp` and `Kc`; `msg`,
from `Kc`, `Xp` and the verifier's randomness ρ to plain parts; and `sim`, from `Xp` and ρ to
distributions on plain parts. `H.MM D` asks five things: the block sends no oracle; `H.withheld w x`
is always empty; the honest prover's plain parts are `D.msg` at `D.kc w`, `D.pub x` and ρ; `D.Cl` is
kept under `D.put`; and where `D.Cl xp k` holds, `D.msg (D.put M k) xp ρ` over uniform M has the
distribution `D.sim xp ρ`. `GoodM` is `GoodB` (`GoodT` without the clause `exact`) with `H.MM D`,
and the clause that every (x, y, w) in the honest relation meets `D.Cl (D.pub x) (D.kc w)`. In this
file `GoodAt` is the conclusion of `Spec.battV_goodAt`, `MM` that of `Spec.battV_mm`, and `GoodM`
that of `Spec.battV_goodM_sig`.

Zero knowledge. Under the hypotheses of `Spec.battV_mm`, the draw sends nothing, so "draw, then the
sumcheck" is one masked block (Ior/MaskedDraw.lean). Own masks: the k n + 2 coefficients of the
hiding polynomial, at `wAt` (n for each column variable, 1 for the dummy variable, 1 constant), and
the inner entry, at `cAt`: k n + 3 in all (`Spec.battV_own_card`). Under the hypotheses of
`Spec.battV_mm`, its item "masked messages" has the letters `B.maskData`: over these entries,
uniform, all else fixed and the claims true, all that the prover sends, the shown value u too, has
exactly the law of a simulator that reads the targets, the state, and what the verifier sent. What
that law is: Cb/Ld/LdPscMask.lean (uniform on the tuples that pass the checks, times a uniform u).
Why u leaks nothing: u = F(γ) + β c with β ≠ 0 by the type of the challenge set, and c uniform; the
last round polynomials do contain c, and are hidden by U.
Conditions (2 ≤ `B.n`; `B.OwnOK Rd`): the own entries lie at different places, none is an entry of
the matrix, no incoming form reads one; the block reads the entries in Rd only.
Two holders. J names all entries, so hiding coefficients and inner entry may lie in different
messages, sent at different steps. `Spec.battV_two`: if the places are different, overwriting the
own entries is overwriting the inner entry, then the hiding coefficients. `Spec.battV_join`: if the
places are different, in every set of facts on fresh masks that is closed under joining (in this
sense: the closure `MaskFact.JCl X` of a set X, Cb/Req1/LdSegFreshS.lean) the block's fact follows
from two facts at the block's reading: one on the hiding coefficients alone, one on the inner entry
alone.

Main names:
  `Spec.battV_goodAt`: if 2 ≤ `B.n` and `B.Z.OK`: at the base, for each fixed tuple of messages
    (`GoodAt`, Cb/Ld/LdSigLift.lean; told above): complete; round-by-round knowledge sound, the
    identity extracts, the errors above.
  `Spec.battV_mm`: the item at the base (under the conditions above: 2 ≤ `B.n`; `B.OwnOK Rd`).
  `Spec.battV_goodM_sig`: if 2 ≤ `B.n`, `B.Z.OK` and `B.OwnOK Rd`: over a signature S: the bundle
    `GoodM` (Ior/Masked.lean).
In files of their own: that the block reads the entries in Rd only: Cb/Ld/LdBattVLook.lean. Errors,
as probabilities, at most a bound, from four inequalities; countability: Cb/Ld/LdBattVBelow.lean.

Why at the base: as for the first form the matrix is, in the protocols that we follow, an encoded
index: an oracle that is no oracle message of a signature but is decoded by the statement. What is
used there are `battV_goodAt` and `battV_mm`, through the lifting rule for claims that read such an
oracle: Cb/Ld/LdBattVSeg.lean.

Limits: this file does not say in which oracles matrix and masks lie. It does not say that the own
entries are fresh when the block begins. It says nothing on running times or succinct forms.
Declared differences to the text that we follow (by a reading of a print of the technical report;
not held against the report's latest edition). (a) All coefficients of a round
polynomial are sent and the verifier checks the sum; the text leaves out one coefficient a round,
which the verifier recomputes. So the count of scalars is 1 + k (n + 1) + 2 + 1, and the simulator
reads the targets. (b) The degree n of the column variables' round polynomials is a parameter with n
≥ 2; the text has 2. (c) All that Cb/Ld/LdPsc.lean declares.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdBatt
import Cb.Req1.LdSegFreshS

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

/-! ## Tensor forms -/

section Ten
variable {E J Rw : Type} [Field E] [Fintype Rw] {k : ℕ}

/-- vᵀM, a vector on the columns -/
def tenCol (mAt : Rw × (Fin k → Bool) → J) (m : J → E) (v : Rw → E) : (Fin k → Bool) → E := fun b =>
  ∑ r, v r * m (mAt (r, b))
/-- The tensor form < v ⊗ c, M >, and the tensor form at a point: < v ⊗ eq(z, ·), M > -/
def tenForm (mAt : Rw × (Fin k → Bool) → J) (v : Rw → E) (c : (Fin k → Bool) → E) (m : J → E) : E :=
  ∑ b, c b * tenCol mAt m v b
def tenAt (mAt : Rw × (Fin k → Bool) → J) (v : Rw → E) (z : Fin k → E) (m : J → E) : E :=
  Alg.mle (tenCol mAt m v) z

end Ten

/-- The parameters. -/
structure BattVPar (E : Type) [Field E] [Fintype E] where
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
  /-- the names of the claims; their row vectors, column vectors and incoming mask forms -/
  Q : Type
  [finQ : Fintype Q]
  g : St → Q → Rw → E
  cf : St → Q → (Fin k → Bool) → E
  slM : Q → Slf E St J
  /-- the coefficients -/
  Z : Evader E Q
  /-- the largest degree of a round polynomial of a column variable -/
  n : ℕ
  /-- where the coefficients of the hiding polynomial lie; where the one inner mask entry lies -/
  wAt : PIdx (List.replicate k (pfCube E n) ++ [pDummy E 1]) → J
  cAt : J

attribute [instance] BattVPar.finJ BattVPar.finRw BattVPar.finQ

namespace BattVPar
variable {E : Type} [Field E] [Fintype E] (B : BattVPar E)

/-- the left side of the claim q -/
def lhs (st : B.St) (q : B.Q) (m : B.J → E) : E :=
  tenForm B.mAt (B.g st q) (B.cf st q) m + ∑ j, B.slM q st j * m j

/-- The claims of the input statement x = (targets, state). -/
def InHolds (x : (B.Q → E) × B.St) (m : B.J → E) : Prop := ∀ q, B.lhs x.2 q m = x.1 q

abbrev fmt : List (PFmt E) := List.replicate B.k (pfCube E B.n)
/-- a point of the column variables as a function of the variable -/
abbrev fn (X : HPt (pVars B.fmt (pdPlains E B.n B.k))) : Fin B.k → E :=
  hFnOf (pfCube E B.n) B.k (pdPlains E B.n B.k) X

/-- The batched map, as a function of the point. -/
def bmap (st : B.St × B.Z.D) (m : B.J → E) (z : Fin B.k → E) : E :=
  ∑ q, B.Z.ze st.2 q * Alg.mle (B.cf st.1 q) z * tenAt B.mAt (B.g st.1 q) z m

/-- The parameters of the sumcheck: plain weights on the cube of the columns; one revealed map, the
batched map; the summand is its value. -/
def our : PscOur E where
  St := B.St × B.Z.D
  J := B.J
  fmt := B.fmt
  dat := fun _ => pdPlains E B.n B.k
  A := Unit
  B := Empty
  F := fun st m _ X => B.bmap st m (B.fn X)
  Fb := fun _ _ b _ => b.elim
  S0 := fun _ _ v => v ()
  S1 := fun _ _ _ b => b.elim
  DY := 1
  slS := fun st j => ∑ q, B.Z.ze st.2 q * B.slM q st.1 j
  wAt := B.wAt
  cAt := fun _ => B.cAt

/-- the one claim after the draw: the combination of the targets; the seed joins the state -/
def nx (x : (B.Q → E) × B.St) (ρ : B.Z.D) : E × B.our.par.St := (∑ q, B.Z.ze ρ q * x.1 q, (x.2, ρ))

variable (Ex : ExtSpec)

/-- The block. -/
def battV : IOR ((B.Q → E) × B.St) Ex B.our.par.Out Ex :=
  (IOR.draw B.Z.D B.nx Ex).seq (B.our.par.psc Ex)

/-- The honest side: no coins; nothing is withheld; the witness stays. -/
def hon {Wt : Type} (msg : Wt → B.J → E) : (B.battV Ex).Honest Wt Wt :=
  (IOR.Honest.draw B.Z.D B.nx Ex Wt).seq (B.our.par.hon Ex msg)

/-- The numbers. -/
def nums (Kc : Type) : IOR.Nums Kc (B.battV Ex) :=
  (IOR.Nums.draw Kc B.Z.D B.nx Ex B.Z.err).seq (B.our.par.nums Ex Kc)

/-! ### What comes out -/

/-- the state in the output, and the coefficients that its seed gives -/
def stOf (o : B.our.par.Out) : B.St := (show B.St × B.Z.D from o.st).1
def chi (o : B.our.par.Out) (q : B.Q) : E := B.Z.ze (show B.St × B.Z.D from o.st).2 q
/-- the point γ of the column variables; the challenge β of the dummy variable; the value shown -/
def outPt (o : B.our.par.Out) : Fin B.k → E := B.fn (B.our.ini o.st (B.our.par.hp o.st o.pt))
def beta (o : B.our.par.Out) : E := B.our.lst o.st (B.our.par.hp o.st o.pt)
def shown (o : B.our.par.Out) : E := o.vals ()
/-- the row vector of the tensor form that comes out -/
def outG (o : B.our.par.Out) : B.Rw → E := fun r =>
  ∑ q, B.chi o q * Alg.mle (B.cf (B.stOf o) q) (B.outPt o) * B.g (B.stOf o) q r

/-- The row on the hiding coefficients and the incoming masks. -/
def RowA (o : B.our.par.Out) (m : B.J → E) : Prop :=
  ∑ i, hSl (B.our.par.vars o.st) (B.our.par.hp o.st o.pt) i *
        m (B.wAt (pIx (B.fmt ++ [pDummy E 1]) (B.our.datD o.st) i)) +
      o.eps * (∏ i, B.outPt o i) * ∑ q, B.chi o q * ∑ j, B.slM q (B.stOf o) j * m j =
    o.fin - o.eps * B.shown o

/-- The tensor row at the point γ, with the one inner mask entry. -/
def RowB (o : B.our.par.Out) (m : B.J → E) : Prop :=
  tenAt B.mAt (B.outG o) (B.outPt o) m + B.beta o * m B.cAt = B.shown o

/-- The joints at the base: A0, any joint on (state, oracles, witness), is carried along unchanged
beside the claims. -/
def baseIn {Kc Wt : Type} (A0 : IOR.Rels Kc B.St Ex Wt) (msg : Wt → B.J → E) :
    IOR.Rels Kc ((B.Q → E) × B.St) Ex Wt where
  rel := fun x y w => A0.rel x.2 y w ∧ B.InHolds x (msg w)
  relR := fun a w => A0.relR (a.1.2, a.2) w ∧ B.InHolds a.1 (msg w)
  on := fun a => A0.on (a.1.2, a.2)
  core := A0.core
def baseOut {Kc Wt : Type} (A0 : IOR.Rels Kc B.St Ex Wt) (msg : Wt → B.J → E) :
    IOR.Rels Kc B.our.par.Out Ex Wt where
  rel := fun o y w => A0.rel (B.stOf o) y w ∧ B.RowA o (msg w) ∧ B.RowB o (msg w)
  relR := fun a w => A0.relR (B.stOf a.1, a.2) w ∧ B.RowA a.1 (msg w) ∧ B.RowB a.1 (msg w)
  on := fun a => A0.on (B.stOf a.1, a.2)
  core := A0.core

/-! ### The own entries -/

/-- The conditions on the own entries. -/
structure OwnOK (Rd : B.J → Prop) : Prop where
  inj  : Function.Injective B.wAt
  wc   : ∀ i, B.wAt i ≠ B.cAt
  own  : ∀ i, Rd (B.wAt i)
  ownC : Rd B.cAt
  rdM  : ∀ a, Rd (B.mAt a)
  rdS  : ∀ q st j, ¬ Rd j → B.slM q st j = 0
  /-- no own entry is an entry of the matrix; no incoming form reads one -/
  wM   : ∀ i a, B.wAt i ≠ B.mAt a
  cM   : ∀ a, B.cAt ≠ B.mAt a
  wS   : ∀ q st i, B.slM q st (B.wAt i) = 0
  cS   : ∀ q st, B.slM q st B.cAt = 0

/-- no incoming form reads an entry of the matrix -/
def FormsOff : Prop := ∀ q st a, B.slM q st (B.mAt a) = 0

/-- The letters of the item "masked messages", at the base and over a signature. -/
def maskData {Wt : Type} (msg : Wt → B.J → E) (Rd : B.J → Prop) : IOR.MaskData (B.battV Ex) Wt :=
  (B.our.par.maskData Ex msg (B.our.own Rd)).afterDraw B.Z.D B.nx B.InHolds
def maskSig (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (msg : S.Msg → B.J → E) (Rd : B.J → Prop) :
    IOR.MaskData ((B.battV E₀).keep S.Smp S.ext) (S.Wit × Wp) :=
  ((B.maskData E₀ (fun w : S.Msg × Wp => msg w.1) Rd).keep S.Smp S.ext).mapW fun w =>
    (S.msgs w.1, w.2)

/-- the names of the hiding coefficients -/
abbrev WIx : Type := PIdx (B.fmt ++ [pDummy E 1])

open Classical in
/-- what the block reads of the entries: those in Rd; all others set to 0 -/
def cut (Rd : B.J → Prop) (m : B.J → E) : B.J → E := fun j => if Rd j then m j else 0

/-- The two parts of the block's fact on fresh masks, at the block's reading: the hiding
coefficients alone; the inner entry alone. -/
def factW {Wt : Type} (msg : Wt → B.J → E) (Rd : B.J → Prop) : IOR.MaskFact Wt :=
  ⟨B.J → E, fun w => B.cut Rd (msg w), B.WIx → E, fun M k => Function.extend B.wAt M k⟩
def factC {Wt : Type} (msg : Wt → B.J → E) (Rd : B.J → Prop) : IOR.MaskFact Wt :=
  ⟨B.J → E, fun w => B.cut Rd (msg w), Unit → E,
    fun M k => Function.extend (fun _ : Unit => B.cAt) M k⟩

end BattVPar

/-! ## The statements -/

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

/-- A tensor form whose column vector is eq(z, ·) is the tensor form at the point z. -/
def battV_at_point : Prop :=
  ∀ (J Rw : Type) [Fintype Rw] (k : ℕ) (mAt : Rw × (Fin k → Bool) → J) (v : Rw → E)
      (z : Fin k → E) (m : J → E),
    tenForm mAt v (Alg.eqk z) m = tenAt mAt v z m

/-- The tensor row of the first form is the tensor form at a point. -/
def battV_first : Prop :=
  ∀ (B : BattPar E) (v : B.Rw → E) (z : Fin B.k → E) (m : B.J → E), B.ten v z m = tenAt B.mAt v z m

/-- The one claim after the draw is a sum claim: over the cube of the columns, with plain weights,
of the batched map. -/
def battV_sum : Prop :=
  ∀ (B : BattVPar E) (x : (B.Q → E) × B.St) (ρ : B.Z.D) (m : B.J → E),
    B.our.SumHolds (B.nx x ρ) m ↔ ∑ q, B.Z.ze ρ q * B.lhs x.2 q m = ∑ q, B.Z.ze ρ q * x.1 q

/-- All claims hold: then the sum claim holds, at every seed. -/
def battV_fwd : Prop :=
  ∀ (B : BattVPar E) (x : (B.Q → E) × B.St) (ρ : B.Z.D) (m : B.J → E),
    B.InHolds x m → B.our.SumHolds (B.nx x ρ) m

/-- If `B.Z.OK`: for fixed entries of which not all claims hold, the sum claim holds at no more
seeds than the evader's number. -/
def battV_cnt : Prop :=
  ∀ (B : BattVPar E), B.Z.OK →
    ∀ (x : (B.Q → E) × B.St) (m : B.J → E),
      ¬ B.InHolds x m → cnt (fun ρ : B.Z.D => B.our.SumHolds (B.nx x ρ) m) ≤ B.Z.err

/-- If 2 ≤ `B.n`: the conditions of the sumcheck: φ(ψ) = 1 (`VarsOK`); degree 2 in each column
variable, so at most `B.n` (`DegX`), 1 in the value of the map (`DegY`); challenges are their
values, so different challenges have different values (`ValInj`). -/
def battV_ok : Prop :=
  ∀ B : BattVPar E, 2 ≤ B.n → B.our.VarsOK ∧ B.our.DegX ∧ B.our.DegY ∧ B.our.ValInj

/-- If 1 ≤ `B.n`: the output claims of the sumcheck (`OutHolds`) are the two rows. -/
def battV_rows : Prop :=
  ∀ (B : BattVPar E),
    1 ≤ B.n → ∀ (o : B.our.par.Out) (m : B.J → E), B.our.par.OutHolds o m ↔ B.RowA o m ∧ B.RowB o m

/-- What the two rows read. The first: the hiding coefficients, and what the incoming forms read.
The second: the matrix, and the inner entry. -/
def battV_rowA_reads : Prop :=
  ∀ (B : BattVPar E) (o : B.our.par.Out) (m m' : B.J → E), (∀ i, m (B.wAt i) = m' (B.wAt i)) →
    (∀ q j, B.slM q (B.stOf o) j ≠ 0 → m j = m' j) → (B.RowA o m ↔ B.RowA o m')
def battV_rowB_reads : Prop :=
  ∀ (B : BattVPar E) (o : B.our.par.Out) (m m' : B.J → E),
    (∀ a, m (B.mAt a) = m' (B.mAt a)) → m B.cAt = m' B.cAt → (B.RowB o m ↔ B.RowB o m')

/-- If `B.OwnOK Rd` and `B.FormsOff`: the first row reads neither the matrix nor the inner entry: it
says the same of all entries that differ there only. -/
def battV_rowA_off : Prop :=
  ∀ (B : BattVPar E) (Rd : B.J → Prop), B.OwnOK Rd → B.FormsOff →
    ∀ (o : B.our.par.Out) (m m' : B.J → E),
      (∀ j, (∀ a, j ≠ B.mAt a) → j ≠ B.cAt → m j = m' j) → (B.RowA o m ↔ B.RowA o m')

/-- In whatever the verifier outputs the coefficient of the inner entry is not 0. -/
def battV_nz : Prop :=
  ∀ (B : BattVPar E) (Ex : ExtSpec) (x : (B.Q → E) × B.St) (y : Ex.Str)
      (τ : Tr (B.battV Ex).shape) (o : B.our.par.Out),
    (B.battV Ex).out x y τ = some o → B.beta o ≠ 0

open Classical in
/-- The second row is a claim of the first form's input: for parameters B' of the first form on the
same entries and the same matrix, a state st' and a name q' with the row vector, the point and "β at
the inner entry" as incoming form. -/
def battV_pend : Prop :=
  ∀ (B : BattVPar E) (o : B.our.par.Out) (St' Q' : Type) [Fintype Q'] (g' : St' → Q' → B.Rw → E)
      (pt' : St' → Q' → Fin B.k → E) (slM' : Q' → Slf E St' B.J) (Z' : Evader E Q') (n' : ℕ)
      (wAt' : PIdx (List.replicate B.k (pfCube E n')) → B.J) (st' : St') (q' : Q'),
    g' st' q' = B.outG o → pt' st' q' = B.outPt o →
    (∀ j, slM' q' st' j = if j = B.cAt then B.beta o else 0) →
    ∀ m : B.J → E,
      B.RowB o m ↔
      (⟨St', B.J, B.Rw, B.k, B.mAt, Q', g', pt', slM', Z', n', wAt'⟩ : BattPar E).lhs st' q' m =
        B.shown o

/-- The conditions on the own entries give those of the sumcheck. -/
def battV_own : Prop := ∀ (B : BattVPar E) (Rd : B.J → Prop), B.OwnOK Rd → B.our.OwnOur Rd

/-- Two holders: if `B.wAt` is injective and never `B.cAt`, overwriting the own entries is
overwriting the inner entry, then the hiding coefficients. -/
def battV_two : Prop :=
  ∀ (B : BattVPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → B.J → E) (Rd : B.J → Prop),
    Function.Injective B.wAt → (∀ i, B.wAt i ≠ B.cAt) →
    ∀ (M : (B.maskData Ex msg Rd).Mk) (k : B.J → E), (B.maskData Ex msg Rd).put M k =
      Function.extend B.wAt M.1 (Function.extend (fun _ : Unit => B.cAt) M.2 k)

/-- Two holders: if `B.wAt` is injective and never `B.cAt`, the block's fact follows from the two
parts' facts, in every set of facts that is closed under joining (in this sense: the closure
`MaskFact.JCl X` of a set X, Cb/Req1/LdSegFreshS.lean). -/
def battV_join : Prop :=
  ∀ (B : BattVPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → B.J → E)
      (Rd : B.J → Prop) (X : MaskFact Wt → Prop),
    Function.Injective B.wAt → (∀ i, B.wAt i ≠ B.cAt) → MaskFact.JCl X (B.factW msg Rd) →
    MaskFact.JCl X (B.factC msg Rd) → MaskFact.JCl X (B.maskData Ex msg Rd).fact

/-- At the base, for each fixed tuple of messages. -/
def battV_goodAt : Prop :=
  ∀ (B : BattVPar E) (Ex : ExtSpec) (M Wp Kc : Type)
      (A0 : Rels Kc B.St Ex (M × Wp)) (msg : M → B.J → E),
    2 ≤ B.n → B.Z.OK →
    GoodAt (B.battV Ex) (B.hon Ex fun w => msg w.1) (B.baseIn Ex A0 fun w => msg w.1)
      (B.baseOut Ex A0 fun w => msg w.1) (fun _ _ _ wp => wp) (B.nums Ex Kc)

/-- The item "masked messages". -/
def battV_mm : Prop :=
  ∀ (B : BattVPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → B.J → E) (Rd : B.J → Prop),
    2 ≤ B.n → B.OwnOK Rd → (B.hon Ex msg).MM (B.maskData Ex msg Rd)

/-- Over a signature: a masked block. -/
def battV_goodM_sig : Prop :=
  ∀ (S : Sig E) (B : BattVPar E) (E₀ : ExtSpec) (Wp Kc : Type) (A0 : Rels Kc B.St E₀ (S.Msg × Wp))
      (msg : S.Msg → B.J → E) (Rd : B.J → Prop),
    2 ≤ B.n → B.Z.OK → B.OwnOK Rd →
    GoodM ((B.battV E₀).keep S.Smp S.ext) (S.liftH (B.hon E₀ fun w => msg w.1))
      (S.over (B.baseIn E₀ A0 fun w => msg w.1)) (S.over (B.baseOut E₀ A0 fun w => msg w.1))
      (fun _ _ w => w) ((B.nums E₀ Kc).keep S.Smp S.ext) (B.maskSig S E₀ Wp msg Rd)

/-- The number of rounds; the errors, as counts; the size of the last challenge set but one; the
number of own mask entries. -/
def battV_len : Prop := ∀ (B : BattVPar E) (Ex : ExtSpec), (B.battV Ex).shape.length = B.k + 4
def battV_err : Prop :=
  ∀ (B : BattVPar E) (Ex : ExtSpec) (Kc : Type),
    (B.nums Ex Kc).err =
      Err.app (s := [IOR.drawRound B.Z.D])
        (t := (pRound0 E :: pRounds (B.fmt ++ [pDummy E 1])) ++ [pRoundV E Unit])
        ((B.Z.err, ()) : Err [IOR.drawRound B.Z.D])
        (Err.app (s := pRound0 E :: pRounds (B.fmt ++ [pDummy E 1])) (t := [pRoundV E Unit])
          ((1, pErr (B.fmt ++ [pDummy E 1])) : Err (pRound0 E :: pRounds (B.fmt ++ [pDummy E 1])))
          ((0, ()) : Err [pRoundV E Unit])) ∧
    (B.fmt ++ [pDummy E 1]).map PFmt.n = List.replicate B.k B.n ++ [1] ∧
    Fintype.card (pDummy E 1).Ch = Fintype.card E - 1
def battV_own_card : Prop :=
  ∀ B : BattVPar E, Fintype.card B.WIx = B.k * B.n + 2 ∧ Fintype.card (B.WIx ⊕ Unit) = B.k * B.n + 3

end Spec
end
end Cb
