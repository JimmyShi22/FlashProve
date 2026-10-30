-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpEnd.lean: the end claim of the table's product trees in the lookup, closed by one
sumcheck for a polynomial summand.

Definitions and statements (in `Cb.Spec`). Proofs: Cb/Ld/LdLkpEndProofs.lean.
This file reduces the end claim, by one sumcheck, to two linear rows on the entries.
`GoodAt` (Cb/Ld/LdSigLift.lean) has among its fields completeness in the sense of `Honest.Acc`
(Ior/Honest.lean) and, for each fixed tuple of messages, round-by-round knowledge soundness (`Know`,
Ior/Know.lean).
`GoodB` is `IOR.GoodT` without its clause on zero knowledge. `IOR.GoodT` (likewise `IOR.Good`,
Ior/Chain.lean) bundles what is asked of one reduction, with its honest side, between two joints, at
given numbers; among its clauses: completeness between the honest relations, outside sets of
verifier randomness whose probabilities further clauses bound by the numbers; round-by-round
knowledge soundness (`Know`) between the relaxed relations, on the input joint's set of statements,
with a given extractor, at the numbers' list of errors; and one on honest-verifier zero knowledge.
In this file `GoodAt` is what `Spec.ldLkpEnd_goodAt` concludes, `GoodB` what `Spec.ldLkpEnd_good`
concludes.
At the base means between joints in which the tuple of messages is a part of the witness, before the
lift over a signature (Cb/Ld/LdSigLift.lean).

The claim. The leaves of the table's product trees are 1 + bit(b) cp(b), b a corner of the cube in k
variables: bit(b) = m (tAt b) is an entry of an oracle message, cp is a public vector (first
challenge, less 1, less the table's entry that b names). The leaves are never sent.
The trees end with a claim on the multilinear extension of the leaves at a point z, under an
incoming mask form:
        (extension of  b ↦ 1 + m (tAt b) cp b  at z)  +  < inc, m >  =  target.
As a sum claim: the sum, under equality weights at z, of 1 + CP(X) Y(X), CP and Y the multilinear
extensions of cp and of the bits (`Spec.ldLkpEnd_sum`). That is the input claim of the sumcheck
`B.psc : PscOur E`: the state is of any type X, a parameter, with readers z, cp, inc (so that a
caller plugs in the state that its chain has reached); one revealed map (Y); degree 2 in each of the
k variables; degree 1 in the dummy variable (`pDummy`, Cb/Ld/LdPsc.lean). k + 3 rounds.
It ends in the sumcheck's two rows with public targets: the row on the hiding polynomial's
coefficients (which takes in the incoming form), and one linear row on the bits under an inner mask:
Y(γ) + β c = v (`Spec.ldLkpEnd_row`).

Main names:
  `Spec.ldLkpEnd_vars`, `Spec.ldLkpEnd_degX`, `Spec.ldLkpEnd_degY`: all conditions of the sumcheck
    (`PscOur.VarsOK`, `ValInj`, `DegX`, `DegY`, Cb/Ld/LdPsc.lean) hold of `B.psc`: stated here,
    proved in Cb/Ld/LdLkpEndProofs.lean.
  `Spec.ldLkpEnd_goodAt`: at the base, for each fixed tuple of messages of any type, any joint A0
    riding along: `GoodAt` from (A0 and the claim) to (A0 and the two rows); the identity extracts;
    no hypothesis is left beyond those of its statement.
  `Spec.ldLkpEnd_good`: the same over a signature: all of `IOR.GoodT` but zero knowledge. Knowledge
    soundness covers only the statements at which A0's condition holds and samples and words of S
    are collision-free (`S.CF`, Cb/Ld/LdSig.lean).

Notation:
  `B`: of type `LkEnd E`: the parameters;
  `B.X`, `B.z`, `B.cp`, `B.inc`: the states, and what is read off them: the point, the public
    vector, the incoming mask form;
  `B.k`, `B.tAt`: the number of variables, and where the bits stand;
  `B.wAt`, `B.cAt`: own masks;
  `Y`: `B.Y m`: the multilinear extension of the bits;
  γ, β, c, v in "Y(γ) + β c = v", by the text of `Spec.ldLkpEnd_row`:
    γ: `B.fn o.st (B.psc.ini o.st (B.psc.par.hp o.st o.pt))`;
    β: `B.psc.lst o.st (B.psc.par.hp o.st o.pt)`;
    c: `m B.cAt`;
    v: `o.vals ()`;
  `A0`: a joint (`IOR.Rels`, Ior/Chain.lean);
  `S`: a signature, the oracle messages of a statement (`Sig`, Cb/Ld/LdSig.lean).

Limits: a choice of this library. The summand is affine in Y, so the map could stay unrevealed: that
cheaper way (k + 1 rounds, one row) is Cb/Ld/LdLkpEndU.lean. The text that we follow allows both and
counts neither.
This file says nothing on zero knowledge (masked messages: Cb/Ld/LdPscZk.lean).
It does not say which corner names which (bit position, table entry): cp is any public vector here.
It does not say that the bits are 0 or 1: by type they are any elements of E (the bit test:
Cb/Ld/LdLkpBit.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLineAt

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

/-- The parameters. -/
structure LkEnd (E : Type) [Field E] [Fintype E] where
  /-- the states, and what is read off them: the point, the public vector, the incoming mask form -/
  X : Type
  J : Type
  [finJ : Fintype J]
  /-- the number of variables, and where the bits stand -/
  k : ℕ
  tAt : (Fin k → Bool) → J
  z : X → Fin k → E
  cp : X → (Fin k → Bool) → E
  inc : X → J → E
  /-- own masks -/
  wAt : PIdx (List.replicate k (pfCube E 2) ++ [pDummy E 1]) → J
  cAt : J

attribute [instance] LkEnd.finJ

namespace LkEnd
variable {E : Type} [Field E] [Fintype E] (B : LkEnd E)

/-- The claim; x = (target, state). -/
def Holds (x : E × B.X) (m : B.J → E) : Prop :=
  Alg.mle (fun b => 1 + m (B.tAt b) * B.cp x.2 b) (B.z x.2) + ∑ j, B.inc x.2 j * m j = x.1

/-- the multilinear extension of the bits -/
def Y (m : B.J → E) (x : Fin B.k → E) : E := Alg.mle (fun b => m (B.tAt b)) x

abbrev fn (s : B.X) (X : HPt (pVars (List.replicate B.k (pfCube E 2)) (pdEqs E 2 B.k (B.z s)))) :
    Fin B.k → E :=
  hFnOf (pfCube E 2) B.k (pdEqs E 2 B.k (B.z s)) X

/-- The sumcheck. -/
def psc : PscOur E where
  St := B.X
  J := B.J
  fmt := List.replicate B.k (pfCube E 2)
  dat := fun s => pdEqs E 2 B.k (B.z s)
  A := Unit
  B := Empty
  F := fun s m _ X => B.Y m (B.fn s X)
  Fb := fun _ _ b _ => b.elim
  S0 := fun s X v => 1 + Alg.mle (B.cp s) (B.fn s X) * v ()
  S1 := fun _ _ _ b => b.elim
  DY := 1
  slS := B.inc
  wAt := B.wAt
  cAt := fun _ => B.cAt

open Classical in
/-- the row on the bits as a linear form on the entries -/
def rowA (s : B.psc.par.St) (_ : B.psc.par.A) (X : HPt (B.psc.par.vars s)) (j : B.J) : E :=
  (∑ b, if B.tAt b = j then Alg.eqk (B.fn s (B.psc.ini s X)) b else 0) +
    if j = B.cAt then B.psc.lst s X else 0

/-- The input joint: A0 rides along. -/
def relsIn {Ex : ExtSpec} {Wt Kc : Type} (A0 : IOR.Rels Kc B.X Ex Wt) (msg : Wt → B.J → E) :
    IOR.Rels Kc (E × B.X) Ex Wt :=
  ⟨fun x y w => A0.rel x.2 y w ∧ B.Holds x (msg w),
    fun a w => A0.relR (a.1.2, a.2) w ∧ B.Holds a.1 (msg w),
    fun a => A0.on (a.1.2, a.2),
    A0.core⟩

end LkEnd

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

/-- The claim is the sumcheck's input claim. -/
def ldLkpEnd_sum : Prop :=
  ∀ (B : LkEnd E) (x : E × B.X) (m : B.J → E), B.psc.SumHolds x m ↔ B.Holds x m
def ldLkpEnd_vars : Prop := ∀ B : LkEnd E, B.psc.VarsOK ∧ B.psc.ValInj
def ldLkpEnd_degX : Prop := ∀ B : LkEnd E, B.psc.DegX
def ldLkpEnd_degY : Prop := ∀ B : LkEnd E, B.psc.DegY

/-- The input joint is the sumcheck's own. -/
def ldLkpEnd_joint : Prop :=
  ∀ (B : LkEnd E) (Ex : ExtSpec) (Wt Kc : Type) (A0 : Rels Kc B.X Ex Wt) (msg : Wt → B.J → E),
    B.relsIn A0 msg = B.psc.baseIn A0 msg

/-- The end claim at the base. -/
def ldLkpEnd_goodAt : Prop :=
  ∀ (B : LkEnd E) (Ex : ExtSpec) (M Wp Kc : Type)
      (A0 : Rels Kc B.X Ex (M × Wp)) (msg : M → B.J → E),
    GoodAt (B.psc.par.psc Ex) (B.psc.par.hon Ex fun w => msg w.1) (B.relsIn A0 fun w => msg w.1)
      (B.psc.par.baseOut A0 fun w => msg w.1) (fun _ _ _ wp => wp) (B.psc.par.nums Ex Kc)

/-- The end claim over a signature. -/
def ldLkpEnd_good : Prop :=
  ∀ (B : LkEnd E) (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type)
      (A0 : Rels Kc B.X E₀ (S.Msg × Wp)) (msg : S.Msg → B.J → E),
    GoodB ((B.psc.par.psc E₀).keep S.Smp S.ext) (S.liftH (B.psc.par.hon E₀ fun w => msg w.1))
      (S.over (B.relsIn A0 fun w => msg w.1)) (S.over (B.psc.par.baseOut A0 fun w => msg w.1))
      (fun _ _ w => w) ((B.psc.par.nums E₀ Kc).keep S.Smp S.ext)

/-- The output rows are linear rows with public targets. -/
def ldLkpEnd_lin : Prop := ∀ B : LkEnd E, B.psc.par.LinA B.rowA ∧ B.psc.par.LinB fun _ b => b.elim
def ldLkpEnd_rows : Prop :=
  ∀ (B : LkEnd E) (o : B.psc.par.Out) (m : B.J → E),
    B.psc.par.OutHolds o m ↔
    (B.psc.par.slU fun _ b => b.elim).Holds (B.psc.par.tU o, o) m ∧
    (B.psc.par.slE B.rowA ()).Holds (o.vals (), o) m

/-- The row on the bits. -/
def ldLkpEnd_row : Prop :=
  ∀ (B : LkEnd E) (o : B.psc.par.Out) (m : B.J → E),
    B.psc.par.EHolds o m () ↔
    B.Y m (B.fn o.st (B.psc.ini o.st (B.psc.par.hp o.st o.pt))) +
        m B.cAt * B.psc.lst o.st (B.psc.par.hp o.st o.pt) = o.vals ()

/-- The constant taken out. -/
def ldLkpEnd_less : Prop :=
  ∀ (B : LkEnd E) (x : E × B.X) (m : B.J → E),
    B.Holds x m ↔
    Alg.mle (fun b => B.cp x.2 b * m (B.tAt b)) (B.z x.2) + ∑ j, B.inc x.2 j * m j = x.1 - 1

def ldLkpEnd_len : Prop := ∀ (B : LkEnd E) (Ex : ExtSpec), (B.psc.par.psc Ex).shape.length = B.k + 3

end Spec
end
end Cb
