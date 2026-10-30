-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpEndU.lean: the end claim of the table's product trees, closed without revealing a value
(exactly: no map is revealed: `PscPar.core`, Cb/Ld/LdPsc.lean).

Definitions and statements (in `Cb.Spec`). Proofs: Cb/Ld/LdLkpEndUProofs.lean.
In the lookup argument the products over the table are taken by product trees, which end in a claim
on the multilinear extension of their leaves at a point. This file reduces that claim, by one
sumcheck, to one linear row on the entries.
`GoodAt` (Cb/Ld/LdSigLift.lean) has among its fields completeness in the sense of `Honest.Acc`
(Ior/Honest.lean) and, for each fixed tuple of messages, round-by-round knowledge soundness (`Know`,
Ior/Know.lean).

The claim is that of Cb/Ld/LdLkpEnd.lean: (extension of b ↦ 1 + m (tAt b) cp b at z) + < inc, m > =
target, cp public. As a sum under equality weights at z its summand is 1 + CP(X) Y(X) (CP: the
multilinear extension of cp), which is affine in the one map Y (the extension of the bits).
So the map need not be revealed: the sumcheck for a polynomial summand is run without dummy
variable, without last round, without inner mask (`PscPar.core` of Cb/Ld/LdPsc.lean, no revealed
map): k + 1 rounds (`Spec.ldLkpEndU_len`). The claim after these rounds has a coefficient ε, a point
γ and a last value (`PscPar.Mid`: `eps`, `pt`, `fin`). Write U for the hiding polynomial (`hU`,
Cb/Ld/LdHide.lean), ψ for the product of the public polynomials (`hPsi`, the same file). The
sumcheck ends in one linear row with a public target (`Spec.ldLkpEndU_row`, `Spec.ldLkpEndU_tg`),
        U(γ) + ε ψ(γ) < inc, m > + ε CP(γ) Y(γ)  =  (last value) - ε,
which reads the coefficients of the hiding polynomial, the incoming masks and the bits.
The two ways. Cb/Ld/LdLkpEnd.lean reveals the value (k + 3 rounds: a dummy variable and a last round
more; an inner mask, `cAt`; two rows, the one on the bits free of the hiding coefficients). This
file is the cheaper way. The text that we follow allows both and counts neither; which of them a
lookup uses is the assembly's choice.

Main names:
  `B.par`: the sumcheck's parameters, a `PscPar E`.
  `Spec.ldLkpEndU_sum`: its input claim is the claim.
  `Spec.ldLkpEndU_vars`, `Spec.ldLkpEndU_deg`: all conditions of the sumcheck (`PscPar.VarsOK`,
    `ValInj`, `DegOK`, Cb/Ld/LdPsc.lean) hold of `B.par`: stated here, proved in
    Cb/Ld/LdLkpEndUProofs.lean.
  `Spec.ldLkpEndU_goodAt`: at the base, any tuple type, any joint riding along: `GoodAt`.
  `Spec.ldLkpEndU_good`: over a signature: `GoodB`. `GoodB` is `IOR.GoodT` without its clause on
    zero knowledge.

Limits: a condition that comes with the cheaper way, for whoever assembles: the one row reads hiding
coefficients, incoming masks and the bits; so these must lie in oracles that one later test reads
together, or the row has to be split. With the value revealed the row on the bits reads the bits and
one inner mask only.
This file says nothing on zero knowledge (masked messages).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpEnd

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

/-- The parameters. -/
structure LkEndU (E : Type) [Field E] [Fintype E] where
  X : Type
  J : Type
  [finJ : Fintype J]
  k : ℕ
  tAt : (Fin k → Bool) → J
  z : X → Fin k → E
  cp : X → (Fin k → Bool) → E
  inc : X → J → E
  /-- own masks: the coefficients of the hiding polynomial in k variables -/
  wAt : PIdx (List.replicate k (pfCube E 2)) → J

attribute [instance] LkEndU.finJ

namespace LkEndU
variable {E : Type} [Field E] [Fintype E] (B : LkEndU E)

/-- The claim; x = (target, state). -/
def Holds (x : E × B.X) (m : B.J → E) : Prop :=
  Alg.mle (fun b => 1 + m (B.tAt b) * B.cp x.2 b) (B.z x.2) + ∑ j, B.inc x.2 j * m j = x.1

def Y (m : B.J → E) (x : Fin B.k → E) : E := Alg.mle (fun b => m (B.tAt b)) x

abbrev fn (s : B.X) (X : HPt (pVars (List.replicate B.k (pfCube E 2)) (pdEqs E 2 B.k (B.z s)))) :
    Fin B.k → E :=
  hFnOf (pfCube E 2) B.k (pdEqs E 2 B.k (B.z s)) X

/-- The sumcheck: no revealed map; the one map stays as a term of the end claim. -/
def par : PscPar E where
  St := B.X
  J := B.J
  fmt := List.replicate B.k (pfCube E 2)
  dat := fun s => pdEqs E 2 B.k (B.z s)
  A := Empty
  B := Unit
  G := fun _ _ a _ => a.elim
  Gb := fun s m _ X => B.Y m (B.fn s X)
  S0 := fun _ _ _ => 1
  S1 := fun s X _ _ => Alg.mle (B.cp s) (B.fn s X)
  slS := B.inc
  wAt := B.wAt

open Classical in
/-- the map as a linear form on the entries -/
def rowB (s : B.par.St) (_ : B.par.B) (X : HPt (B.par.vars s)) (j : B.J) : E :=
  ∑ b, if B.tAt b = j then Alg.eqk (B.fn s X) b else 0

/-- The input joint: A0 rides along. -/
def relsIn {Ex : ExtSpec} {Wt Kc : Type} (A0 : IOR.Rels Kc B.X Ex Wt) (msg : Wt → B.J → E) :
    IOR.Rels Kc (E × B.X) Ex Wt :=
  ⟨fun x y w => A0.rel x.2 y w ∧ B.Holds x (msg w),
    fun a w => A0.relR (a.1.2, a.2) w ∧ B.Holds a.1 (msg w),
    fun a => A0.on (a.1.2, a.2),
    A0.core⟩

/-- the end claim's public part, in the fields of an output claim with no values -/
def outOf (zz : B.par.Mid) : B.par.Out := ⟨zz.st, zz.eps, zz.pt, zz.fin, fun a : Empty => a.elim⟩

end LkEndU

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

def ldLkpEndU_sum : Prop :=
  ∀ (B : LkEndU E) (x : E × B.X) (m : B.J → E), B.par.SumHolds x m ↔ B.Holds x m
def ldLkpEndU_vars : Prop := ∀ B : LkEndU E, B.par.VarsOK ∧ B.par.ValInj
def ldLkpEndU_deg : Prop := ∀ B : LkEndU E, B.par.DegOK
def ldLkpEndU_joint : Prop :=
  ∀ (B : LkEndU E) (Ex : ExtSpec) (Wt Kc : Type) (A0 : Rels Kc B.X Ex Wt) (msg : Wt → B.J → E),
    B.relsIn A0 msg = B.par.baseIn A0 msg

/-- At the base. -/
def ldLkpEndU_goodAt : Prop :=
  ∀ (B : LkEndU E) (Ex : ExtSpec) (M Wp Kc : Type)
      (A0 : Rels Kc B.X Ex (M × Wp)) (msg : M → B.J → E),
    GoodAt (B.par.core Ex) (B.par.honC Ex fun w => msg w.1) (B.relsIn A0 fun w => msg w.1)
      (B.par.baseMid A0 fun w => msg w.1) (fun _ _ _ wp => wp) (B.par.numsC Ex Kc)

/-- Over a signature. -/
def ldLkpEndU_good : Prop :=
  ∀ (B : LkEndU E) (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type)
      (A0 : Rels Kc B.X E₀ (S.Msg × Wp)) (msg : S.Msg → B.J → E),
    GoodB ((B.par.core E₀).keep S.Smp S.ext) (S.liftH (B.par.honC E₀ fun w => msg w.1))
      (S.over (B.relsIn A0 fun w => msg w.1)) (S.over (B.par.baseMid A0 fun w => msg w.1))
      (fun _ _ w => w) ((B.par.numsC E₀ Kc).keep S.Smp S.ext)

/-- The end claim is one linear row with a public target. -/
def ldLkpEndU_row : Prop :=
  ∀ (B : LkEndU E) (zz : B.par.Mid) (m : B.J → E),
    B.par.MidHolds zz m ↔ (B.par.slU B.rowB).Holds (B.par.tU (B.outOf zz), B.outOf zz) m
/-- its public target: the last value less ε -/
def ldLkpEndU_tg : Prop :=
  ∀ (B : LkEndU E) (zz : B.par.Mid), B.par.tU (B.outOf zz) = zz.fin - zz.eps

def ldLkpEndU_len : Prop := ∀ (B : LkEndU E) (Ex : ExtSpec), (B.par.core Ex).shape.length = B.k + 1

end Spec
end
end Cb
