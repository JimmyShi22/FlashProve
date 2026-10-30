-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLine.lean: two claims on values of revealed maps into one sum claim (`PscOur.SumHolds`)
("the line").

Definitions and statements (in `Cb.Spec`). Proofs: Cb/Ld/LdLineProofs.lean.
In standard terms: two evaluation claims at one point γ become one claim, by a random combination
with the coefficients (1 - ρ, ρ); where the two maps are, at γ, the multilinear extensions of the
two halves of a table on the cube, that is a claim on the value of the table's multilinear extension
at (γ, ρ).

Why: a sumcheck for a polynomial summand (Cb/Ld/LdPsc.lean, the instance `PscOur`) ends with rows
"F_a(γ) + β c_a = v_a" on the values of its revealed maps (`PscOur.A`). If two of these maps are
never sent, being the two halves of one map that is itself given by a sum, the two rows are joined:
  the verifier sends ρ from all of E; the prover sends nothing; the new claim is the combination
    with the coefficients (1 - ρ, ρ):
      (1 - ρ) F_0(γ) + ρ F_1(γ) + β ((1 - ρ) c_0 + ρ c_1) = (1 - ρ) v_0 + ρ v_1,
  and it is the input claim of the next sumcheck: its sum is (1 - ρ) F_0(γ) + ρ F_1(γ), its incoming
    form (`PscOur.slS`) reads the two inner masks c_0, c_1 (`PscOur.cAt`) of the sumcheck before,
    with the coefficients β (1 - ρ), β ρ.
One round, one verifier message, no query, at most one bad ρ.

Main names:
1. `LinePar`, the abstract layer (P: the sumcheck before; N: the one that follows). Two conditions
on the parameters:
  `Virt`: N's sum at the new state is (1 - ρ) F_0(γ) + ρ F_1(γ).
  `Form`: N's incoming form at the new state is β ((1 - ρ) c_0 + ρ c_1).
  The main statements: `Spec.ldLine_cnt`, `Spec.ldLine_piece` (over a signature; it takes a third
    condition: `L.toIn.Back`: `PscIn.Back`, Cb/Ld/LdZero.lean).
2. `LineCube`, the case in use: P's point γ has k coordinates (`gam`, a field: only `Halves` ties it
to P's point); N's summand is G; N's j-th variable (j from 0) is coordinate `sg` j of G's point,
weighted at coordinate `sg` j of (γ, ρ) (`sg`: a field, a permutation of the k + 1 coordinates; by
default the identity). One condition:
  `Halves`: F_b at γ is the multilinear extension, at γ, of the table x ↦ G(x, b) on the cube.
  `Spec.ldLineC_virt`, `Spec.ldLineC_form`, `Spec.ldLineC_back`: then the conditions of the abstract
    layer hold (`Virt` under `Halves`; `Form` and `PscIn.Back` (Cb/Ld/LdZero.lean) without a
    condition).
  The main statement: `Spec.ldLineC_piece`.

Limits:
ρ is drawn from all of E. G is given on points that are functions on the coordinates. The degrees of
N's summand stay conditions of the sumcheck that follows.
`LineCube` covers a map whose table on the cube is given pointwise by the next summand (a level of a
product tree). A map with an inner sum of its own (a row vector times a matrix, a matrix product),
where some outer variables are set to the point and the others stay in the sum, is covered by the
abstract layer only (its `Virt` must be proved for each use).
On zero knowledge: the record `IOR.Piece` (Ior/Tail.lean), which `Spec.ldLine_piece` and
`Spec.ldLineC_piece` conclude, has in its field `good` (`IOR.Good`, Ior/Chain.lean) the clause
`exact` (`Honest.Exact`, Ior/Honest.lean), at the budget of `Nums.draw` (Ior/Draw.lean) (nothing is
sent); that c_0, c_1 are used by nothing else is a matter of the chain's masks.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdZero
import Cb.Ld.LdBat

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

/-! ## 1. The abstract layer -/

/-- The parameters. -/
structure LinePar (E : Type) [Field E] [Fintype E] where
  /-- the sumcheck before, and the one that follows -/
  P : PscOur E
  N : PscOur E
  /-- the two revealed maps -/
  a : Bool → P.A
  /-- where an entry of the earlier naming lies in the later one -/
  jm : P.J → N.J
  /-- the new state, and the old one read off it -/
  nx : P.par.Out → E → N.St
  old : N.St → P.par.Out

namespace LinePar
variable {E : Type} [Field E] [Fintype E] (L : LinePar E)

/-- the point γ of the sumcheck before, without its last coordinate; the last coordinate β -/
def gm (o : L.P.par.Out) : HPt (L.P.vars o.st) := L.P.ini o.st (L.P.par.hp o.st o.pt)
def be (o : L.P.par.Out) : E := L.P.lst o.st (L.P.par.hp o.st o.pt)
/-- the entries in the earlier naming -/
def em (m : L.N.J → E) : L.P.J → E := fun j => m (L.jm j)
/-- the true value of a map at γ; its inner mask -/
def fv (o : L.P.par.Out) (m : L.N.J → E) (b : Bool) : E := L.P.F o.st (L.em m) (L.a b) (L.gm o)
def cv (m : L.N.J → E) (b : Bool) : E := m (L.jm (L.P.cAt (L.a b)))

/-- The step, as a case of the general one. -/
def toIn : PscIn E where
  T := L.N
  St0 := L.P.par.Out
  I := Bool
  ev := Evader.line E
  val := fun o m b => L.fv o m b + L.cv m b * L.be o
  tg := fun o b => o.vals (L.a b)
  nx := L.nx
  old := L.old

/-- The two conditions. -/
def Virt : Prop :=
  ∀ o ρ m, hSumAll (L.N.vars (L.nx o ρ)) (L.N.sum (L.nx o ρ) m) =
    (1 - ρ) * L.fv o m false + ρ * L.fv o m true
def Form : Prop :=
  ∀ o ρ m, ∑ j, L.N.slS (L.nx o ρ) j * m j = L.be o * ((1 - ρ) * L.cv m false + ρ * L.cv m true)

end LinePar

/-! ## 2. The two halves of a table on the cube -/

/-- The parameters of the case in use, with those of the sumcheck that follows. -/
structure LineCube (E : Type) [Field E] [Fintype E] where
  P : PscOur E
  a : Bool → P.A
  /-- the number of coordinates of γ, and γ as a function on them -/
  k : ℕ
  gam : P.par.Out → Fin k → E
  /-- the entries of the sumcheck that follows -/
  J : Type
  [finJ : Fintype J]
  jm : P.J → J
  /-- the degree of its round polynomials; its maps and its summand, on points in k + 1
  coordinates -/
  n : ℕ
  A : Type
  [finA : Fintype A]
  B : Type
  [finB : Fintype B]
  F : P.par.Out → (J → E) → A → (Fin (k + 1) → E) → E
  Fb : P.par.Out → (J → E) → B → (Fin (k + 1) → E) → E
  S0 : P.par.Out → (Fin (k + 1) → E) → (A → E) → E
  S1 : P.par.Out → (Fin (k + 1) → E) → (A → E) → B → E
  DY : ℕ
  wAt : PIdx (List.replicate (k + 1) (pfCube E n) ++ [pDummy E DY]) → J
  cAt : A → J
  /-- the order of the rounds: the j-th variable of the sumcheck that follows (j from 0, in the
  order of their rounds) is coordinate sg j of the summand's point and has the equality weight at
  coordinate sg j of (γ, ρ); by default the j-th variable is coordinate j -/
  sg : Equiv.Perm (Fin (k + 1)) := Equiv.refl _

attribute [instance] LineCube.finJ LineCube.finA LineCube.finB

namespace LineCube
variable {E : Type} [Field E] [Fintype E] (C : LineCube E)

/-- The summand that follows, as a function of a point. -/
def G (o : C.P.par.Out) (m : C.J → E) (x : Fin (C.k + 1) → E) : E :=
  C.S0 o x (fun a => C.F o m a x) + ∑ b, C.S1 o x (fun a => C.F o m a x) b * C.Fb o m b x

/-- the point (γ, ρ): ρ is the last coordinate -/
def pt (s : C.P.par.Out × E) : Fin (C.k + 1) → E := Fin.snoc (C.gam s.1) s.2

/-- the point (γ, ρ) in the order of the rounds: entry j is coordinate sg j -/
def ptS (s : C.P.par.Out × E) : Fin (C.k + 1) → E := fun j => C.pt s (C.sg j)

/-- a point of the sumcheck that follows, read by coordinate: coordinate i is the variable number
sg⁻¹ i -/
abbrev fn (s : C.P.par.Out × E)
    (X : HPt (pVars (List.replicate (C.k + 1) (pfCube E C.n)) (pdEqs E C.n (C.k + 1) (C.ptS s)))) :
    Fin (C.k + 1) → E :=
  fun i => hFnOf (pfCube E C.n) (C.k + 1) (pdEqs E C.n (C.k + 1) (C.ptS s)) X (C.sg.symm i)

open Classical in
/-- The sumcheck that follows: state (the output of the sumcheck before, ρ); equality weights at (γ,
ρ), in the order of the rounds; incoming form β (1 - ρ) at c_0, β ρ at c_1. -/
def next : PscOur E where
  St := C.P.par.Out × E
  J := C.J
  fmt := List.replicate (C.k + 1) (pfCube E C.n)
  dat := fun s => pdEqs E C.n (C.k + 1) (C.ptS s)
  A := C.A
  B := C.B
  F := fun s m a X => C.F s.1 m a (C.fn s X)
  Fb := fun s m b X => C.Fb s.1 m b (C.fn s X)
  S0 := fun s X v => C.S0 s.1 (C.fn s X) v
  S1 := fun s X v b => C.S1 s.1 (C.fn s X) v b
  DY := C.DY
  slS := fun s j =>
    C.P.lst s.1.st (C.P.par.hp s.1.st s.1.pt) *
      ((if j = C.jm (C.P.cAt (C.a false)) then 1 - s.2 else 0) +
        if j = C.jm (C.P.cAt (C.a true)) then s.2 else 0)
  wAt := C.wAt
  cAt := C.cAt

def toLine : LinePar E where
  P := C.P
  N := C.next
  a := C.a
  jm := C.jm
  nx := fun o ρ => (o, ρ)
  old := fun s => s.1

/-- The two maps are the halves, in the last coordinate, of the table of the summand's values on the
cube. -/
def Halves : Prop :=
  ∀ (o : C.P.par.Out) (m : C.J → E) (b : Bool),
    C.P.F o.st (fun j => m (C.jm j)) (C.a b) (C.P.ini o.st (C.P.par.hp o.st o.pt)) =
      Alg.mle (fun x : Fin C.k → Bool => C.G o m (Alg.corner (Fin.snoc x b))) (C.gam o)

end LineCube

/-! ## The statements -/

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

/-- "All claims hold" says: the two rows of the sumcheck before hold. -/
def ldLine_all : Prop :=
  ∀ (L : LinePar E) o m, L.toIn.AllHold o m ↔ ∀ b, L.P.par.EHolds o (L.em m) (L.a b)
/-- States: under `L.Virt` and `L.Form`, the new claim is the input claim of the sumcheck that
follows. -/
def ldLine_link : Prop := ∀ L : LinePar E, L.Virt → L.Form → L.toIn.Link
/-- the new target -/
def ldLine_tg : Prop :=
  ∀ (L : LinePar E) (o : L.P.par.Out) (ρ : E),
    (L.toIn.nxX o ρ).1 = (1 - ρ) * o.vals (L.a false) + ρ * o.vals (L.a true)
def ldLine_ok : Prop := ∀ L : LinePar E, L.toIn.ev.OK
def ldLine_err : Prop := ∀ L : LinePar E, L.toIn.ev.err = 1
/-- Under `L.Virt` and `L.Form`, for each fixed tuple of entries of which one of the two rows
fails: at most one ρ at which the new claim holds. -/
def ldLine_cnt : Prop :=
  ∀ L : LinePar E, L.Virt → L.Form →
    ∀ o m, ¬ (∀ b, L.P.par.EHolds o (L.em m) (L.a b)) →
      cnt (fun ρ : E => L.N.SumHolds (L.toIn.nxX o ρ) m) ≤ 1

/-- The line over a signature. States: under `L.Virt`, `L.Form` and `L.toIn.Back` it is an
`IOR.Piece` (a piece of a chain, Ior/Tail.lean), with the identity as extractor, at the numbers
`Nums.draw .. 1` (Ior/Draw.lean), from q to q for every q. -/
def ldLine_piece : Prop :=
  ∀ (L : LinePar E) (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type)
      (R0 : Rels Kc L.P.par.Out E₀ (S.Msg × Wp)) (msg : S.Msg → L.N.J → E)
      (q : Finset (E₀.prod S.ext).Pos → Prop),
    L.Virt → L.Form → L.toIn.Back →
    Piece (IOR.draw L.toIn.ev.D (S.drawNx L.toIn.nxX) (E₀.prod S.ext))
      (Honest.draw L.toIn.ev.D (S.drawNx L.toIn.nxX) (E₀.prod S.ext) (S.Wit × Wp))
      (S.over ⟨fun o y w => R0.rel o y w ∧ ∀ b, L.P.par.EHolds o (L.em (msg w.1)) (L.a b),
        fun a w => R0.relR a w ∧ ∀ b, L.P.par.EHolds a.1 (L.em (msg w.1)) (L.a b),
        R0.on, R0.core⟩)
      (S.over (L.toIn.relsOut R0 msg)) (fun _ _ w => w)
      (Nums.draw Kc L.toIn.ev.D (S.drawNx L.toIn.nxX) (E₀.prod S.ext) 1) q q

/-- The extension of a table at (γ, ρ), ρ the last coordinate. -/
def ldLine_mle_snoc : Prop :=
  ∀ (k : ℕ) (u : (Fin (k + 1) → Bool) → E) (γ : Fin k → E) (ρ : E),
    Alg.mle u (Fin.snoc γ ρ : Fin (k + 1) → E) =
      (1 - ρ) * Alg.mle (fun x => u (Fin.snoc x false)) γ +
        ρ * Alg.mle (fun x => u (Fin.snoc x true)) γ

/-- The case in use meets the conditions of the abstract layer (`Virt` under `C.Halves`). -/
def ldLineC_virt : Prop := ∀ C : LineCube E, C.Halves → C.toLine.Virt
def ldLineC_form : Prop := ∀ C : LineCube E, C.toLine.Form
def ldLineC_back : Prop := ∀ C : LineCube E, C.toLine.toIn.Back
def ldLineC_vars : Prop := ∀ C : LineCube E, C.next.VarsOK ∧ C.next.ValInj

/-- The line on the two halves of a table, over a signature. States: under `C.Halves` it is an
`IOR.Piece` (Ior/Tail.lean), with the identity as extractor, at the numbers `Nums.draw .. 1`, from q
to q for every q. -/
def ldLineC_piece : Prop :=
  ∀ (C : LineCube E) (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type)
      (R0 : Rels Kc C.P.par.Out E₀ (S.Msg × Wp)) (msg : S.Msg → C.J → E)
      (q : Finset (E₀.prod S.ext).Pos → Prop),
    C.Halves →
    Piece (IOR.draw C.toLine.toIn.ev.D (S.drawNx C.toLine.toIn.nxX) (E₀.prod S.ext))
      (Honest.draw C.toLine.toIn.ev.D (S.drawNx C.toLine.toIn.nxX) (E₀.prod S.ext) (S.Wit × Wp))
      (S.over ⟨fun o y w => R0.rel o y w ∧ ∀ b, C.P.par.EHolds o (C.toLine.em (msg w.1)) (C.a b),
        fun a w => R0.relR a w ∧ ∀ b, C.P.par.EHolds a.1 (C.toLine.em (msg w.1)) (C.a b),
        R0.on, R0.core⟩)
      (S.over (C.toLine.toIn.relsOut R0 msg)) (fun _ _ w => w)
      (Nums.draw Kc C.toLine.toIn.ev.D (S.drawNx C.toLine.toIn.nxX) (E₀.prod S.ext) 1) q q

end Spec
end
end Cb
