-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdZero.lean: claims on values into one sum claim; the zerocheck.

In standard terms: the zerocheck: the claim that functions vanish at all corners of the cube in k
variables becomes one sumcheck claim: the verifier draws coefficients and a point z of E^k, and the
new claim is that the sum over the cube, with equality weights at z, of the combination of the
functions with these coefficients is 0.

Definitions and statements (each a `Prop` in `Cb.Spec`). Proofs: Cb/Ld/LdZeroProofs.lean; for
`Spec.ldZero_ok_lag` and the statements `Spec.ldZeroS_*`: Cb/Ld/LdZeroSkipProofs.lean.

1. The general step (`PscIn`). There are claims named by a finite set I: "the value val_i of the
   messages' entries is tg_i" (values need not be linear in the entries). The prover sends nothing.
   The verifier sends one message, a seed β of a zero-evader on I (`Cb.Evader` of
   Cb/Gen/BatEvader.lean).
   An evader (`Cb.Evader`, Cb/Gen/BatEvader.lean): the seeds, the coefficients that a seed gives,
   and a number err; its property (`Evader.OK`): a vector other than 0 is annihilated by at most err
   seeds.
   The new claim is one: the combination of the values with the seed's coefficients is the
   combination of the targets. So far this is the batching of Cb/Ld/LdBat.lean. Here the new claim
   is the input claim of a sumcheck (Cb/Ld/LdPsc.lean: `PscOur.SumHolds`, the true sum in k
   variables):
      `PscIn.Link`: a condition on the parameters; proved for the two zerochecks of this file.
      `PscIn.Back`: the new state remembers the old one, so that whatever else is claimed rides
        along.
   One round, one verifier message, no query; the verifier never rejects; oracles and witness stay:
   `IOR.draw` of Ior/Draw.lean.
      `Spec.pscIn_piece`: under `Z.Link`, `Z.Back` and `Z.ev.OK`: over a signature S
        (Cb/Ld/LdSig.lean), relaxation by decoding with the sample on both sides: a piece of a chain
        (so `IOR.Good`: complete, knowledge sound, on the collision-free statements that meet R0's
        condition (the input joint's field `on`), with the identity and the one error ev.err,
        nothing to simulate), from S.over (all claims, and R0) to S.over (T's sum claim, and R0).
2. Evaders. `Evader.one` (one claim, no seed, number 0); `Evader.prod` (coefficients that are
   products; number err₁ |D₂| + |D₁| err₂); `Evader.lag` (Lagrange weights of a domain at a point;
   number |domain| - 1).
3. The zerocheck on the cube (`ZeroCube`). Claim: each of the functions G_t (t in a finite set Tt),
   G_t(x) = S0_t(st; x, F(x)) + ∑_b S1_t,b(st; x, F(x)) Fb_b(x), vanishes at all corners of the cube
   in k variables.
   The verifier sends, in one message, a seed c of an evader "co" on Tt and a point z from all of
   E^k. The sumcheck that follows is `Z.next : PscOur E`; its j-th variable (j from 0) is
   coordinate `sg` j of the functions' point, weighted at coordinate `sg` j of z (`sg`: a field, a
   permutation of the k coordinates; by default the identity).
      Errors, as a count of the |co.D| |E|^k messages: co.err |E|^k + |co.D| k |E|^(k-1)
      (`Spec.ldZero_err`); for one function (Tt = Unit, co = `Evader.one`): k |E|^(k-1) of |E|^k.
      `Spec.ldZero_piece` (under `Z.co.OK`): the zerocheck over a signature.
4. With the first variable over a domain (`ZeroSkip`): the functions vanish on (domain × cube in k
   variables); the verifier's point is (z₀, z); Lagrange weights at z₀, equality weights at z. For
   one function: (|domain| - 1 + k) |E|^k of |E|^(k+1). The statements `Spec.ldZeroS_*`: those on
   the evader, the variables and the piece ask that the domain's points are distinct;
   `Spec.ldZeroS_vars` also that the domain is not empty; those on the evader and the piece ask
   `Z.co.OK`. `ZeroSkip` has no field `sg`: its j-th cube variable is coordinate j.

Limits: points are drawn from all of E. The summand that follows is given by S0, S1, F, Fb on points
that are functions on the coordinates (Fin k → E).
`Evader.OK` with a number that reaches the number of seeds holds for free.
The degrees of the summand (`PscOur.DegX`, `PscOur.DegY`) stay conditions of the sumcheck that
follows.
This file says nothing on running times.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdPscSig
import Cb.Ld.LdPscVarsMix
import Cb.Ld.LdLkpChain
import Cb.Gen.BatEvader

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

/-! ## 1. Claims on values into one sum claim -/

/-- The parameters of the step. -/
structure PscIn (E : Type) [Field E] [Fintype E] where
  /-- the sumcheck that follows -/
  T : PscOur E
  /-- the states before the step -/
  St0 : Type
  /-- the names of the claims -/
  I : Type
  [finI : Fintype I]
  ev : Evader E I
  /-- values and targets -/
  val : St0 → (T.J → E) → I → E
  tg : St0 → I → E
  /-- the new state, and the old one read off it -/
  nx : St0 → ev.D → T.St
  old : T.St → St0

attribute [instance] PscIn.finI

namespace PscIn
variable {E : Type} [Field E] [Fintype E] (Z : PscIn E)

/-- All claims hold. -/
def AllHold (st : Z.St0) (m : Z.T.J → E) : Prop := ∀ i, Z.val st m i = Z.tg st i

/-- The new claim is a sum claim: sum and incoming form of T at the new state are the combination of
the values. -/
def Link : Prop :=
  ∀ st β m, hSumAll (Z.T.vars (Z.nx st β)) (Z.T.sum (Z.nx st β) m) +
      ∑ j, Z.T.slS (Z.nx st β) j * m j =
    ∑ i, Z.ev.ze β i * Z.val st m i
def Back : Prop := ∀ st β, Z.old (Z.nx st β) = st

/-- the new explicit part: (the combination of the targets, the new state) -/
def nxX (st : Z.St0) (β : Z.ev.D) : E × Z.T.St := (∑ i, Z.ev.ze β i * Z.tg st i, Z.nx st β)

variable {Ex : ExtSpec} {M Wp Kc : Type}

/-- what rides along, read at the old state -/
def ride (R0 : IOR.Rels Kc Z.St0 Ex (M × Wp)) : IOR.Rels Kc Z.T.St Ex (M × Wp) :=
  ⟨fun st y w => R0.rel (Z.old st) y w,
    fun a w => R0.relR (Z.old a.1, a.2) w,
    fun a => R0.on (Z.old a.1, a.2),
    R0.core⟩

/-- The two joints at the base: all claims, and R0; T's sum claim, and R0. -/
def relsIn (R0 : IOR.Rels Kc Z.St0 Ex (M × Wp)) (msg : M → Z.T.J → E) :
    IOR.Rels Kc Z.St0 Ex (M × Wp) :=
  ⟨fun st y w => R0.rel st y w ∧ Z.AllHold st (msg w.1),
    fun a w => R0.relR a w ∧ Z.AllHold a.1 (msg w.1),
    R0.on, R0.core⟩
def relsOut (R0 : IOR.Rels Kc Z.St0 Ex (M × Wp)) (msg : M → Z.T.J → E) :
    IOR.Rels Kc (E × Z.T.St) Ex (M × Wp) :=
  Z.T.baseIn (Z.ride R0) fun w => msg w.1

end PscIn

/-! ## 2. Evaders -/

/-- one claim: no seed, the coefficient 1 -/
@[reducible] def Evader.one (E : Type) [Field E] : Evader E Unit :=
  { D := Unit, ze := fun _ _ => 1, err := 0 }

/-- Coefficients that are products. -/
@[reducible] def Evader.prod {E I₁ I₂ : Type} [Field E] (Z₁ : Evader E I₁) (Z₂ : Evader E I₂) :
    Evader E (I₁ × I₂) :=
  { D := Z₁.D × Z₂.D, ze := fun ρ i => Z₁.ze ρ.1 i.1 * Z₂.ze ρ.2 i.2,
    err := Z₁.err * Fintype.card Z₂.D + Fintype.card Z₁.D * Z₂.err }

/-- The Lagrange weights of a domain at a point. -/
@[reducible] def Evader.lag (E : Type) [Field E] [Fintype E] {D : Type} [Fintype D]
    [DecidableEq D] (dom : D → E) : Evader E D :=
  { D := E, ze := fun z x => (Lagrange.basis Finset.univ dom x).eval z, err := Fintype.card D - 1 }

/-! ## 3. The zerocheck on the cube -/

/-- The parameters of the zerocheck on the cube, with those of the sumcheck that follows. -/
structure ZeroCube (E : Type) [Field E] [Fintype E] where
  St : Type
  J : Type
  [finJ : Fintype J]
  /-- the number of variables; the degree of the round polynomials that follow -/
  k : ℕ
  n : ℕ
  /-- the functions that vanish, and the evader that combines them -/
  Tt : Type
  [finT : Fintype Tt]
  co : Evader E Tt
  /-- the maps: those that the sumcheck will reveal, and the others -/
  A : Type
  [finA : Fintype A]
  B : Type
  [finB : Fintype B]
  F : St → (J → E) → A → (Fin k → E) → E
  Fb : St → (J → E) → B → (Fin k → E) → E
  S0 : St → Tt → (Fin k → E) → (A → E) → E
  S1 : St → Tt → (Fin k → E) → (A → E) → B → E
  /-- for the sumcheck that follows: the degree in the revealed maps, its own masks -/
  DY : ℕ
  wAt : PIdx (List.replicate k (pfCube E n) ++ [pDummy E DY]) → J
  cAt : A → J
  /-- the order of the rounds: the j-th variable of the sumcheck that follows (j from 0, in the
  order of their rounds) is coordinate sg j of the functions' point and has the equality weight at
  coordinate sg j of the drawn point; by default the j-th variable is coordinate j -/
  sg : Equiv.Perm (Fin k) := Equiv.refl _

attribute [instance] ZeroCube.finJ ZeroCube.finT ZeroCube.finA ZeroCube.finB

namespace ZeroCube
variable {E : Type} [Field E] [Fintype E] (Z : ZeroCube E)

/-- The functions. -/
def G (st : Z.St) (m : Z.J → E) (t : Z.Tt) (x : Fin Z.k → E) : E :=
  Z.S0 st t x (fun a => Z.F st m a x) + ∑ b, Z.S1 st t x (fun a => Z.F st m a x) b * Z.Fb st m b x

/-- The claim: every function vanishes at every corner. -/
def ZeroHolds (st : Z.St) (m : Z.J → E) : Prop :=
  ∀ t (b : Fin Z.k → Bool), Z.G st m t (Alg.corner b) = 0

/-- the drawn point in the order of the rounds: entry j is coordinate sg j -/
def zS (z : Fin Z.k → E) : Fin Z.k → E := fun j => z (Z.sg j)

/-- a point of the sumcheck that follows, read by coordinate: coordinate i is the variable number
sg⁻¹ i -/
abbrev fn (z : Fin Z.k → E)
    (X : HPt (pVars (List.replicate Z.k (pfCube E Z.n)) (pdEqs E Z.n Z.k (Z.zS z)))) :
    Fin Z.k → E :=
  fun i => hFnOf (pfCube E Z.n) Z.k (pdEqs E Z.n Z.k (Z.zS z)) X (Z.sg.symm i)

/-- The sumcheck that follows: state (st, (seed, point)); equality weights at the point, in the
order of the rounds; summand ∑_t co(seed)_t G_t; no incoming form. -/
def next : PscOur E where
  St := Z.St × (Z.co.D × (Fin Z.k → E))
  J := Z.J
  fmt := List.replicate Z.k (pfCube E Z.n)
  dat := fun s => pdEqs E Z.n Z.k (Z.zS s.2.2)
  A := Z.A
  B := Z.B
  F := fun s m a X => Z.F s.1 m a (Z.fn s.2.2 X)
  Fb := fun s m b X => Z.Fb s.1 m b (Z.fn s.2.2 X)
  S0 := fun s X v => ∑ t, Z.co.ze s.2.1 t * Z.S0 s.1 t (Z.fn s.2.2 X) v
  S1 := fun s X v b => ∑ t, Z.co.ze s.2.1 t * Z.S1 s.1 t (Z.fn s.2.2 X) v b
  DY := Z.DY
  slS := fun _ _ => 0
  wAt := Z.wAt
  cAt := Z.cAt

/-- The zerocheck as a step into a sumcheck. -/
def toIn : PscIn E where
  T := Z.next
  St0 := Z.St
  I := Z.Tt × (Fin Z.k → Bool)
  ev := Z.co.prod (Evader.eqPt E (Fin Z.k))
  val := fun st m i => Z.G st m i.1 (Alg.corner i.2)
  tg := fun _ _ => 0
  nx := fun st β => (st, β)
  old := fun s => s.1

end ZeroCube

/-! ## 4. The first variable over a domain -/

/-- The parameters of the zerocheck on (domain × cube). -/
structure ZeroSkip (E : Type) [Field E] [Fintype E] where
  St : Type
  J : Type
  [finJ : Fintype J]
  /-- the domain -/
  D : Type
  [finD : Fintype D]
  [decD : DecidableEq D]
  dom : D → E
  /-- the number of cube variables; the degrees of the round polynomials that follow -/
  k : ℕ
  n₁ : ℕ
  n : ℕ
  Tt : Type
  [finT : Fintype Tt]
  co : Evader E Tt
  A : Type
  [finA : Fintype A]
  B : Type
  [finB : Fintype B]
  F : St → (J → E) → A → E → (Fin k → E) → E
  Fb : St → (J → E) → B → E → (Fin k → E) → E
  S0 : St → Tt → E → (Fin k → E) → (A → E) → E
  S1 : St → Tt → E → (Fin k → E) → (A → E) → B → E
  DY : ℕ
  wAt : PIdx (pfSkip E n₁ n D k ++ [pDummy E DY]) → J
  cAt : A → J

attribute [instance] ZeroSkip.finJ ZeroSkip.finD ZeroSkip.decD ZeroSkip.finT
  ZeroSkip.finA ZeroSkip.finB

namespace ZeroSkip
variable {E : Type} [Field E] [Fintype E] (Z : ZeroSkip E)

def G (st : Z.St) (m : Z.J → E) (t : Z.Tt) (x₀ : E) (x : Fin Z.k → E) : E :=
  Z.S0 st t x₀ x (fun a => Z.F st m a x₀ x) +
    ∑ b, Z.S1 st t x₀ x (fun a => Z.F st m a x₀ x) b * Z.Fb st m b x₀ x

/-- The claim: every function vanishes at every point of (domain × corners). -/
def ZeroHolds (st : Z.St) (m : Z.J → E) : Prop :=
  ∀ t d (b : Fin Z.k → Bool), Z.G st m t (Z.dom d) (Alg.corner b) = 0

abbrev fn (z₀ : E) (z : Fin Z.k → E)
    (X : HPt (pVars (pfSkip E Z.n₁ Z.n Z.D Z.k) (pdSkipW E Z.n₁ Z.n Z.dom z₀ Z.k z))) :
    Fin Z.k → E :=
  hFnOf (pfCube E Z.n) Z.k (pdEqs E Z.n Z.k z) X.2

/-- The sumcheck that follows: Lagrange weights at z₀, equality weights at z. -/
def next : PscOur E where
  St := Z.St × (Z.co.D × (E × (Fin Z.k → E)))
  J := Z.J
  fmt := pfSkip E Z.n₁ Z.n Z.D Z.k
  dat := fun s => pdSkipW E Z.n₁ Z.n Z.dom s.2.2.1 Z.k s.2.2.2
  A := Z.A
  B := Z.B
  F := fun s m a X => Z.F s.1 m a X.1 (Z.fn s.2.2.1 s.2.2.2 X)
  Fb := fun s m b X => Z.Fb s.1 m b X.1 (Z.fn s.2.2.1 s.2.2.2 X)
  S0 := fun s X v => ∑ t, Z.co.ze s.2.1 t * Z.S0 s.1 t X.1 (Z.fn s.2.2.1 s.2.2.2 X) v
  S1 := fun s X v b => ∑ t, Z.co.ze s.2.1 t * Z.S1 s.1 t X.1 (Z.fn s.2.2.1 s.2.2.2 X) v b
  DY := Z.DY
  slS := fun _ _ => 0
  wAt := Z.wAt
  cAt := Z.cAt

def toIn : PscIn E where
  T := Z.next
  St0 := Z.St
  I := Z.Tt × (Z.D × (Fin Z.k → Bool))
  ev := Z.co.prod ((Evader.lag E Z.dom).prod (Evader.eqPt E (Fin Z.k)))
  val := fun st m i => Z.G st m i.1 (Z.dom i.2.1) (Alg.corner i.2.2)
  tg := fun _ _ => 0
  nx := fun st β => (st, β)
  old := fun s => s.1

end ZeroSkip

/-! ## The statements -/

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

/-- Under `Z.Link`, the new claim says that the combination of the gaps is 0; it holds at every seed
if all claims hold (`pscIn_fwd`). -/
def pscIn_iff : Prop :=
  ∀ Z : PscIn E, Z.Link →
    ∀ st β m, Z.T.SumHolds (Z.nxX st β) m ↔ ∑ i, Z.ev.ze β i * (Z.val st m i - Z.tg st i) = 0
def pscIn_fwd : Prop :=
  ∀ Z : PscIn E, Z.Link → ∀ st β m, Z.AllHold st m → Z.T.SumHolds (Z.nxX st β) m

/-- Under `Z.Link` and `Z.ev.OK`, for each fixed tuple of entries of which not all claims hold: at
most ev.err seeds at which the new claim holds. -/
def pscIn_cnt : Prop :=
  ∀ Z : PscIn E, Z.Link → Z.ev.OK →
    ∀ st m, ¬ Z.AllHold st m → cnt (fun β : Z.ev.D => Z.T.SumHolds (Z.nxX st β) m) ≤ Z.ev.err

/-- The step over a signature. -/
def pscIn_piece : Prop :=
  ∀ (Z : PscIn E) (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type) (R0 : Rels Kc Z.St0 E₀ (S.Msg × Wp))
      (msg : S.Msg → Z.T.J → E) (q : Finset (E₀.prod S.ext).Pos → Prop),
    Z.Link → Z.Back → Z.ev.OK →
    Piece (IOR.draw Z.ev.D (S.drawNx Z.nxX) (E₀.prod S.ext))
      (Honest.draw Z.ev.D (S.drawNx Z.nxX) (E₀.prod S.ext) (S.Wit × Wp)) (S.over (Z.relsIn R0 msg))
      (S.over (Z.relsOut R0 msg)) (fun _ _ w => w)
      (Nums.draw Kc Z.ev.D (S.drawNx Z.nxX) (E₀.prod S.ext) Z.ev.err) q q

/-- The evaders have the property `Evader.OK`: the product if both factors have it, the Lagrange
weights if the domain's points are distinct. -/
def ldZero_ok_one : Prop := (Evader.one E).OK
def ldZero_ok_prod : Prop :=
  ∀ (I₁ I₂ : Type) [Fintype I₁] [Fintype I₂] (Z₁ : Evader E I₁) (Z₂ : Evader E I₂),
    Z₁.OK → Z₂.OK → (Z₁.prod Z₂).OK
def ldZero_ok_lag : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D] (dom : D → E),
    Function.Injective dom → (Evader.lag E dom).OK

/-- The zerocheck on the cube meets the conditions of the step (`ev.OK` under `Z.co.OK`); "all
claims hold" is its claim. -/
def ldZero_link : Prop := ∀ Z : ZeroCube E, Z.toIn.Link
def ldZero_back : Prop := ∀ Z : ZeroCube E, Z.toIn.Back
def ldZero_ok : Prop := ∀ Z : ZeroCube E, Z.co.OK → Z.toIn.ev.OK
def ldZero_all : Prop := ∀ (Z : ZeroCube E) st m, Z.toIn.AllHold st m ↔ Z.ZeroHolds st m
/-- the new target is 0 -/
def ldZero_tg : Prop := ∀ (Z : ZeroCube E) st β, (Z.toIn.nxX st β).1 = 0
/-- The variables of the sumcheck that follows meet their conditions. -/
def ldZero_vars : Prop := ∀ Z : ZeroCube E, Z.next.VarsOK ∧ Z.next.ValInj
/-- The number of bad messages. -/
def ldZero_err : Prop :=
  ∀ Z : ZeroCube E, Z.toIn.ev.err =
    Z.co.err * Fintype.card E ^ Z.k + Fintype.card Z.co.D * (Z.k * Fintype.card E ^ (Z.k - 1))

/-- The zerocheck over a signature. -/
def ldZero_piece : Prop :=
  ∀ (Z : ZeroCube E) (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type) (R0 : Rels Kc Z.St E₀ (S.Msg × Wp))
      (msg : S.Msg → Z.J → E) (q : Finset (E₀.prod S.ext).Pos → Prop),
    Z.co.OK →
    Piece (IOR.draw Z.toIn.ev.D (S.drawNx Z.toIn.nxX) (E₀.prod S.ext))
      (Honest.draw Z.toIn.ev.D (S.drawNx Z.toIn.nxX) (E₀.prod S.ext) (S.Wit × Wp))
      (S.over ⟨fun st y w => R0.rel st y w ∧ Z.ZeroHolds st (msg w.1),
        fun a w => R0.relR a w ∧ Z.ZeroHolds a.1 (msg w.1),
        R0.on, R0.core⟩)
      (S.over (Z.toIn.relsOut R0 msg)) (fun _ _ w => w)
      (Nums.draw Kc Z.toIn.ev.D (S.drawNx Z.toIn.nxX) (E₀.prod S.ext) Z.toIn.ev.err) q q

/-- The same with the first variable over a domain. The statements on the evader (`ldZeroS_ok`), the
variables (`ldZeroS_vars`) and the piece (`ldZeroS_piece`) ask that the domain's points are
distinct; `ldZeroS_vars` also that the domain is not empty; those on the evader and the piece ask
`Z.co.OK`. -/
def ldZeroS_link : Prop := ∀ Z : ZeroSkip E, Z.toIn.Link
def ldZeroS_back : Prop := ∀ Z : ZeroSkip E, Z.toIn.Back
def ldZeroS_ok : Prop := ∀ Z : ZeroSkip E, Function.Injective Z.dom → Z.co.OK → Z.toIn.ev.OK
def ldZeroS_all : Prop := ∀ (Z : ZeroSkip E) st m, Z.toIn.AllHold st m ↔ Z.ZeroHolds st m
def ldZeroS_vars : Prop :=
  ∀ Z : ZeroSkip E, Function.Injective Z.dom → Nonempty Z.D → Z.next.VarsOK ∧ Z.next.ValInj
def ldZeroS_err : Prop :=
  ∀ Z : ZeroSkip E, Z.toIn.ev.err =
    Z.co.err * (Fintype.card E * Fintype.card E ^ Z.k) +
      Fintype.card Z.co.D *
        ((Fintype.card Z.D - 1) * Fintype.card E ^ Z.k +
          Fintype.card E * (Z.k * Fintype.card E ^ (Z.k - 1)))
def ldZeroS_piece : Prop :=
  ∀ (Z : ZeroSkip E) (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type) (R0 : Rels Kc Z.St E₀ (S.Msg × Wp))
      (msg : S.Msg → Z.J → E) (q : Finset (E₀.prod S.ext).Pos → Prop),
    Function.Injective Z.dom → Z.co.OK →
    Piece (IOR.draw Z.toIn.ev.D (S.drawNx Z.toIn.nxX) (E₀.prod S.ext))
      (Honest.draw Z.toIn.ev.D (S.drawNx Z.toIn.nxX) (E₀.prod S.ext) (S.Wit × Wp))
      (S.over ⟨fun st y w => R0.rel st y w ∧ Z.ZeroHolds st (msg w.1),
        fun a w => R0.relR a w ∧ Z.ZeroHolds a.1 (msg w.1),
        R0.on, R0.core⟩)
      (S.over (Z.toIn.relsOut R0 msg)) (fun _ _ w => w)
      (Nums.draw Kc Z.toIn.ev.D (S.drawNx Z.toIn.nxX) (E₀.prod S.ext) Z.toIn.ev.err) q q

end Spec
end
end Cb
