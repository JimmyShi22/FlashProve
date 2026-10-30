-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Tok.lean: a sumcheck over the token positions whose claimed sum is hidden and sent, as
an interactive oracle reduction with its knowledge soundness.

In the layers' sub-proof two sumchecks have this form: the products of the norms' rows, and the
terms of the lookup's join. The summand, at a position x, is a sum of terms: a coefficient that is
read off the state, times at most two values at x of vectors. Vectors are of three kinds. Two are
computed from the entries of the committed messages. The extension of a SHOWN vector is revealed
at the last point, under a mask. A KEPT vector's is not: a term has at most one kept factor, and
the value of the kept part at the last point stands in the first output row. The third kind is
public: it does not read the entries, and its extension at the point is a factor that the verifier
computes: a term may be a coefficient, times a public vector, times a kept one, with no shown
factor (in the terms of the lookup's join: a rotary table times the normed input of the queries
and keys). The sum is taken under the equality weights at a point that is read off the state, so
it may consist of challenges of earlier blocks. The rounds, as the programs have them: the claimed
sum under a mask and the sum of the hiding polynomial, then a coefficient; one round for each bit
of the position, in which the linear and the quadratic coefficient are sent and the constant one
is left out (round j binds coordinate j of the point; in the convention of `Blocks.ext` coordinate
0 belongs to the top bit); one round in a further variable, with dy scalars; the end values of the
shown vectors.

Main names:
  `TokL`: the parameters. `t0`: the terms without a kept factor; `tb b`: the terms whose kept
    factor is b; `tc b`: the terms with a public factor and the kept factor b. `h0`, `hb`: no term
    of t0 or tb has more than two factors, nor more than dy shown ones.
  `TokL.toSum`: the parameters of Cb/Pv/Lay/Sum.lean.
  `TokL.eq0`, `TokL.pick_ok`: in every round the constant coefficient may be the one that is left
    out. `TokL.out_some`: so the verifier refuses nothing.
  `TokL.blk`, `TokL.knowAt`, `TokL.know`: the reduction and its knowledge soundness for each fixed
    tuple of messages: from "what rides, and Psi at the true masked sum" to "what rides, Psi at
    the sent scalar, and the sumcheck's output claims". Psi is any claim on the state, the sent
    scalar and the entries.
  `TokL.errs`: its errors: 1, then 2 for each bit, then dy, 0.
  `TokL.inc_sum`, `TokL.sum_iff`, `TokL.tsum_eq`: the incoming form is the one mask of the sent
    sum; what the sum claim says; the true masked sum: the extension of the summand `smd` at the
    point, plus that mask.
  `TokL.ev_iff`: what the output row on a shown vector's end value says.

Limits: nothing is said on what the vectors, the coefficients and the point are in the model, nor
is the order of the rounds compared with the programs' here. `h0` and `hb` are fields of the
record: a user pays them. Of the first output row nothing is said but that it is the library's
(`PscPar.UHolds`). The errors are numbers of bad draws, round by round. Every draw is from the
whole field, but the further variable's, which is from the elements other than 0. "For each fixed
tuple of messages" asks of a user that every entry that the maps, forms and claims of the record
read is fixed before the block's first draw. Nothing is said on the honest prover, on completeness
or on zero knowledge. The sentences on what the programs do are by reading: nothing is compared
with the programs here. This reduction is not joined to the one before it or behind it in the
sub-proof: that the two joints agree is not shown in this folder.

-/
import Cb.Pv.Lay.Sum
import Cb.Pv.Lay.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Johnson.L5.Door

noncomputable section

/-- The parameters of a sumcheck over the token positions. -/
structure TokL (E : Type) [Field E] [Fintype E] where
  J : Type
  [finJ : Fintype J]
  /-- the number of bits of a position -/
  k : ℕ
  St : Type
  /-- the shown vectors and the kept ones -/
  A : Type
  [finA : Fintype A]
  B : Type
  [finB : Fintype B]
  vA : St → (J → E) → A → ℕ → E
  vB : St → (J → E) → B → ℕ → E
  /-- the point of the equality weights -/
  pnt : St → Fin k → E
  /-- the terms: a coefficient, the shown factors -/
  t0 : List ((St → E) × List A)
  tb : B → List ((St → E) × List A)
  /-- the public vectors: they do not read the entries -/
  C : Type
  vC : St → C → ℕ → E
  /-- the terms: a coefficient, a public factor; the kept factor is b; no shown factor -/
  tc : B → List ((St → E) × C)
  /-- the degree in the shown values -/
  dy : ℕ
  h0 : ∀ t ∈ t0, t.2.length ≤ 2 ∧ t.2.length ≤ dy
  hb : ∀ b, ∀ t ∈ tb b, t.2.length ≤ 1 ∧ t.2.length ≤ dy
  /-- own masks: the sent sum's; the hiding polynomial's coefficients; one for each end value -/
  rJ : J
  wAt : PIdx (ldPartFmt E k (fun _ => 2) ++ [pDummy E dy]) → J
  cAt : A → J
  /-- what else is claimed of state and entries -/
  Rd : St → (J → E) → Prop

attribute [instance] TokL.finJ TokL.finA TokL.finB

variable {E : Type} [Field E] [Fintype E]

namespace TokL
variable (L : TokL E)

/-- a term of the record as a term of the library's builder -/
def tm (t : (L.St → E) × List L.A) : LdPartTm E L.St L.A L.k := ⟨fun st _ => t.1 st, t.2⟩

/-- a term with a public factor: the factor's extension at the point stands in the coefficient -/
def tmC (t : (L.St → E) × L.C) : LdPartTm E L.St L.A L.k :=
  ⟨fun st z => t.1 st * Blocks.ext L.k (L.vC st t.2) (Blocks.nat z), []⟩

@[reducible] def Sm : LdPartSm E L.St L.J where
  k := L.k
  A := L.A
  F := fun st m a z => Blocks.ext L.k (L.vA st m a) (Blocks.nat z)
  terms := L.t0.map L.tm
  w := fun st j => some (L.pnt st j)

open Classical in
/-- the incoming form: the one mask of the sent sum -/
def inc : Slf E L.St L.J := fun _ j => if j = L.rJ then 1 else 0

@[reducible] def Mk : LdPartMk L.Sm := ⟨fun _ => 2, L.dy, L.inc, L.wAt, L.cAt⟩

@[reducible] def Kp : KeptSm L.Sm where
  B := L.B
  Fb := fun st m b z => Blocks.ext L.k (L.vB st m b) (Blocks.nat z)
  kt := fun b => (L.tb b).map L.tm ++ (L.tc b).map L.tmC

theorem ok : L.Kp.OK L.Mk (fun _ _ => 1) (fun _ _ => 1) where
  base :=
    { map := fun _ _ _ => degLE_ext L.k (Equiv.refl _) _
      fit := fun t ht => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
        refine ⟨fun _ => 0, fun st => Alg.DegLE.const _ _, fun i => ?_⟩
        have := (L.h0 s hs).1
        show 0 + (s.2.map fun _ => 1).sum ≤ 2
        simp
        exact this
      plain := fun _ _ h => by simp at h
      dy := fun t ht => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
        exact (L.h0 s hs).2 }
  mapB := fun _ _ _ => degLE_ext L.k (Equiv.refl _) _
  fitB := fun b t ht => by
    rcases List.mem_append.1 ht with h | h
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
      refine ⟨fun _ => 0, fun st => Alg.DegLE.const _ _, fun i => ?_⟩
      have := (L.hb b s hs).1
      show 0 + (s.2.map fun _ => 1).sum + 1 ≤ 2
      simp
      omega
    · obtain ⟨s, _, rfl⟩ := List.mem_map.1 h
      exact ⟨fun _ => 1,
        fun st => Alg.DegLE.const_mul (s.1 st) (degLE_ext L.k (Equiv.refl _) (L.vC st s.2)),
        fun _ => le_refl 2⟩
  dyB := fun b t ht => by
    rcases List.mem_append.1 ht with h | h
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
      exact (L.hb b s hs).2
    · obtain ⟨s, _, rfl⟩ := List.mem_map.1 h
      exact Nat.zero_le _

/-- The parameters of the general sumcheck. -/
@[reducible] def toSum : SumL E where
  St := L.St
  J := L.J
  S := L.Sm
  M := L.Mk
  Q := L.Kp
  da := fun _ _ => 1
  db := fun _ _ => 1
  ok := L.ok
  Rd := L.Rd

/-- In every round the sum of the constant 1 is 1: the constant coefficient may be left out. -/
theorem eq0 : Eq0 L.toSum.T.par :=
  our_eq0 L.toSum.T fun st => ldPart_eq0 L.k (fun _ => 2) fun j => L.pnt st j

theorem pick_ok : ∀ st, HFixs.OK (L.toSum.T.par.vars st) (F₀ L.toSum.T.par st) :=
  F₀_ok _ L.eq0

section Block
variable {Ex : ExtSpec} {M Wp Kc : Type} (R0 : Rels Kc L.St Ex (M × Wp)) (msg : M → L.J → E)
  (Psi : L.St → E → (L.J → E) → Prop)

/-- The reduction. -/
def blk : IOR L.St Ex ((L.St × E) × L.toSum.T.par.Out) Ex := L.toSum.rblk (F₀ L.toSum.T.par)

/-- The verifier refuses nothing. -/
theorem out_some (x : L.St) (y : Ex.Str) (τ : Tr (shapeR L.toSum.T.par)) :
    ((L.blk (Ex := Ex)).out x y τ).isSome := by
  have h := ride_out L.toSum.T.par (F₀ L.toSum.T.par) (id : L.St → L.St) Ex L.pick_ok x y τ
  show ((rideR L.toSum.T.par (F₀ L.toSum.T.par) (id : L.St → L.St) Ex).out x y τ).isSome
  rw [h]
  rfl

theorem knowAt :
    KnowAt (L.blk (Ex := Ex)) (L.toSum.rrelIn R0 msg Psi) (L.toSum.rrelOut R0 msg Psi)
      (fun _ _ _ wp => wp)
      (L.toSum.reps (Ex := Ex) (F₀ L.toSum.T.par)) :=
  L.toSum.rknowAt R0 msg _ Psi

/-- Knowledge soundness, for each fixed tuple of messages. -/
theorem know (m : M) :
    (L.blk (Ex := Ex)).red.Know (L.toSum.rrelIn R0 msg Psi).on
      (fun a wp => (L.toSum.rrelIn R0 msg Psi).relR a (m, wp))
      (fun b wp => (L.toSum.rrelOut R0 msg Psi).relR b (m, wp)) (fun _ _ wp => wp)
      (L.toSum.reps (Ex := Ex) (F₀ L.toSum.T.par)) :=
  (L.knowAt R0 msg Psi).know m

/-- The errors, round by round. -/
theorem errs : TWhole.errList (L.toSum.reps (Ex := Ex) (F₀ L.toSum.T.par)) =
    1 :: (List.replicate L.k 2 ++ [L.dy, 0]) := by
  rw [L.toSum.rerrs]
  simp [List.ofFn_const]

end Block

/-- the summand at a position -/
def smd (st : L.St) (m : L.J → E) (X : ℕ) : E :=
  (L.t0.map fun t => t.1 st * (t.2.map fun a => L.vA st m a X).prod).sum +
    ∑ b, (((L.tb b).map fun t => t.1 st * (t.2.map fun a => L.vA st m a X).prod).sum +
        ((L.tc b).map fun t => t.1 st * L.vC st t.2 X).sum) * L.vB st m b X

theorem inc_sum (st : L.St) (m : L.J → E) : ∑ j, L.inc st j * m j = m L.rJ := by
  classical
  unfold inc
  simp

/-- What the sum claim says: the extension of the summand at the point, under the one mask. -/
theorem sum_iff (τ : E) (st : L.St) (m : L.J → E) :
    L.toSum.T.SumHolds (τ, st) m ↔
      Blocks.ext L.k (L.smd st m) (Blocks.nat (L.pnt st)) + m L.rJ = τ := by
  rw [L.Kp.sum_iff L.Mk, ext_eq_mle]
  have e : ∀ b : Fin L.k → Bool, L.Kp.val st m (Alg.corner b) = L.smd st m (Alg.num b) := by
    intro b
    unfold KeptSm.val KeptSm.polB LdPartSm.val LdPartSm.pol smd
    simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def, tm, tmC,
      ext_corner, List.map_nil, List.prod_nil, mul_one]
  simp only [e]
  rw [show ∑ j, L.Mk.slS st j * m j = m L.rJ from L.inc_sum st m]
  rfl

/-- The true masked sum. -/
theorem tsum_eq (st : L.St) (m : L.J → E) :
    tsum L.toSum.T.par st m = Blocks.ext L.k (L.smd st m) (Blocks.nat (L.pnt st)) + m L.rJ :=
  ((L.sum_iff _ st m).1
    ((psc_our_sum E L.toSum.T (tsum L.toSum.T.par st m, st) m).1
      (tsum_holds L.toSum.T.par st m))).symm

/-- What the output row on a shown vector's end value says. -/
theorem ev_iff (o : L.toSum.T.par.Out) (m : L.J → E) (a : L.A) :
    L.toSum.T.par.EHolds o m a ↔
      Blocks.ext L.k (L.vA o.st m a) (Blocks.nat (L.Kp.outPt L.Mk o)) +
          m (L.cAt a) * L.Kp.outB L.Mk o =
        o.vals a :=
  L.Kp.val_iff L.Mk o m a

end TokL
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.TokL.out_some
#print axioms Cb.Pv.Lay.TokL.knowAt
#print axioms Cb.Pv.Lay.TokL.errs
#print axioms Cb.Pv.Lay.TokL.sum_iff
#print axioms Cb.Pv.Lay.TokL.ev_iff
