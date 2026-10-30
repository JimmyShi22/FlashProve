-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Inner.lean: the batched sumcheck of a layers' sub-proof's inner products, as an
interactive oracle reduction with its knowledge soundness.

All inner products of the sub-proof (activations against weights, and the like) are laid side by
side on one cube and summed. The claim is
    (sum over the corners x of the cube of the summand at x) + < inc, m > = target.
The summand is a sum of terms: a coefficient, which is a function of the state and of the point,
times at most two values of maps that are revealed at the last point. The record also allows terms
with one further factor that is KEPT: its value at the last point is never sent and stands in the
first output row. inc reads masks of values that earlier blocks have sent; the target is public.
The rounds, as the programs have them: the sum of the hiding polynomial, then a coefficient; one
round for each variable, under the plain sum g(0) + g(1), in which the constant and the quadratic
coefficient are sent and the LINEAR one is left out; one round in a further variable, with two
scalars; the end values.

Main names:
  `InnL`: the parameters: the maps as functions of the point with their degrees (`hF`, `hFb`), the
    terms, and the conditions `h0`, `hb`: the degrees add up to at most 2 in each variable and to
    at most 2 in the revealed values.
  `InnL.toSum`: the parameters of Cb/Pv/Lay/Sum.lean: every variable under the plain form.
  `InnL.blk V`, `InnL.knowAt`, `InnL.know`: the reduction for any short sumcheck V, and its
    knowledge soundness for each fixed tuple of messages: from "what rides, and the sum claim" to
    "what rides, and the sumcheck's output claims".
  `InnL.errs`: its errors: 1, then 2 for each variable, then 2, 0.
  `InnL.sum_iff`: what the input claim says. `InnL.ev_iff`: what the output row on a revealed
    map's end value says.

Limits: nothing is said on what the maps, the coefficients, inc and the target are in the model.
`hF`, `hFb`, `h0`, `hb` are fields of the record: a user pays them. In the programs the claimed
sum of this sumcheck names entries of an array that is committed to only behind it; how that is
laid in this record is not shown here. No value of `InnL` is built here. Of the first output row
nothing is said but that it is the library's. Which coefficient a short sumcheck V leaves out is
V's own, and V may be one whose verifier refuses everything; for the linear coefficient see
Cb/Pv/Lay/Merge.lean. The errors are numbers of bad draws, round by round. Every draw is from the
whole field, but the further variable's, which is from the elements other than 0. "For each fixed
tuple of messages" asks of a user that every entry that the maps, forms and claims of the record
read is fixed before the block's first draw. Nothing is said on the honest prover, on completeness
or on zero knowledge. The sentences on what the programs do are by reading: nothing is compared
with the programs here. This reduction is not joined to the one before it or behind it in the
sub-proof: that the two joints agree is not shown in this folder.

-/
import Cb.Pv.Lay.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole

noncomputable section

/-- The parameters of the batched sumcheck of the inner products. -/
structure InnL (E : Type) [Field E] [Fintype E] where
  J : Type
  [finJ : Fintype J]
  /-- the number of variables -/
  k : ℕ
  St : Type
  /-- the revealed maps and the kept ones, with their degrees -/
  A : Type
  [finA : Fintype A]
  B : Type
  [finB : Fintype B]
  F : St → (J → E) → A → (Fin k → E) → E
  Fb : St → (J → E) → B → (Fin k → E) → E
  da : A → Fin k → ℕ
  db : B → Fin k → ℕ
  hF : ∀ st m a, Alg.DegLE (da a) (F st m a)
  hFb : ∀ st m b, Alg.DegLE (db b) (Fb st m b)
  /-- the terms -/
  t0 : List (LdPartTm E St A k)
  tb : B → List (LdPartTm E St A k)
  h0 : ∀ t ∈ t0, (∃ dc : Fin k → ℕ, (∀ st, Alg.DegLE dc (t.coef st)) ∧
    ∀ i, dc i + (t.atoms.map fun a => da a i).sum ≤ 2) ∧ t.atoms.length ≤ 2
  hb : ∀ b, ∀ t ∈ tb b, (∃ dc : Fin k → ℕ, (∀ st, Alg.DegLE dc (t.coef st)) ∧
    ∀ i, dc i + (t.atoms.map fun a => da a i).sum + db b i ≤ 2) ∧ t.atoms.length ≤ 2
  /-- the incoming form and the target -/
  inc : Slf E St J
  tg : St → E
  /-- own masks -/
  wAt : PIdx (ldPartFmt E k (fun _ => 2) ++ [pDummy E 2]) → J
  cAt : A → J
  /-- what else is claimed of state and entries -/
  Rd : St → (J → E) → Prop

attribute [instance] InnL.finJ InnL.finA InnL.finB

variable {E : Type} [Field E] [Fintype E]

namespace InnL
variable (L : InnL E)

@[reducible] def Sm : LdPartSm E L.St L.J where
  k := L.k
  A := L.A
  F := L.F
  terms := L.t0
  w := fun _ _ => none

@[reducible] def Mk : LdPartMk L.Sm := ⟨fun _ => 2, 2, L.inc, L.wAt, L.cAt⟩

@[reducible] def Kp : KeptSm L.Sm where
  B := L.B
  Fb := L.Fb
  kt := L.tb

theorem ok : L.Kp.OK L.Mk L.da L.db where
  base :=
    { map := L.hF
      fit := fun t ht => (L.h0 t ht).1
      plain := fun _ _ _ => by norm_num
      dy := fun t ht => (L.h0 t ht).2 }
  mapB := L.hFb
  fitB := fun b t ht => (L.hb b t ht).1
  dyB := fun b t ht => (L.hb b t ht).2

/-- The parameters of the general sumcheck. -/
@[reducible] def toSum : SumL E where
  St := L.St
  J := L.J
  S := L.Sm
  M := L.Mk
  Q := L.Kp
  da := L.da
  db := L.db
  ok := L.ok
  Rd := L.Rd

section Block
variable {Ex : ExtSpec} {M Wp Kc : Type} (R0 : Rels Kc L.St Ex (M × Wp)) (msg : M → L.J → E)
  (V : ShortK L.toSum.T.par Ex)

/-- The reduction. -/
def blk : IOR L.St Ex L.toSum.T.par.Out Ex := L.toSum.blk L.tg V

theorem knowAt :
    KnowAt (L.blk V) (L.toSum.relIn R0 msg L.tg) (L.toSum.relOut R0 msg) (fun _ _ _ wp => wp)
      V.ε :=
  L.toSum.knowAt R0 msg L.tg V

/-- Knowledge soundness, for each fixed tuple of messages. -/
theorem know (m : M) :
    (L.blk V).red.Know (L.toSum.relIn R0 msg L.tg).on
      (fun a wp => (L.toSum.relIn R0 msg L.tg).relR a (m, wp))
      (fun b wp => (L.toSum.relOut R0 msg).relR b (m, wp)) (fun _ _ wp => wp) V.ε :=
  (L.knowAt R0 msg V).know m

/-- The errors, round by round. -/
theorem errs : TWhole.errList V.ε = 1 :: (List.replicate L.k 2 ++ [2, 0]) := by
  rw [L.toSum.errs V]
  simp [List.ofFn_const]

end Block

/-- What the input claim says. -/
theorem sum_iff (st : L.St) (m : L.J → E) :
    L.toSum.T.SumHolds (L.tg st, st) m ↔
      ∑ b : Fin L.k → Bool, L.Kp.val st m (Alg.corner b) + ∑ j, L.inc st j * m j =
        L.tg st := by
  rw [L.Kp.sum_iff L.Mk]
  simp [ldPartWt]

/-- What the output row on a revealed map's end value says. -/
theorem ev_iff (o : L.toSum.T.par.Out) (m : L.J → E) (a : L.A) :
    L.toSum.T.par.EHolds o m a ↔
      L.F o.st m a (L.Kp.outPt L.Mk o) + m (L.cAt a) * L.Kp.outB L.Mk o = o.vals a :=
  L.Kp.val_iff L.Mk o m a

end InnL
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.InnL.knowAt
#print axioms Cb.Pv.Lay.InnL.errs
#print axioms Cb.Pv.Lay.InnL.sum_iff
#print axioms Cb.Pv.Lay.InnL.ev_iff
