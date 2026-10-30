-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Prod.lean: one product layer of a layers' sub-proof, as an interactive oracle reduction
with its knowledge soundness.

In the layers' sub-proof three sumchecks have this form (the squares of the norms, the gated
products, the gated products of the routed experts). The claim is
    (sum over x of eq(point, x) * vL(x) * vR(x)) + < inc, m > = target,
where vL and vR are two maps on a cube of k variables, computed from the entries m of the committed
messages, inc is a linear form that reads masks of values sent earlier, and the target is public.
The rounds, as the programs have them: the sum of the hiding polynomial, then a coefficient; one
round for each variable, in which two of the three coefficients are sent; one round in a further
variable; the two end values; and a last round with an empty message in which one element is drawn.
In these three sumchecks nothing reads that element.

The variables may be bound in any order: e : Fin k ≃ Fin k, and round j binds coordinate e j of the
point. The point is read off the state, so it may consist of challenges of earlier blocks.

Main names:
  `ProdL`: the parameters. `Rd` is what else is claimed of state and entries: it rides along.
  `ProdL.T`: the sumcheck's record, a value of the library's builder (Cb/Part/LdPartPsc.lean): every
    variable under the equality form, two revealed maps, no other map, degree 2 in the further
    variable.
  `ProdL.conds`: the four conditions of the sumcheck.
  `ProdL.sum_iff`: what the input claim says (`Sg`).
  `ProdL.out_iff`: what the output claims say: one row on names (`Rw1`, the library's `LdPartRw`),
    and for each of the two maps a row on its value at the output point (`EV`). The output point is
    stored by coordinate, not by round.
  `ProdL.blk V`: the reduction, for any short sumcheck V (Cb/G6/Letter.lean).
  `ProdL.knowAt`, `ProdL.know`: its knowledge soundness for each fixed tuple of messages, from "what
    rides, and Sg" to "what rides, the row on names, the two rows on values".
  `ProdL.errs`: its errors, round by round: 1, then 2 for each variable, then 2, 0, 1.
  `ProdL.eq0`: in every round the constant coefficient may be the one that is left out.

Limits: nothing is said on what vL, vR, the point, inc and the target are in the model. Nothing is
said on the honest prover, on completeness or on zero knowledge. V is any short sumcheck in the
sense of Cb/G6/Letter.lean. The sumcheck's own knowledge soundness is that record's field `know`:
`knowAt` takes it from V, pays the three conditions that the field asks by `conds`, and adds the
step from `Sg` to the sumcheck's input claim, the last draw, and the step to the output rows. The
field is no open hypothesis: at all parameters the library has a value of the record, `V₀`
(Cb/G6/Pick.lean), whose `know` is a theorem (`short_knowAt`, Cb/G6/Carried.lean).
That record lays no law on what V's verifier accepts: one that refuses
everything fills it, and the statements here hold of it too. The errors are counts of bad draws in a
round, out of the set that is drawn from: all of E; in the round of the further variable, E without
0. The last round's error is 1, the number that the programs' plan gives it; the proof needs 0. "As
the programs have them" is by reading the programs: nothing here compares the rounds with them (the
planner's lists: OnBytes/Tie/Pv/Lay/Rounds.lean). No file of this folder joins this block's output
claims to another block's input claims.

-/
import Cb.G6.Pick
import Cb.G6.Join
import Cb.Part.LdPartPost
import Cb.Part.LdPartPscProofs
import Cb.Ld.LdPscProofsOur

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole

noncomputable section

section Ext
variable {E : Type} [Field E]

theorem ext_eq_mle (g : ℕ) (v : ℕ → E) (z : Fin g → E) :
    Blocks.ext g v (Blocks.nat z) = Alg.mle (fun b => v (Alg.num b)) z := by
  rw [← Alg.mleN_eq_mle]
  unfold Blocks.ext Alg.mleN
  exact sum_congr rfl fun X _ => by rw [Blocks.eqN_nat]

theorem ext_corner (g : ℕ) (v : ℕ → E) (b : Fin g → Bool) :
    Blocks.ext g v (Blocks.nat (Alg.corner b)) = v (Alg.num b) := by
  rw [ext_eq_mle, Alg.mle_corner]

/-- An extension read through a permutation of the coordinates has degree 1 in each variable. -/
theorem degLE_ext (k : ℕ) (e : Fin k ≃ Fin k) (v : ℕ → E) :
    Alg.DegLE (fun _ : Fin k => 1)
      (fun z : Fin k → E => Blocks.ext k v (Blocks.nat fun i => z (e.symm i))) := by
  simp only [ext_eq_mle]
  have h : (fun z : Fin k → E => Alg.mle (fun b => v (Alg.num b)) fun i => z (e.symm i)) =
      fun z => Alg.mle (fun b : Fin k → Bool => v (Alg.num fun i => b (e.symm i))) z := by
    funext z
    have := Alg.mle_equiv e (fun b => v (Alg.num b)) (fun i => z (e.symm i))
    simp only [Equiv.symm_apply_apply] at this
    exact this.symm
  rw [h]
  exact Alg.DegLE.mle _

end Ext

/-- The parameters of a product layer. -/
structure ProdL (E : Type) [Field E] [Fintype E] where
  /-- the names of the entries -/
  J : Type
  [finJ : Fintype J]
  /-- the number of variables -/
  k : ℕ
  /-- round j binds coordinate e j -/
  e : Fin k ≃ Fin k
  /-- the states before the block -/
  St : Type
  /-- the two maps -/
  vm : St → (J → E) → Bool → ℕ → E
  /-- the point of the equality weights -/
  pnt : St → Fin k → E
  /-- the incoming form and the target -/
  inc : Slf E St J
  tg : St → E
  /-- own masks: the hiding polynomial's coefficients; one entry for each end value -/
  wAt : PIdx (ldPartFmt E k (fun _ => 2) ++ [pDummy E 2]) → J
  cAt : Bool → J
  /-- what else is claimed of state and entries -/
  Rd : St → (J → E) → Prop

attribute [instance] ProdL.finJ

variable {E : Type} [Field E] [Fintype E]

namespace ProdL
variable (L : ProdL E)

/-- the sum of terms: one term, the product of the two maps -/
@[reducible] def Sm : LdPartSm E L.St L.J where
  k := L.k
  A := Bool
  F := fun st m b z => Blocks.ext L.k (L.vm st m b) (Blocks.nat fun i => z (L.e.symm i))
  terms := [⟨fun _ _ => 1, [false, true]⟩]
  w := fun st j => some (L.pnt st (L.e j))

@[reducible] def Mk : LdPartMk L.Sm := ⟨fun _ => 2, 2, L.inc, L.wAt, L.cAt⟩

theorem ok : L.Sm.OK L.Mk (fun _ _ => 1) where
  map := fun _ _ _ => degLE_ext L.k L.e _
  fit := fun t ht => by
    rw [List.mem_singleton.1 ht]
    exact ⟨fun _ => 0, fun st => Alg.DegLE.const _ _, fun _ => by simp⟩
  plain := fun _ _ h => by simp at h
  dy := fun t ht => by
    rw [List.mem_singleton.1 ht]
    simp

/-- The sumcheck's record. -/
abbrev T : PscOur E := L.Sm.our L.Mk

theorem conds : L.T.VarsOK ∧ L.T.ValInj ∧ L.T.DegX ∧ L.T.DegY := ldPartPsc_ok E _ _ _ _ _ L.ok

/-- The input claim. -/
def Sg (st : L.St) (m : L.J → E) : Prop :=
  Blocks.ext L.k (fun X => L.vm st m false X * L.vm st m true X) (Blocks.nat (L.pnt st)) +
    ∑ j, L.inc st j * m j = L.tg st

theorem sum_iff (t : E) (st : L.St) (m : L.J → E) :
    L.T.SumHolds (t, st) m ↔
      Blocks.ext L.k (fun X => L.vm st m false X * L.vm st m true X) (Blocks.nat (L.pnt st)) +
        ∑ j, L.inc st j * m j = t := by
  rw [ldPartPsc_sum E, ext_eq_mle,
    ← Alg.mle_equiv L.e (fun b => L.vm st m false (Alg.num b) * L.vm st m true
        (Alg.num b)) (L.pnt st)]
  have hc : ∀ b : Fin L.k → Bool, L.Sm.val st m (Alg.corner b) =
      L.vm st m false (Alg.num fun i => b (L.e.symm i)) * L.vm st m true (Alg.num fun i => b
          (L.e.symm i)) := by
    intro b
    unfold LdPartSm.val LdPartSm.pol
    have hb : (fun i => (Alg.corner b : Fin L.k → E) (L.e.symm i)) = Alg.corner fun i => b
        (L.e.symm i) := rfl
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons,
      List.prod_nil, mul_one, one_mul, add_zero, hb, ext_corner]
  simp only [hc]
  rfl

/-- the output point, stored by coordinate; the last challenge -/
abbrev oPt (o : L.T.par.Out) : Fin L.k → E := fun i => L.Sm.outPt L.Mk o (L.e.symm i)
abbrev oBe (o : L.T.par.Out) : E := L.Sm.outB L.Mk o

/-- the one row on names -/
@[reducible] def Rw1 : LdPartRw E L.T.par.Out L.J where
  Jr := Unit
  co := fun o _ n => L.T.par.slU (fun _ b => b.elim) o n
  tg := fun o _ => L.T.par.tU o

/-- the row on an end value -/
def EV (o : L.T.par.Out) (m : L.J → E) (b : Bool) : Prop :=
  Blocks.ext L.k (L.vm o.st m b) (Blocks.nat (L.oPt o)) + m (L.cAt b) * L.oBe o = o.vals b

theorem ev_iff (o : L.T.par.Out) (m : L.J → E) (b : Bool) : L.T.par.EHolds o m b ↔ L.EV o m b :=
  ldPartPsc_val E _ _ L.Sm L.Mk o m b

theorem row_iff (o : L.T.par.Out) (m : L.J → E) : L.T.par.UHolds o m ↔ L.Rw1.Says o m := by
  rw [psc_row_U E L.T.par (fun _ b => b.elim) (fun _ _ b => b.elim) o m]
  exact ⟨fun h _ => h, fun h => h ()⟩

theorem out_iff (o : L.T.par.Out) (m : L.J → E) :
    L.T.par.OutHolds o m ↔ L.Rw1.Says o m ∧ ∀ b, L.EV o m b :=
  and_congr (L.row_iff o m) (forall_congr' fun b => L.ev_iff o m b)

/-- In every round the sum of the constant 1 is 1: the constant coefficient may be left out. -/
theorem eq0 : Eq0 L.T.par :=
  our_eq0 L.T fun st => ldPart_eq0 L.k (fun _ => 2) fun j => L.pnt st (L.e j)

/-! ### The reduction -/

section Block
variable {Ex : ExtSpec} {M Wp Kc : Type} (R0 : Rels Kc L.St Ex (M × Wp)) (msg : M → L.J → E)

/-- what rides: the base, and what else is claimed -/
@[reducible] def A0 : Rels Kc L.St Ex (M × Wp) :=
  ⟨fun st y w => R0.rel st y w ∧ L.Rd st (msg w.1), fun a w => R0.relR a w ∧ L.Rd a.1 (msg w.1),
    R0.on, R0.core⟩

/-- the joint before the block -/
@[reducible] def relIn : Rels Kc L.St Ex (M × Wp) :=
  ⟨fun st y w => (L.A0 R0 msg).rel st y w ∧ L.Sg st (msg w.1),
    fun a w => (L.A0 R0 msg).relR a w ∧ L.Sg a.1 (msg w.1), R0.on, R0.core⟩

/-- the joint behind the block -/
@[reducible] def relOut : Rels Kc L.T.par.Out Ex (M × Wp) :=
  ⟨fun o y w => (L.A0 R0 msg).rel o.st y w ∧ L.Rw1.Says o (msg w.1) ∧ ∀ b, L.EV o (msg w.1) b,
    fun a w => (L.A0 R0 msg).relR (a.1.st, a.2) w ∧ L.Rw1.Says a.1 (msg w.1)
        ∧ ∀ b, L.EV a.1 (msg w.1) b,
    fun a => R0.on (a.1.st, a.2), R0.core⟩

variable (V : ShortK L.T.par Ex)

/-- The reduction: the target is read off the state; the short sumcheck; the last draw. -/
def blk : IOR L.St Ex L.T.par.Out Ex :=
  (V.R.pre (fun st => some (L.tg st, st)) (ExtMap.id Ex)).seq
    (IOR.draw E (fun (o : L.T.par.Out) (_ : E) => o) Ex)

/-- its errors -/
def eps : Err (L.blk V).shape :=
  Err.app (s := V.R.shape) V.ε (Nums.draw Kc E (fun (o : L.T.par.Out) (_ : E) => o) Ex 1).err

theorem knowAt :
    KnowAt (L.blk V) (L.relIn R0 msg) (L.relOut R0 msg) (fun _ _ _ wp => wp) (L.eps
        (Kc := Kc) V) := by
  obtain ⟨hV, hI, hX, hY⟩ := L.conds
  have h1 := V.know ((psc_our_ok E L.T).1 hV) (psc_our_deg E L.T hX hY) ((psc_our_ok E L.T).2 hI)
    M Wp Kc (L.A0 R0 msg) msg
  have h2 : KnowAt (V.R.pre (fun st => some (L.tg st, st)) (ExtMap.id Ex)) (L.relIn R0 msg)
      (L.T.par.baseOut (L.A0 R0 msg) fun w => msg w.1) (fun _ _ _ wp => wp) V.ε :=
    knowAt_preMap (A' := L.relIn R0 msg) (A := L.T.par.baseIn (L.A0 R0 msg) fun w => msg w.1)
      (fun st => (L.tg st, st)) (fun _ _ h => h)
      (fun st _ w _ h => ⟨h.1, (L.sum_iff (L.tg st) st _).1 ((psc_our_sum E L.T _ _).1 h.2)⟩) h1
  have h3 : KnowAt (IOR.draw E (fun (o : L.T.par.Out) (_ : E) => o) Ex)
      (L.T.par.baseOut (L.A0 R0 msg) fun w => msg w.1) (L.relOut R0 msg) (fun _ _ _ wp => wp)
      (Nums.draw Kc E (fun (o : L.T.par.Out) (_ : E) => o) Ex 1).err :=
    knowAt_draw _ _ _ 1 (fun _ _ _ h => h) fun o y m _ =>
      le_trans (le_of_eq (cnt_false fun _ h => by
        obtain ⟨wp, h1, h2⟩ := h
        exact h2 ⟨h1.1, (L.out_iff o _).2 h1.2⟩)) (Nat.zero_le _)
  exact knowAt_seq h2 h3

/-- Knowledge soundness, for each fixed tuple of messages. -/
theorem know (m : M) :
    (L.blk V).red.Know (L.relIn R0 msg).on (fun a wp => (L.relIn R0 msg).relR a (m, wp))
      (fun b wp => (L.relOut R0 msg).relR b (m, wp)) (fun _ _ wp => wp) (L.eps (Kc := Kc) V) :=
  (L.knowAt R0 msg V).know m

/-- The errors, round by round. -/
theorem errs : TWhole.errList (L.eps (Kc := Kc) V) = 1 :: (List.replicate L.k 2 ++ [2, 0, 1]) := by
  refine (errList_app V.ε (Nums.draw Kc E (fun (o : L.T.par.Out) (_ : E) => o) Ex 1).err).trans ?_
  rw [V.nums, errList_draw]
  have h : L.T.par.fmt.map PFmt.n = List.replicate L.k 2 ++ [2] := by
    show ((ldPartFmt E L.k fun _ => 2) ++ [pDummy E 2]).map PFmt.n = _
    rw [List.map_append, ldPartVars_degs E]
    simp [List.ofFn_const]
    rfl
  rw [h]
  simp

end Block

end ProdL
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.ProdL.conds
#print axioms Cb.Pv.Lay.ProdL.sum_iff
#print axioms Cb.Pv.Lay.ProdL.out_iff
#print axioms Cb.Pv.Lay.ProdL.knowAt
#print axioms Cb.Pv.Lay.ProdL.errs
#print axioms Cb.Pv.Lay.ProdL.eq0
