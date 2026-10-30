-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Stack.lean: several open claims are combined under the powers of one drawn element, and
the combination is proved by the batched sumcheck of the inner products. One interactive oracle
reduction with its knowledge soundness.

In the layers' sub-proof two claims are open before the batched sumcheck: the lookup's join, with
the hidden sum of the terms in the terms' place, and "the kept part of the sumcheck of the terms
is what its first row, divided by its coefficient, says" (Cb/Pv/Lay/Over.lean). Both are written
as "an expression in state and entries is 0". One element is drawn; nothing is sent. The
combination under its powers, from the power 0 on, is the claimed sum of the batched sumcheck
(Cb/Pv/Lay/Inner.lean).

Main names:
  `StackL`: the parameters: nc expressions `val`; the batched sumcheck's parameters `inn`; `nx`:
    its state, made of the old state and the element; `link`: its sum claim says that the
    combination is 0.
  `StackL.blk V`, `StackL.knowAt`, `StackL.know`: the reduction for any short sumcheck V, and its
    knowledge soundness for each fixed tuple of messages: from "what rides, and every expression
    is 0" to "what rides, and the sumcheck's output claims".
  `StackL.errs`: its errors: nc - 1, 1, then 2 for each variable, then 2, 0.

Limits: `link`, `back` and `hRd` are fields of the record, and so are the conditions of `inn`: a
user pays them. `link` is asked at every state, element and tuple of entries, without a condition.
That the programs' start form, summand and target meet it is not shown here; in the programs that
start form names entries of an array that is committed to only behind the sumcheck: that weight lies
wholly on `link`. No value of `StackL` is built anywhere in this library: outside this file the
record is named only as a letter, (L : StackL E), of a statement, and in one such statement's name
(StackL.shape_eq) (Cb/Pv/Lay/ShapesTok.lean [not in this library], OnBytes/Tie/Pv/Lay/Errs.lean,
OnBytes/Tie/Pv/Lay/RoundsTok.lean [not in this library]). So `knowAt`, `know`
and `errs` speak of a class of which no member is shown, neither at the programs' forms nor at a
small example. V may be a short sumcheck whose verifier refuses everything. The errors are numbers
of bad draws, round by round. Every draw is
from the whole field, but the further variable's, which is from the elements other than 0. "For
each fixed tuple of messages" asks of a user that every entry that the maps, forms and claims of
the record read is fixed before the block's first draw. Nothing is said on the honest prover, on
completeness or on zero knowledge. The sentences on what the programs do are by reading: nothing
is compared with the programs here. This reduction is not joined to the one before it or behind it
in the sub-proof: that the two joints agree is not shown in this folder.

-/
import Cb.Pv.Lay.Inner
import Cb.G6.Johnson.Layers.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers

noncomputable section

/-- The parameters. -/
structure StackL (E : Type) [Field E] [Fintype E] where
  /-- the batched sumcheck -/
  inn : InnL E
  /-- the states before the draw; the new state, and the old one read off it -/
  St : Type
  nx : St → E → inn.St
  old : inn.St → St
  back : ∀ st β, old (nx st β) = st
  /-- the number of claims; the expressions that are claimed to be 0 -/
  nc : ℕ
  val : St → (inn.J → E) → Fin nc → E
  link : ∀ st β m, inn.toSum.T.SumHolds (inn.tg (nx st β), nx st β) m ↔
    ∑ i : Fin nc, β ^ (i : ℕ) * val st m i = 0
  /-- what else is claimed of state and entries -/
  Rd : St → (inn.J → E) → Prop
  hRd : ∀ x m, inn.Rd x m ↔ Rd (old x) m

variable {E : Type} [Field E] [Fintype E]

namespace StackL
variable (L : StackL E)

section Block
variable {Ex : ExtSpec} {M Wp Kc : Type} (R0 : Rels Kc L.St Ex (M × Wp)) (msg : M → L.inn.J → E)

/-- the joint before: what rides, and every expression is 0 -/
@[reducible] def relIn : Rels Kc L.St Ex (M × Wp) :=
  ⟨fun st y w => (R0.rel st y w ∧ L.Rd st (msg w.1)) ∧ ∀ i, L.val st (msg w.1) i = 0,
    fun a w => (R0.relR a w ∧ L.Rd a.1 (msg w.1)) ∧ ∀ i, L.val a.1 (msg w.1) i = 0,
    R0.on, R0.core⟩

/-- the base, read at the old state -/
@[reducible] def R1 : Rels Kc L.inn.St Ex (M × Wp) :=
  ⟨fun x y w => R0.rel (L.old x) y w, fun a w => R0.relR (L.old a.1, a.2) w,
    fun a => R0.on (L.old a.1, a.2), R0.core⟩

/-- the joint behind -/
@[reducible] def relOut : Rels Kc L.inn.toSum.T.par.Out Ex (M × Wp) :=
  L.inn.toSum.relOut (L.R1 R0) msg

variable (V : ShortK L.inn.toSum.T.par Ex)

/-- The reduction: the draw; the batched sumcheck. -/
def blk : IOR L.St Ex L.inn.toSum.T.par.Out Ex := (IOR.draw E L.nx Ex).seq (L.inn.blk V)

/-- its errors -/
def eps : Err (L.blk V).shape :=
  Err.app (s := (IOR.draw E L.nx Ex).shape) (Nums.draw Kc E L.nx Ex (L.nc - 1)).err V.ε

theorem knowAt :
    KnowAt (L.blk V) (L.relIn R0 msg) (L.relOut R0 msg) (fun _ _ _ wp => wp)
      (L.eps (Kc := Kc) V) := by
  have h1 : KnowAt (IOR.draw E L.nx Ex) (L.relIn R0 msg)
      (L.inn.toSum.relIn (L.R1 R0) msg L.inn.tg) (fun _ _ _ wp => wp)
      (Nums.draw Kc E L.nx Ex (L.nc - 1)).err :=
    knowAt_draw _ _ _ (L.nc - 1)
      (fun st y β h => by
        show R0.on (L.old (L.nx st β), y)
        rw [L.back]
        exact h)
      fun st y m _ => by
        refine le_trans (cnt_mono fun β h => ?_) (cnt_badPow fun i => L.val st (msg m) i)
        obtain ⟨wp, ⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
        have g1 : R0.relR (st, y) (m, wp) := by
          have : R0.relR (L.old (L.nx st β), y) (m, wp) := h1
          rwa [L.back] at this
        have g2 : L.Rd st (msg m) := by
          have := (L.hRd (L.nx st β) (msg m)).1 h2
          rwa [L.back] at this
        exact ⟨fun h0 => h4 ⟨⟨g1, g2⟩, fun i => congrFun h0 i⟩, (L.link st β (msg m)).1 h3⟩
  exact knowAt_seq h1 (L.inn.knowAt (L.R1 R0) msg V)

/-- Knowledge soundness, for each fixed tuple of messages. -/
theorem know (m : M) :
    (L.blk V).red.Know (L.relIn R0 msg).on (fun a wp => (L.relIn R0 msg).relR a (m, wp))
      (fun b wp => (L.relOut R0 msg).relR b (m, wp)) (fun _ _ wp => wp) (L.eps (Kc := Kc) V) :=
  (L.knowAt R0 msg V).know m

/-- The errors, round by round. -/
theorem errs : TWhole.errList (L.eps (Kc := Kc) V) =
    (L.nc - 1) :: 1 :: (List.replicate L.inn.k 2 ++ [2, 0]) := by
  refine (errList_app _ _).trans ?_
  exact congrArg (fun l => (L.nc - 1) :: l) (L.inn.errs V)

end Block

end StackL
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.StackL.knowAt
#print axioms Cb.Pv.Lay.StackL.errs
