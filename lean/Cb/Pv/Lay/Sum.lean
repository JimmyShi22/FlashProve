-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Sum.lean: a masked sumcheck over a sum of terms, with or without kept maps, with or
without a claimed sum that is sent, as an interactive oracle reduction with its knowledge
soundness.

Three forms of sumchecks of the layers' sub-proof are mapped into this file's record: the products
of the norms' rows and the terms (Cb/Pv/Lay/Tok.lean: the claimed sum is hidden and is sent in the
first message, before the sum of the hiding polynomial), and the batched inner products
(Cb/Pv/Lay/Inner.lean: the claimed sum is a form in earlier masks with a public target; nothing
but the sum of the hiding polynomial is sent first).

The rounds, as the programs have them: the first message, then a coefficient is drawn; one round
for each variable, in which one coefficient of the round polynomial is left out; one round in a
further variable; the end values of the revealed maps.

Main names:
  `SumL`: the parameters: the library's sum of terms S with what the sumcheck adds (M), the kept
    maps Q (Cb/Pv/Lay/Kept.lean), their conditions `ok`, and `Rd`: what else is claimed of state
    and entries.
  `SumL.T`: the sumcheck's record. `SumL.conds`: its four conditions.
  `SumL.blk V`, `SumL.knowAt`, `SumL.know`, `SumL.errs`: the reduction without a sent sum, for any
    short sumcheck V (Cb/G6/Letter.lean): from "what rides, and the sum claim at the target read
    off the state" to "what rides, and the output claims".
  `SumL.rblk F`, `SumL.rknowAt`, `SumL.rknow`, `SumL.rerrs`: the reduction with a sent sum z, for
    picks F of the coefficients that are left out: from "what rides, and Psi at the true masked
    sum" to "what rides, Psi at z, and the output claims". Psi is any claim on the state, the sent
    scalar and the entries.
  The errors are in both cases 1, the degrees of the variables, the degree in the further
    variable, 0.

Limits: nothing is said on what the maps, the forms and the targets are in the model. `ok` is a
field of the record: a user pays it. A short sumcheck V may be one whose verifier refuses
everything; knowledge soundness holds of it and then says nothing. The output claims are the
library's own (`PscPar.OutHolds`): the first row bears the kept maps' values at the last point.
The errors are numbers of bad draws, round by round. Every draw is from the whole field, but the
further variable's, which is from the elements other than 0. "For each fixed tuple of messages"
asks of a user that every entry that the maps, forms and claims of the record read is fixed before
the block's first draw. Nothing is said on the honest prover, on completeness or on zero
knowledge. The sentences on what the programs do are by reading: nothing is compared with the
programs here. This reduction is not joined to the one before it or behind it in the sub-proof:
that the two joints agree is not shown in this folder.

-/
import Cb.Pv.Lay.Kept
import Cb.G6.Pick
import Cb.G6.Join
import Cb.Pv.Lay.Ride

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Johnson.L5.Door

noncomputable section

/-- The parameters. -/
structure SumL (E : Type) [Field E] [Fintype E] where
  St : Type
  J : Type
  [finJ : Fintype J]
  S : LdPartSm E St J
  M : LdPartMk S
  Q : KeptSm S
  da : S.A → Fin S.k → ℕ
  db : Q.B → Fin S.k → ℕ
  ok : Q.OK M da db
  /-- what else is claimed of state and entries -/
  Rd : St → (J → E) → Prop

attribute [instance] SumL.finJ

variable {E : Type} [Field E] [Fintype E]

namespace SumL
variable (L : SumL E)

/-- The sumcheck's record. -/
abbrev T : PscOur E := L.Q.our L.M

theorem conds : L.T.VarsOK ∧ L.T.ValInj ∧ L.T.DegX ∧ L.T.DegY := L.Q.conds L.M L.da L.db L.ok

theorem degs : L.T.par.fmt.map PFmt.n = List.ofFn L.M.n ++ [L.M.DY] := L.Q.degs L.M

section Block
variable {Ex : ExtSpec} {M Wp Kc : Type} (R0 : Rels Kc L.St Ex (M × Wp)) (msg : M → L.J → E)

/-- what rides: the base, and what else is claimed -/
@[reducible] def A0 : Rels Kc L.St Ex (M × Wp) :=
  ⟨fun st y w => R0.rel st y w ∧ L.Rd st (msg w.1),
    fun a w => R0.relR a w ∧ L.Rd a.1 (msg w.1),
    R0.on, R0.core⟩

/-! ### Without a sent sum -/

variable (tg : L.St → E)

/-- the joint before the block: what rides, and the sum claim at the target -/
@[reducible] def relIn : Rels Kc L.St Ex (M × Wp) :=
  ⟨fun st y w => (L.A0 R0 msg).rel st y w ∧ L.T.SumHolds (tg st, st) (msg w.1),
    fun a w => (L.A0 R0 msg).relR a w ∧ L.T.SumHolds (tg a.1, a.1) (msg w.1), R0.on, R0.core⟩

/-- the joint behind the block: what rides, and the output claims -/
@[reducible] def relOut : Rels Kc L.T.par.Out Ex (M × Wp) :=
  L.T.par.baseOut (L.A0 R0 msg) fun w => msg w.1

variable (V : ShortK L.T.par Ex)

/-- The reduction: the target is read off the state; the short sumcheck. -/
def blk : IOR L.St Ex L.T.par.Out Ex := V.R.pre (fun st => some (tg st, st)) (ExtMap.id Ex)

theorem knowAt :
    KnowAt (L.blk tg V) (L.relIn R0 msg tg) (L.relOut R0 msg) (fun _ _ _ wp => wp) V.ε := by
  obtain ⟨hV, hI, hX, hY⟩ := L.conds
  have h1 := V.know ((psc_our_ok E L.T).1 hV) (psc_our_deg E L.T hX hY) ((psc_our_ok E L.T).2 hI)
    M Wp Kc (L.A0 R0 msg) msg
  have h2 : KnowAt (V.R.pre (fun st => some (tg st, st)) (ExtMap.id Ex)) (L.relIn R0 msg tg)
      (L.T.par.baseOut (L.A0 R0 msg) fun w => msg w.1) (fun _ _ _ wp => wp) V.ε :=
    knowAt_preMap (A' := L.relIn R0 msg tg) (A := L.T.par.baseIn (L.A0 R0 msg) fun w => msg w.1)
      (fun st => (tg st, st)) (fun _ _ h => h)
      (fun st _ w _ h => ⟨h.1, (psc_our_sum E L.T _ _).1 h.2⟩) h1
  exact h2

/-- Knowledge soundness, for each fixed tuple of messages. -/
theorem know (m : M) :
    (L.blk tg V).red.Know (L.relIn R0 msg tg).on (fun a wp => (L.relIn R0 msg tg).relR a (m, wp))
      (fun b wp => (L.relOut R0 msg).relR b (m, wp)) (fun _ _ wp => wp) V.ε :=
  (L.knowAt R0 msg tg V).know m

/-- The errors, round by round. -/
theorem errs : TWhole.errList V.ε = 1 :: (List.ofFn L.M.n ++ [L.M.DY, 0]) := by
  rw [V.nums, L.degs]
  simp

/-! ### With a sent sum -/

variable (F : ∀ st, HFixs (L.T.par.vars st)) (Psi : L.St → E → (L.J → E) → Prop)

/-- the joint before: what rides, and Psi at the true masked sum -/
@[reducible] def rrelIn : Rels Kc L.St Ex (M × Wp) :=
  rideIn L.T.par (id : L.St → L.St) Ex (fun w : M × Wp => msg w.1) (L.A0 R0 msg) Psi

/-- the joint behind: what rides, Psi at the sent scalar, and the output claims -/
@[reducible] def rrelOut : Rels Kc ((L.St × E) × L.T.par.Out) Ex (M × Wp) :=
  rideOut L.T.par (id : L.St → L.St) Ex (fun w : M × Wp => msg w.1) (L.A0 R0 msg) Psi

/-- The reduction: the claimed sum is sent first. -/
def rblk : IOR L.St Ex ((L.St × E) × L.T.par.Out) Ex := rideR L.T.par F id Ex

/-- its errors -/
def reps : Err (L.rblk (Ex := Ex) F).shape := rideE L.T.par F (id : L.St → L.St) Ex

theorem rknowAt :
    KnowAt (L.rblk F) (L.rrelIn R0 msg Psi) (L.rrelOut R0 msg Psi) (fun _ _ _ wp => wp)
      (L.reps (Ex := Ex) F) := by
  obtain ⟨hV, hI, hX, hY⟩ := L.conds
  exact ride_knowAt L.T.par F id Ex M Wp Kc (L.A0 R0 msg) msg Psi
    ((psc_our_ok E L.T).1 hV) (psc_our_deg E L.T hX hY) ((psc_our_ok E L.T).2 hI)

theorem rknow (m : M) :
    (L.rblk F).red.Know (L.rrelIn R0 msg Psi).on (fun a wp => (L.rrelIn R0 msg Psi).relR a (m, wp))
      (fun b wp => (L.rrelOut R0 msg Psi).relR b (m, wp)) (fun _ _ wp => wp)
      (L.reps (Ex := Ex) F) :=
  (L.rknowAt R0 msg F Psi).know m

/-- The errors, round by round. -/
theorem rerrs :
    TWhole.errList (L.reps (Ex := Ex) F) = 1 :: (List.ofFn L.M.n ++ [L.M.DY, 0]) := by
  have h : TWhole.errList (L.reps (Ex := Ex) F) = 1 :: (L.T.par.fmt.map PFmt.n ++ [0]) :=
    rideE_list L.T.par F id Ex
  rw [h, L.degs]
  simp

end Block

end SumL
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.SumL.knowAt
#print axioms Cb.Pv.Lay.SumL.errs
#print axioms Cb.Pv.Lay.SumL.rknowAt
#print axioms Cb.Pv.Lay.SumL.rerrs
