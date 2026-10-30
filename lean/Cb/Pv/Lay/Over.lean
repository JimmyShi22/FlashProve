-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Over.lean: the first output row of a sumcheck with kept maps, solved for the kept part.

In the layers' sub-proof the sumcheck of the terms keeps maps. Its first output row reads
    U + eps * psi * < inc, m > + eps * (the kept part at the last point) = fin - eps * S0,
where U is the hiding polynomial at the last point, a form in the block's own masks. The programs
do not add this row to the claims. They divide it by eps and put the result, a form in masks with
a public part, in the place of the kept part in the claimed sum of the NEXT sumcheck. For that eps
must not be 0: the programs refuse a proof in which the drawn eps is 0, although eps is drawn from
the whole field.

Main names:
  `keptAt Y o m`: the kept part at the last point.
  `overAt Y o m`: the row's other members, divided by eps.
  `over_iff`: where eps is not 0 the first output row says that the two are equal.
  `TokL.oblk`: the sumcheck over the token positions (Cb/Pv/Lay/Tok.lean), followed by the refusal
    of eps = 0.
  `TokL.orel`: the joint behind it. Its condition is the old one and "eps is not 0"; its claims
    are: what rides, Psi at the sent scalar, "the kept part is overAt", and the rows on the end
    values.
  `TokL.oknowAt`, `TokL.oknow`: knowledge soundness for each fixed tuple of messages, with the
    same errors as without the refusal: to refuse more costs soundness nothing.

Limits: an honest prover is refused where eps = 0 is drawn, one draw of as many as the field has
elements: nothing is said here on completeness. Nothing is said on zero knowledge. The sentences
on what the programs do are by reading: nothing is compared with the programs here. This reduction
is not joined to the one before it or behind it in the sub-proof: that the two joints agree is not
shown in this folder.

-/
import Cb.Pv.Lay.Tok

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Johnson.L5.Door

noncomputable section

section Row
variable {E : Type} [Field E] (Y : PscPar E)

/-- the kept part at the last point -/
def keptAt (o : Y.Out) (m : Y.J → E) : E :=
  ∑ b, Y.S1 o.st (Y.hp o.st o.pt) o.vals b * Y.Gb o.st m b (Y.hp o.st o.pt)

/-- the row's other members, divided by eps -/
def overAt (o : Y.Out) (m : Y.J → E) : E :=
  (o.fin - hU (Y.vars o.st) (Y.W o.st m) (Y.hp o.st o.pt)) / o.eps -
    Y.S0 o.st (Y.hp o.st o.pt) o.vals - hPsi (Y.vars o.st) (Y.hp o.st o.pt) * Y.inc o.st m

theorem over_iff (o : Y.Out) (m : Y.J → E) (h : o.eps ≠ 0) :
    Y.UHolds o m ↔ keptAt Y o m = overAt Y o m := by
  unfold PscPar.UHolds keptAt overAt
  constructor
  · intro e
    field_simp
    linear_combination e
  · intro e
    rw [e]
    field_simp
    ring

end Row

variable {E : Type} [Field E] [Fintype E]

namespace TokL
variable (L : TokL E)

section Block
variable {Ex : ExtSpec} {M Wp Kc : Type} (R0 : Rels Kc L.St Ex (M × Wp)) (msg : M → L.J → E)
  (Psi : L.St → E → (L.J → E) → Prop)

open Classical in
/-- eps = 0 is refused -/
def refuse (b : (L.St × E) × L.toSum.T.par.Out) : Option ((L.St × E) × L.toSum.T.par.Out) :=
  if b.2.eps = 0 then none else some b

theorem refuse_some {b b' : (L.St × E) × L.toSum.T.par.Out} (h : L.refuse b = some b') :
    b' = b ∧ b.2.eps ≠ 0 := by
  classical
  unfold refuse at h
  split at h
  · cases h
  · exact ⟨(Option.some.inj h).symm, by assumption⟩

/-- The reduction. -/
def oblk : IOR L.St Ex ((L.St × E) × L.toSum.T.par.Out) Ex :=
  (L.blk (Ex := Ex)).post L.refuse (ExtMap.id Ex)

/-- The joint behind it. -/
@[reducible] def orel : Rels Kc ((L.St × E) × L.toSum.T.par.Out) Ex (M × Wp) :=
  ⟨fun b y w => (L.toSum.A0 R0 msg).rel b.1.1 y w ∧ Psi b.1.1 b.1.2 (msg w.1) ∧
      keptAt L.toSum.T.par b.2 (msg w.1) = overAt L.toSum.T.par b.2 (msg w.1) ∧
      ∀ a, L.toSum.T.par.EHolds b.2 (msg w.1) a,
    fun a w => (L.toSum.A0 R0 msg).relR (a.1.1.1, a.2) w ∧ Psi a.1.1.1 a.1.1.2 (msg w.1) ∧
      keptAt L.toSum.T.par a.1.2 (msg w.1) = overAt L.toSum.T.par a.1.2 (msg w.1) ∧
      ∀ c, L.toSum.T.par.EHolds a.1.2 (msg w.1) c,
    fun a => R0.on (a.1.1.1, a.2) ∧ a.1.2.eps ≠ 0, R0.core⟩

theorem oknowAt :
    KnowAt (L.oblk (Ex := Ex)) (L.toSum.rrelIn R0 msg Psi) (L.orel R0 msg Psi) (fun _ _ _ wp => wp)
      (L.toSum.reps (Ex := Ex) (F₀ L.toSum.T.par)) :=
  knowAt_post (fun _ _ _ wp => wp) L.refuse (ExtMap.id Ex) (fun _ _ w => w) (L.knowAt R0 msg Psi)
    (extMap_isLocal.1 Ex)
    (fun x y x' h e => by
      obtain ⟨rfl, h0⟩ := L.refuse_some e
      exact ⟨h, h0⟩)
    (fun u x y x' w _ e hw => by
      obtain ⟨rfl, h0⟩ := L.refuse_some e
      exact ⟨hw.1, hw.2.1, (over_iff L.toSum.T.par _ _ h0).2 hw.2.2.1, hw.2.2.2⟩)
    (fun _ _ _ _ _ _ => rfl)

/-- Knowledge soundness, for each fixed tuple of messages. -/
theorem oknow (m : M) :
    (L.oblk (Ex := Ex)).red.Know (L.toSum.rrelIn R0 msg Psi).on
      (fun a wp => (L.toSum.rrelIn R0 msg Psi).relR a (m, wp))
      (fun b wp => (L.orel R0 msg Psi).relR b (m, wp)) (fun _ _ wp => wp)
      (L.toSum.reps (Ex := Ex) (F₀ L.toSum.T.par)) :=
  (L.oknowAt R0 msg Psi).know m

end Block

end TokL
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.over_iff
#print axioms Cb.Pv.Lay.TokL.oknowAt
