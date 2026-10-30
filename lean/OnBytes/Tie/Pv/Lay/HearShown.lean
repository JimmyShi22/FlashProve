-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/HearShown.lean: behind the batched sumcheck of a layers' sub-proof, what the
verifier's state shows under the slots of its end values; and the target of the sumcheck of the
gated products.

The start forms of the later sumchecks (the gated products, the routed experts' products, the
merge) are sums of slots of the batched sumcheck's end values. A sumcheck's target is the public
part of its start form: the form with what was shown in the place of each slot.

Main names:
  `filled_shown_other`: outside the slots that a filling takes, what is shown stays.
  `stack_shown`: behind hearStack, under slot sA0 + i stands the i-th end value heard.
  `GatedTg`, `own_recs3`: the records of OnBytes/Tie/Pv/Lay/HearCanon.lean (`own_recs2`) with one
    target more: that of the gated products' sumcheck reads as the second end value heard in the
    batched sumcheck.
 `valsOf_at`, `t5_of`: so the fifth of the targets' equations holds at all letters whose claim
 there names as its target one end value of the batched sumcheck's output, if that name stands
 second in the list of names.

Limits: of the five targets that OnBytes/Tie/Pv/Lay/HearCanon.lean leaves (`Tg5`) one is shown
here, under two premises on the letters and the list of names. The targets of the sums of squares,
of the batched sumcheck, of the routed experts' products and of the merge are not treated.
-/
import OnBytes.Tie.Pv.Lay.HearCanon
import OnBytes.Tie.Pv.Lay.Slots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Model.Layer
open Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay OnBytes.Tie.Pv.Lay.Eng
open OnBytes.Psc (Weight hearMany hearOne hidingEntries)
open OnBytes.Tie.Pv.Att (PscH)

/-- Outside the slots that a filling takes, what is shown stays. -/
theorem filled_shown_other {F G : Fork} {first : Nat} {l : List E} {factor : E}
    (a : Filled F G first l factor) (j : Nat) (hj : j < first ∨ first + l.length ≤ j) :
    G.shown j = F.shown j := by
  obtain ⟨b1, _, b3⟩ := a.other j hj
  unfold Fork.shown
  rw [a.ns, b1, b3 false]

/-- Behind hearStack: under the slots of the batched sumcheck's end values stand the values
heard. -/
theorem stack_shown {lamS n : Nat} {C : Aff} {F2 F3 F3' : Fork} {Kk : HeardStack} {p4 : Psc}
    {H4 : PscH} (s : StackSaid lamS n C F2 F3 Kk p4 H4)
    (f1 : Filled (taken F2 (1 + 2 * lamS + (2 + n))) F3' Kk.sA0 H4.v H4.beta)
    (f2 : Filled F3' F3 p4.first (List.replicate p4.walk.1.length zeroE) (subE zeroE oneE))
    (i : Nat) (hi : i < n) : F3.shown (Kk.sA0 + i) = some (H4.v.getD i zeroE) := by
  obtain ⟨τ, _, en⟩ := s.psc
  have hw : p4.walk.1.length = 1 + 2 * lamS + 2 := by
    rw [en.walkLen, entries_three _ _ 2 (fun w hw => by rw [List.eq_of_mem_replicate hw]; rfl) rfl,
      List.length_replicate]
  rw [filled_shown_other f2 (Kk.sA0 + i) (Or.inr (by
    rw [List.length_replicate, hw, en.first, s.sA0]
    omega))]
  exact f1.shown i (by rw [s.vals]; exact hi)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- What the records' targets read as, beyond the two token sumchecks'. -/
structure GatedTg (D : OwnH) (p5 : Psc) : Prop where
  /-- the gated products' layer starts from the second end value of the batched sumcheck -/
  t5 : ρ.val p5.target = ρ.val (D.H4.v.getD 1 zeroE)

omit [Fintype K] in
/-- `own_recs2` (OnBytes/Tie/Pv/Lay/HearCanon.lean) with the target of the gated products' layer. -/
theorem own_recs3 {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {O : Own} {F G : Fork}
    {D : OwnH} {H0 : Heard} {tT : Tsc} {hd2 : Level} {claims : Array WsClaim}
    (s : OwnSaidL P hp g fo O F G D H0 tT hd2 claims) :
    ∃ p1 p3 p4 p5 p6 : Psc, Recs7 P hp g O D H0 tT hd2 p1 p3 p4 p5 p6 ∧ TokTg ρ D H0 p3 ∧
      GatedTg ρ D p5 := by
  obtain ⟨F4, F7, F8, F1, F1', F2, F3, F3', F5, F6, t3, C, p4, c1, c5, _, a2, _, _, a5, a6, a7, a8,
    _, _, a11, a12, a13, fn, a14, _, _, a17⟩ := s.recs
  obtain ⟨p1, b1, b2⟩ := a2.recAt
  obtain ⟨tT', Fm, e1, g5, g6⟩ := a14.said
  have et : tT' = tT := Option.some.inj (e1.symm.trans s.hasT)
  rw [et] at g6
  obtain ⟨τ5, p5, q1, q2, q3⟩ := g5.psc
  have b5 : RecAt D.H5 (levelWeights P.rd.muH (downFrom O.K.rs O.K.fin.wD ++ O.H.ztF)
      (orderRange P.rd.muH)) P.rd.muH 2 2 p5 := by
    refine ⟨⟨_, τ5, _, q2⟩, ?_, g5.sentY, g5.vals⟩
    refine List.eq_replicate_iff.2 ⟨by rw [List.length_map, g5.rounds], fun b hb => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    exact g5.two x hx
  obtain ⟨p6, b6, d6⟩ := g6.recAt
  have sh := stack_shown a11 a12 a13 1 (by omega)
  rw [← fn.sH1] at sh
  have e5 := publicPart_slot_word F3 O.K.sH1 _ τ5 sh q1
  refine ⟨p1, t3.p, p4, p5, p6, ⟨b1, b2, a5.recAt, a6.recAt, by rw [a7], by rw [a8], a11.recAt,
    a11.row, b5, q3, b6, d6, a17.recAt⟩, ⟨a5.target ρ, a6.target ρ⟩, ⟨?_⟩⟩
  rw [q2.target, e5, ρ.add, ρ.mul, ρ.zero, ρ.one, zero_add, one_mul]

omit [Fintype K] in
/-- The end value under the name that stands at place i of the list. -/
theorem valsOf_at {A : Type} (sh : List A) (hn : sh.Nodup) (l : List E) (i : Nat)
    (hi : i < sh.length) : valsOf ρ sh l sh[i] = ρ.val (l.getD i zeroE) := by
  classical
  unfold valsOf
  rw [List.Nodup.idxOf_getElem hn i hi]

/-- The fifth target, at letters whose claim at the gated products' sumcheck names as its target the
end value a₀ of the batched sumcheck's output, where a₀ stands second in the list of names. -/
theorem t5_of (D : OwnH) (nz : Nz7 ρ D) (H0 : Heard) (O : Own) (hd2 : Level)
    (p1 p3 p4 p5 p6 : Psc) {M X : Type} {T : LayTail K M X} (N : Shs T) (x : X)
    (a₀ : T.s4.L.S.A) (hcl : ∀ z r, (T.s5.cl z r).1 = z.2.vals a₀)
    (hN : ∀ l, valsOf ρ N.n4 l a₀ = ρ.val (l.getD 1 zeroE)) (gt : GatedTg ρ D p5) :
    (T.s5.cl ((tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).z4 x)
      (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).d5.rd).1 =
      ρ.val (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).d5.t := by
  rw [hcl]
  show (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).d4.out.vals a₀ = ρ.val p5.target
  unfold StgH.out
  rw [sum_vals]
  show valsOf ρ N.n4 D.H4.v a₀ = _
  rw [hN, gt.t5]

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.valsOf_at
#print axioms OnBytes.Tie.Pv.Lay.t5_of
#print axioms OnBytes.Tie.Pv.Lay.stack_shown
#print axioms OnBytes.Tie.Pv.Lay.own_recs3
