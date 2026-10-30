-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/StartK.lean: CONDITIONAL. THE START FORM OF THE BATCHED
SUMCHECK OF THE LAYERS' OWN ROUNDS (sub-protocol K4): ITS COEFFICIENTS ON THE SLOTS OF THE SECOND
TOKEN SUMCHECK AND ON THOSE THAT THE LOOKUP's END FORM NAMES.

What is here. A LAW ON THE VERIFIER's TEXT: the honest prover is not in it. THE STATEMENTS SPEAK OF
`startOf H om parts` (Johnson/Road/FormsKeysStart.lean), at any state H and any list `parts`. Where
H holds a token sumcheck's state it is: the parts under their weights, plus a constant, less the
slot of the second token sumcheck's claimed sum, less the lookup's end form cEnd, plus om[1] times
the form H.KT. Statements and proofs.

  `cf_startOf`: its coefficient on any slot, where the parts name no slot (hp) and H holds a token
      sumcheck's state (hT).
  `parts_clear`: the calls' factors, as `joinPart` returns them, name no slot (by `gs_joinPart`,
      Johnson/Desc/First/K4/Returns/JoinSlots.lean): its end is hp, word for word. KIN:
      `join_no_slot` in that file has, from the same premise, that each part's shape has an empty
      list of slots.
  `cf_KT`: KT's coefficient, where KT is a sumcheck's own claim divided by minus its joining element
      (hKT). That the library's field reads the program's minus and inverse as its own is the
      library's: `Cb.Fo.PlaneClaims.neg_val` (OnBytes/Tie/Pv/Lookup/Forest/FoPlaneClaims.lean) and
      `OnBytes.Slice.readE_inv` (OnBytes/Slice/ProgField.lean), both called here.
  `startK_cl`: with om the powers (1, x): on the slot of the claimed sum the coefficient is x -
      1.
  `startK_win`: on a slot of the token sumcheck's window it is not 0.
  `startK_cEnd`: on a slot below the claimed sum's it is minus cEnd's coefficient.
  `walk2_one`, `tsc_walk2`: the product P of the psi reads as 1 where each psi does; so at what
      `Fl.tscIn` returns, all of whose weights are equality weights (that such a weight's psi reads
      as 1 is the library's `OnBytes.PscTie.psi_equality`, OnBytes/Tie/Pv/Psc/FlatTie.lean). KIN:
      the library's `ran_walk` (OnBytes/Tie/Pv/Psc/PscWhole.lean) has the same end, `p.walk.2` reads
      as 1, under its own premise `Ran` on the state; and `hidingWalk_eq`
      (OnBytes/Tie/Pv/Psc/FlatTie.lean), by which that law goes, has it of `hidingWalk` at every
      list of equality weights, where `walk2_one` asks the readings of the psi alone, at any
      weights.
  `om_one`: the library's field reads the second of the powers (1, x) as x.

Not shown here. NO HYPOTHESIS OF THE LAWS ON `startOf` IS DISCHARGED IN THIS FILE: hT: H holds a
token sumcheck's state · hp: the parts name no slot (`parts_clear` ends in it, from a return of the
calls' factors; its call is in Law/Live/Whole.lean) · hKT: what KT is · that the sumcheck's state p
is live (`PscLive`) · that its product P reads as 1 (`tsc_walk2` ends in it, from a return of
`Fl.tscIn`; its call is in Law/Live/Stages.lean) · that its start form is the slot of its claimed
sum, which lies below its window · that cEnd names slots below that one alone · that x reads as not
0 (`startK_win`; that x - 1 is not 0 is the caller's). THAT THE START FORM WHICH THE FUNCTION THAT
READS K4's ROUNDS MAKES (`joinStart`, OnBytes/Desc/First/K4/Hear.lean) IS `startOf` OF THE CALLS'
FACTORS is the library's `joinStart_startOf` (Johnson/Road/K4/JoinTie.lean), which is called in
Law/Live/Whole.lean, not here. Nothing on entries. Nothing on what a form is worth.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.PscLive
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.Starts
import Johnson.Desc.First.K4.Returns.JoinSlots
import Johnson.Road.K4.JoinTie
import OnBytes.Desc.First.P1.TscLaw
import OnBytes.Slice.ProgField
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneClaims
import OnBytes.Tie.Pv.Psc.FlatTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Heard aff0)
open OnBytes.Psc (Weight hidingWalk polyAt)
open OnBytes.Road (startOf)
open OnBytes.Desc.First.K4.Slots (SlotsIn slotsIn_mono slotsIn_addMul slotsIn_foldl_mem sl_aff0
  slotsIn_empty slotsIn_slot all_mapM_mem)
open OnBytes.Desc.First.K4.Rt (gs_joinPart)
open OnBytes.Desc.First.P1 (tscIn_tape)

/-- The product P reads as 1 where each variable's psi at its challenge does. -/
theorem walk2_one {K : Type} [CommRing K] (ρ : Reading K) : ∀ l : List (Weight × E),
    (∀ y ∈ l, ρ.val (polyAt y.1.psi y.2) = 1) → ρ.val (hidingWalk l).2 = 1
  | [], _ => ρ.one
  | [(w, g)], h => h (w, g) (List.mem_cons.mpr (Or.inl rfl))
  | (w, g) :: y :: rest, h => by
    show ρ.val (mulE (hidingWalk (y :: rest)).2 (polyAt w.psi g)) = 1
    rw [ρ.mul, walk2_one ρ (y :: rest) fun z hz => h z (List.mem_cons.mpr (Or.inr hz)),
      h (w, g) (List.mem_cons.mpr (Or.inl rfl)), one_mul]

/-- **A token sumcheck's product P reads as 1**: all its weights are equality weights. -/
theorem tsc_walk2 {P : Array E} {lt n dY : ℕ} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) : Reading.gl.val o.p.walk.2 = 1 := by
  obtain ⟨-, T0, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, G0, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, hvars, -⟩ := tscIn_tape h
  unfold Psc.walk
  rw [zipT_eq]
  refine walk2_one Reading.gl _ fun z hz => ?_
  have h1 : z.1 ∈ o.p.vars.toList := (List.of_mem_zip (a := z.1) (b := z.2) hz).1
  rw [hvars] at h1
  rcases List.mem_append.1 h1 with h1 | h1
  · obtain ⟨_, _, e⟩ := List.mem_map.1 h1
    rw [← e]
    exact OnBytes.PscTie.psi_equality Reading.gl _ _ _
  · rw [List.mem_singleton.1 h1]
    exact OnBytes.PscTie.psi_equality Reading.gl _ _ _

/-- The calls' factors name no slot. -/
theorem parts_clear {v : Layer.Env} {alpha theta : E}
    {xs : List ((CallD × Array Bool) × ℕ)}
    {parts : List Aff}
    (h : (xs.mapM fun x => v.joinPart alpha theta x.2 x.1.1 x.1.2) = some parts)
    (S : ℕ → Prop) : ∀ f ∈ parts, SlotsIn S f :=
  all_mapM_mem (Pr := SlotsIn S) _ parts (fun _ _ b hb => gs_joinPart _ _ _ _ _ b hb) h

/-- **The start form's coefficient on any slot.** -/
theorem cf_startOf {H : Heard} {om : Array E} {parts : List Aff} {tT : Tsc} (hT : H.tT = some tT)
    (hp : ∀ S : ℕ → Prop, ∀ f ∈ parts, SlotsIn S f) (j : ℕ) :
    cf Reading.gl (startOf H om parts) j =
      Reading.gl.val (om.getD 1 zeroE) * cf Reading.gl H.KT j - cf Reading.gl (Aff.slot tT.sCl) j -
        cf Reading.gl H.fo.cEnd j := by
  have h0 : SlotsIn (fun i => i ≠ j)
      (parts.zipIdx.foldl (fun (a : Aff) x => a.addMul x.1 (H.fo.e.getD x.2 zeroE)) aff0) :=
    slotsIn_foldl_mem _ _
      (fun f x hx hf => slotsIn_addMul _ hf (hp _ x.1 (List.fst_mem_of_mem_zipIdx hx))) _ sl_aff0
  unfold startOf
  simp only [hT, Option.isSome_some, if_true]
  rw [cf_addMul, cf_sub, cf_sub, cf_add, cf_ofConst, cf_of_slotsIn Reading.gl h0]
  ring

section at_
variable {H : Heard} {parts : List Aff} {tT : Tsc} {p : Psc} {x : E}

/-- KT's coefficient: the own claim's, divided by minus the joining element. -/
theorem cf_KT (hKT : H.KT = (p.rowForm zeroE {}).scale (negE (invE p.eps))) (j : ℕ) :
    cf Reading.gl H.KT j = -(Reading.gl.val p.eps)⁻¹ * cf Reading.gl (p.rowForm zeroE {}) j := by
  have hi : Reading.gl.val (invE p.eps) = (Reading.gl.val p.eps)⁻¹ := OnBytes.Slice.readE_inv p.eps
  rw [hKT, cf_scale, Cb.Fo.PlaneClaims.neg_val Reading.gl, hi]

/-- The second of the powers (1, x) reads as x. -/
theorem om_one (x : E) : Reading.gl.val ((powers x 2).getD 1 zeroE) = Reading.gl.val x := by
  rw [OnBytes.Desc.First.P1.powers_val Reading.gl x 2 1 (by omega), pow_one]

/-- CONDITIONAL. **On the slot of the second token sumcheck's claimed sum: x - 1.** -/
theorem startK_cl (hT : H.tT = some tT) (hp : ∀ S : ℕ → Prop, ∀ f ∈ parts, SlotsIn S f)
    (hKT : H.KT = (p.rowForm zeroE {}).scale (negE (invE p.eps))) (L : PscLive p)
    (h2 : Reading.gl.val p.walk.2 = 1) (hs : p.start = Aff.slot tT.sCl) (hf : tT.sCl < p.first)
    (hc : SlotsIn (fun i => i < tT.sCl) H.fo.cEnd) :
    cf Reading.gl (startOf H (powers x 2) parts) tT.sCl = Reading.gl.val x - 1 := by
  rw [cf_startOf hT hp, cf_KT hKT, cf_rowForm_out Reading.gl p zeroE {} (Or.inl hf), hs,
    cf_slot_self, cf_empty, h2, om_one,
    cf_of_slotsIn Reading.gl (slotsIn_mono (fun i (hi : i < tT.sCl) => Nat.ne_of_lt hi) hc)]
  have he := L.eps
  field_simp
  ring

/-- CONDITIONAL. **On a slot of the second token sumcheck's window: not 0.** -/
theorem startK_win (hT : H.tT = some tT) (hp : ∀ S : ℕ → Prop, ∀ f ∈ parts, SlotsIn S f)
    (hKT : H.KT = (p.rowForm zeroE {}).scale (negE (invE p.eps))) (L : PscLive p)
    (hs : p.start = Aff.slot tT.sCl) (hf : tT.sCl < p.first)
    (hc : SlotsIn (fun i => i < tT.sCl) H.fo.cEnd) (hx : Reading.gl.val x ≠ 0) {j : ℕ}
    (h1 : p.first ≤ j) (h2 : j < p.first + p.walk.1.length) :
    cf Reading.gl (startOf H (powers x 2) parts) j ≠ 0 := by
  have hne : tT.sCl ≠ j := by omega
  have hw := live_win L zeroE (kept := {}) h1 h2 (by rw [hs]; exact slotsIn_slot hne) slotsIn_empty
  rw [cf_startOf hT hp, cf_KT hKT, cf_slot_ne Reading.gl hne, om_one,
    cf_of_slotsIn Reading.gl (slotsIn_mono (fun i (hi : i < tT.sCl) => by omega) hc), sub_zero,
    sub_zero]
  exact mul_ne_zero hx (mul_ne_zero (neg_ne_zero.2 (inv_ne_zero L.eps)) hw)

/-- CONDITIONAL. **On a slot below the claimed sum's: minus the lookup's end form's
coefficient.** -/
theorem startK_cEnd (hT : H.tT = some tT) (hp : ∀ S : ℕ → Prop, ∀ f ∈ parts, SlotsIn S f)
    (hKT : H.KT = (p.rowForm zeroE {}).scale (negE (invE p.eps)))
    (hs : p.start = Aff.slot tT.sCl) (hf : tT.sCl < p.first) {j : ℕ} (hj : j < tT.sCl) :
    cf Reading.gl (startOf H (powers x 2) parts) j = -cf Reading.gl H.fo.cEnd j := by
  have hne : tT.sCl ≠ j := by omega
  rw [cf_startOf hT hp, cf_KT hKT, cf_rowForm_out Reading.gl p zeroE {} (Or.inl (by omega)), hs,
    cf_slot_ne Reading.gl hne, cf_empty]
  ring

end at_

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.walk2_one
#print axioms ProofFile.Honest.K4.Live.tsc_walk2
#print axioms ProofFile.Honest.K4.Live.parts_clear
#print axioms ProofFile.Honest.K4.Live.cf_startOf
#print axioms ProofFile.Honest.K4.Live.cf_KT
#print axioms ProofFile.Honest.K4.Live.om_one
#print axioms ProofFile.Honest.K4.Live.startK_cl
#print axioms ProofFile.Honest.K4.Live.startK_win
#print axioms ProofFile.Honest.K4.Live.startK_cEnd
