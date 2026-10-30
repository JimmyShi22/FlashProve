-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Needs.lean: THE LAYERS' OWN ROUNDS (K4): THE TWO TESTS ON SAMPLED
VALUES IN hear_returns (Johnson/Desc/First/K4/Returns/Whole.lean) ARE NOT IDLE. General laws:
nothing is evaluated.

  tscIn_eps       from a return at a written first round: the drawn eps is laid.
  **hearTerms_coin**   where the element drawn in the second token sumcheck's first round is 0,
                  hearTerms does not return ("coin-zero").
  **hearNorms_merged**   where some call's point does not end as the lookup's own, hearNorms does
                  not return ("internal-g-merged-point").

  tape_length, coinB, coin_of_B   "coin-zero" as a function of the tape with values in Bool, by the
                  round's number (false where the tape has no round of that number); where it is
                  true, hear_returns' premise on the coin holds.
  **hear_coin**   at the top: where the coin is 0 the hearing does not return, under the premises
                  that carry it through hearNorms.
  planNumsB, planNums_of_B   PlanNums as a function with values in Bool; where it is true, PlanNums
                  holds.
  **takes_slotsOf**   the plan's count of a layers' sub-proof's slots is the lookup's, K4's and the
                  smallness test's together: an equation by which the premise "the ledger has room
                  for k4Takes slots" can be checked from the plan's own count. No hearing is in it.

Limits. "Not idle" means: where the test fails, the function named does not return. FOR
"internal-g-merged-point" THAT FUNCTION IS hearNorms, THE HEARING's FIRST PART: no law here carries
the refusal up to the whole hearing, as hear_coin does for "coin-zero". tscIn_eps, hearTerms_coin
and hear_coin take the round with two values sent, as K4's table of rounds has it
(OnBytes/Desc/First/K4/Rounds.lean); coin_of_B and hear_returns' premise speak of any number.
hear_coin asks PlanNums and K3Hands whole, though its proof spends four fields of each. Of the other
premises of hear_returns no such law is here. Under which name K4's block refuses is not said.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.Whole
import OnBytes.Desc.First.K4.HearCalls
import OnBytes.Model.LayerPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Desc.First.P1 (bind_some pure_some must_some need_some)

/-- Where the token sumcheck returns at a tape whose first round bears the name of a masked
sumcheck's first round, draws nothing by the rule that never gives 0, sends two values and draws
one, the element drawn in that round is the eps of what it returns. -/
theorem tscIn_eps {P : Array E} {lt n dY w0 : Nat} {F G : Fork} {cl mu eps : E} {t u : Tape}
    {o : Tsc}
    (h : Fl.tscIn P lt n dY F (⟨some RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ :: t) =
      some (o, G, u)) : o.p.eps = eps := by
  unfold Fl.tscIn at h
  obtain ⟨o1, G1, u1, h1, h⟩ := bind_some.mp h
  obtain ⟨⟨sEnd, p⟩, G2, u2, h2, h⟩ := bind_some.mp h
  obtain ⟨rfl, _, _⟩ := pure_some.mp h
  exact (pscEnds_head h2).eps.trans (tscRounds_head h1).1

/-- **"coin-zero" is not idle**: where the element drawn in the second token sumcheck's first round
is 0, hearTerms does not return. -/
theorem hearTerms_coin {P : Pub} {H : Heard} {F : Fork} {w0 : Nat} {cl mu eps : E} {t : Tape}
    (hz : isZeroE eps = true) (out : Heard × Fork × Tape) :
    hearTerms engFl P H F (⟨some RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ :: t) ≠
      some out := by
  intro h
  obtain ⟨H', G, u⟩ := out
  obtain ⟨tT, G1, u1, row, p', h1, h2, _, _⟩ := hearTerms_calls h
  rw [tscIn_eps h1, hz] at h2
  cases h2

/-- **"internal-g-merged-point" is not idle**: where some call's point does not end as the lookup's
own, hearNorms does not return. -/
theorem hearNorms_merged {P : Pub} {g : Nat} {fo : Forest.Heard} {F : Fork} {t : Tape}
    {Z : Array E} {ends : Array (Array E)} (hZ : (lastOf fo.zx P.y.h.la).toOption = some Z)
    (hE : (fo.zk.mapM fun zk => (lastOf zk P.y.h.la).toOption) = some ends)
    (hv : ends.all (· == Z) = false) (out : Heard × Fork × Tape) :
    hearNorms engFl P g fo F t ≠ some out := by
  intro h
  obtain ⟨H', G, u⟩ := out
  unfold hearNorms at h
  obtain ⟨PV, _, _, _, h⟩ := bind_some.mp h
  have key : ∀ (ZE tkh : Array E) (F' : Fork) (t' : Tape), ¬ ((do
      engFl.mustAs "forest-depth-G" (decide (P.y.h.la ≤ fo.shape.dT))
      let Z ← engFl.get (lastOf fo.zx P.y.h.la).toOption
      let ends ← engFl.get (fo.zk.mapM fun zk => (lastOf zk P.y.h.la).toOption)
      engFl.check (ofGroup g "internal-g-merged-point") (ends.all (· == Z))
      let ztF ← engFl.get (lastOf fo.zx P.y.h.lt).toOption
      let sW ← engFl.claimsIn (ledNS P.y.h.xl * P.y.NI)
      let gp ← engFl.batch (ledNS P.y.h.xl)
      let rhoI ← engFl.point .join P.rd.lNI
      let (C, rho) := normsStart P.y sW gp rhoI PV
      let wpl ← engFl.levelIn P.rd.muV rho C (orderDefault P.rd.muV)
      let sPv ← engFl.claimsIn (ledNP P.y.h.xl * P.y.NI)
      let omV ← engFl.batch (ledNP P.y.h.xl * P.y.NI)
      let tV ← engFl.tscIn PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2
      pure ({ fo, PV, ZE, tkh, ztF, sW, gp, wpl, sPv, omV, tV } : Heard) : Fl Heard) F' t' =
        some (H', G, u)) := by
    intro ZE tkh F' t' h
    obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
    obtain ⟨Z', _, _, a1, h⟩ := bind_some.mp h
    have q1 := (need_some.mp a1).1
    obtain ⟨ends', _, _, a2, h⟩ := bind_some.mp h
    have q2 := (need_some.mp a2).1
    obtain ⟨_, _, _, a3, h⟩ := bind_some.mp h
    have q3 := (must_some.mp a3).1
    rw [hZ] at q1
    rw [hE] at q2
    obtain rfl := Option.some.inj q1
    obtain rfl := Option.some.inj q2
    rw [hv] at q3
    cases q3
  by_cases hg : (g == 0) = true
  · simp only [hg, if_true] at h
    obtain ⟨ZE, _, _, _, h⟩ := bind_some.mp h
    obtain ⟨tkh, _, _, _, h⟩ := bind_some.mp h
    exact key ZE tkh _ _ h
  · simp only [hg, if_false, Bool.false_eq_true] at h
    obtain ⟨ZE, _, _, _, h⟩ := bind_some.mp h
    obtain ⟨tkh, _, _, _, h⟩ := bind_some.mp h
    exact key ZE tkh _ _ h

/-! ## The coin's premise by the round's number, and the refusals at the top -/

/-- A tape of rows' shape has as many rounds as there are rows. -/
theorem tape_length : ∀ {ds : List Rd} {t : Tape}, TapeOf ds t → t.length = ds.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: ds, _ :: t, h => by
    rw [List.length_cons, List.length_cons, tape_length (ds := ds) (t := t) h.2]

/-- **"coin-zero" as a function of the tape with values in Bool**: the tape has a round behind
hearNorms' rows, and no element that this round draws is 0. Where the tape is too short to have that
round, coinB is false. -/
def coinB (P : Pub) (g : Nat) (t : Tape) : Bool :=
  match t[(rowsNorms P g).length]? with
  | some r => r.drawn.all fun e => !isZeroE e
  | none => false

/-- Where coinB is true, hear_returns' premise on the coin holds. -/
theorem coin_of_B {P : Pub} {g : Nat} {t : Tape} (h : coinB P g t = true) :
    ∀ t₁ s0 eps t₂, TapeOf (rowsNorms P g) t₁ →
      t = t₁ ++ ⟨some RoundName.pscEpsilon.name, 0, 0, s0, [eps]⟩ :: t₂ → isZeroE eps = false := by
  intro t₁ s0 eps t₂ h1 e
  unfold coinB at h
  rw [e, ← tape_length h1, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at h
  simpa using h

/-- **At the top: where the coin is 0 the hearing does not return**, under room in the ledger, the
tape's shape up to that round, PlanNums, K3Hands and the test on the merged point: more than is
spent: they serve to carry the hearing through hearNorms. -/
theorem hear_coin (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) {F : Fork} {k : Nat}
    {t₁ t₂ : Tape} {Z ztF : Array E} {ends : Array (Array E)} {cl mu eps : E}
    (hR : Room F (slotsNorms P + k)) (hT : TapeOf (rowsNorms P g) t₁) (hN : PlanNums P hp g)
    (hK : K3Hands P fo F Z ztF ends) (vM : ends.all (· == Z) = true)
    (hz : isZeroE eps = true) :
    hearFl P hp g fo F
      (t₁ ++ ⟨some RoundName.pscEpsilon.name, 0, 0, [cl, mu], [eps]⟩ :: t₂) = none := by
  obtain ⟨H1, G1, a1, -⟩ := hearNorms_returns P g fo hR hT
    (⟨some RoundName.pscEpsilon.name, 0, 0, [cl, mu], [eps]⟩ :: t₂) hN.ns hN.np hN.no hN.muV
    hK.depth hK.z hK.ends hK.zt vM
  cases h : hearFl P hp g fo F
      (t₁ ++ ⟨some RoundName.pscEpsilon.name, 0, 0, [cl, mu], [eps]⟩ :: t₂) with
  | none => rfl
  | some out =>
    obtain ⟨o, G, u⟩ := out
    obtain ⟨-, H1', G1', u1, G2, u2, b1, b2, -⟩ := hear_calls h
    rw [a1] at b1
    obtain ⟨rfl, rfl, rfl⟩ := OnBytes.Desc.First.P1.some_triple.mp b1
    exact absurd b2 (hearTerms_coin hz _)

/-! ## The plan's numbers as a function with values in Bool -/

/-- PlanNums as a Bool. -/
def planNumsB (P : Pub) (hp : HPlan2) (g : Nat) : Bool :=
  ledNS P.y.h.xl != 0 && ledNP P.y.h.xl * P.y.NI != 0 && decide (1 ≤ ledNO P.y.h.xl * P.y.NI) &&
    decide (P.rd.muV ≤ P.rd.lNI + P.y.lPd + P.y.h.lt) && decide (1 ≤ nEndT P.y) &&
    decide (9 ≤ P.rd.muH) && decide (9 ≤ P.rd.muH2) &&
    decide (P.rd.muH ≤ min (P.y.h.ll + P.y.lPf) hp.lamS + P.y.h.lt) &&
    decide (P.rd.muH2 ≤ (P.y.h.ll - 1) + min P.y.lfe hp.lamS + P.y.h.lt) &&
    (!(g == 0) || decide (1 ≤ hp.NCL))

/-- Where planNumsB is true, PlanNums holds. -/
theorem planNums_of_B {P : Pub} {hp : HPlan2} {g : Nat} (h : planNumsB P hp g = true) :
    PlanNums P hp g := by
  unfold planNumsB at h
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, fun hg => by
    rcases a10 with q | q
    · rw [hg] at q
      cases q
    · exact q⟩

/-! ## The slots that the hearing takes, against the plan's own count -/

/-- **The plan's count of a layers' sub-proof's slots is the lookup's, K4's and the smallness
test's**, where the plan is one for which K4 is written and has the layout's numbers of rounds and
of weight claims. No hearing is in it. -/
theorem takes_slotsOf {P : Pub} {hp : HPlan2} {g : Nat} (small : Nat) (hc : covers P = true)
    (h1 : hp.lamS = lamSOf P.y) (h2 : hp.NCL = nclOf P.y g) :
    Forest.elems P.y.fo + k4Takes P hp g + small = Layer.slotsOf P.y P.rd g P.wsLay.lk small := by
  unfold covers at hc
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩ := hc
  unfold Layer.slotsOf k4Takes slotsNorms slotsTerms slotsStack slotsGated slotsMerge nclp
    layerSlots tscSlots wsForkSlots sumcheckSlots shownByTerms nEndT roundValues
  simp only [c2, c5, if_true, Bool.false_eq_true, if_false, h1, h2]
  unfold nclOf
  simp only [c2, if_true]
  by_cases hg : (g == 0) = true
  · simp only [hg, if_true]
    omega
  · simp only [hg, if_false, Bool.false_eq_true]
    omega

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.tscIn_eps
#print axioms OnBytes.Desc.First.K4.Rt.hearTerms_coin
#print axioms OnBytes.Desc.First.K4.Rt.hearNorms_merged
#print axioms OnBytes.Desc.First.K4.Rt.tape_length
#print axioms OnBytes.Desc.First.K4.Rt.coin_of_B
#print axioms OnBytes.Desc.First.K4.Rt.hear_coin
#print axioms OnBytes.Desc.First.K4.Rt.planNums_of_B
#print axioms OnBytes.Desc.First.K4.Rt.takes_slotsOf
