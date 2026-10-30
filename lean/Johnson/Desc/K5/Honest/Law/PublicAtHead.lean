-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PublicAtHead.lean: CONDITIONAL, under the library's one head on the
public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): at each of the twelve groups' stored plans a,
the public premises of the files on the honest prover's side of an attention segment's own rounds
hold at the place (a.S, a.own) and the lookup's shape a.fs. It is `public_at_plan`
(Johnson/Desc/K5/Honest/Law/PublicAtPlan.lean) at the head's letters: its two premises are paid by
lemmas of the library's from the head. A joining of lemmas; no algebra is in this file.

How the two premises are paid. That the stored plan is the planner's return, but for the field
`plFor` of its seam's tail, which no statement here reads: `planIs_all`
(Johnson/Desc/First/Att/Door/Law/K5AtConstant.lean). That the plan passes the one test on a plan:
`okAll_plus` (Johnson/Desc/First/Att/Door/Law/K5LeftFitsD.lean), from the yes of the kind's guard
and of the block's own test on the plan, both of which the library draws from the head
(`seated_all`, `seatedOk_guard_all`, Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean: the guard's
yes comes out of the head's field on the named tests, `laid.asks`). So the guard's yes is no premise
beside the head.

A TABLE OF THE PREMISES of the files under Johnson/Desc/K5/Honest/Law/ on the readings, the starts
and the key forms: premise; what gives it.
  PUBLIC, FROM THE HEAD, HERE (`public_at_head`): `Sized`; `Planned`; a token has at most 16 bits;
    `CallsFit`, `KeysFit`; one shift a group; `UnitIs` at the seven units, and at m1, d1 for the two
    softmax-table units; `PairsAre` at the seven units at every key point; the two units' numbers of
    pieces and of variables; the list of softmax-table units is not empty.
  PUBLIC, FROM THE SAME AND A RETURN: `CallsAre`, `KeyPub` (Keys.lean): the library has them from
    the place's four calls, the test's clauses and the return of the verifier's function of the
    points (`callsAre_of`, Johnson/Desc/First/Att/Claims/Place.lean; `key_pub`,
    Johnson/Desc/First/Att/Claims/KeyPubOf.lean); joined in KeysAtPlan.lean.
  BY THE MAKE: `IndexPts`, `BitPts`, `MaxPts` hold at `pubOf` (Weights.lean, Starts.lean).
  FROM `KeyPtsAre` AND THE ABOVE: `DivPts`, `LonePts` (`divPts_of`, `lonePts_of`); `divPts_of` asks
    also that the batching element heard, read, is p's `th`: so by the make at `pubOf`.
  THE LOOKUP'S: `KeyPtsAre`, from `K3Pts` and `KeysFit` (`keyPts_of_keysFit`); `JoinMeets`
    (Join.lean); `LookAll`, `KeyIs` (KeysAtPlan.lean: Lk, hK).
  ON THE READING: `Numerals` (KeysAtPlan.lean: N); the library has it of its reading of the field.
  ON THE RUN: `Drawn`; that the verifier's function of the points returns (`divIn`, `ptsOf`); the
    returns of the runs "first" and "keys"; `RuleAt`'s tie of slots to what was sent.
  ON THE CELLS: `AtIdn` (Idn.lean).
  GIVEN BY NO LEMMA KNOWN HERE: none of the public ones OF THESE FILES.
  NOT OF THESE FILES, and not looked at here: the public premises of the files on the tables and
    their addresses, on the door in front of the block, on the hearing and on the row of parts.

Main names:
  `plan_at_head`    the stored plan's shape, own numbers and lookup's shape are a planner's
                    return's, and that return passes the one test
  `law_at_head`     the same in the stored plan's own letters: the planner of shapes returns its
                    shape, and the plan's law holds of it
  `public_at_head`  **`PublicAll (a.S, a.own) a.fs`**

Limits. The head is a hypothesis; that it is met is not shown here. At the library's full size
alone: twelve groups. Nothing is said of a premise that names a challenge or a cell.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.PublicAtPlan
import Johnson.Desc.First.Att.Door.Law.K5KindWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att.P (planOkAll)
open P5J (AtMgA TS)
open H2K5.Door

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)
include h

/-- **The stored plan is a planner's return in the three fields that are read, and that return
passes the one test on a plan.** Conditional: the head; hg: the group; ea: the group's plan. -/
theorem plan_at_head {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) :
    ∃ A0, Attention.plan a.settings a.inp a.S.cf = Except.ok A0 ∧ a.S = A0.S ∧ a.own = A0.own ∧
      a.fs = A0.fs ∧ planOkAll a.S.cf A0.S A0.fs = true := by
  obtain ⟨h4, _, _⟩ := scope_all h
  obtain ⟨blk, hb⟩ := seated_all h hg
  obtain ⟨hok, hG⟩ := seatedOk_guard_all h hg hb
  have ok := okAll_plus (P5J.At.X Zp) g (beforeAll Zp g) a h.𝔇.sent h.𝔇.l3.rad (planIs_all h) h4 ea
    hG (planOk_plus (beforeAll Zp g) hb hok ea) (claimsOk_plus (beforeAll Zp g) hb hok ea)
  obtain ⟨A0, pf, hA, e⟩ := planIs_all h g a ea
  have eS : a.S = A0.S := by rw [e]
  have eO : a.own = A0.own := by rw [e]
  have eF : a.fs = A0.fs := by rw [e]
  exact ⟨A0, hA, eS, eO, eF, by rw [← eS, ← eF]; exact ok⟩

/-- **The stored plan's shape is a return of the planner of shapes, and the plan's law holds of
it**, in the stored plan's own letters. Conditional as `plan_at_head`. -/
theorem law_at_head {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) :
    Attention.shapeHid a.settings.lidb a.S.cf = Except.ok (a.S, a.fs) ∧
      K5Law.PlanLaw a.S.cf a.S a.fs := by
  obtain ⟨A0, hA, eS, _, eF, ok⟩ := plan_at_head h hg ea
  have hid0 := (OnBytes.Road.L5.plan_shape hA).1
  have hid : Attention.shapeHid a.settings.lidb a.S.cf = Except.ok (a.S, a.fs) :=
    hid0.trans (by rw [← eS, ← eF])
  have ok' : planOkAll a.S.cf a.S a.fs = true := (by rw [← eS, ← eF] at ok; exact ok)
  exact ⟨hid, (Att.P.plan_all hid ok').law⟩

/-- **The public premises of the files on the readings, at the head's letters.** Conditional: the
head; hg: the group; ea: the group's plan. -/
theorem public_at_head {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) : PublicAll ⟨a.S, a.own⟩ a.fs := by
  obtain ⟨A0, hA, eS, eO, eF, ok⟩ := plan_at_head h hg ea
  rw [eS, eO, eF]
  exact public_at_plan hA ok

end

end H2K5.Honest

#print axioms H2K5.Honest.plan_at_head
#print axioms H2K5.Honest.law_at_head
#print axioms H2K5.Honest.public_at_head
