-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/PlanEnvAtBatch.lean: CONDITIONAL. A LAW ON WHAT THE VERIFIER's SUB-PROTOCOLS ACCEPT: the
honest prover is not in it.

What is here. The two runs of claims "front" and "back" of the feed-forward layers' own rounds (sub-protocol K4) have, on the road
on shapes, one premise on the state: `PlanEnv P s` (Johnson/Desc/First/K4/Returns/RunShape.lean; with code: `planEnvB`,
Returns/RunBools.lean): whatever the state holds as the return of K4's rounds has, in its environment, the plan's layout and the
plan's table of scales. Here: IT HOLDS AT EVERY STATE THAT THE FIRST CHAIN's RUN REACHES IN FRONT OF THE BATCHING OF A FEED-FORWARD
LAYERS' SEGMENT (member number 28 g + 9 of the chain's flat list, counted from 0), at P := the opened description's own public
record of the layers (`Bs.G₀.W.layers`). "Reached" is the library's `Reach` (namespace Johnson.Desc.First.Walk.Tied), at its first argument 0
(the number from which the columns are counted): along accepting steps of the chain's members, from any first state. Joinings of the library's:
· `k4_heard_at_front` (Johnson/Desc/First/Link/Law/K4AtFront.lean): at that border the state holds some o as K4's return, and o is a
  return of K4's hearing at that public record with some tokens laid in;
· `hear_public` (OnBytes/Desc/First/K4/HearPublic.lean): the environment of what the hearing returns, field by field;
· `flat_planOk` (Johnson/P1K2R/SitsDoor.lean), `sized_upTo` (Johnson/Desc/First/Look/K03RowsBare.lean): the two premises of
  `k4_heard_at_front`, as in Law/RunsAtBatch.lean.
The library's `k4_planEnv` (Johnson/Desc/First/K4/Returns/RunPays.lean) has the same end at the state right behind K4's own yes
(28 g + 5) alone.

  `planEnv_at_batch`    **at 28 g + 9.**
  `planEnvB_at_batch`   the same, of the Bool.
  `own_at_batch`        at that border the state does hold a return of K4's: so the two above are not idle there.
  `planEnvB_at_head`    **under the head `P5J.AtMgA`, at the base that the table of the road on shapes names.**

Not shown here. THAT ANY STATE IS REACHED THERE. THAT THE PREMISE HOLDS AT THE STATES AT WHICH THE BATCHING CALLS THE TWO RUNS (behind its draw and
behind the runs in front, among which, for "back", is K4's own run "front"). The page on shapes asks a row's premise at
these states, and once in front only where it reads the statement alone; this one reads `S.own?`, which is no part of the statement. The
batching's house has taken that carriage on itself (its letter on the houses' lane, key: "your row's pre at the stand in front of the
batching, and nothing more"); its stones are `rests_own` and `set_own` (Honest/K9/KeepsPaid.lean). If that carriage fails, the debt is K4's house's again. THAT THERE
IS AN OPENING: hS, hR, O and hOk are hypotheses. THE FULL SIZE ALONE; the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on
what a form or a claim is worth.
No property is claimed.
A LAW, NOT A PART: by a reader's walk of import lines its imports reach modules under Johnson/Goal/: no file that defines a part of the proof file's
description may import this one.
-/
import Johnson.Desc.First.Link.Law.K4AtFront
import Johnson.Desc.First.Look.K03RowsBare
import Johnson.Desc.First.K4.Returns.RunBools
import Johnson.P1K2R.SitsDoor
import Johnson.AtFull.Shape.TableFrames
import OnBytes.Desc.First.K4.HearPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Sized)
open OnBytes.Desc.First.K4 (hear_public)
open OnBytes.Desc.First.K4.Rt (PlanEnv planEnvB planEnvB_iff)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- CONDITIONAL on hS, hR, O, hOk and h. In front of a layers' segment's batching the state holds a return of K4's rounds, whose
environment has the plan's layout and table of scales. -/
theorem own_env_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {Q' : Type} {start : Q' → S} {z : Q'} {s : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s)) :
    ∃ o : Own, s.own? = some o ∧ o.v.y = Bs.G₀.W.layers.y ∧ o.v.sc = Bs.G₀.W.layers.sc := by
  have hp := P1K2.flat_planOk O hOk
  obtain ⟨_, R, C, hfold⟩ := h.fold
  have hk : 28 * g + 9 = 14 * (2 * g) + 6 + 2 + 1 := by omega
  rw [hk] at hfold
  obtain ⟨G', hG', hZ'⟩ := VerifiableInference.OnPublicFiles.sized_upTo hS hR O hOk (2 * g) (by omega) 6
    (by omega) hfold
  have hB : ∃ G', s.fork? = some G' ∧ Sized G' := ⟨G', hG', hZ'⟩
  obtain ⟨x, tokv, fo, F₄, o, G, _, t, u, _, _, xP, _, hh, _, _, _, ho, _⟩ :=
    VerifiableInference.Desc.LinkJoin.k4_heard_at_front hS hR O hp hg h hB
  obtain ⟨_, _, iU3, tab, laid, nU3, _, _, _, _, _, _, _, _, ev, _⟩ := hear_public hh
  have v1 : o.v.y = ({ x.2.P with tokv := tokv } : Layer.Pub).y := by rw [ev]
  have v2 : o.v.sc = ({ x.2.P with tokv := tokv } : Layer.Pub).sc := by rw [ev]
  exact ⟨o, ho, v1.trans (congrArg (·.y) xP), v2.trans (congrArg (·.sc) xP)⟩

/-- CONDITIONAL on hS, hR, O, hOk and h. At that border the state holds a return of K4's rounds. -/
theorem own_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {Q' : Type} {start : Q' → S} {z : Q'} {s : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s)) : ∃ o : Own, s.own? = some o := by
  obtain ⟨o, ho, -, -⟩ := own_env_at_batch hS hR O hOk hg h
  exact ⟨o, ho⟩

/-- CONDITIONAL on hS, hR, O, hOk and h. **IN FRONT OF A LAYERS' SEGMENT's BATCHING the premise of K4's two runs on shapes holds.** -/
theorem planEnv_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {Q' : Type} {start : Q' → S} {z : Q'} {s : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s)) : PlanEnv Bs.G₀.W.layers s := by
  obtain ⟨o, ho, h1, h2⟩ := own_env_at_batch hS hR O hOk hg h
  intro o' ho'
  obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
  exact ⟨h1, h2⟩

/-- CONDITIONAL on hS, hR, O, hOk and h. The same, of the Bool. -/
theorem planEnvB_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {Q' : Type} {start : Q' → S} {z : Q'} {s : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s)) : planEnvB Bs.G₀.W.layers s = true :=
  (planEnvB_iff _ _).2 (planEnv_at_batch hS hR O hOk hg h)

/-- CONDITIONAL on the head h, hB and hr. **UNDER THE HEAD, at the base Bs that the table of the road on shapes names**, at every state
reached at 28 g + 9 of the head's own first chain. -/
theorem planEnvB_at_head {Zl : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bt : ProofFile.PureBase}
    (h : P5J.AtMgA OnBytes.secondHashFunction Zl D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bt) {g : ℕ} (hg : g < 12) {Q' : Type}
    {start : Q' → S} {z : Q'} {s : S} (hr : Reach 0 cF.blocksInOrder start (28 * g + 9) (z, s)) :
    planEnvB Bt.G₀.W.layers s = true := by
  obtain ⟨Bs', base', O⟩ := h.laid.opened
  obtain rfl := Johnson.AtFull.Shape.base_one hB O.made
  exact planEnvB_at_batch h.scope h.reads O h.laid.planOk hg hr

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.own_env_at_batch
#print axioms ProofFile.Honest.K4.own_at_batch
#print axioms ProofFile.Honest.K4.planEnv_at_batch
#print axioms ProofFile.Honest.K4.planEnvB_at_batch
#print axioms ProofFile.Honest.K4.planEnvB_at_head
