-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Front/Count.lean: the proofs of `StatedYesHeadAt` and `CountRaw`
(Johnson/Desc/K11/Front/CountStatement.lean), to the letter. Lemmas; none of the library's goals.

How. The first: the lines of `stated_yes_head` (Johnson/Desc/Kinds/Law/DigitsKeptAtDecide.lean),
with the third end of `K3.theOwn_is` (Johnson/Desc/First/Look/K3OwnIs.lean) kept. The second: the
walk back of `backToHeadRaw` (Filled.lean of this folder), for "the ledger in front of 345 has its
sizes"; number 345 as `P4.digits_345` (Johnson/P4R/WaK6At346.lean) finds it; the first lemma; in
scope the place of the head's digits has the shape X.H.tl.f9 and begins at 2168 (`digits_place`,
Johnson/Desc/Kinds/Law/K6PubInScope.lean); the bare lookup's yes holds the ledger's next number at
that beginning (`decide_first`, Johnson/Top/H/K3DecideMore.lean) and leaves it `Forest.elems`
further (`decide_left_some`, Johnson/Top/H/Keep/K3LeftAnyWords.lean; the field next of `PadLeft`,
OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean): 1363 (`plan_in_scope`,
Johnson/Desc/Kinds/Law/HeadPlanWritten.lean); the seat hands that ledger on (`seatDigits_keeps`,
Johnson/Top/H/K3SeatFits.lean); the quiet step lays the claim alone (`quietHead_form`,
Johnson/Desc/Kinds/Law/QuietHeadGives.lean). lk = 18 (`m0lk_in_scope`,
Johnson/Desc/Sound/K11Tests/NumsHeadInScope.lean) and 3570 slots (`slots_in_scope`,
SlotsInScope.lean of that folder): 2168 + 1363 + 2 * 18 + 3 = 3570.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Front.CountStatement
import Johnson.P4R.WaK6At346
import Johnson.Desc.Kinds.Law.K6PubInScope
import Johnson.Top.H.Keep.K3LeftAnyWords
import Johnson.Top.H.K3DecideMore
import Johnson.Desc.Sound.K11Tests.SlotsInScope
import Johnson.Desc.Sound.K11Tests.NumsHeadInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Desc.First.ForkMerge.Front
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc
open VerifiableInference.OnPublicFiles (pieceAt_neD decide_first decide_left_some seatDigits_keeps)
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.First.MergeLaw (hlay_at)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (sized_of_wellLaid blockAt_later quietHead_form)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (digits_place plan_in_scope)

/-- **At the head's segment the quiet step is there, and the lookup is the public data's.** -/
theorem statedYesHeadAt : StatedYesHeadAt := by
  intro Cl claim readers X codes shape a B h hOk i hi hpc hH s c rs gs hd
  obtain ⟨B₁, hB₁, -, e2, -, e4⟩ := K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hW⟩ := K3.theWhole_is claim true X codes shape a B₁ hB₁
  obtain ⟨i', digits, P, sent, laid, hi', hpc', hP, -, -, -, r2, -, hpl⟩ :=
    K3.theOwn_is claim true X codes shape a b hb
  obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
  cases digits with
  | false => exact absurd (hpc'.symm.trans hpc) (pieceAt_neD X i)
  | true =>
    rw [e2] at hd
    rw [e4] at hOk
    have hq : (a.link.bind fun j => K3.quietAt X j (a.piece == K3.pieceAt X j true)) =
        some (K3.quietHead X) := by
      simp [hi, hpc, K3.quietAt, hH]
    rcases hW with ⟨hn, -⟩ | ⟨f, hf, rfl⟩
    · rw [hq] at hn
      cases hn
    · obtain rfl : K3.quietHead X = f := Option.some.inj (hq.symm.trans hf)
      have hOk' : b.planOk = true := by
        have h0 : (b.planOk && true) = true := hOk
        simpa using h0
      have hd' : (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind
          (fun s' => K3.quietHead X s') = .ok c := hd
      cases hb' : b.decide s (rs.take b.rounds.length) (gs.take b.openings) with
      | error e =>
        rw [hb'] at hd'
        cases hd'
      | ok m =>
        rw [hb'] at hd'
        rw [r2] at hb'
        exact ⟨P, sent, laid, _, _, m, hP, K3.Law.blockVia_decide (hpl hOk') hb', hd'⟩

/-- **The count of slots.** -/
theorem countRaw : CountRaw := by
  intro Z D r Zp Np cF xP Bs z sF a h hB hr ha
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨s345, B5, h345, hB5, y5⟩ := P4.reach_last hr
  obtain ⟨s344, B4, h344, hB4, y4⟩ := P4.reach_last h345
  obtain ⟨s343, B3, h343, hB3, y3⟩ := P4.reach_last h344
  obtain ⟨s342, B2, h342, hB2, y2⟩ := P4.reach_last h343
  obtain ⟨s341, B1, h341, hB1, y1⟩ := P4.reach_last h342
  obtain ⟨r5, g5, d5⟩ := P4.step_yes y5
  obtain ⟨r4, g4, d4⟩ := P4.step_yes y4
  obtain ⟨r3, g3, d3⟩ := P4.step_yes y3
  obtain ⟨r2, g2, d2⟩ := P4.step_yes y2
  obtain ⟨r1, g1, d1⟩ := P4.step_yes y1
  have c1 := P4.yes_341 h.scope h.reads O hB1 d1
  have c2 := P4.wellLaid_341 h.scope h.reads O (P4.plan_at O h.laid.planOk 340) h341 Bs'.G₀.W.hS
    (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs'.G₀.W)
  obtain ⟨a0, F1, X0, Q, -, hop, -, e⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.decide_record _ _ _ _ c1
  have ho2 : s342.here = .head { a0 with F := F1, x := some X0, squaresP := some Q } := by rw [e]
  have eL : (seatAt Bs'.G₀.W.hS
      (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs'.G₀.W)).ledger s342 = F1 := by
    rw [e]
    show (S.fork? _).getD {} = F1
    simp [S.fork?, hop]
  have hz2 : Sized ({ a0 with F := F1, x := some X0, squaresP := some Q } : HeadOwn).F := by
    have hL := blockAt_later _ _ _ _ s341 s342 r1 g1 c1
    rw [eL] at hL
    exact hL.sized (sized_of_wellLaid c2)
  have k2 := P4.kept_342 h.scope h.reads O hB2 d2 ho2
  obtain ⟨o3, ho3, hz3⟩ := k2.next ho2 hz2
  have k3 := P4.kept_343 h.scope h.reads O hB3 d3 ho3
  obtain ⟨o4, ho4, hz4⟩ := k3.next ho3 hz3
  have k4 := P4.kept_344 h.scope h.reads O hB4 d4 ho4
  obtain ⟨o5, ho5, hz5⟩ := k4.next ho4 hz4
  -- number 345: the lookup on the digits, with its quiet step
  obtain ⟨Lk, b, b', h1, h2, hb', hla⟩ := IM.k3_of h.scope h.reads O 24 (by decide) true
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope h.scope h.reads O (by decide) _] at h3
  obtain rfl : b = B5 := Option.some.inj (h3.symm.trans hB5)
  obtain ⟨e4, eN, -⟩ := Meaning.scope_plans h.scope h.reads O.public
  have hH : K3.isHead Bs'.G₀.W 24 = true := by
    unfold K3.isHead
    rw [e4, eN]
    rfl
  have hpc : (IM.k3Place 24 true).piece = K3.pieceAt Bs'.G₀.W 24 true := by
    unfold K3.pieceAt
    rw [hH]
    rfl
  obtain ⟨P, sent, laid, n, gs', m, hP, hk, hq⟩ := statedYesHeadAt _ _ _ _ _ _ _ b' hb'
    (IM.plan_alone O h.laid.planOk h1 h2 hla) 24 rfl hpc hH s345 sF r5 g5
    ((IM.k3_yes hla s345 sF r5 g5).1 d5).1
  obtain ⟨p, hp, hsh, hfirst⟩ := digits_place h.scope h.reads O.public
  obtain rfl : p = P := Option.some.inj (hp.symm.trans hP)
  -- the ledger in front of it, and behind
  obtain ⟨F, x, hF, hn, em, hL⟩ := decide_left_some (K3.seatDigits _) _ laid sent p []
    (K3.seatDigits_reads _) _ hsh Reading.gl p.lm s345 m _ _ hk
  have hnx : F.next = p.first := decide_first (K3.seatDigits _) _ laid sent p [] s345 m _ _ F hF hk
  have hF5 : s345.fork? = some F := hF
  have eF : o5.F = F := by
    cases hop5 : o5.opened with
    | false => simp [S.fork?, ho5, hop5] at hF5
    | true => simpa [S.fork?, ho5, hop5] using hF5
  obtain ⟨rs', L⟩ := hL (eF ▸ hz5)
  have hsome : s345.fork?.isSome = true := by
    rw [hF5]
    rfl
  have hm : m.fork? = some x.2 := by
    rw [em]
    exact seatDigits_keeps _ _ _ _ hsome hn
  obtain ⟨a1, _, _, _, claim, ha1, hop1, _, _, _, _, rfl⟩ := quietHead_form Bs'.G₀.W hq
  obtain rfl := Here.head.inj ha
  have e1 : a1.F = x.2 := by simpa [S.fork?, ha1, hop1] using hm
  -- the numbers
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs'.G₀ := (IM.base_made hB).2.2.1
  have l1 : (K11.parOf Zp Bs'.G₀).lay.lk = 18 := by
    rw [← hlay_at hG]
    exact (LT28.K11Tests.m0lk_in_scope h.scope h.pubOne).2
  have l2 := LT28.K11Tests.slots_in_scope h.scope h.reads h.pubOne hG
  have l3 := (plan_in_scope h.scope h.reads O.public).elems
  have l4 := L.padLeft.next
  show a1.F.next + 2 * (K11.parOf Zp Bs'.G₀).lay.lk + 3 = (K11.parOf Zp Bs'.G₀).nMsg
  rw [l1, l2, e1, l4, hnx, hfirst, l3]

end Johnson.Desc.First.ForkMerge.Front

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Front.statedYesHeadAt
#print axioms Johnson.Desc.First.ForkMerge.Front.countRaw
