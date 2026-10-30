-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/LiveOfYes.lean: CONDITIONAL.

What is here. THE TWO HALVES JOINED AT K4's OWN BLOCK. (What K4 is: the head of
Law/Live/NzOfStep.lean; what a mark is, when it is silent, and what a fall is: the head of
Law/MarkWide.lean.) (1) `k4_yes_tapeLive`: where K4's block says yes at the carried state
(`blockAtS`, Johnson/Desc/First/K4/AtS.lean), its hearing has returned at the tape `paired rs
(entries …)` (the library's `blockAtS_hears`, Johnson/Desc/First/K4/AtSHears.lean), AND THAT VERY
TAPE MEETS `TapeLive` (`k4_tapeLive`, Law/Live/TapeOfMark.lean), if a list `own` of challenges
shows the elements that the rounds rs show (hown), the words of a round's one drawn element lie
below the prime (hok), the wider mark is silent at `own` (hM), `k4CoinZero` is silent there (hC),
and the elements drawn by the rule that never gives 0 are not 0 (hNZ). (2) `k4_live_of_yes`: so the
three ends of `k4_live` (Law/Live/Whole.lean) stand at what K4's block has laid into the state
behind it: every slot from the next free number of the ledger in front of K4's block (a.F) up to,
AND WITHOUT, the merge's own slot is live in K4's two lists of forms; so is every slot on which the
lookup's closing form has a coefficient that is not 0; and the next free number of the ledger
behind the hearing is the one behind the merge's own slot. Statements with their proofs: the proofs
are calls of the laws named.

  `k4_yes_tapeLive`   **a yes of K4's block: the hearing's return, and `TapeLive` at its tape.**
  `k4_live_of_yes`   **the three ends of `k4_live` at what K4's block has laid into the state.**

Called. Of the library: `blockAtS_hears` (Johnson/Desc/First/K4/AtSHears.lean). Of K4's own laws:
`k4_tapeLive` (Law/Live/TapeOfMark.lean) · `k4_live` (Law/Live/Whole.lean).

Kin. THE THIRD END, «the next free number behind the hearing is the one behind the merge's own
slot», IS THE LIBRARY's `merge_last` (Johnson/Road/K4/MergeBelow.lean) WITH THE EQUATION's SIDES
EXCHANGED: that law takes hF and the hearing's return alone: neither `TapeLive` nor any hypothesis
on the draws. It stands here because `k4_live` ends in it. The same file's `mergeBelow_kept` has it
under the library's `KeptAtS`, for what the state behind holds.

Not shown here. THAT THE HYPOTHESES HOLD AT ANY RUN: this file gives no example of the hypotheses
together; its writers know of none that has been through Lean. A BLOCK IS SHOWN ITS ROUNDS WITHOUT
THE SEALED DIGEST: so h comes at rs := the member's rounds under `noDigest`, and `own` is the list
of the challenges there as the view has them (`Fmt.View`: what the verifier is shown of a proof):
`k4_own_noDigest` (Law/Live/TapeOfMark.lean) gives hown at these two. hok IS NOT GIVEN BY THE
BLOCK's YES; who gives it: Law/Live/OkTyped.lean; hNZ follows from hok and the first test of the
step that shows the block its rounds: Law/Live/NzOfStep.lean; neither is called here: WITH BOTH
CALLED, AND hown: `k4_live_of_yes_words` (Law/Live/TapeOfWords.lean). hC IS KEPT AS A HYPOTHESIS
HERE THOUGH THE HEARING HAS RETURNED: it follows from h: that the element which the hearing tests
is the one that round number `k4CoinRound` of the tape drew is typed in Law/Live/CoinOfYes.lean
(`k4_coin_of_yes`), which imports this file. THE EVENT OF hC IS NOT SAVED BY THAT: IT STANDS INSIDE
h. The fall `k4Fall`'s silence gives hC too. (2) takes besides: ha and hfo, which name the state's
part in front and what the lookup has returned there; hF, hfree and N on that ledger and that
return, as `k4_live` does; hll and hLam on the layout (Law/Live/AtFull.lean has both at the full
size, CONDITIONAL, and not at the public data at which K4's hearing runs; Law/Live/AtBase.lean has
both at `Bs.G₀.W.layers`, under the library's `P5J.AtMgA` and hB (`ProofFile.baseOf` returns Bs at the
public part)); hy and hlf on the caller's forms. The public data Qk are tied to the place's
parameters by three equations (eP, ehp, eg). The merge's own slot, and the lookup's planes:
Law/Live/AtYes.lean. Nothing on what a form is worth.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.TapeOfMark
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.Whole
import Johnson.Desc.First.K4.AtSHears

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Live
open OnBytes.K.Kc (paired)
open OnBytes.Desc.First.K4 (Par blockAtS blockAtS_hears hear engFl)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc.First (S LayOwn)

/-- CONDITIONAL: on h, eP, ehp, eg, hown, hok, hM, hC and hNZ. **A YES OF K4's BLOCK: THE HEARING's
RETURN, AND `TapeLive` AT ITS TAPE.** -/
theorem k4_yes_tapeLive {p : Par} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (h : (blockAtS p).decide s rs cols = .ok s')
    (Qk : K4Pub) (eP : Qk.P = p.P) (ehp : Qk.hp = p.hp) (eg : Qk.g = p.g)
    (own : List Fmt.Drawn)
    (hown : ∀ n : Nat, (rs[n]?).map (·.drawn.elems) = (own[n]?).map (·.elems))
    (hok : ∀ r ∈ rs, ∀ t, r.drawn.elems = [t] → Fmt.Fld.two.okE t = true) {fr : List Fmt.Drawn}
    (hM : (k4MarkWide Qk).test fr own = none) (hC : k4CoinZero Qk own = none)
    (hNZ : ∀ (i : Nat) (d : OnBytes.Desc.First.K4.Rd) (r : Fmt.RoundView),
      (OnBytes.Desc.First.K4.rounds Qk.P Qk.hp Qk.g)[i]? = some d → d.notZero ≠ 0 →
      rs[i]? = some r → ∀ t ∈ r.drawn.elems, OnBytes.Slice.toE t ≠ 0) :
    ∃ (a : LayOwn) (fo : OnBytes.Model.Forest.Heard) (o : OnBytes.Model.Layer.Own)
      (G : OnBytes.Model.Fork),
      s.here = .lay a ∧ a.fo = some fo ∧
      hear engFl { p.P with tokv := s.tokv } p.hp p.g fo a.F
        (paired rs (OnBytes.Desc.First.K4.entries p.P p.hp p.g)) = some (o, G, []) ∧
      s' = { s with here := .lay { a with F := G, own := some o }, rowsOwed := none } ∧
      TapeLive (paired rs (OnBytes.Desc.First.K4.entries p.P p.hp p.g)) := by
  obtain ⟨a, fo, o, G, h1, -, h3, h4, -, h6, h7⟩ := blockAtS_hears h
  refine ⟨a, fo, o, G, h1, h3, h6, h7, ?_⟩
  have T := k4_tapeLive Qk rs (by rw [eP, ehp, eg]; exact h4) own hown hok hM hC hNZ
  rw [eP, ehp, eg] at T
  exact T

/-- CONDITIONAL: on the hypotheses of `k4_yes_tapeLive`, and on ha, hfo, hF, hfree, N, hll, hLam, hy
and hlf. **THE THREE ENDS OF `k4_live` AT WHAT K4's BLOCK HAS LAID INTO THE STATE.** -/
theorem k4_live_of_yes {p : Par} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (h : (blockAtS p).decide s rs cols = .ok s')
    (Qk : K4Pub) (eP : Qk.P = p.P) (ehp : Qk.hp = p.hp) (eg : Qk.g = p.g)
    (own : List Fmt.Drawn)
    (hown : ∀ n : Nat, (rs[n]?).map (·.drawn.elems) = (own[n]?).map (·.elems))
    (hok : ∀ r ∈ rs, ∀ t, r.drawn.elems = [t] → Fmt.Fld.two.okE t = true) {fr : List Fmt.Drawn}
    (hM : (k4MarkWide Qk).test fr own = none) (hC : k4CoinZero Qk own = none)
    (hNZ : ∀ (i : Nat) (d : OnBytes.Desc.First.K4.Rd) (r : Fmt.RoundView),
      (OnBytes.Desc.First.K4.rounds Qk.P Qk.hp Qk.g)[i]? = some d → d.notZero ≠ 0 →
      rs[i]? = some r → ∀ t ∈ r.drawn.elems, OnBytes.Slice.toE t ≠ 0)
    {a : LayOwn} {fo : OnBytes.Model.Forest.Heard} (ha : s.here = .lay a) (hfo : a.fo = some fo)
    (hF : OnBytes.PscRun.Sized a.F) (hfree : ∀ j, a.F.next ≤ j → ¬ OnBytes.PscRun.Filled a.F j)
    (N : _root_.Fo.Tp.PadNames fo a.F) (hll : p.P.y.h.ll - 1 = 1) (hLam : p.P.y.LamM ≤ 2) :
    ∃ (o : OnBytes.Model.Layer.Own) (G : OnBytes.Model.Fork),
      s' = { s with here := .lay { a with F := G, own := some o }, rowsOwed := none } ∧
      ∀ (rows : Bool) (Q : OnBytes.Model.Layer.Pub) (U : OnBytes.Model.Fork)
        (lf : List OnBytes.Model.Aff), Q.y = p.P.y →
        VerifiableInference.Desc.K4Values.frontForms rows Q p.g o U = some lf →
        (∀ j, a.F.next ≤ j → j < o.wo.sFv → VerifiableInference.Desc.K9H.liveAt
          (VerifiableInference.Desc.First.K8.Honest.plainOf lf ++
            VerifiableInference.Desc.First.K8.Honest.layersBack o) j = true) ∧
        (∀ j, cf OnBytes.Model.Reading.gl fo.cEnd j ≠ 0 →
          VerifiableInference.Desc.K9H.liveAt
            (VerifiableInference.Desc.First.K8.Honest.plainOf lf ++
              VerifiableInference.Desc.First.K8.Honest.layersBack o) j = true) ∧
        G.next = o.wo.sFv + 1 := by
  obtain ⟨a', fo', o, G, h1, h3, h6, h7, T⟩ := k4_yes_tapeLive h Qk eP ehp eg own hown hok hM hC hNZ
  obtain rfl : a = a' := by
    have e := ha.symm.trans h1
    injection e
  obtain rfl : fo = fo' := Option.some.inj (hfo.symm.trans h3)
  exact ⟨o, G, h7, fun rows Q U lf hy hlf =>
    k4_live (P := { p.P with tokv := s.tokv }) hF hfree N h6 T hll hLam hy hlf⟩

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.k4_yes_tapeLive
#print axioms ProofFile.Honest.K4.Live.k4_live_of_yes
