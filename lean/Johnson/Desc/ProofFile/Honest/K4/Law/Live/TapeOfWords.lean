-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/TapeOfWords.lean: CONDITIONAL.

What is here. THE PIECES JOINED, SO THAT LEAN HAS CHECKED THAT EACH GIVER's CONCLUSION IS THE
HYPOTHESIS THAT IT IS MEANT FOR. (What K4 is: the head of Law/Live/NzOfStep.lean; what a mark is,
when it is silent, and what a fall is: the head of Law/MarkWide.lean.) `k4_tapeLive`
(Law/Live/TapeOfMark.lean) takes six hypotheses; of three of them the givers are called here (hfit
and hC have givers too, from a yes of K4's block: that file's head): hown (`k4_own_noDigest`, the
same file), hok (`k4_hok_of_words` with `k4_hok_noDigest`, Law/Live/OkTyped.lean) and hNZ
(`k4_nz_of_step`, Law/Live/NzOfStep.lean). HERE THEY ARE CALLED TOGETHER, at one list `mine` of
rounds as a step is handed them: (1) `k4_tapeLive_of_words`: the tape that K4's block makes of
`mine` without the sealed digest meets `TapeLive`, where the verifier's table fits these rounds
(hfit), `roundsFit` holds at K4's declared rounds and `mine` (hrf: the first test of a step's yes:
`k4_hrf_of_step`), every word of every drawn element of `mine` is below `fieldPrimeWord` (hw), and the
wider mark and `k4CoinZero` are silent at the challenges of `mine` as the view has them (hM, hC).
(2) `k4_live_of_yes_words`: the same three called in `k4_live_of_yes` (Law/Live/LiveOfYes.lean):
its end, letter for letter, from a yes of K4's block at `mine` without the digest. Statements with
their proofs: the proofs are calls of the laws named.

  `k4_tapeLive_of_words`   **the tape meets `TapeLive`: five hypotheses at one list of rounds.**
  `k4_live_of_yes_words`   **the three ends of `k4_live`, with hown, hok and hNZ called.**

Called, all of K4's own laws: `k4_hok_of_words`, `k4_hok_noDigest` (Law/Live/OkTyped.lean) ·
`k4_nz_of_step` (Law/Live/NzOfStep.lean) · `k4_own_noDigest`, `k4_tapeLive`
(Law/Live/TapeOfMark.lean) · `k4_live_of_yes` (Law/Live/LiveOfYes.lean).

Kin. The third end of (2) is the library's `merge_last` (Johnson/Road/K4/MergeBelow.lean) with the
equation's sides exchanged, which takes hF and the hearing's return alone:
Law/Live/LiveOfYes.lean's head.

Not shown here. THAT THE HYPOTHESES HOLD AT ANY RUN: this file gives no example of the hypotheses
together; its writers know of none that has been through Lean. hw: by reading (Lean has not checked
it) the frame's test on challenges (`drawFit`, Honest/Frame.lean) asks it of every round; the cut
from a run's whole list to `mine` is not typed; WHERE A SUB-PROTOCOL's OWN SIDE IS PROVED NO CUT IS
NEEDED: `Good.plays` and `Good.acc` (Honest/Side.lean) take `drawsFit` at the member's own declared
rounds as a premise and speak of that member's own step. hrf ASKS ALSO WHAT IS SENT: the test on
challenges does not give that clause; a step's yes gives hrf whole (`k4_hrf_of_step`, under hd: the
block declares K4's rounds), and so, by reading, does a run's own book-keeping (`chain_kept`,
Honest/Law/Run.lean), cut. In (2) hC follows from h (`k4_coin_of_yes`, Law/Live/CoinOfYes.lean): it
is kept as a hypothesis here; THE EVENT OF hC IS NOT SAVED BY THAT: IT STANDS INSIDE h. hM and hC
stand at ONE list, `mine.map (·.drawn)`: that is the term which the frame hands a fall; a mark is
handed a cut of the bare list of challenges: that the two are one list is owed by the caller. What
else (2) takes: Law/Live/LiveOfYes.lean's head.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.LiveOfYes
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.NzOfStep
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.OkTyped

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Live
open OnBytes.K.Kc (paired)
open OnBytes.Desc.First.K4 (Par blockAtS)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (roundsFit noDigest fieldPrimeWord)
open VerifiableInference.Desc.First (S LayOwn)

/-- CONDITIONAL: on hfit, hrf, hw, hM and hC. **THE TAPE THAT K4's BLOCK MAKES OF THE ROUNDS WITHOUT
THE SEALED DIGEST MEETS `TapeLive`.** -/
theorem k4_tapeLive_of_words (Q : K4Pub) (mine : List Fmt.RoundView)
    (hfit : OnBytes.Desc.First.K4.fitsAll (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)
      (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g) (mine.map noDigest) = true)
    (hrf : roundsFit ((OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g).map fun e => { entry := e })
      mine = true)
    (hw : ∀ r ∈ mine, ∀ x ∈ r.drawn.elems, x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧ x.2.2 < fieldPrimeWord)
    {fr : List Fmt.Drawn} (hM : (k4MarkWide Q).test fr (mine.map (·.drawn)) = none)
    (hC : k4CoinZero Q (mine.map (·.drawn)) = none) :
    TapeLive (paired (mine.map noDigest) (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)) := by
  have hok := k4_hok_of_words mine hw
  have hNZ := k4_nz_of_step Q mine hrf hok
  have hok' := k4_hok_noDigest mine hok
  have hown := k4_own_noDigest mine
  exact k4_tapeLive Q (mine.map noDigest) hfit _ hown hok' (fr := fr) hM hC hNZ

/-- CONDITIONAL: on h, eP, ehp, eg, hrf, hw, hM, hC, ha, hfo, hF, hfree, N, hll and hLam, and behind
them on hy and hlf. **THE THREE ENDS OF `k4_live` AT WHAT K4's BLOCK HAS LAID INTO THE STATE, WITH
hown, hok AND hNZ CALLED.** -/
theorem k4_live_of_yes_words {p : Par} {s s' : S} {mine : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))}
    (h : (blockAtS p).decide s (mine.map noDigest) cols = .ok s')
    (Qk : K4Pub) (eP : Qk.P = p.P) (ehp : Qk.hp = p.hp) (eg : Qk.g = p.g)
    (hrf : roundsFit ((OnBytes.Desc.First.K4.entries Qk.P Qk.hp Qk.g).map fun e => { entry := e })
      mine = true)
    (hw : ∀ r ∈ mine, ∀ x ∈ r.drawn.elems, x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧ x.2.2 < fieldPrimeWord)
    {fr : List Fmt.Drawn} (hM : (k4MarkWide Qk).test fr (mine.map (·.drawn)) = none)
    (hC : k4CoinZero Qk (mine.map (·.drawn)) = none)
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
  have hok := k4_hok_of_words mine hw
  have hNZ := k4_nz_of_step Qk mine hrf hok
  have hok' := k4_hok_noDigest mine hok
  have hown := k4_own_noDigest mine
  exact k4_live_of_yes h Qk eP ehp eg _ hown hok' (fr := fr) hM hC hNZ ha hfo hF hfree N hll hLam

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.k4_tapeLive_of_words
#print axioms ProofFile.Honest.K4.Live.k4_live_of_yes_words
