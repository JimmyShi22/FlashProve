-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/CoinOfYes.lean: CONDITIONAL but for `tapeEps_paired`.

What is here. BEHIND A YES OF K4's OWN BLOCK, K4's FALL IS SILENT: `k4CoinZero`
(Honest/K4/Part.lean), the test of the fall at K4's own member, returns none at K4's challenges. The
verifier's hearing tests the same element by the same Bool: "not `isZeroE tT.p.eps`" in `hearTerms`
(OnBytes/Desc/First/K4/Hear.lean). This file types that the element which the hearing tests is the
first one that round number `k4CoinRound` of the tape drew. The steps: the yes holds a return of the
hearing at the tape of the block's rounds (`blockAtS_hears`, Johnson/Desc/First/K4/AtSHears.lean);
that return holds one of `hearNorms` and one of `hearTerms` at what `hearNorms` leaves
(`hear_parts`, OnBytes/Desc/First/K4/MergeClaims.lean); `hearNorms` leaves the tape from a written
number of rounds on (`hearNorms_tape`, OnBytes/Desc/First/K4/NormsTape.lean), and that number is
`k4CoinRound` (`k4CoinRound_eq`, Law/MarkWide.lean); `hearTerms` begins with a token sumcheck, whose
joining element is the first element drawn in the first round that it reads (`tscIn_heard`,
OnBytes/Desc/First/P1/Heard.lean), and goes on only where the program's test says that this element
is not 0.

  `tapeEps_paired`   the first element drawn in round number n of a tape made of rounds.
  `hearTerms_eps`   where `hearTerms` returns, the first element drawn in the first round that it
      reads is not 0 by the program's test.
  `k4_coin_of_yes`   **`k4CoinZero Qk own = none`, behind a yes of K4's block.**

Kin. THE LIBRARY HAS BOTH LAWS TURNED ROUND, AT A ROUND THAT IS WRITTEN OUT: `hearTerms_coin`
(Johnson/Desc/First/K4/Returns/Needs.lean): where the tape's first round bears the name "PSC
epsilon", sends two values and draws one element, and that element is 0 by the program's test,
`hearTerms` does not return; `hearTerms_eps` says it of any tape, from the return. `hear_coin` (the
same file): the like of the whole hearing, under premises on the ledger, on the tape in front, on
the plan's numbers and on what the lookup returned; `k4_coin_of_yes` takes none of these, starts at
the block's yes and ends in `k4CoinZero`'s letters. THE SAME WAY ROUND, from the hearing's return:
`own_callsG` (Johnson/Road/K4/OwnRecsG.lean) has the test's answer and the token sumcheck's return
at a cut of the tape written through `ksOf`, not by a round's number. `hearTerms_calls`
(OnBytes/Desc/First/K4/HearCalls.lean, beneath this file) gives, where `hearTerms` returns, the
token sumcheck's return and the test's answer: with `tscIn_heard` that is `hearTerms_eps`; it is not
called: the proof opens `hearTerms` anew, by the first lines of `hearTerms_KT`
(OnBytes/Desc/First/K4/HearLaws.lean), whose third clause is the same test's yes at the element as
it is laid, not as the tape has it. The two steps of `hearTerms_eps` (a token sumcheck's joining
element is `tapeEps` of its tape: `tscIn_heard`; the program's test on it) stand inside the proof of
the library's `tail_coin` (Johnson/Road/K4/OwnAt.lean), which takes the test's answer as a premise
and ends on another reading of the element. `tapeEps_cons` (OnBytes/Desc/First/P1/LevelLaw.lean) has
`tapeEps` at a tape's first round; `tapeEps_paired` has it at round number n of a tape made of
rounds.

Not shown here. THE HYPOTHESES ARE GIVEN NOWHERE HERE: h (the yes of `blockAtS p`: not of the
frame's member), eP and eg (the honest side's public data and group are the block's; its plan hp is
not asked), hown (number by number, the ELEMENTS of the challenges own are those of the block's
rounds: no more is tied). No mark, no clause on the tape and no premise on the ledger is asked. ONE
WAY: from a yes. THE EVENT IS NOT SAVED: IT STANDS INSIDE h: where the element is 0 there is no yes,
and the law is silent there; nothing is said on how often that is. WHOEVER SUMS SHARES MAY NOT DROP
THE FALL's (`k4CoinZeroShare`) ON THIS LAW's ACCOUNT. "NOT 0" IS THE PROGRAM's OWN BOOL, `isZeroE …
= false`: no premise on the words (below the prime) is asked, and of words that are not below the
prime nothing more is said; `k4CoinZero` reads the same Bool, so the end is exact. This file gives
no example of the hypotheses together; its writers know of none that has been through Lean.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.LiveOfYes
import OnBytes.Desc.First.K4.NormsTape
import OnBytes.Desc.First.K4.HearLaws
import OnBytes.Desc.First.K4.MergeClaims
import OnBytes.Desc.First.P1.Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Live

section Hearing
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc
open OnBytes.Desc.First.K4 (hearTerms engFl andThen_some)
open OnBytes.Desc.First.P1 (tscIn_heard tapeEps)

/-- The first element drawn in round number n of a tape made of rounds; the program's 0 where there
is no such round or it drew nothing. -/
theorem tapeEps_paired : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (n : Nat),
    tapeEps ((paired rs es).drop n) =
      ((rs[n]?).map fun r => (r.drawn.elems.map E.ofTriple).headD zeroE).getD zeroE
  | [], _, n => by simp [paired, tapeEps]
  | _ :: _, [], 0 => rfl
  | _ :: _, _ :: _, 0 => rfl
  | _ :: rs, [], n + 1 => tapeEps_paired rs [] n
  | _ :: rs, _ :: es, n + 1 => tapeEps_paired rs es n

/-- CONDITIONAL on the return. Where `hearTerms` returns, the first element drawn in the first round
that it reads is not 0 by the program's test. -/
theorem hearTerms_eps {P : OnBytes.Model.Layer.Pub} {H H' : OnBytes.Model.Layer.Heard}
    {F F' : OnBytes.Model.Fork} {t t' : OnBytes.K.Kc.Tape}
    (h : hearTerms engFl P H F t = some (H', F', t')) : isZeroE (tapeEps t) = false := by
  have h' : Fl.andThen (Fl.tscIn H.ztF P.y.h.lt (nEndT P.y) 1) (fun tT =>
      Fl.andThen (Fl.must (!isZeroE tT.p.eps)) (fun _ =>
        Fl.andThen (Fl.pscRow tT.p zeroE {}) (fun x =>
          Fl.ret ({ H with tT := some { tT with p := x.2 },
                           KT := x.1.scale (negE (invE tT.p.eps)) } :
            OnBytes.Model.Layer.Heard)))) F t =
      some (H', F', t') := h
  obtain ⟨tT, _, _, hts, h1⟩ := andThen_some h'
  obtain ⟨_, _, _, hm, _⟩ := andThen_some h1
  obtain ⟨-, -, -, -, -, -, -, -, e, -⟩ := tscIn_heard hts
  have b : (!isZeroE tT.p.eps) = true := (OnBytes.Desc.First.K4.must_some hm).1
  rw [e] at b
  cases hz : isZeroE (tapeEps t) with
  | false => rfl
  | true =>
    rw [hz] at b
    cases b

end Hearing

open OnBytes (E isZeroE zeroE)
open OnBytes.K.Kc (paired)
open OnBytes.Desc.First.K4 (Par blockAtS blockAtS_hears hear_parts hearNorms_tape entries k0)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.P1 (tapeEps)
open VerifiableInference.Desc.First (S LayOwn)

/-- CONDITIONAL on h, eP, eg and hown. **BEHIND A YES OF K4's BLOCK, THE TEST OF K4's FALL SAYS
NOTHING.** -/
theorem k4_coin_of_yes {p : Par} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (h : (blockAtS p).decide s rs cols = .ok s')
    (Qk : K4Pub) (eP : Qk.P = p.P) (eg : Qk.g = p.g)
    (own : List Fmt.Drawn)
    (hown : ∀ n : Nat, (rs[n]?).map (·.drawn.elems) = (own[n]?).map (·.elems)) :
    k4CoinZero Qk own = none := by
  obtain ⟨a, fo, o, G, -, -, -, -, -, h6, -⟩ := blockAtS_hears h
  obtain ⟨-, -, -, -, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, hN, hT, -⟩ :=
    hear_parts h6
  obtain ⟨F4, F7, F8, rhoI, vW, vP, gam, om, w0, wI, d0, dI, -, hd0, hPV, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, hu⟩ := hearNorms_tape hN
  have hd0' : d0.length = p.P.y.h.lt := hd0
  have hlen : (H1.PV.toList.take p.P.y.h.lt).length = p.P.y.h.lt := by
    rw [hPV]
    simp [hd0']
  have hu2 : u1 = (paired rs (entries p.P p.hp p.g)).drop
      (k0 p.g + p.P.rd.muV + 7 + ((H1.PV.toList.take p.P.y.h.lt).length + 3)) := hu
  rw [hlen] at hu2
  have en : k4CoinRound Qk = k0 p.g + p.P.rd.muV + 7 + (p.P.y.h.lt + 3) := by
    rw [k4CoinRound_eq]
    show k0 Qk.g + 2 + (Qk.P.rd.muV + 5) + (Qk.P.y.h.lt + 3) = _
    rw [eP, eg]
    omega
  have hz : isZeroE (tapeEps u1) = false := hearTerms_eps hT
  rw [hu2, ← en, tapeEps_paired] at hz
  have hq := hown (k4CoinRound Qk)
  cases ho : own[k4CoinRound Qk]? with
  | none =>
    have ho' : own[(starts Qk).getD 2 0]? = none := ho
    unfold k4CoinZero
    rw [ho']
  | some d =>
    have ho' : own[(starts Qk).getD 2 0]? = some d := ho
    rw [ho] at hq
    cases hr : rs[k4CoinRound Qk]? with
    | none =>
      rw [hr] at hq
      cases hq
    | some r =>
      rw [hr] at hq hz
      have he : r.drawn.elems = d.elems := Option.some.inj hq
      have hz' : isZeroE ((r.drawn.elems.map E.ofTriple).headD zeroE) = false := hz
      rw [he] at hz'
      unfold k4CoinZero
      rw [ho']
      cases hd : d.elems with
      | nil =>
        rw [hd] at hz'
        have z : isZeroE zeroE = true := rfl
        have hz'' : isZeroE zeroE = false := hz'
        rw [z] at hz''
        cases hz''
      | cons x xs =>
        rw [hd] at hz'
        have hx : isZeroE (E.ofTriple x) = false := hz'
        show (if isZeroE ((d.elems.head?.map E.ofTriple).getD OnBytes.oneE) then some _
          else none) = none
        rw [hd]
        refine if_neg ?_
        show ¬ isZeroE (E.ofTriple x) = true
        rw [hx]
        exact Bool.false_ne_true

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.tapeEps_paired
#print axioms ProofFile.Honest.K4.Live.hearTerms_eps
#print axioms ProofFile.Honest.K4.Live.k4_coin_of_yes
