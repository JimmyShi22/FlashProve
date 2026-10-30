-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/TupleOfAt.lean: **FROM WHAT THE GAME CONCLUDES (TupleAt: ONE WITNESS) TO K12's FILES' TUPLE FORM (ONE MESSAGE A MEMBER).** One statement; its proof is the first arm of tuple_words_or_few
(Johnson/Desc/K12/Law/TupleWords.lean), line by line, WITH TupleAt IN THE PLACE OF THE CALL OF tuple_or_few: words_tuple · allSay_congr. NO NEW MATHEMATICS.
  tupleAt_words   TupleAt h t L S G rd dM dF os e and the premises of words_tuple give: ∃ c (one message a member), all rows that the test takes in say their claims of wordsT D c (words built from c alone) ∧ each c j is a candidate of the member's word as
                  sent (strOf), at any seed at which Send.form gives the record's sample row.
What for: the seam's core at the shared chain's two proximity tests (Johnson/Desc/Sound/SeamCore.lean).

Limits: those of TupleWords.lean: hS | hQ (the yes of siteL and of sampleL at every member) and hfit (the radius against each member's) are premises. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Law.TupleWords
import Johnson.Desc.K12.Law.TupleAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Run
open H2K.First (Seat1 Plain gpL gpG gpP good_of_ok oM oZ skM skZ Good Made entered)
open H2K.Pub (sgOf)

theorem tupleAt_words {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12}
    {t : T12} {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D) (S : Statement) (g : Nat)
    (G : Group) (rd : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD)
    (os : ∀ i, (wRound (dM i)).Orc) (e : ℕ) (hJ : (sgOf a).StageJ e)
    (ht : combineAt t.st g ⟨L, runRows S G⟩ = true)
    (hk : L.k = (sgOf a).h + (sgOf a).g) (hh : L.h = (sgOf a).h)
    (e0s : Fin D.mems.length → ℕ)
    (hS : ∀ j : Fin D.mems.length, ok (siteL D.st.codes a (D.mems.get j)) = true)
    (hQ : ∀ j : Fin D.mems.length, ∃ x, D.st.oracles[(D.mems.get j).id]? = some x ∧
      ok (sampleL D.st.codes (D.mems.get j) x) = true)
    (hfit : ∀ j : Fin D.mems.length,
      e < (e0s j + 1) * 2 ^ ((sgOf a).C.a - aOf D.st.codes (D.mems.get j).sh))
    (hT : TupleAt h t L S G rd dM dF os e) :
    ∃ c : ∀ j : Fin D.mems.length, (portCode D.st.codes (D.mems.get j).sh).J → GE,
      AllSay rdE t.st (runRows S G).toList (wordsT D c) ∧
      ∀ (j : Fin D.mems.length) (x : OnBytes.Oracle),
        D.st.oracles[(D.mems.get j).id]? = some x →
        ∀ (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
        Send.form D.st.codes (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 →
        x.sampleRows.toList = [{ row0 with target := tt }] →
        bitsZ D.st.codes (D.mems.get j).sh ≤ seed.z.length → (β : GE) = readE seed.beta →
        (portOmZ D.st.codes (D.mems.get j).sh (e0s j)).Cand
          (strOf D.st.codes (D.mems.get j).sh (e0s j) (layOf (D.mems.get j)) (dM j) (os j))
          ((readP (bitsZ D.st.codes (D.mems.get j).sh) seed.z, β), fun _ => readE tt) (c j) := by
  obtain ⟨w, hn, hall, hc⟩ := hT
  refine ⟨fun j q => w.1
    ((siteOf D.st.codes a (D.mems.get j) (e0s j) (oM D.L j.val) (oZ D.L j.val) (hS j)).atJ q),
    ?_, fun j x hx seed row0 tt β hform hrows hzl hβ => ?_⟩
  · exact (allSay_congr t.st _ _ _ (words_tuple h hm g rd dM dF os e hJ _ ht hk hh e0s hS hQ w
      hn)).1 hall
  · obtain ⟨x', hx', hq⟩ := hQ j
    rw [hx] at hx'
    cases hx'
    exact hc j (e0s j) (hS j) x hx hq (hfit j) seed row0 tt β hform hrows hzl hβ

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.tupleAt_words
