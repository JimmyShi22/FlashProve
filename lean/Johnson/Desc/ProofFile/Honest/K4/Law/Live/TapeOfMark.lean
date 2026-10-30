-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/TapeOfMark.lean: CONDITIONAL but for `paired_mem`,
`k4_nz_row` and `k4_own_noDigest`.

What is here. FROM THE DRAWS TO THE TAPE. (What K4 is: the head of Law/Live/NzOfStep.lean; what a
mark is, when it is silent, and what a fall is: the head of Law/MarkWide.lean.) `TapeLive t`
(Law/Live/PscLive.lean) asks of every round of a tape that holds just one drawn element that the
element reads as not 0, and as not 1 where the round's name is that of a batching element or of a
joining point. Here: THE TAPE THAT K4's BLOCK HANDS TO ITS HEARING, `paired rs (entries …)`
(OnBytes/K/Kc/Laws.lean), MEETS IT (`k4_tapeLive`), where the verifier's table of K4's rounds fits
the rounds rs (hfit), a list `own` of challenges shows, number by number, the elements that the
rounds rs show (hown; so the two lists are equally long), the words of a round's one drawn element
lie below the prime (hok), the wider mark (Law/MarkWide.lean) is silent at `own` (hM), K4's test on
the one element that the mark leaves out is silent there (hC: `k4CoinZero`, Honest/K4/Part.lean),
and the elements that are drawn by the rule that never gives 0 are not 0 (hNZ). WHY `own` IS A
LETTER OF ITS OWN: a block is shown its rounds WITHOUT THE SEALED DIGEST (`noDigest`,
Johnson/Desc/Block.lean), while a mark's and a fall's tests are handed the challenges as the view
has them (`Fmt.View`: what the verifier is shown of a proof): two lists, with the same elements:
`k4_own_noDigest` gives hown at these two. A round of the tape with just one drawn element is, by
hfit, a row that draws one element: if by the plain rule and not the round that is left out, it is
listed, and silence gives «neither 0 nor 1» (`k4Wide_silent_ne`, Law/MarkWideElem.lean); at the
round that is left out hC gives «not 0», and its name asks no more; a row of the never-zero rule
bears the name `.pscY` (`k4_nz_row`), hNZ gives «not 0», and its name asks no more. A statement
on lists of rounds and challenges: no hearing, no state, no prover is in it. Statements with their
proofs.

  `paired_mem`   a member of the tape is a round with its entry, at one number.
  `k4_nz_row`   the table's rows of the never-zero rule: their name and their two numbers.
  `k4_coin_ne`   where `k4CoinZero` is silent, the element of the round that is left out is not 0.
  `k4_own_noDigest`   the rounds without the digest show the elements of the view's challenges.
  `k4_tapeLive`   **the tape meets `TapeLive`.**

Called. Of the library: `fitsAll_rows` (Johnson/Desc/First/K4/BlockLaws.lean) · `ofE_toE`
(Johnson/Desc/K8/Honest/ChiTyped.lean) · `isZeroE_iff`, `readE_ofTriple`
(OnBytes/Slice/ProgField.lean) · `okE_triple` (OnBytes/Field/ExtEq.lean). Of K4's own laws:
`k4CoinRound_row`, `k4WideRounds_iff` (Law/MarkWide.lean) · `k4Wide_silent_ne`
(Law/MarkWideElem.lean).

Kin. `paired_mem`: the library has what the same tape holds, number by number, where all items are
elements (`paired_holds`, Johnson/Desc/First/Tape/TapePaired.lean), the tape's step (`paired_cons`,
OnBytes/K/Kc/Kit.lean) and another law by the same three arms (`small_paired`,
Johnson/Road/K4/OwnCoin.lean); `tapeEps_paired` (Law/Live/CoinOfYes.lean) has the first element that
round number n of the tape drew. None of these four ends in a member's round and entry at one
number. `k4_own_noDigest`: round by round the library has that `noDigest` leaves the drawn elements
(`drawn_noDigest`, Johnson/Desc/K14/Law/StepsSound.lean and Johnson/Desc/Key/Laid/Draws.lean; the
second clause of `noDigest_alike`, Johnson/Desc/First/Tape/TapeHolds.lean); here it is said of two
lists, number by number, in hown's letters. `k4_coin_ne` goes from a silent test to «not 0»; the
step from the program's test to «not 0», at words below the prime, is the library's `gl_ne_of_word`
(Johnson/Road/K4/OwnCoin.lean) in other letters; from «not three words 0» to «not 0», at words below
the prime: `k4_words_ne` (Law/Live/NzOfStep.lean), by the library's `readsNz_gl`
(Johnson/Desc/First/Att/K05Nz.lean); the like: `gl_ne_zero` (OnBytes/Tie/Pv/Psc/Run/NzCtx.lean).

Not shown here. THAT THE SIX HYPOTHESES HOLD AT ANY RUN: THIS FILE GIVES NO EXAMPLE OF THEM
TOGETHER; ITS WRITERS KNOW OF NONE THAT HAS BEEN THROUGH LEAN. WHO WOULD GIVE THEM, by reading:
hfit: a yes of K4's block (the library's `blockAtS_hears`, Johnson/Desc/First/K4/AtSHears.lean,
fourth clause) · hown: `k4_own_noDigest` · hM and hC: where the mark and the fall `k4Fall` are
silent; that the list which the frame hands them is `own` is not typed; hC also from a yes of K4's
block (`k4_coin_of_yes`, Law/Live/CoinOfYes.lean, above this file): THE EVENT OF hC IS NOT SAVED BY
THAT: IT STANDS INSIDE THE YES · hok AND hNZ ARE NOT GIVEN HERE, AND NOT BY THE YES OF K4's OWN
`decide`: its tests on the stretch ask neither. WHO GIVES THEM: Law/Live/OkTyped.lean (hok: three
doors off the library's laws, and a carrier) and Law/Live/NzOfStep.lean (hNZ); all joined:
Law/Live/TapeOfWords.lean. hok is asked once at the front of the verifier's whole walk
(OnBytes/Desc/First/K4/Hear.lean's head), which does not help where no yes of that walk is in hand;
the library has it at every round of the view of a written transcript (`rvT_okE`,
Johnson/Desc/First/Att/K05SeamOut.lean). hNZ is the format's rule for such a draw (`drawNZ`,
Fmt/Rules6.lean), which is on words (not three words 0), together with words below the prime: THE
STEP THAT SHOWS A BLOCK ITS ROUNDS (`Block.step`, Johnson/Desc/Block.lean) ASKS THE WORDS' HALF
ITSELF (`drawsMarkedNonzeroHaveNonzeroWords`); with hok that is hNZ: Law/Live/NzOfStep.lean. At a typed challenge the library has
the general law on what is shown (`H2K.Fit.fitsDrawn`, Johnson/Desc/K12/Law/FitWritten.lean): not
called. What `TapeLive` gives: Law/Live/Whole.lean.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.PscLive
import Johnson.Desc.ProofFile.Honest.K4.Law.MarkWideElem
import Johnson.Desc.First.K4.BlockLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Live
open OnBytes (E isZeroE)
open OnBytes.K.Kc (paired flatOf)
open OnBytes.Desc.First.K4 (masked layerRds fitsAll_rows entryOf)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc.First.K8.Honest (ofE_toE)

/-- A member of the tape is a round with its entry, at one number. -/
theorem paired_mem : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (x : OnBytes.K.Kc.FlatRound),
    x ∈ paired rs es → ∃ (i : Nat) (r : Fmt.RoundView), rs[i]? = some r ∧ x = flatOf r (es[i]?)
  | [], _, x, h => by
    have h' : x ∈ ([] : List OnBytes.K.Kc.FlatRound) := h
    cases h'
  | r :: rs, [], x, h => by
    have h' : x ∈ flatOf r none :: paired rs [] := h
    rcases List.mem_cons.1 h' with e | h2
    · exact ⟨0, r, List.getElem?_cons_zero, by rw [e, List.getElem?_nil]⟩
    · obtain ⟨i, r', hr, e⟩ := paired_mem rs [] x h2
      exact ⟨i + 1, r', by rw [List.getElem?_cons_succ]; exact hr, by
        rw [e, List.getElem?_nil, List.getElem?_nil]⟩
  | r :: rs, e0 :: es, x, h => by
    have h' : x ∈ flatOf r (some e0) :: paired rs es := h
    rcases List.mem_cons.1 h' with e | h2
    · exact ⟨0, r, List.getElem?_cons_zero, by rw [e, List.getElem?_cons_zero]⟩
    · obtain ⟨i, r', hr, e⟩ := paired_mem rs es x h2
      exact ⟨i + 1, r', by rw [List.getElem?_cons_succ]; exact hr, by
        rw [e, List.getElem?_cons_succ]⟩

/-- The table's rows that draw by the rule that never gives 0: the name of the extra round of a
sumcheck; one element is drawn, and that one by this rule. -/
theorem k4_nz_row (P : OnBytes.Model.Layer.Pub) (hp : OnBytes.Model.Layer.HPlan2) (g : Nat) :
    ∀ d ∈ OnBytes.Desc.First.K4.rounds P hp g, d.notZero ≠ 0 →
      d.name = .pscY ∧ d.drawn = 1 ∧ d.notZero = 1 := by
  intro d hd hn
  unfold OnBytes.Desc.First.K4.rounds at hd
  simp only [layerRds, masked, List.mem_append, List.mem_cons, List.mem_replicate,
    List.not_mem_nil, or_false] at hd
  cases hg : (g == 0) <;> simp only [hg, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  all_goals
    casesm* _ ∨ _
    all_goals
      obtain ⟨-, rfl⟩ := hd
      first
        | exact ⟨rfl, rfl, rfl⟩
        | exact absurd rfl hn

/-- CONDITIONAL: on hC, ho, ht and hk. Where `k4CoinZero` is silent, the element of the round that
the wider mark leaves out is not 0. -/
theorem k4_coin_ne (Q : K4Pub) {own : List Fmt.Drawn} (hC : k4CoinZero Q own = none)
    {dr : Fmt.Drawn} (ho : own[k4CoinRound Q]? = some dr) {t : Fmt.Ext3} (ht : dr.elems = [t])
    (hk : Fmt.Fld.two.okE t = true) : OnBytes.Slice.toE t ≠ 0 := by
  intro e0
  have hz : isZeroE (E.ofTriple t) = true :=
    (OnBytes.Slice.isZeroE_iff _ (by rw [OnBytes.okE_triple]; exact hk)).2
      ((OnBytes.Slice.readE_ofTriple t).trans e0)
  have ho' : own[(starts Q).getD 2 0]? = some dr := ho
  unfold k4CoinZero at hC
  rw [ho'] at hC
  simp [ht, hz] at hC

/-- The rounds without the sealed digest show, number by number, the elements of the challenges as
the view has them. -/
theorem k4_own_noDigest (mine : List Fmt.RoundView) (n : Nat) :
    ((mine.map VerifiableInference.Desc.noDigest)[n]?).map (·.drawn.elems) =
      ((mine.map (·.drawn))[n]?).map (·.elems) := by
  rw [List.getElem?_map, List.getElem?_map]
  cases mine[n]? <;> rfl

/-- CONDITIONAL: on hfit, hown, hok, hM, hC and hNZ. **THE TAPE THAT K4's BLOCK HANDS TO ITS HEARING
MEETS `TapeLive`.** -/
theorem k4_tapeLive (Q : K4Pub) (rs : List Fmt.RoundView)
    (hfit : OnBytes.Desc.First.K4.fitsAll (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)
      (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g) rs = true)
    (own : List Fmt.Drawn)
    (hown : ∀ n : Nat, (rs[n]?).map (·.drawn.elems) = (own[n]?).map (·.elems))
    (hok : ∀ r ∈ rs, ∀ t, r.drawn.elems = [t] → Fmt.Fld.two.okE t = true) {fr : List Fmt.Drawn}
    (hM : (k4MarkWide Q).test fr own = none) (hC : k4CoinZero Q own = none)
    (hNZ : ∀ (i : Nat) (d : OnBytes.Desc.First.K4.Rd) (r : Fmt.RoundView),
      (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)[i]? = some d → d.notZero ≠ 0 →
      rs[i]? = some r → ∀ t ∈ r.drawn.elems, OnBytes.Slice.toE t ≠ 0) :
    TapeLive (paired rs (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)) := by
  intro x hx e he
  obtain ⟨i, r, hr, rfl⟩ := paired_mem _ _ _ hx
  obtain ⟨-, hl2, hrows⟩ := fitsAll_rows hfit
  have hi : i < (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g).length := by
    rw [← hl2]
    exact (List.getElem?_eq_some_iff.1 hr).1
  obtain ⟨d, hd⟩ : ∃ d, (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)[i]? = some d :=
    ⟨_, List.getElem?_eq_getElem hi⟩
  have hen : (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)[i]? = some (entryOf d) := by
    unfold OnBytes.Desc.First.K4.entries
    rw [List.getElem?_map, hd]
    rfl
  obtain ⟨-, -, -, h4, -, -⟩ := hrows i d _ r hd hen hr
  rw [hen] at he ⊢
  have he' : r.drawn.elems.map E.ofTriple = [e] := he
  obtain ⟨t, ht, rfl⟩ : ∃ t, r.drawn.elems = [t] ∧ E.ofTriple t = e := by
    cases hh : r.drawn.elems with
    | nil =>
      rw [hh] at he'
      cases he'
    | cons t l =>
      rw [hh] at he'
      simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at he'
      obtain ⟨a, rfl⟩ := he'
      exact ⟨t, rfl, a⟩
  have hd1 : d.drawn = 1 := by
    rw [← h4, ht]
    rfl
  have hmt : t ∈ r.drawn.elems := by
    rw [ht]
    exact List.mem_singleton.2 rfl
  have hk : Fmt.Fld.two.okE t = true := hok r (List.mem_of_getElem? hr) t ht
  obtain ⟨dr, hown', hdr⟩ : ∃ dr, own[i]? = some dr ∧ dr.elems = [t] := by
    have e := hown i
    rw [hr] at e
    cases ho : own[i]? with
    | none =>
      rw [ho] at e
      cases e
    | some dr =>
      rw [ho] at e
      exact ⟨dr, rfl, (Option.some.inj e).symm.trans ht⟩
  have hw : dr.elems = [OnBytes.Slice.ofE (OnBytes.Slice.toE t)] := by
    rw [hdr, ofE_toE t hk]
  have hv : OnBytes.Model.Reading.gl.val (E.ofTriple t) = OnBytes.Slice.toE t :=
    OnBytes.Slice.readE_ofTriple t
  have hname : (flatOf r (some (entryOf d))).name = some d.name.name := rfl
  rw [hv, hname]
  by_cases hz : d.notZero = 0
  · by_cases hc : i = k4CoinRound Q
    · obtain ⟨d', hd', hn'⟩ := k4CoinRound_row Q
      rw [← hc, hd] at hd'
      obtain rfl : d = d' := Option.some.inj hd'
      refine ⟨k4_coin_ne Q hC (hc ▸ hown') hdr hk, fun hn => ?_⟩
      rw [hn'] at hn
      rcases hn with hn | hn <;> exact absurd hn (by decide)
    · have s := k4Wide_silent_ne Q hM ((k4WideRounds_iff Q i).2 ⟨⟨d, hd, hd1, hz⟩, hc⟩) hown' hw
      exact ⟨s.1, fun _ => s.2⟩
  · refine ⟨hNZ i d r hd hz hr t hmt, fun hn => ?_⟩
    rw [(k4_nz_row Q.P Q.hp Q.g d (List.mem_of_getElem? hd) hz).1] at hn
    rcases hn with hn | hn <;> exact absurd hn (by decide)

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.paired_mem
#print axioms ProofFile.Honest.K4.Live.k4_nz_row
#print axioms ProofFile.Honest.K4.Live.k4_coin_ne
#print axioms ProofFile.Honest.K4.Live.k4_own_noDigest
#print axioms ProofFile.Honest.K4.Live.k4_tapeLive
