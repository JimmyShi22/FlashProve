-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/NzOfStep.lean: CONDITIONAL but for `k4_fit_at`.

What is here. WHO GIVES THE HYPOTHESIS hNZ OF `k4_tapeLive` (Law/Live/TapeOfMark.lean): that the
elements which the rounds of K4 (the sub-protocol of the feed-forward layers' own rounds) draw by
the rule that never gives 0 are not 0. THE STEP THAT SHOWS A BLOCK ITS ROUNDS (`Block.step`,
Johnson/Desc/Block.lean) refuses unless `roundsFit` holds of the block's declared rounds and the
rounds that it is handed, and `roundsFit` asks `drawsMarkedNonzeroHaveNonzeroWords` of each round: the drawn elements that the
entry marks as never 0 are not three words 0. At K4's table such a row bears the name `.pscY`, draws
one element, and that one by this rule (`k4_nz_row`, Law/Live/TapeOfMark.lean). So, where
`roundsFit` holds at K4's declared rounds and the rounds `mine` that the step is handed (hrf), and
the words of a round's one drawn element lie below the prime (hok), hNZ holds at the rounds `mine`
without the sealed digest, to its letter (`k4_nz_of_step`). AND hrf COMES OFF A STEP's YES
(`k4_hrf_of_step`): where a block that declares K4's rounds (the library's `Declares`,
Johnson/Road/K4/PieceTiled.lean) steps with a yes at `mine`: by the library's `step_fits`
(Johnson/Desc/RiderLaw.lean). Statements with their proofs. Four steps are calls of the library's
laws: `nzFit_one` (Johnson/Top/H0/MergeLaw/Beta.lean: one never-zero element is not three words 0),
`readsNz_gl` (Johnson/Desc/First/Att/K05Nz.lean: with words below the prime it reads as not 0),
`readE_ofTriple` (OnBytes/Slice/ProgField.lean: the element that three words spell is read as the
three words) and `step_fits`.

  `k4_fit_at`   where `roundsFit` holds, each round meets `drawsMarkedNonzeroHaveNonzeroWords` and draws as many elements as its
      entry says: by number. (The library has the fact in three other shapes: under the name
      `roundsFit_at`: Johnson/Desc/LinkLaw16.lean, Johnson/Top/H0/MergeLaw/Beta.lean; and all seven
      clauses pair by pair: `roundsFit_iff`, Johnson/Top/H0/StepLaws/RoundsFit.lean. None reads
      both lists by number.)
  `k4_words_ne`   the library's `readsNz_gl` in the letters of hNZ.
  `k4_nz_of_step`   **hNZ, from `roundsFit` and hok.**
  `k4_hrf_of_step`   **`roundsFit` at K4's declared rounds, from a step's yes.**

Not shown here. That a step says yes anywhere. THAT THE MEMBER AT K4's PLACE DECLARES K4's ROUNDS:
the library has it under the hypotheses of its top statements (`declares_alone`,
Johnson/Road/K4/K04Sits.lean, off `IM.k4_of`, Johnson/IMR/K4Seat.lean: whoever imports these two has
modules under Johnson/Goal/ beneath it), and of a term of the seated form by unfolding
(`declares_seatedLot`, Johnson/Road/K4/HearsAsLot.lean): neither is called here. hok IS ASKED HERE
AT THE ROUNDS AS HANDED; `k4_tapeLive` asks it at the rounds without the digest: `k4_hok_noDigest`
(Law/Live/OkTyped.lean) carries it over; who gives hok: that file. IN THE FRAME hNZ NEEDS NO STEP's
YES: its test on challenges (`drawFit`, Honest/Frame.lean) asks `drawsMarkedNonzeroHaveNonzeroWords` and the words of every
round, and the frame's folder has the general law (`drawsFit_at`, `elemOf_ne_zero`,
`firstMarked_of`: Honest/SumLaw/BetaMarked.lean): at K4's table and in hNZ's letters it is not
called.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.TapeOfMark
import Johnson.Desc.First.Att.K05Nz
import Johnson.Desc.RiderLaw
import Johnson.Road.K4.PieceTiled
import Johnson.Top.H0.MergeLaw.Beta

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Live
open OnBytes.Desc.First.K4 (entryOf)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (roundsFit drawsMarkedNonzeroHaveNonzeroWords noDigest)

/-- Where `roundsFit` holds, each round meets `drawsMarkedNonzeroHaveNonzeroWords` and draws as many elements as its entry
says. -/
theorem k4_fit_at : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView), roundsFit ds rs = true →
    ∀ (i : Nat) (d : Fmt.DeclaredRound) (r : Fmt.RoundView), ds[i]? = some d → rs[i]? = some r →
      drawsMarkedNonzeroHaveNonzeroWords d r = true ∧ r.drawn.elems.length = d.entry.drawE
  | [], [], _ => fun i d r hd _ => by simp at hd
  | [], _ :: _, h => absurd (show false = true from h) Bool.false_ne_true
  | _ :: _, [], h => absurd (show false = true from h) Bool.false_ne_true
  | d0 :: ds, r0 :: rs, h => by
    simp only [roundsFit, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨-, hl⟩, -⟩, -⟩, -⟩, -⟩, hn⟩, hr⟩ := h
    intro i d r hd hr'
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hd hr'
      subst hd
      subst hr'
      exact ⟨hn, hl⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hd hr'
      exact k4_fit_at ds rs hr i d r hd hr'

/-- CONDITIONAL: on hk and hn. Three words below the prime that are not all 0 read as not 0. -/
theorem k4_words_ne {t : Fmt.Ext3} (hk : Fmt.Fld.two.okE t = true) (hn : t ≠ (0, 0, 0)) :
    OnBytes.Slice.toE t ≠ 0 := by
  intro e0
  exact VerifiableInference.Desc.First.Att.P.readsNz_gl t hk hn
    ((OnBytes.Slice.readE_ofTriple t).trans e0)

/-- CONDITIONAL: on hrf and hok. **THE HYPOTHESIS hNZ OF `k4_tapeLive`, TO ITS LETTER, AT THE ROUNDS
WITHOUT THE SEALED DIGEST.** -/
theorem k4_nz_of_step (Q : K4Pub) (mine : List Fmt.RoundView)
    (hrf : roundsFit ((OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g).map fun e => { entry := e })
      mine = true)
    (hok : ∀ r ∈ mine, ∀ t, r.drawn.elems = [t] → Fmt.Fld.two.okE t = true) :
    ∀ (i : Nat) (d : OnBytes.Desc.First.K4.Rd) (r : Fmt.RoundView),
      (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)[i]? = some d → d.notZero ≠ 0 →
      (mine.map noDigest)[i]? = some r → ∀ t ∈ r.drawn.elems, OnBytes.Slice.toE t ≠ 0 := by
  intro i d r hd hz hr t ht
  obtain ⟨hn, h1, h2⟩ := k4_nz_row Q.P Q.hp Q.g d (List.mem_of_getElem? hd) hz
  rw [List.getElem?_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.1 hr
  have ht' : t ∈ r0.drawn.elems := ht
  have hdecl : ((OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g).map
      fun e => ({ entry := e } : Fmt.DeclaredRound))[i]? = some { entry := entryOf d } := by
    unfold OnBytes.Desc.First.K4.entries
    rw [List.getElem?_map, List.getElem?_map, hd]
    rfl
  obtain ⟨hnz, hlen⟩ := k4_fit_at _ _ hrf i _ r0 hdecl hr0
  have hlen' : r0.drawn.elems.length = 1 := hlen.trans h1
  obtain ⟨t0, e0⟩ := List.length_eq_one_iff.1 hlen'
  rw [e0] at ht'
  obtain rfl : t = t0 := List.mem_singleton.1 ht'
  have hne : t ≠ (0, 0, 0) :=
    VerifiableInference.Desc.First.MergeLaw.nzFit_one (d := { entry := entryOf d }) h1 h2 e0 hnz
  exact k4_words_ne (hok r0 (List.mem_of_getElem? hr0) t e0) hne

/-- CONDITIONAL: on h, hd, eP, ehp and eg. **`roundsFit` AT K4's DECLARED ROUNDS, FROM A STEP's
YES** of a block that declares them. -/
theorem k4_hrf_of_step {T Cl : Type} {ft : Nat} {b : VerifiableInference.Desc.Block T Cl} {s s' : T}
    {mine : List Fmt.RoundView} {cols : List VerifiableInference.Desc.OpenedColumn} {k : Nat}
    (h : b.step ft s mine cols = .ok (s', k)) {par : OnBytes.Desc.First.K4.Par}
    (hd : OnBytes.Road.K4.Declares b par) (Q : K4Pub) (eP : Q.P = par.P) (ehp : Q.hp = par.hp)
    (eg : Q.g = par.g) :
    roundsFit ((OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g).map fun e => { entry := e })
      mine = true := by
  have hf := VerifiableInference.Desc.step_fits h
  rw [hd] at hf
  rw [eP, ehp, eg]
  exact hf

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.k4_fit_at
#print axioms ProofFile.Honest.K4.Live.k4_words_ne
#print axioms ProofFile.Honest.K4.Live.k4_nz_of_step
#print axioms ProofFile.Honest.K4.Live.k4_hrf_of_step
