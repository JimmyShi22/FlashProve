-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/BetaFit.lean: FROM THE TEST `drawsFit` ON A LIST OF CHALLENGES
(Johnson/Desc/ProofFile/Honest/Frame.lean), ASKED AT THE DECLARED ROUNDS OF AN ATTENTION SEGMENT's
OWN MEMBER (`rounds p`), TO ONE PREMISE OF THE LAW ON THE SECOND MARK (`k5Live_of_silent`,
Johnson/Desc/K5/Honest/Law/LiveMark.lean): what the round of each sumcheck's further variable drew
is not 0 (`BetaNz`). OF ANOTHER PREMISE OF THAT LAW, that the list has all the listed rounds (hlen),
ONE STEP ALONE IS HERE: the number of a declared round is below the list's length (`len_of_fit`).
That a listed round is a declared one is not in this file: `live_len_of_fit`,
Johnson/Desc/ProofFile/Honest/K5/Law/MarksFit.lean, has it, and so hlen.

Why. `drawsFit` is a premise of every sentence "at every list of challenges" over the frame. It asks
of each round's challenge the general step's test on "never 0" and that every word of an element is
below the prime: the two halves of the test `nzE` on one element.

Main names:
  `drawsFit_at`: round by round. (That the two lists have one length: `drawsFit_length`,
    Johnson/Desc/ProofFile/Honest/Law/Along.lean, called.)
  `nzE_of_fitY`: at a declared round "PSC Y" … 1 1 the one element drawn passes `nzE`.
  `betaNz_of_fit`: **`drawsFit` (rounds p) own ⟹ `BetaNz` p.own ⟨zk, own⟩.**
  `len_of_fit`: each number below the number of declared rounds is below the list's length.

Limits. Nothing on how often `drawsFit` holds. No count and no probability.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.K5.Honest.Law.LiveMark
import Johnson.Desc.K5.Honest.Law.PartEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE okE okF isZeroE)
open VerifiableInference.Desc (drawsMarkedNonzeroHaveNonzeroWords fieldPrimeWord)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att.P (Par rounds entriesOf script)
open H2K5.Honest (nzE firstOfDrawn one_at_own BetaNz betaRounds beta_entry Chal)

/-- Round by round. -/
theorem drawsFit_at : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    drawsFit ds Rs = true → ∀ (n : ℕ) (d : Fmt.DeclaredRound), ds[n]? = some d →
      ∃ R, Rs[n]? = some R ∧ drawFit d R = true
  | [], _, _, _, _, hd => nomatch hd
  | _ :: _, [], h, _, _, _ => nomatch h
  | d₀ :: ds, R₀ :: Rs, h, 0, d, hd => by
    have h' : (drawFit d₀ R₀ && drawsFit ds Rs) = true := h
    rw [Bool.and_eq_true] at h'
    obtain rfl : d₀ = d := Option.some.inj hd
    exact ⟨R₀, rfl, h'.1⟩
  | d₀ :: ds, R₀ :: Rs, h, n + 1, d, hd => by
    have h' : (drawFit d₀ R₀ && drawsFit ds Rs) = true := h
    rw [Bool.and_eq_true] at h'
    exact drawsFit_at ds Rs h'.2 n d hd

/-- **At a declared round of a further variable the one element drawn passes the test on one
element.** w: the bits of work. Conditional: h: the challenge is one that the round can draw. -/
theorem nzE_of_fitY {w dY : ℕ} {R : Fmt.Drawn}
    (h : drawFit { entry := { MaskedSum.entry "PSC Y" dY 1 1 with work := w } } R = true) :
    nzE (firstOfDrawn R) = true := by
  unfold drawFit at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hl, _⟩, _⟩, _⟩, _⟩, hn⟩, hk⟩, _⟩ := h
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.1 (show R.elems.length = 1 from beq_iff_eq.1 hl)
  have e1 : firstOfDrawn R = E.ofTriple t := by
    unfold firstOfDrawn
    rw [ht]
    simp
  have hne : t ≠ (0, 0, 0) := by
    unfold drawsMarkedNonzeroHaveNonzeroWords at hn
    rw [show Fmt.kindOf ({ MaskedSum.entry "PSC Y" dY 1 1 with work := w } : Fmt.Entry).name =
      some .elems from (by decide : Fmt.kindOf "PSC Y" = some .elems)] at hn
    intro e0
    have hn' : (([Fmt.Draw.elemNZ].zip R.elems).all
        fun x => x.1 != .elemNZ || x.2 != (0, 0, 0)) = true := hn
    rw [ht, e0] at hn'
    exact absurd hn' (by decide)
  rw [ht] at hk
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hk
  unfold nzE
  rw [e1, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · show (okF t.1 && okF t.2.1 && okF t.2.2) = true
    simp only [okF, Bool.and_eq_true, decide_eq_true_eq]
    exact hk
  · cases hz : isZeroE (E.ofTriple t) with
    | false => rfl
    | true =>
      exfalso
      have e2 := (OnBytes.Slice.isZeroE_eq _).1 hz
      apply hne
      have c0 : t.1 = 0 := congrArg E.c0 e2
      have c1 : t.2.1 = 0 := congrArg E.c1 e2
      have c2 : t.2.2 = 0 := congrArg E.c2 e2
      exact Prod.ext c0 (Prod.ext c1 c2)

/-- **THE PREMISE ON THE ROUNDS OF THE FURTHER VARIABLES, FROM THE TEST ON THE LIST OF CHALLENGES.**
zk: any key points. Conditional: h. -/
theorem betaNz_of_fit (p : Par) (zk : Array (Array E)) {own : List Fmt.Drawn}
    (h : drawsFit (rounds p) own = true) : BetaNz p.own ⟨zk, own⟩ := by
  intro n hn
  obtain ⟨dY, he⟩ := beta_entry p.own n hn
  have hd : (rounds p)[n]? =
      some { entry := { MaskedSum.entry "PSC Y" dY 1 1 with work := p.work } } := by
    unfold rounds
    rw [List.getElem?_map, he]
    rfl
  obtain ⟨R, hR, hf⟩ := drawsFit_at _ _ h n _ hd
  rw [one_at_own zk hR]
  exact nzE_of_fitY hf

/-- Each number of a declared round is below the list's length. Conditional: h; hn. -/
theorem len_of_fit (p : Par) {own : List Fmt.Drawn} (h : drawsFit (rounds p) own = true) {n : ℕ}
    {d : Fmt.DeclaredRound} (hn : (rounds p)[n]? = some d) : n < own.length := by
  rw [drawsFit_length _ _ h]
  exact (List.getElem?_eq_some_iff.1 hn).1

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.drawsFit_at
#print axioms ProofFile.Honest.K5.nzE_of_fitY
#print axioms ProofFile.Honest.K5.betaNz_of_fit
#print axioms ProofFile.Honest.K5.len_of_fit
