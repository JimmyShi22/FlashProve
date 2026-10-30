-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/Shown.lean: kind K13, the members' batching: from what the frame
shows of a round to the rounds of the kind's honest prover. Statements with their proofs: helpers
for the law on the frame's `play` at the kind's row.
Main names:
  `k13Dr c`: a challenge that is one element, and nothing else.
  `said_shown`: a message of elements, as the frame shows it beside such a challenge, is the round
    `shownRound` (Johnson/Desc/K13/Honest/MovesAtM3.lean) of these elements, each read in the
    library's field and laid back into words below the prime.
  `oneElem`, `fit_one`: a challenge that fits an entry which samples one element and nothing else is
    such a challenge, but for the sealed digest.
  `fits_batt`: the challenges that fit the kind's rounds: x, eps and one for each variable.

What is not claimed. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.Part
import Johnson.Desc.ProofFile.Honest.Law.Play

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes (E zeroE)
open OnBytes.Slice (GE toE ofE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.K13 (Where battRounds sigmaEntry epsEntry roundEntry)
open VerifiableInference.Desc.K13.Honest (shownRound)

/-- A challenge that is one element, and nothing else. -/
def k13Dr (c : E) : Fmt.Drawn := ⟨[c.triple], [], [], none⟩

/-- **A message of elements, as the frame shows it.** -/
theorem said_shown (l : List E) (c : E) :
    (⟨(sayE l).vals.map Said.got, k13Dr c⟩ : Fmt.RoundView) =
      shownRound (l.map fun a => k13E (Reading.gl.val a)) c := by
  unfold sayE shownRound k13Dr
  simp only [List.map_map]
  rfl

/-- The entry samples one element and nothing else. -/
def oneElem (e : Fmt.Entry) : Prop := e.drawE = 1 ∧ e.poss = 0 ∧ e.trits = 0

/-- A challenge that fits such an entry. -/
theorem fit_one {d : Fmt.DeclaredRound} (h : oneElem d.entry) {R : Fmt.Drawn}
    (hf : drawFit d R = true) :
    ∃ c : E, bare R = k13Dr c := by
  unfold drawFit at hf
  simp only [Bool.and_eq_true, beq_iff_eq, h.1, h.2.1, h.2.2] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hf
  obtain ⟨el, po, tr, dg⟩ := R
  have e2 : po = [] := List.length_eq_zero_iff.1 h2
  have e3 : tr = [] := List.length_eq_zero_iff.1 h3
  obtain ⟨a, e1⟩ := List.length_eq_one_iff.1 h1
  have e1' : el = [a] := e1
  subst e1' e2 e3
  exact ⟨E.ofTriple a, rfl⟩

/-- As many such challenges as a list of such rounds has members. -/
theorem fits_ones : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, oneElem d.entry) → drawsFit ds Rs = true →
    ∃ cs : List E, Rs.map bare = cs.map k13Dr ∧ cs.length = ds.length
  | [], [], _, _ => ⟨[], rfl, rfl⟩
  | d :: ds, R :: Rs, h, hf => by
    have hf' : (drawFit d R && drawsFit ds Rs) = true := hf
    rw [Bool.and_eq_true] at hf'
    obtain ⟨c, hc⟩ := fit_one (h d List.mem_cons_self) hf'.1
    obtain ⟨cs, h1, h2⟩ := fits_ones ds Rs (fun e he => h e (List.mem_cons_of_mem _ he)) hf'.2
    refine ⟨c :: cs, ?_, by simp only [List.length_cons, h2]⟩
    simp only [List.map_cons, hc, h1]
  | [], _ :: _, _, hf => by cases hf
  | _ :: _, [], _, hf => by cases hf

/-- **The challenges that fit the kind's rounds.** -/
theorem fits_batt (p : Where) (Rs : List Fmt.Drawn) (hf : drawsFit (battRounds p) Rs = true) :
    ∃ (x eps : E) (gs : List E), Rs.map bare = k13Dr x :: k13Dr eps :: gs.map k13Dr ∧
      gs.length = p.lin.kCol := by
  obtain ⟨cs, h1, h2⟩ := fits_ones (battRounds p) Rs (fun d hd => by
    unfold battRounds at hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨rfl, rfl, rfl⟩
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨rfl, rfl, rfl⟩
    rw [List.eq_of_mem_replicate hd]
    exact ⟨rfl, rfl, rfl⟩) hf
  have h3 : cs.length = 2 + p.lin.kCol := by
    rw [h2]
    simp only [battRounds, List.length_cons, List.length_replicate]
    omega
  match cs, h1, h3 with
  | x :: eps :: gs, h1, h3 =>
    exact ⟨x, eps, gs, h1, by simp only [List.length_cons] at h3; omega⟩
  | [], _, h3 => simp only [List.length_nil] at h3; omega
  | [_], _, h3 => simp only [List.length_cons, List.length_nil] at h3; omega

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.said_shown
#print axioms ProofFile.Honest.K13.fit_one
#print axioms ProofFile.Honest.K13.fits_ones
#print axioms ProofFile.Honest.K13.fits_batt
