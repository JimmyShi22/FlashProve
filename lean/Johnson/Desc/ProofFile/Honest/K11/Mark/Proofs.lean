-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/Mark/Proofs.lean: the proofs of `HeadMergeMarkDebt` and
`HeadMergeMarkSilent` (Honest/K11/Mark/Statement.lean), to the letter. Lemmas; none of the library's
goals.

How. The sentence: `markDebt_of_list_blocks` (Johnson/P1K8R/MarkRounds.lean), general in the member,
the list and the test at a round: the mark's test speaks just where some listed round's drawn value
is bad, by its text; and where the test at a round speaks at a drawn value whose one element is
written from a field element x, x is 0: what is written has words below the prime (`okE_writeE`,
OnBytes/Slice/KeyOfRecBack.lean), and on such words "all three are 0" is "reads as 0"
(`isZeroE_iff`, OnBytes/Slice/ProgField.lean). Where the mark says nothing: no listed round's drawn
value is bad: so each holds one element, which reads other than 0 (`notZero_val`,
Johnson/Desc/K9/Honest/SlotsLive.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Mark.Statement
import OnBytes.Slice.KeyOfRecBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E)
open OnBytes.Model (Reading)
open OnBytes.Slice (writeE okE_writeE isZeroE_iff readE_writeE)
open VerifiableInference.Desc.K9H (notZero notZero_val)
open Johnson.Desc.First.ForkMerge.Live (laterDraws)
open _root_.P1K8 (anyBad markDebt_of_list_blocks)

/-- Where the test at a round speaks at what is written from x: x is 0. -/
theorem mergeBad_zero (dr : Fmt.Drawn) (x : Cb.Gl.E) (h : mergeBad dr = true)
    (he : dr.elems = [OnBytes.Slice.ofE x]) : x = 0 := by
  unfold mergeBad at h
  rw [he] at h
  have h0 : notZero (E.ofTriple (OnBytes.Slice.ofE x)) = false := by
    simpa using h
  have h1 : notZero (writeE x) = false := h0
  unfold notZero at h1
  rw [okE_writeE, Bool.true_and] at h1
  have h2 : OnBytes.isZeroE (writeE x) = true := by
    simpa using h1
  have h3 := (isZeroE_iff (writeE x) (okE_writeE x)).1 h2
  rw [readE_writeE] at h3
  exact h3

/-- **The mark's sentence.** -/
theorem headMergeMarkDebt : HeadMergeMarkDebt := by
  intro P ds Q h1
  refine markDebt_of_list_blocks (headMergeMark P) mergeBad (mergeListed P.lay.lk) ds ?_
    (fun dr x hb he => Or.inl (mergeBad_zero dr x hb he)) h1 rfl Q
  intro fr own hs
  by_cases hb : anyBad mergeBad (fun i => decide (i ∈ mergeListed P.lay.lk)) 0 own = true
  · exact hb
  · have : (headMergeMark P).test fr own = none := if_neg hb
    rw [this] at hs
    cases hs

/-- Where no listed value is bad, a listed round's value is not. -/
theorem notBad_at (mk : Nat → Bool) : ∀ (l : List Fmt.Drawn) (j i : Nat) (d : Fmt.Drawn),
    anyBad mergeBad mk j l = false → l[i]? = some d → mk (j + i) = true → mergeBad d = false
  | [], _, _, _, _, h, _ => by simp at h
  | x :: l, j, 0, d, h, hd, hm => by
    obtain rfl : x = d := Option.some.inj hd
    have h' : ((mk j && mergeBad x) || anyBad mergeBad mk (j + 1) l) = false := h
    rw [Bool.or_eq_false_iff] at h'
    have hm' : mk j = true := hm
    rw [hm', Bool.true_and] at h'
    exact h'.1
  | x :: l, j, i + 1, d, h, hd, hm => by
    have h' : ((mk j && mergeBad x) || anyBad mergeBad mk (j + 1) l) = false := h
    rw [Bool.or_eq_false_iff] at h'
    refine notBad_at mk l (j + 1) i d h'.2 (by simpa using hd) ?_
    have e : j + 1 + i = j + (i + 1) := by omega
    rw [e]
    exact hm

/-- A value that is not bad holds one element, which reads other than 0. -/
theorem notBad_reads (d : Fmt.Drawn) (h : mergeBad d = false) :
    ∀ e ∈ d.elems.map E.ofTriple, Reading.gl.val e ≠ 0 := by
  unfold mergeBad at h
  split at h
  · rename_i t ht
    intro e he
    rw [ht] at he
    obtain rfl := List.mem_singleton.1 he
    exact notZero_val _ (by simpa using h)
  · cases h

/-- **Where the mark says nothing.** -/
theorem headMergeMarkSilent : HeadMergeMarkSilent := by
  intro P fr rs hs hrest e he
  have hb : anyBad mergeBad (fun i => decide (i ∈ mergeListed P.lay.lk)) 0 (rs.map (·.drawn)) =
      false := by
    cases hv : anyBad mergeBad (fun i => decide (i ∈ mergeListed P.lay.lk)) 0
        (rs.map (·.drawn)) with
    | false => rfl
    | true =>
      have : (headMergeMark P).test fr (rs.map (·.drawn)) = some _ := if_pos hv
      rw [this] at hs
      cases hs
  unfold laterDraws at he
  obtain ⟨r, hr, her⟩ := List.mem_flatMap.1 he
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hr
  rw [List.getElem?_drop] at hk
  by_cases hl : 1 + k < P.lay.lk + 2
  · refine notBad_reads r.drawn (notBad_at _ (rs.map (·.drawn)) 0 (1 + k) r.drawn hb
      (by rw [List.getElem?_map, hk]; rfl) ?_) e her
    rw [Nat.zero_add]
    refine decide_eq_true ?_
    unfold mergeListed
    rw [List.mem_range'_1]
    omega
  · exact hrest (1 + k) r hk (by omega) e her

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.mergeBad_zero
#print axioms ProofFile.Honest.K11.headMergeMarkDebt
#print axioms ProofFile.Honest.K11.notBad_at
#print axioms ProofFile.Honest.K11.notBad_reads
#print axioms ProofFile.Honest.K11.headMergeMarkSilent
