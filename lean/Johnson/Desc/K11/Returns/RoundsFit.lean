-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/RoundsFit.lean: the proof of `HeadMergeRoundsFit`
(Johnson/Desc/K11/Returns/Statement.lean), to the letter: rounds that pass the step's own test
(`roundsFit`, Johnson/Desc/Block.lean) at the kind's declared rounds have the merge's form. Lemmas;
none of the library's goals.

How. One round's share of the test, what it says part by part, the cut of an entry without answers
and roots (msg / 24 elements of the extension field) and that the test does not read the sealed
digest are the library's: `roundFit`, `roundFit_parts`, `cut_elems`, `noDigest_fit`
(Johnson/Desc/First/Tape/TapeFits.lean). The merge's entries
(`mergeEntries`) state 0, 24, 48 (for each column bit), 24 and 24 bytes, no position and no matrix
entry.

The chief names:
  `scalars_of_items`   a message whose items are n elements of the extension field holds n scalars
  `fit_sent`           one round that passes the test, at an entry of n scalars and k draws
  `fit_bits`           the rounds in the column bits and the two behind them
  `headMergeRoundsFit`

Limits. Nothing on any property.
-/
import Johnson.Desc.K11.Returns.Statement
import Johnson.Desc.First.Tape.TapeFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open OnBytes (E)
open OnBytes.Model (RoundName)
open VerifiableInference.Desc (roundsFit noDigest itemOf)
open VerifiableInference.Desc.First.Tape (roundFit roundFit_parts cut_elems noDigest_fit)
open VerifiableInference.Desc.Part.MaskedSum (scalars Sent)

/-- A message whose items are n elements of the extension field holds n scalars. -/
theorem scalars_of_items : ∀ (l : List Fmt.ItemValue) (n : Nat),
    l.map itemOf = List.replicate n Fmt.Item.e → ∃ s, scalars l = some s ∧ s.length = n
  | [], n, h => by
    have e : n = 0 := by
      have := congrArg List.length h
      simpa using this.symm
    exact ⟨[], rfl, e.symm⟩
  | g :: l, 0, h => by simp at h
  | g :: l, n + 1, h => by
    rw [List.map_cons, List.replicate_succ, List.cons.injEq] at h
    obtain ⟨s, h1, h2⟩ := scalars_of_items l n h.2
    cases g with
    | e x =>
      refine ⟨E.ofTriple x :: s, ?_, by rw [List.length_cons, h2]⟩
      show (scalars l).map _ = _
      rw [h1]
      rfl
    | f _ => cases h.1
    | word _ => cases h.1
    | root _ => cases h.1
    | answer _ => cases h.1

/-- One round that passes the test, at an entry that states n scalars, k draws of elements, no
answer, no root, no position and no matrix entry. -/
theorem fit_sent {e : Fmt.Entry} {r : Fmt.RoundView} (n : Nat) (h : roundFit e r = true)
    (h1 : e.answers = 0) (h2 : e.roots = 0) (h3 : e.msg = 24 * n) (h4 : e.poss = 0)
    (h5 : e.trits = 0) :
    (∃ s, Sent r n e.drawE s (r.drawn.elems.map E.ofTriple)) ∧ r.drawn.poss = [] ∧
      r.drawn.trits = [] := by
  obtain ⟨a1, a2, a3, a4⟩ := roundFit_parts h
  rw [cut_elems e h2 h1, h3, Nat.mul_div_cancel_left n (by decide)] at a1
  obtain ⟨s, b1, b2⟩ := scalars_of_items r.vals n a1
  refine ⟨⟨s, b1, b2, a2, rfl⟩, ?_, ?_⟩
  · exact List.eq_nil_of_length_eq_zero (by rw [a3]; exact h4)
  · exact List.eq_nil_of_length_eq_zero (by rw [a4]; exact h5)

/-- The rounds in the column bits and the two behind them. -/
theorem fit_bits (work : Nat) : ∀ (lk : Nat) (rs : List Fmt.RoundView),
    roundsFit ((List.replicate lk
        ({ name := RoundName.pscRound.name, work := work, msg := 48, drawE := 1 } : Fmt.Entry) ++
      ([{ name := RoundName.pscY.name, work := work, msg := 24, drawE := 1, drawNZ := 1 },
        { name := RoundName.pscValues.name, msg := 24 }] : List Fmt.Entry)).map
      fun e => { entry := e }) rs = true →
    ∃ (u : List Fmt.RoundView) (rY rv : Fmt.RoundView), rs = u ++ [rY, rv] ∧ u.length = lk ∧
      (∀ r ∈ u, (∃ s d, Sent r 2 1 s d) ∧ r.drawn.poss = [] ∧ r.drawn.trits = []) ∧
      ((∃ s d, Sent rY 1 1 s d) ∧ rY.drawn.poss = [] ∧ rY.drawn.trits = []) ∧
      ((∃ s, Sent rv 1 0 s []) ∧ rv.drawn.poss = [] ∧ rv.drawn.trits = [])
  | 0, [rY, rv], h => by
    have h' : (roundFit _ rY && (roundFit _ rv && true)) = true := h
    simp only [Bool.and_eq_true, and_true] at h'
    obtain ⟨⟨sY, aY⟩, pY⟩ := fit_sent 1 h'.1 rfl rfl rfl rfl rfl
    obtain ⟨⟨sV, aV⟩, pV⟩ := fit_sent 1 h'.2 rfl rfl rfl rfl rfl
    have hd : rv.drawn.elems.map E.ofTriple = [] := by
      have e : rv.drawn.elems = [] := List.eq_nil_of_length_eq_zero aV.2.2.1
      rw [e]
      rfl
    rw [hd] at aV
    exact ⟨[], rY, rv, rfl, rfl, fun _ hr => (List.not_mem_nil hr).elim, ⟨⟨sY, _, aY⟩, pY⟩,
      ⟨⟨sV, aV⟩, pV⟩⟩
  | 0, [], h => by cases h
  | 0, [_], h => by simp [roundsFit] at h
  | 0, _ :: _ :: _ :: _, h => by simp [roundsFit] at h
  | lk + 1, [], h => by cases h
  | lk + 1, r :: rs, h => by
    have h' : (roundFit _ r && roundsFit _ rs) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨u, rY, rv, e, hu, hU, hY, hV⟩ := fit_bits work lk rs h'.2
    obtain ⟨⟨s, a⟩, p⟩ := fit_sent 2 h'.1 rfl rfl rfl rfl rfl
    refine ⟨r :: u, rY, rv, by rw [e]; rfl, by rw [List.length_cons, hu], ?_, hY, hV⟩
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact ⟨⟨s, _, a⟩, p⟩
    · exact hU r' hr'

/-- **Rounds that pass the step's own test at the kind's declared rounds have the merge's form.** -/
theorem headMergeRoundsFit : HeadMergeRoundsFit := by
  intro P rs h
  rw [← noDigest_fit] at h
  generalize rs.map noDigest = qs at h
  match qs, h with
  | [], h => cases h
  | [_], h => simp [headClaimMergeKind, mergeEntries, roundsFit] at h
  | r₀ :: r1 :: rest, h =>
    have h' : (roundFit _ r₀ && (roundFit _ r1 && roundsFit _ rest)) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨s0, a0⟩, p0⟩ := fit_sent 0 h'.1 rfl rfl rfl rfl rfl
    obtain ⟨⟨s1, a1⟩, p1⟩ := fit_sent 1 h'.2.1 rfl rfl rfl rfl rfl
    obtain ⟨u, rY, rv, e, hu, hU, hY, hV⟩ := fit_bits P.work P.lay.lk rest h'.2.2
    subst e
    have hv0 : r₀.vals = [] := by
      have c := (roundFit_parts h'.1).1
      rw [cut_elems _ rfl rfl] at c
      simpa using c
    refine ⟨?_, r₀, r1, rY, rv, u, rfl, hu, hv0, a0.2.2.1, ⟨s1, _, a1⟩, fun r hr => (hU r hr).1,
      hY.1, hV.1⟩
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact p0
    rcases List.mem_cons.1 hr with rfl | hr
    · exact p1
    rcases List.mem_append.1 hr with hr | hr
    · exact (hU r hr).2
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hY.2
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hV.2
    · cases hr

end Johnson.Desc.First.ForkMerge.Returns

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Returns.scalars_of_items
#print axioms Johnson.Desc.First.ForkMerge.Returns.fit_sent
#print axioms Johnson.Desc.First.ForkMerge.Returns.fit_bits
#print axioms Johnson.Desc.First.ForkMerge.Returns.headMergeRoundsFit
