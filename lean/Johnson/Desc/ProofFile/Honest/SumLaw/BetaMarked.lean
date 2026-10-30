-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/BetaMarked.lean: A TEST WITH CODE ON A CALL's SHAPE AND THE
DECLARED ROUNDS: THE FORMAT MARKS THE CHALLENGE OF THE FURTHER VARIABLE Y AS NEVER 0. Definitions,
and statements with their proofs.

Why. At a call with end values the masked sumcheck's part sends each end value plus beta times a
mask entry; beta is Y's challenge. The format marks which elements of a round are sampled as never 0
(`Fmt.dsElems`), and the frame's `drawFit` holds a challenge against that mark (`drawsMarkedNonzeroHaveNonzeroWords`) and against
the prime.
Main names:
  `betaMarked`: without ends: true. With ends: the declared round number vs.length + 1, from 0,
    samples at least one element, and the format marks the first as never 0.
  `word_ok`, `read_ne_zero`: three words below the prime that are not all 0 read as an element other
    than 0 (`ok_of_lt` and `gl_ne_zero` of Johnson/Top/H0/MergeLaw/Beta.lean, stated anew to the
    letter so that this file does not import that one, which stands above one kind's own files; near
    kin there, in another form: `roundsFit_at` beside `drawsFit_at`, `nzFit_one` beside
    `elemOf_ne_zero`).
  `elemOf_ne_zero`: a challenge that fits such a round holds an element that reads other than 0.
  `drawsFit_at`: a list of challenges that fits, at one round.
  `beta_ne_zero`: **under the test, Y's challenge reads other than 0.** `last_is_Y`: a fact on
    lists: the last element of the first challenge and the variables' is that challenge's. (That
    this last element is the factor which the part lays on the end values' mask entries stands in
    `sumOut_vals`, SumShown.lean.)
  `firstMarked_of`, `entries_Y`, `betaMarked_of_like`, `betaMarked_entries`: the test accepts at
    declared rounds that agree with the call's own entries (Johnson/Desc/Part/MaskedSum4.lean) in
    name and numbers sampled; so at rounds made of these entries, at every call.
  `second_marked_rejected`: the test on ONE round rejects a round of two elements of which the
    second alone is marked. (The statement of SumExact.lean fails at such declared rounds: said here
    without a theorem; no theorem of this folder shows it.)

Limits. At ends with no end value the factor multiplies nothing: the test is then asked by
SumExact.lean's statements and is idle: sufficient, not needed (shown by no theorem here). The test
reads the mark; that the challenge reads other than 0 wants `drawsFit` beside it. That no round can
sample such a challenge as 0 is the entry's rule of sampling, as `drawFit` has it. The masked
sumcheck's own verifier text (Johnson/Desc/Part/MaskedSum4.lean) does not test it; the general step
in front of it does (`roundsFit` asks `drawsMarkedNonzeroHaveNonzeroWords`, `viewWordsBelowPrime` the words: Johnson/Desc/Block.lean). The
three `#guard` commands evaluate the test on one round at entries written out here; at the library's
own entries the theorem is `betaMarked_entries`. No distribution occurs. No property of a protocol
is stated.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Said

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc (Oracle drawsMarkedNonzeroHaveNonzeroWords fieldPrimeWord)
open VerifiableInference.Desc.Part.MaskedSum (Call)

/-- The round samples at least one element, and the format marks the first as never 0. -/
def firstMarked (d : Fmt.DeclaredRound) : Bool :=
  decide (1 ≤ d.entry.drawE) &&
    (Fmt.kindOf d.entry.name).any fun κ => (Fmt.dsElems d.entry κ).head? == some .elemNZ

/-- **Y's challenge is marked as never 0.** -/
def betaMarked (k : Call) (rs : List (Fmt.DeclaredRound × List Oracle)) : Bool :=
  match k.ends with
  | none => true
  | some _ => (rs[k.vs.length + 1]?).any fun r => firstMarked r.1

/-- A word below the prime, as the format's test has it. -/
theorem word_ok {w : UInt64} (h : w < fieldPrimeWord) : Fmt.Fld.two.ok w = true := by
  have : w.toNat < fieldPrimeWord.toNat := UInt64.lt_iff_toNat_lt.1 h
  simpa [Fmt.Fld.ok, Fmt.Fld.p, fieldPrimeWord] using this

/-- Three words below the prime that are not all 0 read as an element other than 0. -/
theorem read_ne_zero {x : Fmt.Ext} (h1 : x.1 < fieldPrimeWord) (h2 : x.2.1 < fieldPrimeWord)
    (h3 : x.2.2 < fieldPrimeWord) (hx : x ≠ (0, 0, 0)) : Reading.gl.val (E.ofTriple x) ≠ 0 := by
  intro h
  have h' : OnBytes.Slice.toE x = OnBytes.Slice.toE Fmt.Fld.zeroE := by
    rw [OnBytes.Slice.toE_zeroE]
    exact h
  refine hx (OnBytes.Slice.toE_inj x Fmt.Fld.zeroE ?_ (by decide) h')
  simp [Fmt.Fld.okE, word_ok h1, word_ok h2, word_ok h3]

/-- **A challenge that fits a round whose first element is marked holds an element that reads other
than 0.** -/
theorem elemOf_ne_zero (d : Fmt.DeclaredRound) (R : Fmt.Drawn) (hf : drawFit d R = true)
    (hm : firstMarked d = true) : Reading.gl.val (elemOf R) ≠ 0 := by
  simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨hlen, -⟩, -⟩, -⟩, -⟩, hnz⟩, hw⟩, -⟩ := hf
  simp only [firstMarked, Bool.and_eq_true, decide_eq_true_eq] at hm
  obtain ⟨h1, hk⟩ := hm
  cases hR : R.elems with
  | nil =>
    rw [hR] at hlen
    simp only [List.length_nil] at hlen
    omega
  | cons x xs =>
    cases hκ : Fmt.kindOf d.entry.name with
    | none =>
      rw [hκ] at hk
      cases hk
    | some κ =>
      rw [hκ] at hk
      have hk' : (Fmt.dsElems d.entry κ).head? = some .elemNZ := beq_iff_eq.1 hk
      obtain ⟨tl, htl⟩ : ∃ tl, Fmt.dsElems d.entry κ = .elemNZ :: tl := by
        cases hD : Fmt.dsElems d.entry κ with
        | nil =>
          rw [hD] at hk'
          cases hk'
        | cons y tl =>
          rw [hD] at hk'
          exact ⟨tl, by rw [Option.some.inj hk']⟩
      unfold drawsMarkedNonzeroHaveNonzeroWords at hnz
      rw [hκ] at hnz
      have hnz' : (((Fmt.dsElems d.entry κ).zip R.elems).all
        fun y => y.1 != .elemNZ || y.2 != (0, 0, 0)) = true := hnz
      rw [htl, hR, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hnz'
      have hx : x ≠ (0, 0, 0) := by
        have := hnz'.1
        simpa using this
      rw [hR, List.all_cons, Bool.and_eq_true] at hw
      have hw' := hw.1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw'
      have e : elemOf R = E.ofTriple x := by
        unfold elemOf
        rw [hR]
        rfl
      rw [e]
      exact read_ne_zero hw'.1.1 hw'.1.2 hw'.2 hx

/-- A list of challenges that fits, at one round. -/
theorem drawsFit_at : ∀ (Ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn), drawsFit Ds Rs = true →
    ∀ (i : Nat) (d : Fmt.DeclaredRound), Ds[i]? = some d → ∃ R, Rs[i]? = some R ∧ drawFit d R = true
  | [], _, _, i, d, hd => by simp at hd
  | _ :: _, [], h, _, _, _ => by simp [drawsFit] at h
  | d0 :: Ds, R0 :: Rs, h, i, d, hd => by
    simp only [drawsFit, Bool.and_eq_true] at h
    cases i with
    | zero =>
      obtain rfl : d0 = d := by simpa using hd
      exact ⟨R0, rfl, h.1⟩
    | succ i =>
      obtain ⟨R, hR, hf⟩ := drawsFit_at Ds Rs h.2 i d (by simpa using hd)
      exact ⟨R, by simpa using hR, hf⟩

/-- **Under the test, Y's challenge reads other than 0.** -/
theorem beta_ne_zero (k : Call) (rs : List (Fmt.DeclaredRound × List Oracle)) (ds : List Fmt.Drawn)
    (hb : betaMarked k rs = true) (hd : drawsFit (rs.map (·.1)) ds = true)
    (he : k.ends.isSome = true) :
    ∃ R, ds[k.vs.length + 1]? = some R ∧ Reading.gl.val (elemOf R) ≠ 0 := by
  unfold betaMarked at hb
  cases hk : k.ends with
  | none =>
    rw [hk] at he
    cases he
  | some e =>
    rw [hk] at hb
    cases hr : rs[k.vs.length + 1]? with
    | none =>
      simp only [hr] at hb
      cases hb
    | some r =>
      simp only [hr] at hb
      obtain ⟨R, hR, hf⟩ := drawsFit_at _ ds hd (k.vs.length + 1) r.1 (by
        rw [List.getElem?_map, hr]
        rfl)
      exact ⟨R, hR, elemOf_ne_zero r.1 R hf hb⟩

/-- The last element of the first challenge and the variables', where these are n + 1, is the
element of the challenge number n + 1, from 0, of all. -/
theorem last_is_Y (d0 : Fmt.Drawn) (dv dl : List Fmt.Drawn) (n : Nat) (R : Fmt.Drawn)
    (hN : dv.length = n + 1) (hR : (d0 :: (dv ++ dl))[n + 1]? = some R) :
    (drawnE (d0 :: dv)).getLastD zeroE = elemOf R := by
  have h1 : dv[n]? = some R := by
    rw [List.getElem?_cons_succ, List.getElem?_append_left (by omega)] at hR
    exact hR
  rw [drawnE_eq, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.length_map,
    List.length_cons, hN, List.getElem?_map]
  show (((d0 :: dv)[n + 1]?).map elemOf).getD zeroE = _
  rw [List.getElem?_cons_succ, h1]
  rfl

/-- The test on a round reads the entry's name and two of its numbers alone: at those of the
library's entry for Y it accepts. -/
theorem firstMarked_of (d : Fmt.DeclaredRound) (h1 : d.entry.name = "PSC Y") (h2 : d.entry.drawE = 1)
    (h3 : d.entry.drawNZ = 1) : firstMarked d = true := by
  unfold firstMarked Fmt.dsElems
  rw [h1, h2, h3]
  decide

/-- The library's entry number vs.length + 1, from 0, of a call with end values is Y's. -/
theorem entries_Y (k : Call) (e : VerifiableInference.Desc.Part.MaskedSum.Ends)
    (he : k.ends = some e) :
    (VerifiableInference.Desc.Part.MaskedSum.entries k)[k.vs.length + 1]? =
      some (VerifiableInference.Desc.Part.MaskedSum.entry "PSC Y" e.dY 1 1) := by
  unfold VerifiableInference.Desc.Part.MaskedSum.entries
  rw [he, List.getElem?_append_right (by
    rw [List.length_append, List.length_map]
    simp only [List.length_cons, List.length_nil]
    omega)]
  have : k.vs.length + 1 -
      ([VerifiableInference.Desc.Part.MaskedSum.entry "PSC epsilon" (k.lead + 1) 1 0] ++
        k.vs.map fun v => VerifiableInference.Desc.Part.MaskedSum.entry "PSC round" (v.d - 1) 1
          0).length = 0 := by
    rw [List.length_append, List.length_map]
    simp only [List.length_cons, List.length_nil]
    omega
  rw [this]
  rfl

/-- **Declared rounds that agree with the call's own entries in what the frame's test on challenges
reads pass the test.** The name and the four numbers are those that a caller's premise of that form
names; the name and two numbers are read. (The frame's test reads the range of positions too; these
entries sample none.) -/
theorem betaMarked_of_like (k : Call) (rs : List (Fmt.DeclaredRound × List Oracle))
    (h : rs.map (fun r => (r.1.entry.name, r.1.entry.drawE, r.1.entry.drawNZ, r.1.entry.poss,
        r.1.entry.trits)) =
      (VerifiableInference.Desc.Part.MaskedSum.entries k).map fun e =>
        (e.name, e.drawE, e.drawNZ, e.poss, e.trits)) : betaMarked k rs = true := by
  unfold betaMarked
  cases he : k.ends with
  | none => rfl
  | some e =>
    have h1 := congrArg (·[k.vs.length + 1]?) h
    simp only [List.getElem?_map, entries_Y k e he, Option.map_some] at h1
    cases hr : rs[k.vs.length + 1]? with
    | none =>
      rw [hr] at h1
      cases h1
    | some r =>
      rw [hr] at h1
      have h2 := Option.some.inj h1
      simp only [Prod.mk.injEq] at h2
      exact firstMarked_of r.1 h2.1 h2.2.1 h2.2.2.1

/-- **At rounds that are made of the call's own entries the test accepts**, at every call. -/
theorem betaMarked_entries (k : Call) :
    betaMarked k ((VerifiableInference.Desc.Part.MaskedSum.entries k).map fun x =>
      ({ entry := x }, [])) = true :=
  betaMarked_of_like k _ (by
    rw [List.map_map]
    rfl)

/-- **A round of two elements of which the second alone is marked is rejected**: the part's factor
is the first element. -/
theorem second_marked_rejected :
    firstMarked { entry := VerifiableInference.Desc.Part.MaskedSum.entry "PSC Y" 2 2 1 } =
      false := by
  decide

-- at the library's own entry for Y the test on the round accepts; at its entry for a variable's
-- round it rejects; so it does at a round of two elements of which the second alone is marked
#guard firstMarked { entry := VerifiableInference.Desc.Part.MaskedSum.entry "PSC Y" 2 1 1 }
#guard !firstMarked { entry := VerifiableInference.Desc.Part.MaskedSum.entry "PSC round" 2 1 0 }
#guard !firstMarked { entry := VerifiableInference.Desc.Part.MaskedSum.entry "PSC Y" 2 2 1 }

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.word_ok
#print axioms ProofFile.Honest.SumLaw.read_ne_zero
#print axioms ProofFile.Honest.SumLaw.elemOf_ne_zero
#print axioms ProofFile.Honest.SumLaw.drawsFit_at
#print axioms ProofFile.Honest.SumLaw.beta_ne_zero
#print axioms ProofFile.Honest.SumLaw.last_is_Y
#print axioms ProofFile.Honest.SumLaw.firstMarked_of
#print axioms ProofFile.Honest.SumLaw.entries_Y
#print axioms ProofFile.Honest.SumLaw.betaMarked_of_like
#print axioms ProofFile.Honest.SumLaw.betaMarked_entries
#print axioms ProofFile.Honest.SumLaw.second_marked_rejected
