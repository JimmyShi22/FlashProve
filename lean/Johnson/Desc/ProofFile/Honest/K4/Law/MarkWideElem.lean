-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/MarkWideElem.lean: statements with their proofs; no definition.
Over the library and Law/MarkWide.lean alone.

What is here. WHAT THE SILENCE OF THE WIDER MARK (Law/MarkWide.lean) SAYS OF A FIELD ELEMENT. The
test on a round (`zeroOrOne`, Law/Mark.lean) compares words; Law/Mark.lean has: where it speaks at a
written field element x, x is 0 or 1. Here the other way: where it says no at a written field
element x, x is neither 0 nor 1 (`zeroOrOne_false_elem`). So, where the mark is silent, at a listed
round whose challenge shows a written field element x alone: x ≠ 0 and x ≠ 1 (`k4Wide_silent_ne`).
At a typed challenge of a round that samples one element and nothing else the challenge does show
such an element (the library's `shows_chi`, Johnson/Desc/K8/Honest/ChiTyped.lean):
`k4Wide_silent_typed`. THAT A LISTED ROUND IS SUCH A ROUND is shown at data whose entries are those
of the verifier's table of K4's rounds and whose kinds are their names' (`k4_markWide_h1`): a listed
row draws one element by the plain rule, the table's entry carries these two numbers and draws
nothing else, and no name of a round of the model has the kind of seeds or of a sealing
(`k4_kind_plain`). The two joined: `k4Wide_silent_at`.

  `k4_okE_written`   a written element has words below the prime.
  `zeroOrOne_false_elem`   the test on a round says no at a written x: x is neither 0 nor 1.
  `k4Wide_silent_ne`   **silent, listed, a written x: x is neither 0 nor 1.**
  `k4Wide_silent_typed`   **the same at a typed challenge.**
  `k4_kind_names`, `k4_kind_plain`   no name of a round of the model has the kind of seeds or of a
      sealing: the twelve names, each by evaluation.
  `k4_markWide_h1`   **each listed round of the table's own entries samples one element alone.**
  `k4Wide_silent_at`   **silent, listed, at the table's own entries: the typed challenge's element
      is neither 0 nor 1.**

Not shown here. THREE FILES OF THIS FOLDER THAT ARE NAMED HERE ARE NO PART OF THE LIBRARY YET:
Law/Plays.lean, Law/MarkWideDebt.lean, Law/MarkDebt.lean. WHAT THE MARK's SILENCE GIVES AT ANY STATE
OF THE VERIFIER (Law/Live/TapeOfMark.lean and Law/Live/LiveOfYes.lean, conditional): nothing here
ties a member of the list `own` of challenges to what K4's hearing lays into the state.
`zeroOrOne_false_elem` AND `k4Wide_silent_ne` ARE CONDITIONAL ON he: the challenge's elements are
the one written element. Without he nothing is said here: words that are not below the prime may
read as 0 and pass the test; by reading, not as 1: a difference's words lie below the prime whatever
the words. `k4Wide_silent_typed` AND `k4Wide_silent_at` ARE CONDITIONAL ON hd: member number i of
`own` is what the typed challenge v shows: THAT A MEMBER OF THE FRAME's LIST OF A RUN's CHALLENGES
IS SUCH A VALUE IS NOT SHOWN. `k4_markWide_h1` AND `k4Wide_silent_at` ARE CONDITIONAL ON hent AND
hkind; that the data of any description's member meet them is not shown here: by reading,
`k4_rounds` (Law/Plays.lean) with the frame's `KindFits` (Honest/Law/Due.lean) would give both,
round by round. Of a round that is not listed nothing is said.

Kin. THAT A DIFFERENCE HAS WORDS BELOW THE PRIME IS IN THE LIBRARY FIVE TIMES TO THE LETTER:
`okE_sub` (Johnson/Top/H/P1Tie/Words.lean), `ok_sub` (Honest/K3/FastLaw/Read.lean), `okE_subW`
(Johnson/AtFull/Shape/RowFormWritten.lean), and a private `okE_sub'` in
Johnson/Desc/K12/Law/SampleOfSeed.lean and in Johnson/IMR/SampleOfSeedBoth.lean; once more with «a -
b» for the difference: `okE_sub` (Johnson/Desc/Kinds/Law/FromLookup.lean); and at triples of words:
`okE_subE` (Honest/K12/RunByTab.lean); none of these seven files stands in this file's import lines,
and none lies beneath it: so the law is not stated here once more, and its two lines stand as a step
inside the proof of `zeroOrOne_false_elem`, which alone spends it. THAT A WRITTEN ELEMENT HAS WORDS
BELOW THE PRIME (`k4_okE_written`) the library has behind three definitions with this term as their
body: `okE_writeE` (OnBytes/Slice/KeyOfRecBack.lean), `written_okE` (OnBytes/K/IdTableSpell.lean),
`mk_okE_writeE` (OnBytes/Maker/LinkRecordLaws.lean), `okE_ofK` (Johnson/Desc/Kinds/Law/Decode.lean),
`ok_down` (Honest/K3/FastLaw/Read.lean); at the triple of words: `okE_ofE`
(Johnson/Prover/Link/Base.lean); none of these six files lies beneath this one. What `k4_kind_names`
says of all twelve names Johnson/Desc/K13/Law/DeclaredOfWritten.lean says of three written ones
(`plainSigma`, `plainEps`, `plainRound`). `k4_markWide_h1` is the wider sister of `k4_mark_h1`
(Law/MarkDebt.lean).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MarkWide
import Johnson.Desc.K8.Honest.ChiTyped

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E isZeroE subE oneE okE)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (RDT)
open VerifiableInference.Desc.First.K8.Honest (OneElem oneElem_of elOf shows_chi)

/-- A written field element has words below the prime. -/
theorem k4_okE_written (x : Cb.Gl.E) : okE (E.ofTriple (OnBytes.Slice.ofE x)) = true := by
  rw [OnBytes.okE_triple]
  show Fmt.Fld.two.okE (OnBytes.Slice.ofE x) = true
  simp only [Fmt.Fld.okE, OnBytes.Slice.ofE, OnBytes.Slice.ok_ofF, Bool.and_self]

/-- CONDITIONAL: on h and he. **Where the test on a round says no at a written field element x, x is
neither 0 nor 1.** -/
theorem zeroOrOne_false_elem (dr : Fmt.Drawn) (x : Cb.Gl.E) (h : zeroOrOne dr = false)
    (he : dr.elems = [OnBytes.Slice.ofE x]) : x ≠ 0 ∧ x ≠ 1 := by
  unfold zeroOrOne at h
  rw [he] at h
  have h' : (isZeroE (E.ofTriple (OnBytes.Slice.ofE x)) ||
      isZeroE (subE (E.ofTriple (OnBytes.Slice.ofE x)) oneE)) = false := h
  rw [Bool.or_eq_false_iff] at h'
  have ex : OnBytes.Slice.readE (E.ofTriple (OnBytes.Slice.ofE x)) = x :=
    (OnBytes.Slice.readE_ofTriple _).trans (OnBytes.Slice.toE_ofE x)
  constructor
  · intro e0
    have t : isZeroE (E.ofTriple (OnBytes.Slice.ofE x)) = true :=
      (OnBytes.Slice.isZeroE_iff _ (k4_okE_written x)).2 (ex.trans e0)
    rw [h'.1] at t
    cases t
  · intro e1
    -- a difference has words below the prime
    have hs : okE (subE (E.ofTriple (OnBytes.Slice.ofE x)) oneE) = true := by
      rw [OnBytes.okE_triple, OnBytes.subE_triple]
      simp only [Fmt.Fld.okE, Fmt.Fld.subE, Fmt.Fld.ok_sub, Bool.and_self]
    have t : isZeroE (subE (E.ofTriple (OnBytes.Slice.ofE x)) oneE) = true :=
      (OnBytes.Slice.isZeroE_iff _ hs).2
        (by rw [OnBytes.Slice.readE_sub, OnBytes.Slice.readE_one, ex, e1, sub_self])
    rw [h'.2] at t
    cases t

/-- CONDITIONAL: on h, hi, hd and he. **WHERE THE WIDER MARK IS SILENT, AT A LISTED ROUND WHOSE
CHALLENGE SHOWS THE WRITTEN FIELD ELEMENT x ALONE, x IS NEITHER 0 NOR 1.** -/
theorem k4Wide_silent_ne (Q : K4Pub) {fr own : List Fmt.Drawn}
    (h : (k4MarkWide Q).test fr own = none) {i : Nat} (hi : i ∈ k4WideRounds Q) {dr : Fmt.Drawn}
    (hd : own[i]? = some dr) {x : Cb.Gl.E} (he : dr.elems = [OnBytes.Slice.ofE x]) :
    x ≠ 0 ∧ x ≠ 1 :=
  zeroOrOne_false_elem dr x (k4Wide_silent Q h i hi dr hd) he

/-- CONDITIONAL: on h, hi, hO and hd. **THE SAME AT A TYPED CHALLENGE** of a round that samples one
element and nothing else: the element that the challenge gives is neither 0 nor 1. -/
theorem k4Wide_silent_typed (Q : K4Pub) {fr own : List Fmt.Drawn}
    (h : (k4MarkWide Q).test fr own = none) {i : Nat} (hi : i ∈ k4WideRounds Q)
    (e : Fmt.Entry) (k : Fmt.Kind) (hO : OneElem e k) (v : _root_.Run.Ch .two e k)
    (hd : own[i]? = some (_root_.Run.drawnOf .two e k v)) :
    elOf e k v ≠ 0 ∧ elOf e k v ≠ 1 :=
  k4Wide_silent_ne Q h hi hd (by rw [shows_chi e k hO v]; rfl)

/-- The twelve names, each by evaluation. -/
theorem k4_kind_names (r : OnBytes.Model.RoundName) :
    Fmt.kindOf r.name ≠ some .seeds ∧ Fmt.kindOf r.name ≠ some .sealed := by
  cases r <;> decide

/-- CONDITIONAL: on h. No name of a round of the model has the kind of seeds or of a sealing. -/
theorem k4_kind_plain (r : OnBytes.Model.RoundName) {k : Fmt.Kind}
    (h : Fmt.kindOf r.name = some k) : k ≠ .seeds ∧ k ≠ .sealed :=
  ⟨fun e => (k4_kind_names r).1 (e ▸ h), fun e => (k4_kind_names r).2 (e ▸ h)⟩

/-- CONDITIONAL on hent, hkind. **AT THE TABLE's OWN ENTRIES EACH LISTED ROUND SAMPLES ONE FIELD
ELEMENT AND NOTHING ELSE**: the premise on the rounds' data of the law that Law/MarkWideDebt.lean
calls. -/
theorem k4_markWide_h1 (Q : K4Pub) (ds : List RDT)
    (hent : ds.map (·.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) :
    ∀ i d, ds[i]? = some d → i ∈ k4WideRounds Q →
      OneElem d.entry d.kind ∧ d.entry.logN ≤ 64 := by
  intro i d hd hi
  obtain ⟨⟨row, hrow, h1, h2⟩, -⟩ := (k4WideRounds_iff Q i).1 hi
  have he : (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)[i]? =
      some (OnBytes.Desc.First.K4.entryOf row) := by
    unfold OnBytes.Desc.First.K4.entries
    rw [List.getElem?_map, hrow]
    rfl
  have he2 : (ds.map (·.entry))[i]? = some d.entry := by
    rw [List.getElem?_map, hd]
    rfl
  rw [hent, he] at he2
  have e : d.entry = OnBytes.Desc.First.K4.entryOf row := (Option.some.inj he2).symm
  have hk := hkind d (List.mem_of_getElem? hd)
  rw [e] at hk
  have hk2 := k4_kind_plain row.name hk
  rw [e]
  exact ⟨oneElem_of _ _ h1 h2 rfl rfl hk2.1 hk2.2, Nat.zero_le _⟩

/-- CONDITIONAL: on h, hent, hkind, hi, hds and hd. **WHERE THE WIDER MARK IS SILENT, AT A LISTED
ROUND OF DATA WITH THE TABLE's OWN ENTRIES, THE ELEMENT THAT THE TYPED CHALLENGE GIVES IS NEITHER 0
NOR 1.** -/
theorem k4Wide_silent_at (Q : K4Pub) {fr own : List Fmt.Drawn}
    (h : (k4MarkWide Q).test fr own = none) (ds : List RDT)
    (hent : ds.map (·.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) {i : Nat}
    (hi : i ∈ k4WideRounds Q) {d : RDT} (hds : ds[i]? = some d)
    (v : _root_.Run.Ch .two d.entry d.kind)
    (hd : own[i]? = some (_root_.Run.drawnOf .two d.entry d.kind v)) :
    elOf d.entry d.kind v ≠ 0 ∧ elOf d.entry d.kind v ≠ 1 :=
  k4Wide_silent_typed Q h hi d.entry d.kind (k4_markWide_h1 Q ds hent hkind i d hds hi).1 v hd

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_okE_written
#print axioms ProofFile.Honest.K4.zeroOrOne_false_elem
#print axioms ProofFile.Honest.K4.k4Wide_silent_ne
#print axioms ProofFile.Honest.K4.k4Wide_silent_typed
#print axioms ProofFile.Honest.K4.k4_kind_names
#print axioms ProofFile.Honest.K4.k4_kind_plain
#print axioms ProofFile.Honest.K4.k4_markWide_h1
#print axioms ProofFile.Honest.K4.k4Wide_silent_at
