-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/Stretch.lean: "rounds that fit a list of entries", in the
form in which the sentences "the hearing returns" of this folder ask it: three clauses, each of
which splits along a list of entries that is made of two. One definition with code, one structure;
theorems.

Terms. Honest/K3/GLOSSARY.md: see there round, entry, sample and stretch. In this file a stretch is
a list of rounds with `Str`.

What is shown.
  `nzAll es rs`: round for round the library's own test on the elements that an entry states as
    "never 0" (`drawsMarkedNonzeroHaveNonzeroWords`, Johnson/Desc/Block.lean) accepts.
  `Str es rs`: the rounds hold as many scalars and sampled as many elements as the entries state
    (`MaskedSum.Fits`, Johnson/Desc/Part/MaskedSumShape.lean); no position and no matrix entry is
    sampled in them (`elementsAlone`, Johnson/Desc/First/ProdV/Level.lean); `nzAll`.
  `Str.length`, `Str.split`, `Str.nil`, `Str.head`: the tools.
Helpers: `fits_split`, `nzAll_split`, `alone_take`, `alone_drop`.

Hypotheses that remain. `h`: in the tools, `Str` at the list of entries and the rounds in question;
in the helpers, the clause of `Str` that the helper splits (in `fits_split` and `nzAll_split` it
stands without a name, in front of an arrow).

Users. Honest/K3/Shape/ReturnsAtoms.lean imports this file.

Limits. It says nothing of the words' sizes: both the library's test and the hearing's own judge the
three raw words of an element. That rounds which pass a sub-protocol's own test on its rounds
(`roundsFit`, Block.lean) are such a stretch is not shown here. Shown in part: `str_of_roundsFit`
(Honest/K3/Shape/ReturnsFit.lean): at plain entries, declared bare. What stays open: at other
entries and other declarations.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.Block
import Johnson.Desc.Part.MaskedSumShape
import Johnson.Desc.First.ProdV.Level

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open VerifiableInference.Desc (drawsMarkedNonzeroHaveNonzeroWords)
open VerifiableInference.Desc.Part (MaskedSum.Fits)
open VerifiableInference.Desc.First.ProdV (elementsAlone)

/-- Round for round, the library's test on the elements that are stated as "never 0". -/
def nzAll (es : List Fmt.Entry) (rs : List Fmt.RoundView) : Bool :=
  (es.zip rs).all fun x => drawsMarkedNonzeroHaveNonzeroWords { entry := x.1 } x.2

/-- **Rounds that fit a list of entries.** -/
structure Str (es : List Fmt.Entry) (rs : List Fmt.RoundView) : Prop where
  fits : MaskedSum.Fits es rs
  alone : elementsAlone rs = true
  nz : nzAll es rs = true

theorem Str.length {es : List Fmt.Entry} {rs : List Fmt.RoundView} (h : Str es rs) :
    rs.length = es.length := h.fits.length

theorem Str.nil : Str [] [] := ⟨trivial, rfl, rfl⟩

theorem fits_split : ∀ {a b : List Fmt.Entry} {rs : List Fmt.RoundView}, MaskedSum.Fits (a ++ b) rs →
    MaskedSum.Fits a (rs.take a.length) ∧ MaskedSum.Fits b (rs.drop a.length)
  | [], _, _, h => ⟨trivial, h⟩
  | _ :: _, _, [], h => h.elim
  | _ :: a, b, _ :: rs, h =>
    let ⟨h1, h2⟩ := fits_split (a := a) (b := b) (rs := rs) h.2
    ⟨⟨h.1, h1⟩, h2⟩

theorem nzAll_split : ∀ {a b : List Fmt.Entry} {rs : List Fmt.RoundView}, nzAll (a ++ b) rs = true →
    nzAll a (rs.take a.length) = true ∧ nzAll b (rs.drop a.length) = true
  | [], _, _, h => ⟨rfl, h⟩
  | _ :: _, _, [], _ => ⟨rfl, by simp [nzAll]⟩
  | e :: a, b, r :: rs, h => by
    have h' : (drawsMarkedNonzeroHaveNonzeroWords { entry := e } r && nzAll (a ++ b) rs) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨h1, h2⟩ := nzAll_split (a := a) (b := b) (rs := rs) h'.2
    refine ⟨?_, h2⟩
    show (drawsMarkedNonzeroHaveNonzeroWords { entry := e } r && nzAll a (rs.take a.length)) = true
    rw [h'.1, h1]
    rfl

theorem alone_take {rs : List Fmt.RoundView} (h : elementsAlone rs = true) (n : Nat) :
    elementsAlone (rs.take n) = true := by
  unfold elementsAlone at h ⊢
  rw [List.all_eq_true] at h ⊢
  exact fun r hr => h r (List.mem_of_mem_take hr)

theorem alone_drop {rs : List Fmt.RoundView} (h : elementsAlone rs = true) (n : Nat) :
    elementsAlone (rs.drop n) = true := by
  unfold elementsAlone at h ⊢
  rw [List.all_eq_true] at h ⊢
  exact fun r hr => h r (List.mem_of_mem_drop hr)

/-- **A stretch at a list that is made of two is two stretches.** Conditional on the stretch. -/
theorem Str.split {a b : List Fmt.Entry} {rs : List Fmt.RoundView} (h : Str (a ++ b) rs) :
    Str a (rs.take a.length) ∧ Str b (rs.drop a.length) :=
  ⟨⟨(fits_split h.fits).1, alone_take h.alone _, (nzAll_split h.nz).1⟩,
    ⟨(fits_split h.fits).2, alone_drop h.alone _, (nzAll_split h.nz).2⟩⟩

/-- The front of a longer list of rounds, where a stretch is cut off a stretch's front. Conditional
on the stretch. -/
theorem Str.head {a b : List Fmt.Entry} {rs : List Fmt.RoundView} {n : Nat}
    (h : Str (a ++ b) (rs.take n)) : Str a (rs.take a.length) := by
  have h1 := h.split.1
  have hl : (a ++ b).length = (rs.take n).length := h.length.symm
  have hn : a.length ≤ n := by
    rw [List.length_append, List.length_take] at hl
    omega
  rwa [List.take_take, Nat.min_eq_left hn] at h1

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.Str.length
#print axioms ProofFile.Honest.K3.Shape.Str.nil
#print axioms ProofFile.Honest.K3.Shape.fits_split
#print axioms ProofFile.Honest.K3.Shape.nzAll_split
#print axioms ProofFile.Honest.K3.Shape.alone_take
#print axioms ProofFile.Honest.K3.Shape.alone_drop
#print axioms ProofFile.Honest.K3.Shape.Str.split
#print axioms ProofFile.Honest.K3.Shape.Str.head
