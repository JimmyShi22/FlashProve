-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/StretchNumbers.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
THE PUBLIC NUMBERS ON WHICH A PAYER OF THE PREMISE stretch OF `K6HeadBelow`
(Honest/K6/Law/ScriptBelowFree.lean) HANGS, AT THE MEMBER AT K6's PLACE: what the maker of the book
of coins makes of that member's declared rounds (`planParts`, Honest/BookEntries.lean): eight
parts, as our row has; their own scalars, which add up to the library's `takesOf`; none of them
among the merges that are guessed off the kinds; no round named "FOLD epsilon". No definition; ten
theorems. THE TOP IS CONDITIONAL: the hypothesis h.

What for. The book's authors have stated (in a letter; in no file yet) a lemma on the whole book:
what a sub-protocol of a segment spends is one stretch of the segment's mask row, under three
premises on the member: none of its parts is among the merges' ends; it holds no fold; it has a
scalar of its own; and with the number of its parts and the sum of their own scalars as letters.
These are had here for K6's member. "The own scalars of a list of parts, added up" is spelt as its
foldl.

  `k6_scalarsIn_entry`, `k6_names_of`, `k6_pairs_of`   what the maker reads of a round of the kind's
                         table: its name and the number of scalars that it sends; not the bits of
                         work
  `k6_cut_closed`, `k6_scalars_closed`, `k6_names_closed`   THREE CLOSED FACTS, BY LEAN's KERNEL, at
                         lt = 10 and lPd = 13: the cut [1, 1, 26, 1, 1, 13, 13, 26]; each part's own
                         scalars [0, 9, 51, 0, 7, 28, 26, 52]; no round is named "FOLD epsilon"
  `k6_planParts_place`      GENERAL: every part of a block bears the block's place
  `k6_not_merge`         GENERAL: no part at a place of the kind K6 is among `mergesByName`'s ends
  `k6_numbers_of_rounds` AT ANY BLOCK of the kind K6 that declares the kind's rounds at lt = 10 and
                         lPd = 13, at any bits of work: the five facts, as numbers
  `k6_stretch_numbers`   **UNDER h, AT THE MEMBER AT K6's PLACE: the five, in our own letters**

Limits.
  * THE PREMISE stretch IS NOT PAID HERE: that wants the authors' lemma, which lies in no file; that
    the description over which it speaks has this chain; the own scalars of the segment's parts in
    front; and that no two members stand at one place.
  * BY THE NUMERALS: the full size alone. At other sizes nothing is said, though the cut's form does
    not hang on them.
  * h: the full size and the format's second hash function alone.
  * Public numbers alone: nothing on an entry of the book, on a value, or on a run.
  * A law, no part: modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.RowAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.FitsScope
import Johnson.Desc.ProofFile.Honest.K6.GoodRounds
import Johnson.Desc.ProofFile.Honest.BookWhole
import Johnson.Desc.Kinds.Law.TakesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.Kinds (Round Head.Par Head.parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf takesOf)
open OnBytes.Maker (WholeD)

/-- The maker's count of a round's scalars, at a round of the kind's table: the number that it
sends. -/
theorem k6_scalarsIn_entry (w : Nat) (r : Round) :
    scalarsIn ({ entry := r.entry w } : Fmt.DeclaredRound) = r.sent := by
  show (24 * r.sent - 32 * 0 - 24 * 0) / 24 = r.sent
  omega

/-- The names do not hang on the bits of work. -/
theorem k6_names_of (w : Nat) (l : List Round) :
    (l.map fun r => ({ entry := r.entry w } : Fmt.DeclaredRound)).map (·.entry.name) =
      l.map (·.name) := by
  rw [List.map_map]
  rfl

/-- Nor do the pairs that the maker reads. -/
theorem k6_pairs_of (w : Nat) (l : List Round) :
    (l.map fun r => ({ entry := r.entry w } : Fmt.DeclaredRound)).map
        (fun r => (r.entry.name, scalarsIn r)) = l.map fun r => (r.name, r.sent) := by
  rw [List.map_map]
  exact List.map_congr_left fun r _ => Prod.ext rfl (k6_scalarsIn_entry w r)

set_option maxRecDepth 100000 in
/-- **A closed fact: the maker's cut.** -/
theorem k6_cut_closed :
    cutOfNames .K6 ((headRoundsOf 10 13).map (·.name)) = [1, 1, 26, 1, 1, 13, 13, 26] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **A closed fact: each part's own scalars.** -/
theorem k6_scalars_closed :
    ((stretchesBy ((headRoundsOf 10 13).map fun r => (r.name, r.sent))
      [1, 1, 26, 1, 1, 13, 13, 26]).zipIdx.map fun x =>
        x.1.foldl (fun n r => if frameNames.contains r.1 then n else n + r.2) 0) =
      [0, 9, 51, 0, 7, 28, 26, 52] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **A closed fact: no fold.** -/
theorem k6_names_closed : ∀ q ∈ headRoundsOf 10 13, q.name ≠ "FOLD epsilon" := by
  decide +kernel

/-- GENERAL: every part of a block bears the block's place. -/
theorem k6_planParts_place {S Cl : Type} (b : Block S Cl) :
    ∀ p ∈ planParts b, p.addr.place = b.place := by
  intro p hp
  unfold planParts at hp
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hp
  rfl

/-- GENERAL: no part at a place of the kind K6 is among the merges that are guessed off the kinds
and the counts. -/
theorem k6_not_merge {S Cl S' Cl' : Type} (bs : List (Block S' Cl')) {b : Block S Cl}
    (hk : b.place.kind = .K6) : ∀ p ∈ planParts b, p.addr ∉ (mergesByName bs).ends := by
  intro p hp hm
  have hm' : p.addr ∈ ((bs.flatMap planParts).filter fun q => q.isSum && q.endScalars == 1 &&
      (q.addr.place.kind == .K4 || q.addr.place.kind == .K11)).map (·.addr) := hm
  obtain ⟨q, hq, e⟩ := List.mem_map.1 hm'
  have hf := (List.mem_filter.1 hq).2
  have e' : q.addr.place.kind = .K6 := by rw [e, k6_planParts_place b p hp, hk]
  rw [e'] at hf
  simp at hf

/-- **AT ANY BLOCK OF THE KIND K6 THAT DECLARES THE KIND's ROUNDS AT lt = 10 AND lPd = 13**, at any
bits of work w: eight parts; their own scalars add up to 173; none among the merges' ends, at any
list bs; no round named "FOLD epsilon". -/
theorem k6_numbers_of_rounds {S Cl S' Cl' : Type} {b : Block S Cl} {w : Nat}
    (hk : b.place.kind = .K6)
    (hr : b.rounds = (headRoundsOf 10 13).map fun r => { entry := r.entry w })
    (bs : List (Block S' Cl')) :
    (planParts b).length = 8 ∧
    (planParts b).foldl (fun n p => n + p.ownScalars) 0 = 173 ∧
    (∀ p ∈ planParts b, p.addr ∉ (mergesByName bs).ends) ∧
    (∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") := by
  have e : planParts b = (stretchesBy ((headRoundsOf 10 13).map fun r => (r.name, r.sent))
      [1, 1, 26, 1, 1, 13, 13, 26]).zipIdx.map fun x => ⟨⟨b.place, x.2⟩, x.1⟩ := by
    unfold planParts partsCut
    rw [hr, hk, k6_names_of, k6_pairs_of, k6_cut_closed]
  have h1 : (planParts b).map (·.ownScalars) = [0, 9, 51, 0, 7, 28, 26, 52] := by
    rw [e, List.map_map]
    exact k6_scalars_closed
  refine ⟨?_, ?_, k6_not_merge bs hk, ?_⟩
  · have h2 := congrArg List.length h1
    rw [List.length_map] at h2
    exact h2
  · have h3 : (planParts b).foldl (fun n p => n + p.ownScalars) 0 =
        ((planParts b).map (·.ownScalars)).foldl (· + ·) 0 := by
      rw [List.foldl_map]
    rw [h3, h1]
    rfl
  · intro r hr'
    rw [hr] at hr'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr'
    exact k6_names_closed q hq

variable {X W₀ Rc Tr : Type} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: the hypothesis h. **THE NUMBERS ON WHICH A PAYER OF THE PREMISE stretch HANGS, AT
THE MEMBER AT K6's PLACE**: as many parts as our row has; their own scalars add up to the library's
`takesOf`; none among the merges' ends; no fold; a scalar of its own. -/
theorem k6_stretch_numbers (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) {b : Block P5J.TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder)
    (hp : b.place = IM.k6Place) :
    (planParts b).length = (headRow (X := X) wit
      (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place).length ∧
    (planParts b).foldl (fun n p => n + p.ownScalars) 0 =
      takesOf (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) ∧
    (∀ p ∈ planParts b, p.addr ∉ (mergesByName cF.blocksInOrder).ends) ∧
    (∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") ∧
    (planParts b).foldl (fun n p => n + p.ownScalars) 0 ≠ 0 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have Fu : HeadFull (P5J.At.X Zp) := by
    have q := headFull_in_scope h.scope h.reads O.public
    rw [O.W] at q
    exact q
  have hlt : headLt (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) = 10 := Fu.lt
  have hlP : headLPd (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) = 13 := by
    show (letI := (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).sizes;
      VerifiableInference.Desc.Kinds.Norm.lPd) = 13
    unfold VerifiableInference.Desc.Kinds.Norm.lPd
    rw [show (letI := (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).sizes;
      VerifiableInference.Desc.Kinds.Norm.d) = 5120 from Fu.num.d]
    decide
  have hk : b.place.kind = .K6 := by rw [hp]
  have hr : b.rounds = (headRoundsOf 10 13).map fun q =>
      { entry := q.entry (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).work } := by
    rw [(head_seated_at_head h b hb hp).1, headRounds_are, hlt, hlP]
  obtain ⟨n1, n2, n3, n4⟩ := k6_numbers_of_rounds hk hr cF.blocksInOrder
  have ht : takesOf (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) = 173 := by
    show 41 + 8 * headLt (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) +
      4 * headLPd (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) = 173
    rw [hlt, hlP]
  refine ⟨n1.trans rfl, n2.trans ht.symm, n3, n4, ?_⟩
  rw [n2]
  decide

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_scalarsIn_entry
#print axioms ProofFile.Honest.K6.k6_names_of
#print axioms ProofFile.Honest.K6.k6_pairs_of
#print axioms ProofFile.Honest.K6.k6_cut_closed
#print axioms ProofFile.Honest.K6.k6_scalars_closed
#print axioms ProofFile.Honest.K6.k6_names_closed
#print axioms ProofFile.Honest.K6.k6_planParts_place
#print axioms ProofFile.Honest.K6.k6_not_merge
#print axioms ProofFile.Honest.K6.k6_numbers_of_rounds
#print axioms ProofFile.Honest.K6.k6_stretch_numbers
