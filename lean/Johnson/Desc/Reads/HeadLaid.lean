-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/HeadLaid.lean: what is left of the row claim_read_same_index at the output head's
link, said over the tables part by part; and how a declared read's tables are found in a list.

Why. `head_of_parts` (Reads/HeadAddressed.lean) asks that each of the five declarations is joined.
The toy of Reads/HeadMember.lean pays that by the equation `TablesAre` (Reads/DeclRow.lean), which
is false of the head's five declarations at an honest list: there the link's tables are of three
kinds, laid in turns. The road that is open at an honest list is `PartsLaid` with `PartsFit` and
`Whole` (`joined_of_parts`, Reads/Join.lean).

What is here.
  `head_of_laid`: a step of the row at the head. `HeadClaimByDecls P` follows from `P.Sane` and, at
    every state with closed tables: the test on lengths; each of the five declarations is whole, its
    parts fit the record, and its tables are laid part by part with the declared weights;
    `SeatFits`; a row of U3 has an entry; the request's C is the policy's C in K.
  `head_w_of_laid`: the same for `HeadClaimW` (Reads/HeadWeights.lean), with one stretch in the two
    requests.
  `laid_of_mem`: a tool, for all records, lists and declarations. Where for each part q the list
    holds a table of the third vector on the matrix mat + q, with the declared run, the first entry
    start + q * (k * (m / len)), and an array that reads as the declared weights below the run's
    length, the declared read's tables are laid part by part.

Of OnBytes/Model/ this file names the records `HTailF2` and `HFun`.

Limits. None of the premises is shown of a description. Four forms of 35. Nothing on soundness.


-/
import Johnson.Desc.Reads.HeadWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open Cb.Pv.Tail
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2 HFun)

/-- **A declared read's tables, found in a list.** -/
theorem laid_of_mem {K : Type} (tl : HTailF2) (funs : Array HFun) (val : E → K) (d : ReadDecl E)
    (h : ∀ q, q < d.parts → ∃ Fn ∈ funs.toList, Fn.tree = 2 ∧ Fn.mat = d.mat + q ∧
      Fn.len = d.len ∧
      Fn.start = d.start + q * ((sizeU3 tl funs).k d.mat * ((sizeU3 tl funs).m d.mat / d.len)) ∧
      ∀ j, j < d.len → val (Fn.phi.getD j zeroE) = val (d.w j)) :
    PartsLaid (sizeU3 tl funs) (phiU3 val funs) val d := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  obtain ⟨Fn, hFn, h1, h2, h3, h4, h5⟩ := h q (List.mem_range.1 hq)
  have hmem : Fn ∈ u3Tabs funs := List.mem_filter.2 ⟨hFn, beq_iff_eq.2 h1⟩
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hmem
  refine ⟨n, ?_, fun j hj => ?_⟩
  · have e : ((u3Tabs funs).map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab))[n]? =
        some ⟨Fn.mat, Fn.len, Fn.start⟩ := at_map hn
    rw [h2, h3, h4] at e
    exact e
  · show val (((u3Tabs funs).getD n default).phi.getD j zeroE) = _
    rw [List.getD_eq_getElem?_getD, hn, Option.getD_some]
    exact h5 j hj

end VerifiableInference.Reads

namespace VerifiableInference.Reads.AtHead

open VerifiableInference.Desc.Kinds
open OnBytes.Model (Reading)

variable {K : Type} [CommRing K]

/-- **What is left, over the tables part by part.** -/
theorem head_of_laid (P : HeadLetters K) (hS : P.Sane)
    (h : ∀ s, P.AtClose s →
      lensB (P.funs s) = true ∧
      (∀ d ∈ P.decls s,
        d.Whole ((P.letters.size () s).m d.mat) ((P.letters.size () s).k d.mat) ∧
        PartsFit (P.letters.size () s) d ∧
        PartsLaid (P.letters.size () s) (P.letters.phi () s) P.val d) ∧
      SeatFits P s ∧ 0 < P.seat.cols ∧ ((P.req s).pol.C : K) = (P.policy.C : K)) :
    HeadClaimByDecls P :=
  head_of_parts P hS fun s hs =>
    ⟨(h s hs).1, fun d hd => ⟨((h s hs).2.1 d hd).1,
      joined_of_parts ((h s hs).2.1 d hd).2.2 ((h s hs).2.1 d hd).2.1 ((h s hs).2.1 d hd).1⟩,
      (h s hs).2.2⟩

/-- The same for the statement with the clause on the weights. -/
theorem head_w_of_laid (P : HeadLetters K) (hS : P.Sane)
    (h : ∀ s, P.AtClose s →
      lensB (P.funs s) = true ∧
      (∀ d ∈ P.decls s,
        d.Whole ((P.letters.size () s).m d.mat) ((P.letters.size () s).k d.mat) ∧
        PartsFit (P.letters.size () s) d ∧
        PartsLaid (P.letters.size () s) (P.letters.phi () s) P.val d) ∧
      SeatFits P s ∧ 0 < P.seat.cols ∧ ((P.req s).pol.C : K) = (P.policy.C : K))
    (hq : ∀ s, P.AtClose s →
      (P.req s).r = (P.request s).r ∧ (P.req s).e = (P.request s).e) :
    HeadClaimW P := by
  refine ⟨head_of_laid P hS h, fun s hs => ?_⟩
  obtain ⟨ρ, hρ⟩ := hS.2.2.2
  exact weights_of_requests P s hρ.symm (h s hs).2.2.1.T (hq s hs).1 (hq s hs).2

end VerifiableInference.Reads.AtHead

#print axioms VerifiableInference.Reads.laid_of_mem
#print axioms VerifiableInference.Reads.AtHead.head_of_laid
#print axioms VerifiableInference.Reads.AtHead.head_w_of_laid
