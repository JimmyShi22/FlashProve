-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Fill.lean: CONDITIONAL: the clauses on values that the
statement on the rows of an attention segment's masked sumchecks asks (`PartVals`,
Honest/K5/Law/RowsK5.lean), part by part, from what is known of each summand. Statements with their
proofs.

EVERY STATEMENT IS CONDITIONAL. What is paid here are the clauses on a summand's form: tame, the
number of end values, its text. The coins under a sumcheck's own slots and the start form's worth
stay premises throughout, and so do the ties between the challenges that a summand reads and those
that the hearing holds.
Main names:
  `partVals_products`   the gathering at a sumcheck of products
  `partVals_key`        the sumcheck on the key at the index: tame, the end values and the text are
                        paid (Johnson/Desc/K5/Honest/Law/TameSD.lean, ReadSD.lean), under "the
                        plan's numbers are the shape's"

Limits. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.RowsK5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork World)
open OnBytes.Slice (GE)
open VerifiableInference.Desc.Part (MaskedSum.Heard)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open VerifiableInference.Desc.First.Att.P (Heard chal batched)
open H2K5.Honest (Summand K5In shapes iSD keyVars sSD sdOf sdDs rhoOf om4Of Planned productsShape)

variable (V X : Type) (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
  (Z : Seat5) (wit : V → K5In) (w : K5In) (heard ds : List Fmt.Drawn) (Wd : World GE)

/-- **The clauses on values at a sumcheck of products, gathered.** CONDITIONAL on each of them: this
is the gathering alone, with the part's shape in the row's own form. -/
theorem partVals_products (q : Nat) (C : Aff) (lead n np : Nat) (hh : MaskedSum.Heard)
    (Wt : Array E) (hq : (shapes Z.P.x)[q]? = some (productsShape lead n np))
    (hT : (summandAt Z w heard ds q).Tame Reading.gl (List.replicate n 4) 2)
    (hn : (summandAt Z w heard ds q).ends = 2 * np)
    (hc : CoinsUnder V X Bk rows look Z wit Wd q (List.replicate n 4) (prodEnds np) hh)
    (hs : C.value Reading.gl Wd = Reading.gl.val (summandAt Z w heard ds q).total)
    (hg : GoodProducts (prodEnds np) hh Wt (summandAt Z w heard ds q)) :
    PartVals V X Bk rows look Z wit w heard ds Wd q C (List.replicate n 4) (prodEnds np) hh
      (GoodProducts (prodEnds np) hh Wt) where
  shape := ⟨lead, by
    rw [hq, List.map_replicate]
    rfl⟩
  tame := hT
  ends := hn
  coins := hc
  start := hs
  good := hg

/-- **The clauses on values at the sumcheck on the key at the index.** CONDITIONAL on: the plan's
numbers are the shape's; the two arrays that the summand reads at the part's front, the challenges
of the score at the index and the batching element's powers, are those that the hearing holds; the
coins under the sumcheck's own slots; the start form's worth. Tame, the number of end values and the
summand's text are paid. Where the verifier's function for the named points refuses at the part's
front, the first of the two arrays is empty (`maxOf`, Johnson/Desc/K5/Honest/Index.lean): whoever
shows the first tie will want that function's return there. -/
theorem partVals_key (hd : Heard) (Pl : Planned Z.P)
    (hrho : rhoOf Z.P (chalOf Z (heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iSD Z.P.x)))) =
      chal hd.atIndex)
    (hom : om4Of Z.P (chalOf Z (heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iSD Z.P.x)))) =
      hd.om')
    (hc : CoinsUnder V X Bk rows look Z wit Wd (iSD Z.P.x) (keyDs Z.P.x) (keyEnds Z.P.x) hd.key)
    (hs : (batched Z.P.x.pairs hd.om' hd.atIndex.sEnd 2 1).value Reading.gl Wd =
      Reading.gl.val (summandAt Z w heard ds (iSD Z.P.x)).total) :
    PartVals V X Bk rows look Z wit w heard ds Wd (iSD Z.P.x)
      (batched Z.P.x.pairs hd.om' hd.atIndex.sEnd 2 1) (keyDs Z.P.x) (keyEnds Z.P.x) hd.key
      (GoodKey Z.P.g (keyVars Z.P.x) (keyEnds Z.P.x) (chal hd.atIndex) hd.om') := by
  have hds : keyDs Z.P.x = sdDs Z.P.g := by
    unfold keyDs sdDs
    rw [Pl.lt, Pl.lgk]
  refine ⟨⟨0, H2K5.Honest.shape_iSD Z.P.x⟩, ?_, ?_, hc, hs, ⟨w, ?_⟩, ?_, ?_, ?_⟩
  · rw [summandAt_iSD, hds]
    show (sSD Z.P w _).Tame Reading.gl (sdDs Z.P.g) (Z.P.x.lt + 1)
    rw [Pl.lt]
    exact H2K5.Honest.tame_sSD Reading.gl Z.P w _
  · rw [summandAt_iSD]
    show Z.P.g.Lam + Z.P.g.NP * Z.P.g.lt = Z.P.x.Lam + Z.P.x.pairs * Z.P.x.lt
    rw [Pl.Lam, Pl.pairs, Pl.lt]
  · rw [summandAt_iSD, H2K5.Honest.sSD_eq, hrho, hom]
  · show (keyDs Z.P.x).map Var.plain = _
    rw [hds]
  · show Z.P.x.lt + 1 = _
    rw [Pl.lt]
  · show Z.P.x.Lam + Z.P.x.pairs * Z.P.x.lt = _
    rw [Pl.Lam, Pl.pairs, Pl.lt]

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.partVals_products
#print axioms ProofFile.Honest.K5.partVals_key
