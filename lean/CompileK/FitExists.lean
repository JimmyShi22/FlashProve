-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/FitExists.lean: for every interface whose oracles are strings, and 0 < lam, and a few data
that are handed in (the row of `dataAny`), there are samplers, numberings and numbers of openings
that fit: data of the compilation, up to three conditions on the interface and the parameters
themselves.

Definitions, one statement (`Compile.Batch.Spec.exists_fitK`) and its proof. A tool for guards
against empty theorems.





The compiler's statements
ask for data D : DataK L lam (samplers of the
verifier messages from blocks, numberings of positions and coins, announced numbers of openings,
..) and for conditions FitK D M κ₀ n on them. Here such data are made for any L, by choice, from a
few that are handed in (the row of `dataAny`).

Main names:
  `drawsOf lam sl s`: in every round: a number below the number of values of the verifier message,
    from blocks (`BS.pos`, Iop/DrawOf.lean, with sl bits of slack), read as a verifier message along
    some numbering. Bias of a block: kapSl sl = 1 + 2^-sl.
  `numPosOf`, `numPosBOf`: some numberings of the positions.
  `dataAny ..`: the data: these; all decisions classical; announced numbers of openings: all
    positions; depthReq := k. Handed in: pT, pL, pB, a padding symbol z, parameters p and an index
    i₀.
  `Spec.exists_fitK`: if 0 < lam, and three conditions that are `FitK`'s own clauses at these data
    and stay hypotheses: L.maxBatchSize = 2^k (a condition on L: the number of slots is a power of two; k is
    handed in), the annotation has its format (on L alone), the budget holds of (p, M) (on the
    parameters p that are handed in): FitK (dataAny ..) M (kapSl sl) n, n the largest total of
    blocks of the three protocols. What is built: the four other clauses (bias, samplers, blocks,
    openings).

Limits: these data are no proposal for a protocol: the numberings are chosen, so nothing can be
computed with them; the announced numbers of openings are as large as can be, so the verifier's
count of queries tVB is far from tight. The limit goes with the data: `DataK.W`
(CompileK/Main.lean) is made from these samplers and numberings: the committer, the prover and
the verifier of a scheme compiled at that wire take them, and it is `noncomputable` as they are.

This file says nothing on an implementation of the typed oracles over one oracle.


Terms: lean/GLOSSARY.md.
-/
import CompileK.Main
import Iop.DrawOf
import Iop.DrawProofs

set_option autoImplicit false

noncomputable section

namespace Iop
open scoped ENNReal

/-- In every round a sampler from blocks. -/
def drawsOf (lam sl : ℕ) : (s : Shape) → s.Draws lam
  | [] => ()
  | r :: s =>
    ((BS.pos lam sl (Fintype.card r.Chal) Fintype.card_pos).map (Fintype.equivFin r.Chal).symm,
      drawsOf lam sl s)

theorem drawsOf_good {lam : ℕ} (hlam : 0 < lam) (sl : ℕ) :
    ∀ s : Shape, Shape.Draws.Good (kapSl sl) s (drawsOf lam sl s)
  | [] => trivial
  | _ :: s => ⟨BS.map_good _ (BS.pos_good hlam sl _ _), drawsOf_good hlam sl s⟩

/-- some numberings of the positions -/
def numPosOf : (s : Shape) → (h : s.IsPoint) → s.NumPos h
  | [], _ => ()
  | r :: s, (pt, pts) => (@Fintype.equivFin r.Pos pt.finPos, numPosOf s pts)

def numPosBOf : (s : Shape) → (A : RoundSplits s) → (h : s.IsPoint) → s.NumPosB A h
  | [], _, _ => ()
  | r :: s, (a, A), (pt, pts) =>
      letI := pt.finPos
      (Fintype.equivFin {p : r.Pos // a.own p = false},
        Fintype.equivFin {p : r.Pos // a.own p = true},
        numPosBOf s A pts)

end Iop

namespace Compile.Batch
open Iop Top.Batch Top.ProgDraw
open scoped ENNReal

variable {I X : Type}

open Classical in
/-- The data, by choice. -/
def dataAny (L : BatchProtocol I X) (lam sl k : ℕ) (pT : L.offline.shape.IsPoint) (pL : L.link.shape.IsPoint)
    (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (p : Params) (i₀ : I) : DataK L lam where
  pT := pT
  pL := pL
  pB := pB
  z := z
  no := ⟨@Fintype.card _ pT.fintypeOPos + Fintype.card (oneExternalString L.wordLength L.Symbol).Pos,
    @Fintype.card _ pL.fintypeOPos + Fintype.card (twoExternalStrings L.wordLength L.Symbol).Pos,
    @Fintype.card _ pB.fintypeOPos + Fintype.card (oneExternalString L.wordLength L.Symbol).Pos⟩
  dr := ⟨drawsOf lam sl _, drawsOf lam sl _, drawsOf lam sl _⟩
  ax := { posT := numPosOf _ pT, posL := numPosOf _ pL, posB := numPosBOf _ _ pB,
          numRI := Fintype.equivFin _, numT := Fintype.equivFin _, numL := Fintype.equivFin _,
          numB0 := Fintype.equivFin _, numB := Fintype.equivFin _,
          decT := fun _ _ _ => inferInstance, decL := fun _ _ _ => inferInstance,
          decB := fun _ _ _ => inferInstance, depthReq := k }
  p := p
  i₀ := i₀

/-- the largest total of blocks -/
def blocksOf (L : BatchProtocol I X) (lam sl : ℕ) : ℕ :=
  max (Shape.Draws.totB _ (drawsOf lam sl L.offline.shape))
    (max (Shape.Draws.totB _ (drawsOf lam sl L.link.shape))
      (Shape.Draws.totB _ (drawsOf lam sl L.onlineBatch.loc.shape)))

namespace Spec

/-- Under the hypotheses below, there are data that fit. -/
def exists_fitK : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (M : LH.Nums) (lam sl k : ℕ) (pT : L.offline.shape.IsPoint)
      (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (p : Params) (i₀ : I),
    0 < lam → L.maxBatchSize = 2 ^ k → L.onlineBatch.ann.Fmt → Budget p M →
    FitK (dataAny L lam sl k pT pL pB z p i₀) M (kapSl sl) (blocksOf L lam sl)

end Spec

theorem exists_fitK : Spec.exists_fitK := by
  intro I X L M lam sl k pT pL pB z p i₀ hlam hN hF hB
  refine ⟨one_le_kapSl sl,
    ⟨drawsOf_good hlam sl _, drawsOf_good hlam sl _, drawsOf_good hlam sl _⟩,
    ⟨le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩,
    ⟨fun x ρ pl => ?_, fun x ρ pl => ?_, fun x ρ pl => ?_⟩,
    hN, hF, hB⟩
  · exact Nat.add_le_add (@Finset.card_le_univ _ pT.fintypeOPos _) (Finset.card_le_univ _)
  · exact Nat.add_le_add (@Finset.card_le_univ _ pL.fintypeOPos _) (Finset.card_le_univ _)
  · exact Nat.add_le_add (@Finset.card_le_univ _ pB.fintypeOPos _) (Finset.card_le_univ _)

end Compile.Batch
