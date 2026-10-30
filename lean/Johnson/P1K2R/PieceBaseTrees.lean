-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/PieceBaseTrees.lean: code switching (K2): AT THE ROW OF PIECES (h.row L, at the
closed constant): THE PIECE AT A PLACE OF THE KIND MEETS, TOGETHER, THE TWO FACTS THAT THE SECOND
AND THE THIRD TIE ASK OF IT: its base is the table's count of trees in front of the place · its
first round's data lists as many trees as the kind's numbers say roots, its second round's none.
ONE LEMMA; every step a call. NO BLOCK IMPORTS THIS FILE.
  piece_base_trees   (h.row L)[i]? = some q · i < 357 · cF.blocksInOrder[i]? = some B · B.rounds =
                     K2.rounds p · bookFit N ps (toldOf cF.blocksInOrder) = true · i ≤ ps.length ⟹ q.base =
                     N.treesAt ps[i]? ∧ q.ds.map (·.trees.length) = [p.roots, 0]
  piece_base_trees_at   the same at the constant's own numbers and places (P5J.At.N Zp cF ·
                        P5J.At.ps): bookFit by bookFit_withTold (At.N is laid
                        «withTold»); ONE PREMISE MORE: hn : At.ps.Nodup (closed)
WHY THE TWO MEET. atRow_more (Johnson/Desc/Kinds/Law/RowAtConst.lean) hands ONE structure
for that very piece: PieceMore (Johnson/Desc/Sound/PieceMore.lean): its field «base» is what
base_treesAt (Johnson/Desc/Sound/PieceFence.lean) turns into the first fact; its field «rounds»
says, round by round, that the data's trees are as many as the declared round's roots: the second.
Both are drawn off one list of declared rounds.
WHAT IT DOES NOT SAY. That p.roots is the number of trees of the written sending's lay:
P1K2.numsAt_roots (Johnson/Top/H0/Tw/K2C/PieceTrees.lean) has n.roots = lay.shapes.size at the
lot's numbers n; the tie of n.codes | n.sent to the written ones is other files'. That q is the
kind's typed piece at [d₁, d₂]: k2_written_at_row (Johnson/P1K2R/PlaceThree.lean):
with it q.ds = [d₁, d₂]. No soundness is claimed.
-/
import Johnson.Desc.Kinds.Law.RowAtConst
import Johnson.Desc.Kinds.Law.RowLenAtConst
import Johnson.Desc.Sound.PieceFence
import Johnson.Desc.First.BookFitTold
import Johnson.Top.H0.Tw.K2C.Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (Numbers bookFit bookFit_withTold)
open VerifiableInference.Desc.First.K2 (P2)
open VerifiableInference.Desc.Sound (base_treesAt toldOf)
open VerifiableInference.Desc.Kinds.Head.Law (atRow_more atRow_lift atRow_blocks atRow_told
  atRow_in ps_length)

theorem piece_base_trees {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (i : Nat) (q)
    (hq : (h.row L)[i]? = some q) (hi : i < 357) (B : Block P5J.TS ProofFile.Cl)
    (hB : cF.blocksInOrder[i]? = some B) (p : P2)
    (hr : B.rounds = VerifiableInference.Desc.First.K2.rounds p) (N : Numbers) (ps : List Place)
    (hf : bookFit N ps (toldOf cF.blocksInOrder) = true) (hk : i ≤ ps.length) :
    q.base = N.treesAt ps[i]? ∧ q.ds.map (·.trees.length) = [p.roots, 0] := by
  obtain ⟨hm, _⟩ := atRow_more h L q₁ q₂ q₃ i q hq (atRow_in h i hi)
  have hl := atRow_lift h L q₁ q₂ q₃ i q B hq hB
  have hb : q.b.rounds = VerifiableInference.Desc.First.K2.rounds p := by
    rw [hl]
    exact hr
  refine ⟨base_treesAt hm (atRow_blocks h) N ps
    ((congrArg (bookFit N ps) atRow_told).trans hf) hk, ?_⟩
  have hF := hm.rounds
  rw [hb] at hF
  obtain ⟨r₁, r₂, e⟩ : ∃ r₁ r₂, VerifiableInference.Desc.First.K2.rounds p = [r₁, r₂] :=
    ⟨_, _, rfl⟩
  have er : (VerifiableInference.Desc.First.K2.rounds p).map (·.entry.roots) = [p.roots, 0] := rfl
  rw [e] at hF er
  generalize q.ds = ds at hF
  cases hF with
  | cons a t =>
    cases t with
    | cons b u =>
      cases u
      simp only [List.map_cons, List.map_nil] at er ⊢
      rw [a.2.2.2.2.2, b.2.2.2.2.2]
      exact er

/-- The same at the constant's own numbers and places. -/
theorem piece_base_trees_at {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (i : Nat) (q)
    (hq : (h.row L)[i]? = some q) (hi : i < 357) (B : Block P5J.TS ProofFile.Cl)
    (hB : cF.blocksInOrder[i]? = some B) (p : P2)
    (hr : B.rounds = VerifiableInference.Desc.First.K2.rounds p) (hn : P5J.At.ps.Nodup) :
    q.base = (P5J.At.N Zp cF).treesAt P5J.At.ps[i]? ∧
      q.ds.map (·.trees.length) = [p.roots, 0] :=
  piece_base_trees h L q₁ q₂ q₃ i q hq hi B hB p hr (P5J.At.N Zp cF) P5J.At.ps
    (bookFit_withTold _ P5J.At.ps (P5J.At.told cF) hn) (by rw [ps_length]; omega)

end P1K2

#print axioms P1K2.piece_base_trees_at
#print axioms P1K2.piece_base_trees
