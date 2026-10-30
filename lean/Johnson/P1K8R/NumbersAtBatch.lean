-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/NumbersAtBatch.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN
BLOCKS REACH IN FRONT OF A SEGMENT's BATCHING, FIVE NUMBERS OF THE DATA ARE THE BUILT SEGMENT's: the
columns of the array of bits, the number of blocks, the number of rows of cells, `linkedCount`
(Johnson/Desc/K8/Honest/LinkedFew.lean) and `symCount` (SymbolsFew.lean). Lemmas; none of the
library's goals. No prover stands in them; nothing on completeness, soundness or hiding.

  **`numbers_at_batch`**   in the goals' scope, under an opening of the description, at l < 25; K :=
      14 l + 9, or 347 at the head's segment; Xl the built segment: at every (z, s) reached at K and
      every data tl of s: the five equations
  `digitsLaid_of`   `apartB` (Johnson/Desc/K8/Honest/ApartOf.lean) and "the upper virtual rows of
      the digits' array begin at column 0" give `digitsLaid` (DigitsFew.lean)
By: LinkJoin.planned_at_batch (Johnson/Desc/First/Link/Law/PlannedAtDraw.lean) at the library's two
planned readings gD (planned_gD, gD_parts: OkAtBatch.lean, OkDigAt.lean) and rowsRead (planned_rows:
RowsNumberAtBatch.lean), which together hold the six fields that the five numbers read · of_readTl ·
`apartB_iff`.
Limits. The full size's 25 segments. The first chain. No number is evaluated.

-/
import Johnson.Desc.First.Link.Law.OkAtBatch
import Johnson.Desc.First.Link.Law.RowsNumberAtBatch
import Johnson.Desc.K8.Honest.LinkedFew
import Johnson.Desc.K8.Honest.SymbolsFew
import Johnson.Desc.K8.Honest.DigitsFew
import Johnson.Desc.K8.Honest.ApartOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **The data's five numbers in front of a batching are the built segment's.** -/
theorem numbers_at_batch {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) :
    tl.bzColumns = Xl.tl.bzColumns ∧ tl.zzBlocks = Xl.tl.zzBlocks ∧ tl.mz = Xl.tl.mz ∧
      linkedCount tl = linkedCount Xl.tl ∧ symCount tl = symCount Xl.tl := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  obtain ⟨e1, -, e2, -, -, -, e4, -, e5⟩ := LinkJoin.gD_parts (LinkJoin.of_readTl
    (LinkJoin.planned_at_batch LinkJoin.planned_gD hS hR O hx e3 (z, s) h') tl ht)
  have g := LinkJoin.of_readTl
    (LinkJoin.planned_at_batch LinkJoin.planned_rows hS hR O hx e3 (z, s) h') tl ht
  have em : tl.mats = Xl.tl.mats := congrArg (·.2.1) g
  have es : tl.shp = Xl.tl.shp := congrArg (·.2.2.2) g
  refine ⟨?_, e5, e2, ?_, ?_⟩
  · unfold HTailF2.bzColumns
    rw [e1]
  · unfold linkedCount
    rw [e2, e4, em]
  · unfold symCount
    rw [e4, es]

/-- The test on public numbers and the arrays' frame, from its two halves. -/
theorem digitsLaid_of (tl : HTailF2) (F : Fork) (h : apartB tl = true)
    (h0 : ∀ b, b < tl.zzBlocks →
      ((F.trees.getD tl.ix.ZZ {}).rows.getD (tl.zzBlocks + b) {}).L0 = 0) :
    digitsLaid tl F = true := by
  obtain ⟨-, ⟨h2, -⟩, ⟨h3, -⟩, h4⟩ := (apartB_iff tl).1 h
  unfold digitsLaid
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, List.all_eq_true, List.mem_range]
  exact ⟨⟨⟨fun mu hmu => (h4 mu hmu).2.1, h2⟩, h3⟩, h0⟩

end P1K8

#print axioms P1K8.numbers_at_batch
#print axioms P1K8.digitsLaid_of
