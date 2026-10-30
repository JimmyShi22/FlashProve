-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/ReadsLenOfSkel.lean: THE NUMBER OF READS, `(readsList tl funs).length`
(OnBytes/Tie/Pv/Tail/EndLoops.lean), AND WITH IT THE NUMBER OF INDICES THAT THE TIES AND THE READS
TAKE
(`top8`, Johnson/Desc/First/Batch/Law/K8Disc.lean), IS A FUNCTION OF THE STRUCTURE's PLANNED NUMBERS
AND OF
THE SKELETON OF THE LIST OF TABLES (`shapesOf`, OnBytes/Tie/Pv/Tail/ClosedRec.lean: matrix, rows in
a
block, first entry), where every table lies on the third vector: NOT OF THE WEIGHTS. One definition
and
theorems: counting.

  `readsLenOf NM mats sh`: over the matrices mu < NM, over the tables of sh on mu: the matrix's rows
    over the table's rows in a block.
  `reads_length`: **every table on the third vector ⊢ (readsList tl funs).length = readsLenOf tl.NM
    tl.mats (shapesOf funs).**
  `top8_of_skel`: so `top8 tl funs = firstOf tl tl.NM + readsLenOf .. * tl.stepF`.
  `reads_length_at_batch`: **g < 12: at every state reached in front of the batching of the layers'
    segment 2 g: there is the list, and at every structure tl the number of its reads is
    readsLenOf tl.NM tl.mats (layShapes Bs.G₀.W.layers g): the skeleton a term off the public
    parameters** (by `funsSkel_at_batch`, FunsAtBatch.lean).
Limits. That the state's structure has the plan's NM and mats is not shown here. The layers'
segments
alone. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.FunsAtBatch
import Johnson.Desc.First.Batch.Law.K8Disc

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port (readsList segsOf)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes)
open Cb.Pv.Tail (Tab)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The number of reads, off the planned numbers and the skeleton. -/
def readsLenOf (NM : ℕ) (mats : Array TMat) (sh : List Tab) : ℕ :=
  ((List.range NM).map fun mu =>
    (sh.map fun t => if t.mat = mu then (mats.getD mu {}).m / t.len else 0).sum).sum

/-- One matrix's reads, table by table. -/
theorem segs_length (tl : HTailF2) (mu : ℕ) : ∀ L : List HFun, (∀ Fn ∈ L, Fn.tree = 2) →
    (L.flatMap (segsOf tl mu 0)).length = 0 ∧
      (L.flatMap (segsOf tl mu 2)).length =
        ((L.map fun Fn : HFun => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)).map fun t =>
          if t.mat = mu then (tl.mats.getD mu {}).m / t.len else 0).sum
  | [], _ => ⟨rfl, rfl⟩
  | Fn :: L, h => by
    obtain ⟨i0, i2⟩ := segs_length tl mu L fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ht : Fn.tree = 2 := h Fn List.mem_cons_self
    constructor
    · rw [List.flatMap_cons, List.length_append, i0]
      unfold segsOf
      simp [ht]
    · rw [List.flatMap_cons, List.length_append, i2, List.map_cons, List.map_cons, List.sum_cons]
      congr 1
      unfold segsOf
      by_cases e : Fn.mat = mu
      · simp [ht, e]
      · simp [e]

/-- **THE NUMBER OF READS IS THE SKELETON's.** -/
theorem reads_length (tl : HTailF2) (funs : Array HFun) (h : ∀ Fn ∈ funs.toList, Fn.tree = 2) :
    (readsList tl funs).length = readsLenOf tl.NM tl.mats (shapesOf funs) := by
  unfold readsList readsLenOf shapesOf
  rw [List.length_flatMap]
  congr 1
  refine List.map_congr_left fun mu _ => ?_
  obtain ⟨i0, i2⟩ := segs_length tl mu funs.toList h
  show ([0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl mu un)).length = _
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
    i0, i2, Nat.zero_add]

/-- So the number of indices that the ties and the reads take. -/
theorem top8_of_skel (tl : HTailF2) (funs : Array HFun) (h : ∀ Fn ∈ funs.toList, Fn.tree = 2) :
    K9L.top8 tl funs =
      OnBytes.Tie.Pv.Tail.Port.firstOf tl tl.NM + readsLenOf tl.NM tl.mats (shapesOf funs) *
    tl.stepF := by
  unfold K9L.top8
  rw [reads_length tl funs h]

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **IN FRONT OF THE BATCHING OF A LAYERS' SEGMENT.** -/
theorem reads_length_at_batch (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s')) :
    ∃ funs, s'.funs? = some funs ∧ ∀ tl : HTailF2,
      (readsList tl funs).length = readsLenOf tl.NM tl.mats (layShapes Bs.G₀.W.layers g) := by
  obtain ⟨funs, f1, f2, f3⟩ := funsSkel_at_batch hS hR O hg h
  exact ⟨funs, f1, fun tl => by rw [reads_length tl funs f3, f2]⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.segs_length
#print axioms VerifiableInference.Desc.LinkJoin.reads_length
#print axioms VerifiableInference.Desc.LinkJoin.top8_of_skel
#print axioms VerifiableInference.Desc.LinkJoin.reads_length_at_batch
