-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/AttSkelAtBatch.lean: THE 12 ATTENTION SEGMENTS: THE SKELETON OF THE LIST
OF TABLES, THE NUMBER
OF READS, AND THE NUMBER THAT "THE ROWS FIT" BOUNDS, AT EVERY STATE REACHED IN FRONT OF THE
BATCHING: TERMS OFF
THE PUBLIC PARAMETERS. With FunsAtBatch.lean, HeadSkel.lean and RowsNumberAtBatch.lean: ALL 25
SEGMENTS. In
the goals' scope. Statements and proofs: calls.

  `attSkel_at_batch`: **g < 12: reached at 14 (2 g + 1) + 9 ⊢ ∃ a funs, Bs.G₀.W.A[g]? = some a ∧
s.funs? =
    some funs ∧ shapesOf funs = attShapes a.S (nScores a.S) ∧ every table on the third vector**: by
    `funsSkel_att_reached` (Johnson/Desc/First/Att/Door/Law/K5FunsSkelReached.lean:
the
    same at 14 (2 g + 1) + 6, behind the sending of the reads with its quiet step, which makes the
    list there) and `funs_from_reads` (FunsAtBatch.lean).
  `reads_length_att`: so the number of reads there (`reads_length`, ReadsLenOfSkel.lean).
  `rowsNumber_att`: **there are the ledger G, the list funs, the built segment Xl, the plan a: and
at
    every structure tl' that reads as the state's: G.planClaimsF + top8 tl' funs = rowsTerm Xl.tl
    a.nLin (attShapes a.S (nScores a.S)).**
Limits. The closed inequality itself is shown nowhere here. "Reads as the state's": rowsRead tl' =
rowsRead of the state's structure: the caller's. `rowsNumber_att` at the start `ProofFile.startS Z`. No
soundness statement.

-/
import Johnson.Desc.First.Link.Law.RowsNumberAtBatch
import Johnson.Desc.First.Att.Door.Law.K5FunsSkelReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port (readsList)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf attShapes nScores)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE SKELETON IN FRONT OF THE BATCHING, AT THE ATTENTION SEGMENTS.** -/
theorem attSkel_at_batch (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {Q : Type}
    {start : Q → S} {z : Q} {s' : S} (h : Reach 0 c.blocksInOrder start (14 * (2 * g + 1) + 9) (z, s')) :
    ∃ a funs, Bs.G₀.W.A[g]? = some a ∧ s'.funs? = some funs ∧
      shapesOf funs = attShapes a.S (nScores a.S) ∧ ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  obtain ⟨s, r, q⟩ := funs_from_reads hS hR O (l := 2 * g + 1) (by omega) h
  obtain ⟨a, funs, a1, a2, a3, a4⟩ := H2K5.Door.funsSkel_att_reached hS hR O hg r
  exact ⟨a, funs, a1, q.trans a2, a3, a4⟩

/-- So the number of reads there. -/
theorem reads_length_att (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {Q : Type}
    {start : Q → S} {z : Q} {s' : S} (h : Reach 0 c.blocksInOrder start (14 * (2 * g + 1) + 9) (z, s')) :
    ∃ a funs, Bs.G₀.W.A[g]? = some a ∧ s'.funs? = some funs ∧ ∀ tl : HTailF2,
      (readsList tl funs).length =
        readsLenOf tl.NM tl.mats (attShapes a.S (nScores a.S)) := by
  obtain ⟨a, funs, a1, a2, a3, a4⟩ := attSkel_at_batch hS hR O hg h
  exact ⟨a, funs, a1, a2, fun tl => by rw [reads_length tl funs a4, a3]⟩

/-- **THE NUMBER THAT "THE ROWS FIT" BOUNDS, AT THE ATTENTION SEGMENTS.** -/
theorem rowsNumber_att (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s' : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s')) :
    ∃ G funs Xl a tl, s'.fork? = some G ∧ s'.funs? = some funs ∧ s'.tl? = some tl ∧
      Bs.G₀.built[2 * g + 1]? = some Xl ∧ Bs.G₀.W.A[g]? = some a ∧
      ∀ tl', rowsRead tl' = rowsRead tl →
        G.planClaimsF + K9L.top8 tl' funs =
          rowsTerm Xl.tl a.nLin (attShapes a.S (nScores a.S)) := by
  obtain ⟨a, funs, a1, f1, f2, f3⟩ := attSkel_at_batch hS hR O hg h
  obtain ⟨G, n, g1, g2, g3⟩ := planClaims_at_batch hS hR O (l := 2 * g + 1) (by omega) h
  have hn : n = a.nLin := by
    unfold planClaimsAt at g2
    rw [if_neg (by omega), show (2 * g + 1) / 2 = g by omega, a1] at g2
    exact (Option.some.inj g2).symm
  obtain ⟨-, Xl, -, -, -, -, hX, -⟩ := (IM.ground_named hS hR O.pub O.blank).1 g hg
  have hx : ((2 * g + 1, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches := by
    unfold P1K8S.stretches
    refine List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), ?_⟩
    have n24 : 2 * g + 1 ≠ 24 := by omega
    simp [n24]
  have hr := planned_at_batch planned_rows hS hR O hx hX (z, s') h
  obtain ⟨tl, t1, t2⟩ := Option.map_eq_some_iff.1 hr
  refine ⟨G, funs, Xl, a, tl, g1, f1, t1, hX, a1, fun tl' ht => ?_⟩
  rw [top8_congr (ht.trans t2) funs, top8_of_skel Xl.tl funs f3, f2, g3, hn]
  rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.attSkel_at_batch
#print axioms VerifiableInference.Desc.LinkJoin.reads_length_att
#print axioms VerifiableInference.Desc.LinkJoin.rowsNumber_att
