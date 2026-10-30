-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/OmegaTold.lean: AT THE PROOF FILE's OWN DESCRIPTION (ProofFile.fileDescBy at
K14's shared seat and the last chain's seat secondSeatOf, pulled to any type of instances): FROM ITS
DATA AND ITS planOk ALONE: IT TELLS OF THE TREE NUMBER D.t₁ + 1 AN ORACLE MESSAGE THAT HAS THE SHAPE
OF A TREE LAID FOR OMEGA ALONE; SO THE LAST TABLE's TEST ON THE PLAN AT THE TREE OF OMEGA's COPY
("PlanTreeO", Johnson/LLT25R/LastTreeO.lean, whose right side is written
out here) IS A
THEOREM THERE. Two theorems over Johnson/Desc/Book/ToldShared.lean. No definition.


  omega_told_at_proofFile   ∃ o', G.oracleAt (D.t₁ + 1) = some o' ∧
                            ShapeIs (shapeAlone cs S.omega) o'.
  planTreeO_at_proofFile    ∀ lay, layTrees cs #[⟨S.omega, S.omegaLeafClass⟩] = some lay →
                            ∀ o', G.oracleAt (D.t₁ + 1) = some o' →
                            ShapeIs (lay.shapes.getD 0 {}) o'.
LETTERS. cs, S: Z.p.chains.made.sized.proof.codes and ….batch.shape: the shared chain's p14Of and
the last chain's p₁₄Z both read these two (by rfl; the proof spends it). bp, tests, si, last, fo:
free: what K14's sharedSeatOf is handed. get, start, ch (the first chain), g: free.
HOW THE PREMISES OF ToldShared.lean ARE MET. blocksOk of the three flat lists: clauses of planOk ·
hsh: the frame lays the seat's chain by Chain.retype, which keeps `oracles` · withU returns, and
both sendings' trees can be laid: else a sub-protocol of the shared chain fails its test on the
plan · S is lawful: K14's second part's test on the plan asks linOk.
IS IT EMPTY? Two premises: G.data file = .ok D and G.planOk = true. Neither is evaluated in this
file. Whoever runs the description asks both. The first theorem says that the test is
not true for nothing on the description's side: something is told of that tree.
Nothing on soundness.
-/
import Johnson.Desc.ProofFile.Frames1
import Johnson.Desc.ProofFile.Lot.K14Seat
import Johnson.Desc.ProofFile.Lot.LastChain
import Johnson.Desc.Book.ToldShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes
open ProofFile (SecondHashFunctionArgument LinksBy Pub Inst InstPub Cl fileDescBy)
open _root_.Desc.K14 (P14 St sharedSeatOf p14Of chainOf)
open VerifiableInference.Desc.K12.Coin (ShapeIs)

/-- **What the proof file's own description tells of the tree number D.t₁ + 1.** -/
theorem omega_told_at_proofFile {σ Xi' : Type} (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : Pub)
    (bp : List (Nat × Nat)) (tests : P14 → List (Block St Unit)) (si : List String)
    (last : List (Block St Unit) → Block St Unit) (fo : Bool) (N : H2U.Places4)
    (get : σ → First.S) (start : InstPub → σ) (ch : Chain σ Cl) (g : Xi' → Inst)
    (G : FileDescription Xi')
    (hG : G = (fileDescBy o mk Z (sharedSeatOf Z.p.chains bp tests si last fo)
      (P2Third.secondSeatOf Z N) get start ch).pull g)
    (file : String) (D : Maker.WholeD) (hD : G.data file = .ok D) (hp : G.planOk = true) :
    ∃ o', G.oracleAt (D.t₁ + 1) = some o' ∧
      ShapeIs (shapeAlone Z.p.chains.made.sized.proof.codes
        Z.p.chains.made.sized.proof.batch.shape.omega) o' := by
  subst hG
  obtain ⟨b1, b2, b3⟩ := blocksOk_of_planOk _ hp
  have b2' : blocksOk ((chainOf Z.p.chains (p14Of Z.p.chains bp) (tests (p14Of Z.p.chains bp))
      last).retype : Chain St Cl).blocksInOrder = true := b2
  have k := first_ok_retype (Cl' := Cl) (P2Third.secondSeatOf Z N).chain b3
  have k' : (Z.p.chains.made.sized.proof.codes.lengthsOk &&
      linOk Z.p.chains.made.sized.proof.codes Z.p.chains.made.sized.proof.batch.shape &&
      Third.plainArm Z.p.chains.made.sized.proof.batch.shape) = true := k
  simp only [Bool.and_eq_true] at k'
  have hok := ok_of_linOk k'.1.2
  obtain ⟨u, Tu, TO, hU, hTu, hTO⟩ := can_of_back (p14Of Z.p.chains bp)
    (fun b hb => back_ok_retype _ b2' b (List.mem_append_left _ hb))
  exact told_at_shared _ file D Z.p.chains (p14Of Z.p.chains bp) (tests (p14Of Z.p.chains bp)) last
    u Tu TO hD b1 (oraclesOf_retype _ rfl) hU hTu hTO hok

/-- **The last table's test on the plan at the tree of Omega's copy, at the proof file's own
description.** -/
theorem planTreeO_at_proofFile {σ Xi' : Type} (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : Pub)
    (bp : List (Nat × Nat)) (tests : P14 → List (Block St Unit)) (si : List String)
    (last : List (Block St Unit) → Block St Unit) (fo : Bool) (N : H2U.Places4)
    (get : σ → First.S) (start : InstPub → σ) (ch : Chain σ Cl) (g : Xi' → Inst)
    (G : FileDescription Xi')
    (hG : G = (fileDescBy o mk Z (sharedSeatOf Z.p.chains bp tests si last fo)
      (P2Third.secondSeatOf Z N) get start ch).pull g)
    (file : String) (D : Maker.WholeD) (hD : G.data file = .ok D) (hp : G.planOk = true) :
    ∀ lay, layTrees Z.p.chains.made.sized.proof.codes
        #[⟨Z.p.chains.made.sized.proof.batch.shape.omega,
          Z.p.chains.made.sized.proof.batch.shape.omegaLeafClass⟩] = some lay →
      ∀ o', G.oracleAt (D.t₁ + 1) = some o' → ShapeIs (lay.shapes.getD 0 {}) o' := by
  intro lay hl o' ho
  obtain ⟨o'', hat, h3⟩ :=
    omega_told_at_proofFile o mk Z bp tests si last fo N get start ch g G hG file D hD hp
  obtain rfl : o'' = o' := Option.some.inj (hat.symm.trans ho)
  rw [lay_single hl]
  exact h3

end VerifiableInference.Desc.Book

#print axioms VerifiableInference.Desc.Book.omega_told_at_proofFile
#print axioms VerifiableInference.Desc.Book.planTreeO_at_proofFile
