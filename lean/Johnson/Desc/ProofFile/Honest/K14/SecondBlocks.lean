-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SecondBlocks.lean: kind K14: "K14, second part" (the place
⟨3, none, 0, .K14⟩): THE THIRD AND THE FOURTH OF THE FIVE TESTS OF secondRest5
(Honest/K14/OmegaJoin.lean), AND THE FACTS ON THE WEIGHTS (WeightsFit, Honest/K14/DotPads.lean),
FROM ONE PREMISE ON THE ROWS THAT LIE ON THE TABLE AT THE FIRST CHAIN's END. Statements with their
proofs; one definition with code.

  weightsFit_blocks   **weights of a block's form (BlockForm, Honest/K14/BlockForm.lean) name no
                  written-out variable twice, and only their own**: WeightsFit: by the library's
                  distinct_run (Johnson/Desc/First/Pend/RowOk.lean) and form_vars
  secondRest3     secondRest5 WITHOUT ITS THIRD AND ITS FOURTH TEST: the same text less these two
                  entries. THE LAW THAT TIES THE TWO: rest5_of_three
  rest5_of_three  **secondRest5 from secondRest3**, where the border's weights each have a block's
                  form and do not reach beyond the matrix's rows: by varsTest_blocks and
                  cutTest_blocks (Honest/K14/CutBlocks.lean)
  border_rows     **what the start of the last chain takes of the first chain's last state**: that
                  state has one row on the table (the library's First.S.rows), and the border's
                  weights are that row's: by start_at_last (Honest/K14/SecondDoor.lean) and the
                  library's start₃E_inv, firstOutFrom_inv, start₃_inv
                  (Johnson/Desc/Third/Law/AtDoor.lean) and firstOfS_parts
                  (Johnson/Desc/Last/ShapeRowZero.lean)
  blocks_at_border   so, under hR (below), the border's weights have a block's form

WHO CALLS THEM: second_door_three_saidS (Honest/K14/SecondBlocksAtHead.lean) and the statements of
Honest/K14/SecondBlocksAtFold.lean.

THE PREMISE hR. Each row on the table at the first chain's last state s₁ has weights that are the
library's own blocks (stretchBlocks, OnBytes/Iop/Lin.lean) of stretches that do not reach beyond the
matrix's rows, each times an element, AT THE SHAPE AT WHICH THE TESTS ARE ASKED. s₁ IS A VARIABLE:
nothing ties it to a run but the return of the start. hR IS SHOWN HERE OF NO STATE
(Honest/K14/SecondBlocksAtFold.lean: at the return of a fold).

What is not claimed. That hR holds at any run. That the three tests of secondRest3 hold at any run.
That the sub-protocol accepts. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaJoin
import Johnson.Desc.ProofFile.Honest.K14.CutBlocks
import Johnson.Desc.First.Pend.RowOk
import Johnson.Desc.Last.ShapeRowZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (linDotRow linLayOmega linLayW Tensor E stretchBlocks)
open OnBytes.Params (LinShape)
open VerifiableInference.Desc (Own.tensorInOrder Own.placeFits)
open VerifiableInference.Desc.Ground (Clauses ok has)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut FirstEnd₃ takeOver start₃E)
open VerifiableInference.Desc.Third.Law (start₃E_inv firstOutFrom_inv start₃_inv)
open Desc.K14 (St)

/-! ## The facts on the weights -/

/-- **Weights of a block's form name no written-out variable twice, and only their own.** -/
theorem weightsFit_blocks (S : LinShape) (g : List Tensor)
    (h : ∀ w ∈ g, ∃ d q, d ≤ S.kRow ∧ BlockForm S.kRow d q w ∧
      2 ^ d * q + 2 ^ d ≤ S.matrixRows) : WeightsFit g := by
  intro v hv
  obtain ⟨d, q, hd, hf, _⟩ := h v hv
  refine ⟨by rw [hf.2]; exact VerifiableInference.Desc.First.Pend.distinct_run d 0, fun x hx => ?_⟩
  rw [hf.2] at hx
  have := List.mem_range'_1.1 hx
  rw [form_vars hf hd]
  omega

/-! ## Three tests in the place of five -/

/-- secondRest5 (Honest/K14/OmegaJoin.lean) without its third and its fourth test. -/
def secondRest3 (p : P₁₄) (s : S₃) : Clauses :=
  match s.loc.border with
  | none => []
  | some x =>
    ("adopt: statement and book are in step", s.st.oracles.size == s.book.place.size) ::
    ("join: no member twice",
      has s.st.groups[s.loc.own]? (!·.members.contains s.st.oracles.size)) ::
    match takeOver p.S s.loc.own x.shared (s.withCols []) with
    | .error _ => []
    | .ok a =>
      match linDotRow p.S x.g x.shared.psi a.1 (linLayOmega a.2.st.codes p.S) s.loc.w
          (linLayW a.2.st.codes p.S) with
      | none => []
      | some dot =>
        [("addRow: the terms fit their places", has a.2.st.groups[s.loc.own]? fun G =>
            dot.terms.all fun t =>
              Own.tensorInOrder t.v && Own.placeFits a.2.st G t.oracle t.part t.v.vars 0)]

/-- **The third and the fourth test of secondRest5 are true where the border's weights have a
block's form and do not reach beyond the matrix's rows**: so secondRest5 from secondRest3. -/
theorem rest5_of_three (p : P₁₄) (s : S₃)
    (hB : ∀ b, s.loc.border = some b → ∀ w ∈ b.g, ∃ d q, d ≤ p.S.kRow ∧
      BlockForm p.S.kRow d q w ∧ 2 ^ d * q + 2 ^ d ≤ p.S.matrixRows)
    (h3 : ok (secondRest3 p s) = true) : ok (secondRest5 p s) = true := by
  unfold secondRest3 at h3
  unfold secondRest5
  cases hb : s.loc.border with
  | none => rfl
  | some x =>
    rw [hb] at h3
    dsimp only at h3 ⊢
    rw [ok_cons, ok_cons] at h3
    rw [ok_cons, ok_cons, ok_cons, ok_cons]
    simp only [Bool.and_eq_true] at h3 ⊢
    exact ⟨h3.1, h3.2.1, varsTest_blocks p.S x.g (hB x hb), cutTest_blocks p.S x.g (hB x hb),
      h3.2.2⟩

section join
variable (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl)

/-- **What the start of the last chain takes of the first chain's last state**: that state has one
row on the table, and the border's weights are that row's. -/
theorem border_rows (x : ProofFile.InstPub) (s₁ : P5J.TS) (s₂ : St) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s) :
    ∃ r o, s₁.rows = [r] ∧ s.loc.border = some { g := r.g, shared := o } := by
  obtain ⟨f, e, -, hf, -, hst⟩ := start_at_last Zp Np cF x s₁ s₂ s hs
  obtain ⟨f', hf', hs'⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hst
  obtain ⟨-, -, -, -, -, r, hr, hg⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf'
  obtain ⟨-, -, rfl⟩ := start₃_inv _ _ _ _ hs'
  have hp : f.pending = s₁.rows := (VerifiableInference.Desc.Last.firstOfS_parts hf).2.2
  refine ⟨r, VerifiableInference.Desc.Third.sharedOfEnd e, hp ▸ hr, ?_⟩
  show some ({ g := f'.g, shared := VerifiableInference.Desc.Third.sharedOfEnd e } :
    VerifiableInference.Desc.Third.Border) = _
  rw [hg]

/-- **Under hR the border's weights have a block's form and do not reach beyond the matrix's rows.**
hR: each row on the table at the first chain's last state has weights that are the library's own
blocks of stretches that do not reach beyond the matrix's rows, each times an element. -/
theorem blocks_at_border (x : ProofFile.InstPub) (s₁ : P5J.TS) (s₂ : St) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (hR : ∀ row ∈ s₁.rows, ∀ v ∈ row.g,
      ∃ (firstRow : Nat) (values : Array E) (fuel start : Nat) (a : E),
        firstRow + values.size ≤ (ToldDesc.p14At Zp).S.matrixRows ∧
          ∃ t ∈ stretchBlocks (ToldDesc.p14At Zp).S.kRow firstRow values fuel start,
            v = t.scale a) :
    ∀ b, s.loc.border = some b → ∀ w ∈ b.g, ∃ d q, d ≤ (ToldDesc.p14At Zp).S.kRow ∧
      BlockForm (ToldDesc.p14At Zp).S.kRow d q w ∧
        2 ^ d * q + 2 ^ d ≤ (ToldDesc.p14At Zp).S.matrixRows := by
  obtain ⟨r, o, hr, hb⟩ := border_rows Zp Np cF x s₁ s₂ s hs
  intro b hb'
  obtain rfl : b = { g := r.g, shared := o } := Option.some.inj (hb'.symm.trans hb)
  exact blocks_scaled _ _ (hR r (by rw [hr]; exact List.mem_singleton.2 rfl))

end join

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.weightsFit_blocks
#print axioms ProofFile.Honest.K14.rest5_of_three
#print axioms ProofFile.Honest.K14.border_rows
#print axioms ProofFile.Honest.K14.blocks_at_border
