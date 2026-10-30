-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/MasksByPlace.lean:
THE TOOL OF PileByPlace.lean AT THE SENTENCE "EVERY ROW ON THE TABLE NAMES MASK ENTRIES OF
THE INDEX MASKS' MESSAGE ALONE", WRITTEN IN ITS OWN LETTERS (K13.pileMasksC unfolds to just this).
  MasksOk s     the sentence.
  row_masks     the pending row's one mask entry names the number that the row's function was
                handed: by pendingRowO_iff alone; nothing is asked of the ledgers.
  masks_law     PileLawZ MasksOk, GIVEN hM3: kind K13's batching earns the sentence
                (atM3_pileMasks): same: the sentence reads the rows and the number alone; zero: no
                row lies, so it holds outright; push: row_masks.
  start_rows    the first chain's own start has no row, at every public part of an instance.
  fold_masks    **in the goals' scope, given hM3: the sentence holds at every state that a fold over
                a front stretch of the first chain returns from the chain's own start.**
What is not claimed. hM3. Nothing on soundness.

-/
import Johnson.LPFK9R.PileByPlace
import Johnson.IMR.RecRun
import Johnson.Desc.First.Pend.RowMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)
open Johnson.Desc.First.Walk
open Meaning.K2

/-- Every row on the table names mask entries of the index masks' message alone. -/
def MasksOk (s : S) : Prop :=
  (s.rows.all fun r => r.masks.all fun t => t.1.oracle == s.out.indexMasks) = true

/-- The pending row's one mask entry names the number that was handed in. -/
theorem row_masks {lay : WsLay} {im : Nat} {o : WsForkOut} {claims : Nat} {Sh : Params.LinShape}
    {os os' : Array OnBytes.Oracle} {row : TensorRow}
    (h : Pend.pendingRowO lay im o claims Sh os = .ok (row, os')) :
    (row.masks.all fun t => t.1.oracle == im) = true := by
  obtain ⟨-, -, -, -, _, _, -, -, -, -, -, _, -, _, -, l, hl, c, l', ht, rfl, rfl⟩ :=
    (Pend.pendingRowO_iff lay im o claims Sh os os' row).1 h
  rw [List.all_eq_true]
  intro t ht'
  rw [List.mem_singleton] at ht'
  subst ht'
  exact beq_self_eq_true _

/-- **The sentence meets what the tool asks**, given that kind K13's batching earns it. -/
theorem masks_law (hM3 : ∀ (p : K13.Where) (s : S) (rs : List Fmt.RoundView)
      (gs : List (List (Nat × List UInt64))) (t : S),
      (K13.atM3 (Cl := Unit) p).decide s rs gs = .ok t → MasksOk t) : PileLawZ MasksOk where
  same := fun s s' q h => by
    unfold MasksOk at h ⊢
    rw [q.1, q.2.1]
    exact h
  zero := fun Q fvs kCol s t k h0 _ => by
    unfold MasksOk
    rw [(openLayZero_rows k).1, h0]
    rfl
  push := fun X counts left lay lin s t k h => by
    rcases clearWith_cases k with q | ⟨w, r, os, hr, e1, e2, -, -⟩
    · unfold MasksOk at h ⊢
      rw [q.1, q.2.1]
      exact h
    · unfold MasksOk at h ⊢
      rw [e1, e2, List.all_append, h, Bool.true_and]
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      exact row_masks hr
  batch := fun p s rs gs t k _ => hM3 p s rs gs t k

/-- **The first chain's own start has no row.** -/
theorem start_rows {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    (ProofFile.startS Z p).rows = [] := by
  have e0 : Z.s₀ = S.firstRecord Z.first.codes Z.first.shape Z.first.layout := by
    have k := pub_start h
    unfold S.startP at k
    split at k
    · exact (Option.some.inj k).symm
    · cases k
  unfold ProofFile.startS
  dsimp only
  split
  · rw [e0]
    rfl
  · rfl

/-- **IN SCOPE, GIVEN hM3: THE SENTENCE AT EVERY STATE OF THE FOLD.** -/
theorem fold_masks (hM3 : ∀ (p : K13.Where) (s : S) (rs : List Fmt.RoundView)
      (gs : List (List (Nat × List UInt64))) (t : S),
      (K13.atM3 (Cl := Unit) p).decide s rs gs = .ok t → MasksOk t)
    {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (p : ProofFile.InstPub) (ft : Nat)
    (l₁ l₂ : List (Block S Cl)) (hc : c.blocksInOrder = l₁ ++ l₂) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn)
    (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn)
    (hf : foldBlocks ft l₁ (ProofFile.startS Z p) rs cols = .ok r) :
    MasksOk r.1 := by
  have h0 : (ProofFile.startS Z p).rows = [] := start_rows O.pub p
  refine fold_rides (masks_law hM3) hS hR O (ProofFile.startS Z p) ?_ h0 ft l₁ l₂ hc rs cols r hf
  unfold MasksOk
  rw [h0]
  rfl

end LPFK9

#print axioms LPFK9.row_masks
#print axioms LPFK9.masks_law
#print axioms LPFK9.start_rows
#print axioms LPFK9.fold_masks
