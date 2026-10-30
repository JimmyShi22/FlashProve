-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FrontMeans.lean: THE SMALLNESS TEST: WHERE `zeroColumnWeight`
(Johnson/Desc/ProofFile/Honest/K8/Share.lean) FINDS NO COLUMN, NO READ OF THE LIST "K8.equations"
REFUSES FOR A COLUMN's SUM THAT IS 0. Statements and proofs, on the list's own text. No prover.
LEMMAS; NONE OF THE LIBRARY's GOALS. NOTHING IS CLAIMED ON COMPLETENESS, SOUNDNESS OR HIDING.

A read's text makes its entries by `readEnts`, which carries a mark "none of the columns' sums is
0", and then tests the mark ("internal-f-table-read"). The sums are those that the step `eqWeights`
has laid.
  `readEnts_keeps`   where no sum is 0 the mark stays set
  `gamAt_is`         the sum that `eqWeights` lays for a column IS `columnWeight` at the batching
      element
  `front_none`       what "finds no column" says, column by column
  **`live_of_front`**   behind `eqWeights`, at the ledger's batching element: `zeroColumnWeight` =
      none gives `LiveAt` (Johnson/Desc/K8/Honest/FallLive.lean) at every read of a matrix of the
      list
  **`mark_of_front`**   so every read's mark is set: the test on it says yes
The other way (a yes of the list gives `LiveAt`) is Johnson/Desc/K8/Honest/FallLive.lean's
`eqTail_live`.
Limits. On that one test of a read. The read's other steps, which ask no value, can refuse. The list
asks the columns of matrices on which a table lies; `zeroColumnWeight` runs over all.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K8.Share
import Johnson.Desc.K8.Honest.FallLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims VerifiableInference.Desc.First.TailClaims.Law
open VerifiableInference.Desc.First.K8.Honest
open OnBytes.Tie.Pv.Tail.Port

/-- Where no sum is 0 the mark stays set. -/
theorem readEnts_keeps (tl : HTailF2) (Fn : HFun) (sg tU cols : Nat) (minus : E) (gc : Array E) :
    ∀ (count c : Nat) (ents : Array Ent) (out : Array Ent) (nz : Bool),
      tl.readEnts Fn sg tU cols minus gc count c ents true = some (out, nz) →
      (∀ j, c ≤ j → j < c + count → isZeroE (gc.getD j zeroE) = false) → nz = true := by
  intro count
  induction count with
  | zero =>
    intro c ents out nz h _
    simp only [HTailF2.readEnts, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | succ n ih =>
    intro c ents out nz h hz
    unfold HTailF2.readEnts at h
    cases hp : tl.tabAt Fn c sg with
    | none => simp [hp] at h
    | some pos =>
      simp only [hp] at h
      rw [hz c (Nat.le_refl c) (by omega)] at h
      exact ih _ _ _ _ h (fun j h1 h2 => hz j (by omega) (by omega))

/-- The sum that is laid for a column is the column's weight at the batching element. -/
theorem gamAt_is (tl : HTailF2) (chi : E) (hvp : tl.vp = powers chi tl.tau) (mu c : Nat)
    (hc : c < (tl.mats.getD mu {}).k) : (gamAt tl mu).getD c zeroE = columnWeight tl chi mu c := by
  unfold gamAt columnWeight
  rw [getD_map_range _ _ _ _ hc, hvp]

/-- What "finds no column" says. -/
theorem front_none (tl : HTailF2) (chi : E) (h : zeroColumnWeight tl chi = none) (mu : Nat)
    (hmu : mu < tl.NM) (c : Nat) (hc : c < (tl.mats.getD mu {}).k) :
    isZeroE (columnWeight tl chi mu c) = false := by
  unfold zeroColumnWeight at h
  have h1 := List.findSome?_eq_none_iff.1 h mu (List.mem_range.2 hmu)
  have h2 := List.findSome?_eq_none_iff.1 h1 c (List.mem_range.2 hc)
  cases hz : isZeroE (columnWeight tl chi mu c) with
  | false => rfl
  | true =>
    rw [hz] at h2
    exact absurd h2 (by simp)

/-- **Behind the step that lays the sums.** tlb: the data handed to it; st: the list's state, whose
ledger holds the batching element. -/
theorem live_of_front (tlb tl1 : HTailF2) (front : Nat) (st st1 : St)
    (hW : eqWeights tlb front st = .ok (tl1, st1))
    (h : zeroColumnWeight tlb st.1.theta = none) (x : HFun × Nat) (hx : x.1.mat < tl1.NM) :
    LiveAt tl1 x := by
  obtain ⟨hP, e1, hgam⟩ := eqWeights_spec tlb tl1 front st st1 hW
  have h' : zeroColumnWeight tl1 st.1.theta = none :=
    ((congrArg (fun t => zeroColumnWeight t st.1.theta) e1).trans rfl).trans h
  intro c hc
  rw [(hgam x.1.mat hx).2, gamAt_is tl1 st.1.theta hP.vp x.1.mat c hc]
  exact front_none tl1 st.1.theta h' x.1.mat hx c hc

/-- **So every read's mark is set.** -/
theorem mark_of_front (tlb tl1 : HTailF2) (front : Nat) (st st1 : St)
    (hW : eqWeights tlb front st = .ok (tl1, st1))
    (h : zeroColumnWeight tlb st.1.theta = none) (Fn : HFun) (hFn : Fn.mat < tl1.NM)
    (sg tU cols : Nat) (minus : E) (ents out : Array Ent) (nz : Bool)
    (hr : tl1.readEnts Fn sg tU cols minus (tl1.gamV.getD Fn.mat #[]) (tl1.mats.getD Fn.mat {}).k 0
      ents true = some (out, nz)) : nz = true :=
  readEnts_keeps tl1 Fn sg tU cols minus _ _ 0 ents out nz hr fun j _ hj =>
    live_of_front tlb tl1 front st st1 hW h (Fn, sg) hFn j (by simpa using hj)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.readEnts_keeps
#print axioms ProofFile.Honest.K8.live_of_front
#print axioms ProofFile.Honest.K8.mark_of_front
#print axioms ProofFile.Honest.K8.gamAt_is
#print axioms ProofFile.Honest.K8.front_none
