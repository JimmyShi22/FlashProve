-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FitsLater.lean: the executable test `Thread.fits` (Thr.lean) at
the invariants of the shared chain and the second chain at the full size (`lettersShared`,
SharedHead.lean; `lettersLast`, LastHead.lean). `Sits` (File.lean) asks the test at all three
chains; `fits_head` (FitsHead.lean) gives it at the first. No definition.

  1  `fwdFit_beyond`   the test `fwdFit` on forward rows passes at every number, if it passes at a
     number from which on the rows ask and close nothing
  2  `rows_shared_beyond`, `rows_last_beyond`   the two chains' rows ask and close nothing beyond
     their lists of places
  3  `fits_shared`, `fits_last`   the test at the two invariants

What the two lemmas of 3 leave as hypotheses.
  * `hone`: `fwdFit` at the chain's written list of places. It has no free variable.
  * `hp`: the description's own test on the plan (`head_planOk`, FirstSits.lean, gives it).
  * `hfix`: each tree that is available at a border is fixed by the challenges heard there. This is
    a condition on the argument `fixed`.
  * At the second chain also `htk`: each tree in the argument `taken` is declared as taken over.

Limits.
  * Conditional lemmas on this folder's own definitions. `hfix` and `htk` are proved nowhere.
  * Full size only.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.LastHead
import Johnson.Desc.ProofFile.Honest.Thread.Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- The test on forward rows passes at every number `n`, if it passes at `len` and the rows from
`len` on ask and close nothing. -/
theorem fwdFit_beyond {ι : Type} [DecidableEq ι] {start : List ι} {row : Nat → FwdRow ι}
    {len : Nat} (h0 : fwdFit start row len = true)
    (he : ∀ b, len ≤ b → (row b).asks = [] ∧ (row b).shuts = []) (n : Nat) :
    fwdFit start row n = true := by
  unfold fwdFit at h0 ⊢
  refine List.all_eq_true.2 fun b _ => ?_
  by_cases hb : b < len
  · exact List.all_eq_true.1 h0 b (List.mem_range.2 hb)
  · obtain ⟨e1, e2⟩ := he b (Nat.le_of_not_lt hb)
    show (((row b).asks ++ (row b).shuts).all (fwdOpen start row b).contains) = true
    simp only [e1, e2, List.append_nil, List.all_nil]

end ProofFile.Honest

namespace ProofFile.Honest.SharedThread
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS sharedPlaces)
open P5J (TS F0T)

/-- Beyond the list of places the shared chain's forward rows are empty. -/
theorem rows_shared_beyond (split : Bool) (b : Nat) (hb : (sharedPlaces split).length ≤ b) :
    (SharedRows.rows split b).asks = [] ∧ (SharedRows.rows split b).shuts = [] := by
  unfold SharedRows.rows
  rw [List.getElem?_eq_none hb]
  exact ⟨rfl, rfl⟩

/-- **`Thread.fits` at the shared chain's invariant.** -/
theorem fits_shared (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X₀ X P₁ Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
    (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS Desc.K14.St P₁ Wt)
    (shape : Nat → Desc.K14.St → Bool) (nothingLeft : Desc.K14.St → Bool)
    (order : Desc.K14.St → Prop)
    (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
    (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
      Place × Table)
    (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
    (Rd : Nat → Common W₀ Rc OnBytes.TableKey → Desc.K14.St → Prop)
    (Kp : Place → Desc.K14.St → Desc.K14.St → Prop) (w : Common W₀ Rc OnBytes.TableKey)
    (hone : fwdFit SharedRows.start (SharedRows.rows true) (sharedPlaces true).length = true)
    (hp : (F0T OnBytes.secondHashFunction Zp Np cF).planOk = true)
    (hfix : ∀ b, b ≤ (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length →
      ∀ j, j < treesTo (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder b →
      fixed (.own j) ≤ roundsTo (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder b) :
    (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
      w).thread.fits (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length = true := by
  refine Thread.fits_of _ (fwdFit_beyond hone (rows_shared_beyond true) _)
    (fun z hz => ((planOk_all hp).2.1 z hz).2) (fun σ hσ => ?_)
    (fun b hb σ hσ => ?_) (Nat.le_refl 0)
  · have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'
  · have hσ' : σ ∈ (List.range (treesTo (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder b)).map
        Fmt.TreeSource.own := hσ
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hσ'
    show fixed (.own j) ≤ 0 + roundsTo (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder b
    rw [Nat.zero_add]
    exact hfix b hb j (List.mem_range.1 hj)

end ProofFile.Honest.SharedThread

namespace ProofFile.Honest.LastThread
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Last (MeaningL PromMeaningL startLast lastPlaces)
open P5J (TS F0T)

/-- Beyond the list of places the second chain's forward rows are empty. -/
theorem rows_last_beyond (b : Nat) (hb : lastPlaces.length ≤ b) :
    (LastRows.rows b).asks = [] ∧ (LastRows.rows b).shuts = [] := by
  unfold LastRows.rows
  rw [List.getElem?_eq_none hb]
  exact ⟨rfl, rfl⟩

/-- **`Thread.fits` at the second chain's invariant.** The invariant's parameters are named `T`,
with an equation, to keep the hypothesis `hfix` readable. -/
theorem fits_last (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X₀ X Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
    (N : NumbersS) (Mg : Local W₀ Rc ProofFile.Inst Tr → MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt)
    (ML : MeaningL VerifiableInference.Desc.Third.S₃ Wt)
    (PL : PromMeaningL Desc.K14.St VerifiableInference.Desc.Third.S₃ (ProofFile.InstPub × TS))
    (order : VerifiableInference.Desc.Third.S₃ → Prop) (taken : List Fmt.TreeSource)
    (ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
      (ProofFile.InstPub × TS) × Desc.K14.St)
    (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt)
    (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table)
    (fixed : Fmt.TreeSource → Nat) (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → VerifiableInference.Desc.Third.S₃ → Prop)
    (Kp : Place → VerifiableInference.Desc.Third.S₃ → VerifiableInference.Desc.Third.S₃ → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    {T : Thread Bk VerifiableInference.Desc.Third.S₃ ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr)
      (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
    (hT : T = (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd
      Kp w).thread)
    (hone : fwdFit startLast LastRows.rows lastPlaces.length = true)
    (hp : (F0T OnBytes.secondHashFunction Zp Np cF).planOk = true)
    (htk : ∀ σ ∈ taken, ∃ c j, σ = Fmt.TreeSource.taken c j)
    (hfix : ∀ b, b ≤ (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.length → ∀ σ ∈ T.hand b,
      T.fixed σ ≤ T.front + roundsTo T.bs b) :
    T.fits (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.length = true := by
  subst hT
  refine Thread.fits_of _ (fwdFit_beyond hone rows_last_beyond _)
    (fun z hz => ((planOk_all hp).2.2 z hz).2) htk hfix ?_
  show (declsTo (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length).length ≤
    (declsTo (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
        (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length ++
      declsTo (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
        (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length).length
  rw [List.length_append]
  exact Nat.le_add_right _ _

end ProofFile.Honest.LastThread

#print axioms ProofFile.Honest.fwdFit_beyond
#print axioms ProofFile.Honest.SharedThread.rows_shared_beyond
#print axioms ProofFile.Honest.SharedThread.fits_shared
#print axioms ProofFile.Honest.LastThread.rows_last_beyond
#print axioms ProofFile.Honest.LastThread.fits_last
