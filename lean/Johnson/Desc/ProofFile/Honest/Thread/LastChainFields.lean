-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/LastChainFields.lean: on the last chain, what Thread/OpensOfPlan.lean
and Thread/QuietAtBase.lean say of the two others.

  `opened_own_lt`   a tree of the chain's own that a round opens is sent by the border
  `opensAvailable_second`   the test at every border, where the sources that are taken over and opened
                   stand in the thread's list `taken`
  `depthsDeclared_of_all`   `DepthsDeclared` at every border, from one sentence on all the chain's rounds
  `quiet_second`, `quiet_second_at_return`   at the base filling no half of the last chain has a stop

This file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.OpensOfPlan
import Johnson.Desc.ProofFile.Honest.Thread.QuietAtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

section
variable {S Cl V W X Pb Xi : Type} {Bk : ProverCoinCounts}

/-- **A tree of the chain's own that a round opens is sent by the border.** -/
theorem opened_own_lt {F : FileDescription Xi} (hp : F.planOk = true) (T : Thread Bk S Cl V W X Pb) {i : Nat}
    (hi : (T.bs.flatMap (·.rounds), i) ∈ [(F.roundsDeclaredByBlocks.1, 0), (F.roundsDeclaredByBlocks.2.1, 1), (F.roundsDeclaredByBlocks.2.2, 2)])
    (hor : ∀ x ∈ T.bs, x.rounds.map (·.entry.roots) = x.oracles.map (·.length)) {b : Nat}
    {d : Fmt.DeclaredRound} (hd : d ∈ declsTo T.bs b) {o : Fmt.Shape × Fmt.TreeSource} (ho : o ∈ d.opens)
    {n : Nat} (hs : o.2 = .own n) : n < treesTo T.bs b := by
  have hT := inTime_plan hp
  unfold BookPlan.inTime at hT
  have h1 := List.all_eq_true.1 hT (T.bs.flatMap (·.rounds), i) hi
  have hsplit : T.bs.flatMap (·.rounds) =
      declsTo T.bs b ++ (T.bs.drop b).flatMap (·.rounds) := by
    unfold declsTo
    rw [← List.flatMap_append, List.take_append_drop]
  obtain ⟨r, hr⟩ := List.mem_iff_getElem?.1 hd
  have hrl : r < (declsTo T.bs b).length := (List.getElem?_eq_some_iff.1 hr).1
  have hr' : (T.bs.flatMap (·.rounds))[r]? = some d := by
    rw [hsplit, List.getElem?_append_left hrl]
    exact hr
  have h3 := List.all_eq_true.1 (List.all_eq_true.1 h1 (d, r) (by
    have e := mem_zipIdx_of _ 0 r d hr'
    rw [Nat.zero_add] at e
    exact e)) o ho
  rw [hs] at h3
  have h3' : ((BookPlan.roundOfRoot (T.bs.flatMap (·.rounds)) n).any fun j =>
      decide (j + (if BookPlan.holdsSampled F.roots i n then 1 else 0) ≤ r)) = true := h3
  cases hj1 : BookPlan.roundOfRoot (T.bs.flatMap (·.rounds)) n with
  | none =>
    rw [hj1] at h3'
    cases h3'
  | some j =>
    rw [hj1] at h3'
    have hj2 : j + (if BookPlan.holdsSampled F.roots i n then 1 else 0) ≤ r :=
      of_decide_eq_true h3'
    have hjr : j ≤ r := Nat.le_trans (Nat.le_add_right _ _) hj2
    have hlt := root_lt _ n j hj1
    have htake : (T.bs.flatMap (·.rounds)).take (j + 1) = (declsTo T.bs b).take (j + 1) := by
      rw [hsplit, List.take_append_of_le_length (by omega)]
    rw [htake, List.map_take] at hlt
    have hle := sum_take_le ((declsTo T.bs b).map (·.entry.roots)) (j + 1)
      (declsTo T.bs b).length (by omega)
    have hall : ((declsTo T.bs b).map (·.entry.roots)).take (declsTo T.bs b).length =
        (declsTo T.bs b).map (·.entry.roots) := by
      apply List.take_of_length_le
      rw [List.length_map]
    rw [hall] at hle
    have htr : ((declsTo T.bs b).map (·.entry.roots)).sum = treesTo T.bs b :=
      roots_eq_trees (T.bs.take b) fun y hy => hor y (List.mem_of_mem_take hy)
    omega

/-- **The test at every border of the last chain.** -/
theorem opensAvailable_second {F : FileDescription Xi} (hp : F.planOk = true)
    (T : Thread Bk F.S₃ F.Cl V W X Pb) (hbs : T.bs = F.second.blocksInOrder)
    (hor : ∀ x ∈ T.bs, x.rounds.map (·.entry.roots) = x.oracles.map (·.length))
    (htk : ∀ d ∈ T.bs.flatMap (·.rounds), ∀ o ∈ d.opens, ∀ c j, o.2 = .taken c j → o.2 ∈ T.taken)
    (b : Nat) : T.opensAvailable b = true := by
  have hdm : ∀ d ∈ declsTo T.bs b, d ∈ T.bs.flatMap (·.rounds) := by
    intro d hd
    obtain ⟨x, hx, hdx⟩ := List.mem_flatMap.1 hd
    exact List.mem_flatMap.2 ⟨x, List.mem_of_mem_take hx, hdx⟩
  unfold Thread.opensAvailable
  rw [List.all_eq_true]
  intro d hd
  rw [List.all_eq_true]
  intro o ho
  refine decide_eq_true ?_
  cases hs : o.2 with
  | own n =>
    have hn := opened_own_lt hp T (i := 2) (by rw [hbs]; exact .tail _ (.tail _ (.head _))) hor hd ho hs
    exact List.mem_append_right _ (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩)
  | taken c j =>
    have h := htk d (hdm d hd) o ho c j hs
    rw [hs] at h
    exact List.mem_append_left _ h

/-- **`DepthsDeclared` at every border**, from one sentence on all the rounds of the chain. -/
theorem depthsDeclared_of_all (T : Thread Bk S Cl V W X Pb)
    (h : ∀ d ∈ T.bs.flatMap (·.rounds), ∀ o ∈ d.opens, ∀ k w hd,
      (T.table o.2 k w hd).2.logLength = o.1.a) (n : Nat) : DepthsDeclared T n := by
  intro d hd o ho k w hh
  obtain ⟨x, hx, hdx⟩ := List.mem_flatMap.1 hd
  exact h d (List.mem_flatMap.2 ⟨x, List.mem_of_mem_take hx, hdx⟩) o ho k w hh

end

namespace FirstThread
variable {W₀ : Type}

/-- **Every half of the last chain at the base filling has no stop.** -/
theorem quiet_second (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ∀ y ∈ (onlineProverPartsInUse I o S O).second Zq G, RowQuiet y.parts := by
  intro y hy
  have hy' : y ∈ (secondW I o S O Zq G : List (Placed _ _ Unit)) := hy
  unfold secondW at hy'
  split at hy'
  · unfold K12.AtProof.halfW at hy'
    obtain ⟨J, -, rfl⟩ := List.mem_map.1 hy'
    intro q hq
    obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.1 hq
    obtain ⟨h1, h2⟩ := quiet_testHalf J q₀ hq₀
    exact ⟨h1, h2⟩
  · cases hy'

/-- **At a return of `onlineProverFromPublicFiles` at the base filling.** -/
theorem quiet_second_at_return {I : WiderIn W₀} {o o' : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz}
    {O : OnlineProverArguments} {pol lay KL : ByteArray} {R : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok R) :
    ∀ y ∈ R.H.second, RowQuiet y.parts := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok h
  rw [hs]
  exact quiet_second I o S O R.Z R.G

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.opened_own_lt
#print axioms ProofFile.Honest.opensAvailable_second
#print axioms ProofFile.Honest.depthsDeclared_of_all
#print axioms ProofFile.Honest.FirstThread.quiet_second
#print axioms ProofFile.Honest.FirstThread.quiet_second_at_return
