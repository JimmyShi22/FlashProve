-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadFences.lean: two hypotheses of RowPileForwardKinds.lean, each
brought down to a fact on the library's table of open items, which reads no state. No definition.

  1  `head_indexThereB`, `head_index`   wherever the invariant holds at a border at which the item
     `pinI` is open, the message of the index masks is there. The library's promise tests the public
     item `indexThere` wherever `pinI` is open (`pubOfItems`, Johnson/Desc/First/Borders.lean), and
     FormLawI.lean has that test at the invariant
  2  `head_fence`   at a border at which the item `pin m t` is open, every place at which segment
     `m` sends at moment `t` names a tree below the plan's number of trees before that border. This
     is the library's test `fenceFit` (Johnson/Desc/First/FenceFit.lean), which the library shows to
     accept at these numbers (`P5J.AtMg.fence`, Johnson/P5T/FenceAtMg.lean)

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * That `pinI` or `pin m t` is open at a border is a hypothesis. This file shows it for no border.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.FormLawI
import Johnson.Desc.First.FenceFit
import Johnson.P5T.FenceAtMg
import Johnson.Desc.K13.PubK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item Pub openSets start fenceFit_at)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-! ## 1 The message of the index masks is there -/

/-- What the public item `indexThere` tests at the invariant's meaning. -/
theorem head_indexThereB (a : ProofFile.InstPub × TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub Pub.indexThere a =
      VerifiableInference.Desc.K13.indexThereC a.2 := rfl

/-- **Where `pinI` is open and the invariant holds, the message of the index masks is there.** -/
theorem head_index {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E)
    (hi : Item.pinI ∈ ((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[b]?).getD []) :
    s.out.indexMasks < s.st.oracles.size := by
  have e := thr_pubI (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT
    (q := Pub.indexThere)
    (List.mem_flatMap.2 ⟨Item.pinI, hi, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)⟩)
  rw [head_indexThereB] at e
  have e' : (s.st.oracles[s.out.indexMasks]?).isSome = true := e
  by_contra hn
  rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at e'
  cases e'

/-! ## 2 The places of an open pin name trees that are sent before the border -/

/-- **Where `pin m t` is open, every place of segment `m` at moment `t` names a tree below the
plan's number of trees before the border.** -/
theorem head_fence (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat}
    (hb : b ≤ P5J.At.ps.length) {m t : Nat}
    (hp : Item.pin m t ∈ ((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[b]?).getD []) :
    ∀ q ∈ (P5J.At.N Zp cF).sent m t, q.1 < (P5J.At.N Zp cF).treesAt P5J.At.ps[b]? :=
  fun q hq => fenceFit_at (P5J.At.N Zp cF) P5J.At.links P5J.At.ps h.toAtMg.fence b hb q
    (List.mem_flatMap.2 ⟨Item.pin m t, hp, hq⟩)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_indexThereB
#print axioms ProofFile.Honest.FirstThread.head_index
#print axioms ProofFile.Honest.FirstThread.head_fence
