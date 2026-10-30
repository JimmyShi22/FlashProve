-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/OpenNext.lean: an item that is open at a border and that the
row of the sub-protocol there does not close is open at the next border. `mem_fwdStep`
(PaysLaw.lean) is the converse direction. At the first chain's invariant at the full size,
`head_opened_openSets` (OpenBridge.lean) then puts the item into the library's open sets at both
borders. Lemmas on an item `forms` that passes over a sub-protocol ask just that. No definition.

  1  `mem_fwdStep_of`, `opened_next`   the general lemmas
  2  `head_open_both`   at the first chain at the full size: the item is in `IM.openAt` at both
     borders

Limits.
  * Lists of items only: the file says nothing about what an item means.
  * Lemma 2: full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is); not for the item `wrow`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.OpenBridge
import Johnson.IMR.HandsDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- What is open before a row and is not closed by it is open after it. -/
theorem mem_fwdStep_of {ι : Type} [DecidableEq ι] {O : List ι} {r : FwdRow ι} {i : ι} (h1 : i ∈ O)
    (h2 : i ∉ r.shuts) : i ∈ fwdStep O r := by
  show i ∈ (O.filter fun j => !r.shuts.contains j) ++
    r.owes.filter fun j => !(O.filter fun j' => !r.shuts.contains j').contains j
  refine List.mem_append_left _ (List.mem_filter.2 ⟨h1, ?_⟩)
  simp [h2]

/-- An item that is open at a border and is not closed there is open at the next border. -/
theorem opened_next {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b : Nat}
    {i : T.ι} (h1 : i ∈ T.opened b) (h2 : i ∉ (T.row b).shuts) : i ∈ T.opened (b + 1) :=
  mem_fwdStep_of h1 h2

namespace FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
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

/-- The item is in the library's open sets at both borders. -/
theorem head_open_both {b : Nat} (hb : b < 358) {i : Item}
    (hi : i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b)
    (h2 : i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).shuts)
    (hw : i ≠ Item.wrow) :
    i ∈ IM.openAt P5J.At.links P5J.At.ps b ∧ i ∈ IM.openAt P5J.At.links P5J.At.ps (b + 1) :=
  ⟨head_opened_openSets h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega) hi hw,
    head_opened_openSets h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega)
      (opened_next _ hi h2) hw⟩

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.mem_fwdStep_of
#print axioms ProofFile.Honest.opened_next
#print axioms ProofFile.Honest.FirstThread.head_open_both
