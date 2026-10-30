-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/OpenWalk.lean: Johnson/IMR/SeatKeeps.lean's WALK AT AN OPENING's OWN LETTERS
(Johnson/IMR/SeatOpen.lean: IM.Open: onlineDescription's value, each letter by the call that made it): so
that one
chain c serves the walk and the seats.
  open_front: SeatKeeps R okB okP, its two premises at the opening's letters: c.front = [], and
    every block of frontOf c keeps R.
  open_fold: so a fold over the first k entries of c.blocksInOrder, k at most the length of frontOf c, from
    any record.
OBJECT: ProofFile.onlineDescription's value, at every o. USERS: Johnson/IMR/ListsAtDraw.lean, OwnAt.lean.
No soundness.
-/
import Johnson.IMR.SeatKeeps
import Johnson.IMR.SeatOpen
import Johnson.IMR.FoldTools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Pub Cl)

variable {R : S → S → Prop} {okB : Array Stages.LinkH → Prop} {okP : K2.HeadPar → Prop}
  {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **Johnson/IMR/SeatKeeps.lean's walk, at an opening's own letters** (SeatOpen.lean). -/
theorem open_front (H : SeatKeeps R okB okP) (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hB : okB Z.p.built.links) (hP : ∀ l Q, P1K2.pureLetters Bs.G₀ l = some Q → okP Q) :
    c.front = [] ∧ ∀ b ∈ frontOf c, Decides R b := by
  have hall := all_of_made (IM.base_made O.made).2.2.2
  have K₀ : LotsKeep R (ProofFile.pureSeat o Z).lots Bs.G₀ :=
    thePure_keeps H Z hB (pub_firstTree (o := o) (pol := pol) (lay := lay) (KL := KL) O.pub) Bs.G₀
      hP
  exact ⟨chainBy_noFront O.chain, chainBy_front H.refl H.trans O.chain
    (partsAt_base H.refl K₀ hall O.places) (partsAt_frames K₀ hall)
    (fun a mk e f hf => (partsAt_roadW K₀ e f hf).1)⟩

theorem open_fold (H : SeatKeeps R okB okP) (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hB : okB Z.p.built.links) (hP : ∀ l Q, P1K2.pureLetters Bs.G₀ l = some Q → okP Q)
    {k : Nat} (hk : k ≤ (frontOf c).length) {ft : Nat} {s : S} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks ft (c.blocksInOrder.take k) s rs cols = .ok r) : R s r.1 := by
  obtain ⟨h0, K⟩ := open_front H O hB hP
  refine Keeps.foldBlocks_keeps R H.refl H.trans ft _ (fun b hb => K b ?_) s rs cols r h
  rw [flat_eq h0, List.take_append_of_le_length hk] at hb
  exact List.mem_of_mem_take hb

#print axioms open_front
#print axioms open_fold

end Meaning.K2
