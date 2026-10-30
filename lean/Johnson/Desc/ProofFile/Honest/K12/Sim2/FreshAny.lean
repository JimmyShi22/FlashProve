-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the owner's sentence at a part that lends nothing that another spends.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/FreshAny.lean: the frame's sentence fresh at a member at
whose address no entry of the book spends (noneSpent, Small/Field.lean): one call of the frame's
fresh_of_nil. This is the case of both parts of a proximity test at the first chain's last test: no
entry names them as owners. The test on the book is a premise here; noneSpent_at_maker
(BookAtWritten.lean) pays it at the maker's book. It says nothing of the owner of the first fresh
table, whose sentence is its sender's. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Small.Book
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open ProofFile.Honest ProofFile.Honest.Small

variable {S Cl V W X Pb : Type}

/-- **The sentence fresh at a member that no part spends of.** -/
theorem fresh_member (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts)
    (ord : List VerifiableInference.Desc.Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (u : Member V W X Pb)
    (h : noneSpent Bk ⟨σ.block.place, u.number⟩ = true) : FreshMember φ σ Bk ord bud u := by
  intro p sp ca m ds asks _ _ _
  exact fresh_of_nil _ (spentBy_of_noneSpent h p) _ _

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.fresh_member
