-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/MergeAtLinkAt.lean: no soundness is claimed. It does not say that K11 is tied or met.
What MergeAtLink24.lean leaves owed (the equation at lk): «hlk · hst · hr» at the meant term D.lk := ProofFile.linkAt Z (Johnson/Desc/ProofFile/LinkAt.lean: link number m of the proof file's first chain, made off the public part alone).
  pureChainAt_of_open stands in PureChainOfOpen.lean, which this file imports.
  (there) pureChainAt_of_open   IM.Open o pol lay KL F Z Bs base c A B ⇒ ProofFile.onlineFirstChainAt Z = .ok c: the chain that linkAt reads is the opened value's first chain (the walk is the one inside descPure_chain, Johnson/Desc/ProofFile/Law/LinkAtLaw.lean; here from the own fields of the opening IM.Open)
  **merge_at_linkAt**   in the goals' scope: ∃ l name r, ProofFile.linkAt Z 24 = some l ∧ ((K9.statesOfLink l 8).find? fun x => x.1 == "the merge") = some (name, r) ∧ ∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y: mergeFill_at's three premises, to the letter, at m := 24 and D.lk := ProofFile.linkAt Z.
By: merge_at_lk (MergeAtLink24.lean) · linkAt_of (LinkAtLaw.lean). No member. Nothing on soundness.
-/
import Johnson.ToldDescR.MergeAtLink24
import Johnson.ToldDescR.PureChainOfOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ToldDesc
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.ForkMerge (headMergeClaim)

section
variable {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **`mergeFill_at`'s three premises at D.lk := ProofFile.linkAt Z and m := 24.** -/
theorem merge_at_linkAt {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (l : Link S Claim) (name : String) (r : ℕ → S → Except String (List Claim × S)),
      ProofFile.linkAt Z 24 = some l ∧
      ((K9.statesOfLink l 8).find? fun x => x.1 == "the merge") = some (name, r) ∧
      ∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y :=
  merge_at_lk hS hR O (ProofFile.linkAt Z) (ProofFile.Law.linkAt_of Z c (pureChainAt_of_open O) 24)

end

end ToldDesc

#print axioms ToldDesc.merge_at_linkAt
