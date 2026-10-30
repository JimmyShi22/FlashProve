-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/MergeAtLink24.lean: no soundness is claimed.
«hlk · hst · hr»: three premises that mergeFill_at (Johnson/Desc/Sound/MgAt/K11.lean) leaves on the composed meaning's parameter D.lk, at the IOP as written in Lean for the proof file, in the goals' scope.
  find_of_lookup     List.lookup's answer, as List.find?'s on the first component
  **merge_at_link24**  (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
      ∃ l name r, c.links[24]? = some l ∧ ((K9.statesOfLink l 8).find? fun x => x.1 == "the merge") = some (name, r) ∧ ∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y
    c is the first chain of onlineDescription's value (F = fileDescBy … c: IM.Open.desc).
  **merge_at_lk**     the same in mergeFill_at's letters: at every lk : ℕ → Option (Link S Claim) with lk 24 = c.links[24]?: ∃ l name r, hlk ∧ hst ∧ hr.
By: k11_of (Johnson/IMR/K11Seat.lean: the link at 24, its sub-protocol number 8, laid alone) and sitsAs_of_laid (Johnson/K11R/Sits.lean: SitsAs.run: under "the merge" the seated sub-protocol states a run that accepts just where headMergeClaim does).
On the term. The term that is meant is D.lk := ProofFile.linkAt Z. The law is said at the chain's own links, and merge_at_lk asks of lk one equation at 24: whoever defines the term owes that equation (by rfl, if the term is fun m => c.links[m]?).
Not empty: its premises are the goals' scope and the opening of onlineDescription's value, which other laws under Johnson/IMR/ take at the same letters. No member. Nothing on soundness.
-/
import Johnson.K11R.Sits
import Johnson.Desc.First.Batch.ReadersOfLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ToldDesc
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.ForkMerge (headMergeClaim)

/-- `List.lookup`'s answer, as `List.find?`'s on the first component. -/
theorem find_of_lookup {β : Type} : ∀ (l : List (String × β)) (k : String) (v : β),
    l.lookup k = some v → ∃ name, (l.find? fun x => x.1 == k) = some (name, v)
  | [], _, _, h => nomatch h
  | (a, b) :: l, k, v, h => by
    rw [List.lookup_cons] at h
    rw [List.find?_cons]
    by_cases hk : (k == a) = true
    · have ha : (a == k) = true := by rw [beq_iff_eq] at hk ⊢; exact hk.symm
      rw [hk] at h
      simp only [ha]
      exact ⟨a, by rw [Option.some.inj h]⟩
    · have hk' : (k == a) = false := by simpa using hk
      have ha : (a == k) = false := by
        rw [beq_eq_false_iff_ne] at hk' ⊢
        exact fun e => hk' e.symm
      rw [hk'] at h
      simp only [ha]
      exact find_of_lookup l k v h

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At the first chain's link number 24, sub-protocol number 8 states under "the merge" a run that
accepts just where the merge's run of claims does, with the same answers.** -/
theorem merge_at_link24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (l : Link S Claim) (name : String) (r : ℕ → S → Except String (List Claim × S)),
      c.links[24]? = some l ∧
      ((K9.statesOfLink l 8).find? fun x => x.1 == "the merge") = some (name, r) ∧
      ∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y := by
  obtain ⟨Lk, b, e1, e2, hla, -⟩ := IM.k11_of hS hR O
  obtain ⟨r, hr1, hr2⟩ := (K11.sitsAs_of_laid hla).run
  obtain ⟨name, hn⟩ := find_of_lookup b.claims "the merge" r hr1
  refine ⟨Lk, name, r, e1, ?_, hr2⟩
  unfold K9.statesOfLink
  rw [e2]
  exact hn

/-- **In `mergeFill_at`'s letters.** -/
theorem merge_at_lk (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (lk : ℕ → Option (Link S Claim)) (h24 : lk 24 = c.links[24]?) :
    ∃ (l : Link S Claim) (name : String) (r : ℕ → S → Except String (List Claim × S)),
      lk 24 = some l ∧
      ((K9.statesOfLink l 8).find? fun x => x.1 == "the merge") = some (name, r) ∧
      ∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y := by
  obtain ⟨l, name, r, h1, h2, h3⟩ := merge_at_link24 hS hR O
  exact ⟨l, name, r, h24.trans h1, h2, h3⟩

end

end ToldDesc

#print axioms ToldDesc.find_of_lookup
#print axioms ToldDesc.merge_at_link24
#print axioms ToldDesc.merge_at_lk
