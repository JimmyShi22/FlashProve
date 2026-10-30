-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/LedgerBeside.lean: A SECOND TEST BESIDE THE BOOK-KEEPING, AT NO COST. At the
ledger of a proof file's shared chain the promise has one Bool on the chain's own record at each
border ("shape k", BordersShared.lean). A kind's files that want more of the record
than other files' filling of that letter says lay their own test X k BESIDE it: shape k s && X k
s. Every clause that is paid at the old promise (ClauseAt, Johnson/Desc/Sound/LedgerClause.lean) is
then paid at the new one, at the same errors, if X is handed on for certain: at a yes of the block,
inside the new promise in front, X (k + 1) holds of the record behind. No kind is named.

  besideP Pm X    the promise's meaning with X laid beside "shape".
  promQ_beside    the shared promise at border k, at the new meaning: the old one, and X k.
  clause_beside   **the clause at the new promise.**
  beside_beside   two tests laid one after the other are one: so a clause at a promise with more
                  laid beside is, as a term, a clause at one besideP.
By the frame rule of the plain form (Reduction.Leads.conseq, Johnson/Desc/Plain/Leads.lean).
What is not claimed. A rule at letters. A stronger promise in front is a WEAKER law: whoever lays X
owes X at the first border at which it is asked. Nothing on soundness.

-/
import Johnson.Desc.Sound.LedgerRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc.Shared

/-- The promise's meaning with a second test beside the book-keeping. -/
def besideP {S₂ : Type} (Pm : PromMeaning S₂) (X : ℕ → S₂ → Bool) : PromMeaning S₂ :=
  { Pm with shape := fun k s => Pm.shape k s && X k s }

variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
  (e₀ : ∀ k, (actQ N p l k).1 → Wt → Wt) (X : ℕ → S₂ → Bool)

/-- The shared promise at the new meaning: the old one, and X. -/
theorem promQ_beside (k : ℕ) (v : (actQ N p l k).1) :
    promQ N (besideP Pm X) split p l k v ↔ promQ N Pm split p l k v ∧ X k v.1 = true := by
  have hk : PromS.shape k ∈ promsAt split k := by simp [promsAt]
  constructor
  · intro h
    have hs : (Pm.shape k v.1 && X k v.1) = true := h (.shape k) hk
    refine ⟨fun c hc => ?_, (Bool.and_eq_true_iff.1 hs).2⟩
    cases c with
    | tablePromise => exact h .tablePromise hc
    | noColl m => exact h (.noColl m) hc
    | nothingLeft => exact h .nothingLeft hc
    | shape j =>
      obtain rfl := shape_mem split k j hc
      exact (Bool.and_eq_true_iff.1 hs).1
  · rintro ⟨h, hx⟩ c hc
    cases c with
    | tablePromise => exact h .tablePromise hc
    | noColl m => exact h (.noColl m) hc
    | nothingLeft => exact h .nothingLeft hc
    | shape j =>
      obtain rfl := shape_mem split k j hc
      exact Bool.and_eq_true_iff.2 ⟨h (.shape j) hc, hx⟩

/-- **The clause at the new promise.** -/
theorem clause_beside (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl Wt) (ε : Err (uLT C x.ds))
    (hX : ∀ a τ b, onQ₂ N (besideP Pm X) Oc split p l k a → x.ior.red.out a τ = some b →
      X (k + 1) b.1.2 = true)
    (h : ClauseAt N Mg Pm Oc split p l e₀ k x ε) :
    ClauseAt N Mg (besideP Pm X) Oc split p l e₀ k x ε :=
  Reduction.Leads.conseq h
    (fun a ha => ⟨((promQ_beside N Pm split p l X k _).1 ha.1).1, ha.2⟩)
    (fun a τ b ha hout hq =>
      ⟨(promQ_beside N Pm split p l X (k + 1) _).2 ⟨hq.1, hX a τ b ha hout⟩, hq.2⟩)

/-- Two tests laid one after the other are one. -/
theorem beside_beside {S₂ : Type} (Pm : PromMeaning S₂) (X Y : ℕ → S₂ → Bool) :
    besideP (besideP Pm X) Y = besideP Pm fun k s => Y k s && X k s := by
  unfold besideP
  congr 1
  funext k s
  show (Pm.shape k s && X k s && Y k s) = (Pm.shape k s && (Y k s && X k s))
  rw [Bool.and_assoc, Bool.and_comm (X k s)]

end VerifiableInference.Desc.Sound
