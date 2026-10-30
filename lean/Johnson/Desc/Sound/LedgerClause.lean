-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/LedgerClause.lean: WHAT A KIND's FILES OWE AT ONE BLOCK OF A PROOF FILE's SHARED
CHAIN BEHIND "LIN point", AS A NAMED TERM, AND TWO WAYS TO PAY IT. The table lies in other files
(Johnson/Desc/Shared/BordersShared.lean, Johnson/Desc/Sound/BordersSharedQ.lean); the debt is
written in a third place: the clause of the ledger's EachPlainShOwn at one block
(Johnson/Desc/Sound/SharedJointCountLedger.lean, over stepV and shV of
Johnson/Desc/Sound/SharedJoinPlain.lean).

  ClauseAt … e₀ k x ε   the kind's plain law for ONE statement at block k, at the maker's piece x,
                      at the kind's own errors ε, of the SHARED items alone, at the acting parts'
                      values: the shared promise behind holds; and every witness at which all shared
                      items open behind hold gives, by e₀ k, one at which all open in front hold.
                      IT IS the head of EachPlainShOwn … own k (x :: m) at own k x = ε, with stepV
                      and shV unfolded: by unfolding, in one build with that file: share_row
                      (Johnson/Desc/K14/Law/LedgerRow.lean) lays ten clauses as that term.
  clause_of_own       a block WITH a draw: the kind's law in the form of the rule of composition
                      between what its row names in front and behind (closed or read; opened or
                      read), at the extractor e₀ k and the errors ε; and, for certain, the riding of
                      the shared items that the row does not name.
  clause_of_sure      a block WITHOUT a draw: all of it for certain.
What is not claimed. Rules at letters: as empty as their premises. No block's law is shown here.
Nothing on soundness.

-/
import Johnson.Desc.Sound.BordersSharedQ
import Johnson.Desc.Plain.PlainOfOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Plain (leads_of_own_frames)

variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
  (e₀ : ∀ k, (actQ N p l k).1 → Wt → Wt)

/-- The shared items that are open at border k. -/
abbrev openSh (k : ℕ) : ItemS → Prop := openAfter (insSh split) (outsSh split) startSh k

/-- **What a kind's files owe at block k.** -/
def ClauseAt (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl Wt) (ε : Err (uLT C x.ds)) : Prop :=
  x.ior.red.Leads (onQ₂ N Pm Oc split p l k)
    (fun a b => promQ N Pm split p l (k + 1) ((actQ N p l (k + 1)).2 b) ∧
      ∀ w, (∀ i, openSh split (k + 1) i → muQ N Mg p l i (k + 1) ((actQ N p l (k + 1)).2 b) w) →
        ∀ i, openSh split k i →
          muQ N Mg p l i k ((actQ N p l k).2 a) (e₀ k ((actQ N p l k).2 a) w)) ε

/-- **A block with a draw.** -/
theorem clause_of_own (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl Wt) (ε : Err (uLT C x.ds))
    (own : ({ x with ext := fun a _ w => e₀ k ((actQ N p l k).2 a) w, err := ε } :
        Piece C Fr (P₁ × S₂) Cl Wt).GoodIn (onQ₂ N Pm Oc split p l k)
      (fun b => promQ N Pm split p l (k + 1) ((actQ N p l (k + 1)).2 b))
      (fun a w => ∀ i, insSh split k i → muQ N Mg p l i k ((actQ N p l k).2 a) w)
      (fun b w => ∀ i, outsSh split k i → muQ N Mg p l i (k + 1) ((actQ N p l (k + 1)).2 b) w))
    (frames : ∀ a τ b w i, onQ₂ N Pm Oc split p l k a → x.ior.red.out a τ = some b →
      promQ N Pm split p l (k + 1) ((actQ N p l (k + 1)).2 b) → openSh split k i →
      ¬ insSh split k i → muQ N Mg p l i (k + 1) ((actQ N p l (k + 1)).2 b) w →
      muQ N Mg p l i k ((actQ N p l k).2 a) (e₀ k ((actQ N p l k).2 a) w)) :
    ClauseAt N Mg Pm Oc split p l e₀ k x ε :=
  leads_of_own_frames x ε (fun a w => e₀ k ((actQ N p l k).2 a) w) (onQ₂ N Pm Oc split p l k)
    (fun b => promQ N Pm split p l (k + 1) ((actQ N p l (k + 1)).2 b))
    (fun i a w => muQ N Mg p l i k ((actQ N p l k).2 a) w)
    (fun i b w => muQ N Mg p l i (k + 1) ((actQ N p l (k + 1)).2 b) w)
    (openSh split k) (insSh split k) (outsSh split k) own frames

/-- **A block without a draw.** -/
theorem clause_of_sure (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl Wt) (ε : Err (uLT C x.ds))
    (h : ∀ a τ b, onQ₂ N Pm Oc split p l k a → x.ior.red.out a τ = some b →
      promQ N Pm split p l (k + 1) ((actQ N p l (k + 1)).2 b) ∧
        ∀ w, (∀ i, openSh split (k + 1) i →
            muQ N Mg p l i (k + 1) ((actQ N p l (k + 1)).2 b) w) →
          ∀ i, openSh split k i →
            muQ N Mg p l i k ((actQ N p l k).2 a) (e₀ k ((actQ N p l k).2 a) w)) :
    ClauseAt N Mg Pm Oc split p l e₀ k x ε :=
  Reduction.Leads.of_sure (K := x.ior.red) ε h

end VerifiableInference.Desc.Sound
