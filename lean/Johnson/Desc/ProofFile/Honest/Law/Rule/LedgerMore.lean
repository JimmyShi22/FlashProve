-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/LedgerMore.lean: SMALL JOINTS FOR WHOEVER SPENDS `LedgerIs`
(Law/Rule/TiesFall.lean), on our own attacker's marks.

  1  `LedgerIs.mono`, `ledgerIs_thrS`   from a weaker border's sentence to a stronger one; so
     from the thread to the thread with what is said (`ThrS`, Honest/Thread/Said.lean)
  2  `seg_of_fork`   THE OTHER WAY OF `seg_fork` (Law/Rule/LedgerCallers.lean): where the state
     has a ledger it has an open segment's part, with that ledger: for callers whose laws read
     `S.fork?` (kind K3's)
  3  `ledger_fork`   `LedgerIs` in that reader's form
  4  `ledger_head`   and in the form "the chain stands in the head's link, opened" (kind K11's
     reader)

Limits. Unfoldings. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.ProofFile.Honest.Law.Rule.LedgerCallers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.K9 (segAt?)

variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

theorem LedgerIs.mono {At At' : Coins Bk → S → Mid W X → Env → Prop} {A : Type}
    {opn : S → Option A} {slot : A → Nat} {ν : Nat}
    (hA : ∀ k s m En, At' k s m En → At k s m En) (h : LedgerIs At opn slot ν) :
    LedgerIs At' opn slot ν :=
  fun k s m En hT => h k s m En (hA k s m En hT)

theorem ledgerIs_thrS {T : Thread Bk S Cl V W X Pb} (Said : Nat → Coins Bk → Mid W X → Prop)
    {b : Nat} {A : Type} {opn : S → Option A} {slot : A → Nat} {ν : Nat}
    (h : LedgerIs (Thr T b) opn slot ν) : LedgerIs (ThrS T Said b) opn slot ν :=
  h.mono fun _ _ _ _ x => x.1

theorem seg_of_fork {s : VerifiableInference.Desc.First.S} {F : OnBytes.Model.Fork}
    (hF : s.fork? = some F) : ∃ a, segAt? s = some a ∧ a.F = F := by
  have key : ∀ L tl, s.link? = some L → s.tl? = some tl → ∃ a, segAt? s = some a ∧ a.F = F := by
    intro L tl hL ht
    unfold segAt?
    rw [hL, hF, ht]
    exact ⟨_, rfl, rfl⟩
  have hF' := hF
  unfold VerifiableInference.Desc.First.S.fork? at hF'
  split at hF'
  · rename_i o ho
    exact key o.L o.tl (by simp only [VerifiableInference.Desc.First.S.link?, ho])
      (by simp only [VerifiableInference.Desc.First.S.tl?, ho])
  · rename_i o ho
    exact key o.L o.tl (by simp only [VerifiableInference.Desc.First.S.link?, ho])
      (by simp only [VerifiableInference.Desc.First.S.tl?, ho])
  · rename_i o ho
    split at hF'
    · rename_i hop
      exact key o.L o.tl (by simp only [VerifiableInference.Desc.First.S.link?, ho, hop, if_true])
        (by simp only [VerifiableInference.Desc.First.S.tl?, ho, hop, if_true])
    · cases hF'
  · cases hF'

theorem ledger_fork {At : Coins Bk → VerifiableInference.Desc.First.S → Mid W X → Env → Prop}
    {ν : Nat} (h : LedgerIs At segAt? (fun a => a.F.next) ν) {k : Coins Bk}
    {s : VerifiableInference.Desc.First.S} {m : Mid W X} {En : Env} (hT : At k s m En)
    {F : OnBytes.Model.Fork} (hF : s.fork? = some F) : F.next = ν := by
  obtain ⟨a, ha, e⟩ := seg_of_fork hF
  rw [← e]
  exact h k s m En hT a ha

theorem ledger_head {At : Coins Bk → VerifiableInference.Desc.First.S → Mid W X → Env → Prop}
    {ν : Nat} (h : LedgerIs At segAt? (fun a => a.F.next) ν) {k : Coins Bk}
    {s : VerifiableInference.Desc.First.S} {m : Mid W X} {En : Env} (hT : At k s m En)
    {o : VerifiableInference.Desc.First.HeadOwn} (ho : s.here = .head o) (hop : o.opened = true) :
    o.F.next = ν := by
  refine ledger_fork h hT ?_
  unfold VerifiableInference.Desc.First.S.fork?
  rw [ho]
  simp only [hop, if_true]

end ProofFile.Honest

#print axioms ProofFile.Honest.LedgerIs.mono
#print axioms ProofFile.Honest.ledgerIs_thrS
#print axioms ProofFile.Honest.seg_of_fork
#print axioms ProofFile.Honest.ledger_fork
#print axioms ProofFile.Honest.ledger_head
