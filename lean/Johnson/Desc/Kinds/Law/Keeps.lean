-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Keeps.lean: THE ROW LedgerKeeps FOR THE OUTPUT HEAD's BLOCK: where its decision goes
on, the ledger behind is LATER than the ledger in front (OnBytes/Tie/Pv/Psc/PscLater.lean: `Later`:
what lies under a slot that is filled is kept). `decideBy_spec`: what a return of the decision is.
`k6_decide_later`: the block, at any seat whose laying and reading of the ledger fit.
The hearings' part (`Keeps`, keeps_…, keeps_hear, hear_last) lies in Law/KeepsHear.lean,
which this file imports.
OVER HeadFrame.lean (setLedger and setHeard may refuse).
Nothing on soundness.
-/
import Mathlib
import Johnson.Desc.Kinds.HeadKind
import Johnson.Desc.Kinds.Law.KeepsHear

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Fork)
open OnBytes.PscRun (Later took took_later hideRun_keeps)

/-! ## The block -/

/-- What a return of the head's decision is, with the hearing's return. -/
theorem decideBy_spec {S : Type} {rounds : Given → List Round} {hear : Given → Hear HeardAll}
    {weights : Given → Behind → SumOnMatrix} {p : Par} {L : Seat S} {s s' : S}
    {rs : List Fmt.RoundView} (h : decideBy rounds hear weights p L s rs = .ok s') :
    ∃ (g : Given) (H : HeardAll) (F : Fork) (left : List Fmt.RoundView) (w : SumOnMatrix) (s1 s2 : S),
      given p L s = .ok g ∧ hear g (L.ledger s) rs = some (H, F, left) ∧
      L.setLedger s F = .ok s1 ∧ L.setHeard s1 H = .ok s2 ∧ s' = L.setWeightClaim s2 w := by
  unfold decideBy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i g hg
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i v hv
        obtain ⟨H, F, left⟩ := v
        split at h
        · simp at h
        · split at h
          · simp at h
          · rename_i s1 h1
            split at h
            · simp at h
            · rename_i s2 h2
              simp only [Except.ok.injEq] at h
              refine ⟨g, H, F, left, _, s1, s2, hg, ?_, h1, h2, h.symm⟩
              unfold named at hv
              split at hv
              · rename_i y hy
                simp only [Except.ok.injEq] at hv
                rw [← hv]; exact hy
              · simp at hv

/-- **LedgerKeeps for the output head's block**, at a record at which the seat's laying and reading
of the ledger fit: where the two layings that may refuse return, the seat reads behind all three the
ledger that was laid. -/
theorem k6_decide_later {S Cl : Type} (cl : Form → Cl) (L : Seat S) (link piece : Nat) (par : Par)
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hfit : ∀ F H w s1 s2, L.setLedger s F = .ok s1 → L.setHeard s1 H = .ok s2 →
      L.ledger (L.setWeightClaim s2 w) = F)
    (hd : (kind cl L link piece par).decide s rs gs = .ok s') :
    Later (L.ledger s) (L.ledger s') := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) par L s rs
      = .ok s' := hd
  obtain ⟨g, H, F, left, w, s1, s2, _, hh, e1, e2, rfl⟩ := decideBy_spec hd'
  rw [hfit F H w s1 s2 e1 e2]
  exact keeps_hear _ _ _ _ _ hh

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_decide_later
