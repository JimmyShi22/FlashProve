-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MadeLedger.lean: code switching (K2): TWO OF THE MAKINGS THAT ITS SHARES OF e₁ ASK
(hMade, Johnson/P1K2R/SharesAtE.lean): THE TABLE's OWN PUBLIC ITEMS «ledger m» AND «freeAbove m»
HOLD BEHIND EVERY ACCEPT OF THE 24 PLACES THAT OPEN A LINK, in hMade's own letters. A JOIN of
Johnson/Desc/First/LedgerMade.lean with the places' own steps. NO BLOCK IMPORTS
THIS FILE.
  made_ledger_first   a link's first place (the switch joined with the frame's «opened»), 1 ≤ l <
                      24: at every accept s ↦ s': pubAll D base (.ledger l) (z, s') = true ∧
                      pubAll D base (.freeAbove l) (z, s') = true. FROM: the driver's list has the
                      written sort at l (hsub: in scope: P1K2.subs_W) · hnsA | hnsL: THE PLAN's
                      NUMBER OF SLOTS OF SEGMENT l (D.nsOf l) IS THE FRAME's (the attention
                      table's p.ns | the layers' hp.ns)
  made_ledger_sits    wherever a sub-protocol sits over the kind's own behind a door whose way out
                      is "H.1.quiet" (K2.headOpenQ HP): at every accept: the same two at m. FROM:
                      hns: D.nsOf m is the head's letters' HP.hp.ns. (So at «H:2», 339, in the
                      lot's head's dress: P1K2.sits_under_head. THE LOT's OTHER DRESS THERE, the
                      link's, opens no ledger; that it never accepts from a state at which the
                      promise's tests in front hold is P1K2.hands_head_other's matter: NOT JOINED
                      HERE.)
BY: IM.Joined.step · framesOf_arms (Johnson/Top/H0/Walk/FrameRows.lean) ·
ledger_opened_att | _lay · freeAbove_opened_att | _lay · ledger_made | freeAbove_made
(LedgerMade.lean) · K2.headOpenQ_fork (Tw/K2C/HeadLedger.lean) · P1K2.kinds_of_subs.
LIMITS. The premises on the plan are named, not shown. No soundness is claimed.

-/
import Johnson.P1K2R.SharesScope
import Johnson.Desc.First.LedgerMade
import Johnson.Top.H0.Walk.FrameRows
import Johnson.Top.H0.Tw.K2C.HeadLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Pub PubData pubAll pubAll_ledger pubAll_freeAbove
  ledger_opened_att ledger_opened_lay freeAbove_opened_att freeAbove_opened_lay ledger_made
  freeAbove_made)
open VerifiableInference.Desc.First.K2 (HeadPar headOpenQ headOpenQ_fork)
open Johnson.Desc.First.Walk.Seat (framesOf_arms)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (Yes subW k2P Joined)

variable {P : Type}

theorem made_ledger_first {Z : ProofFile.Pub} {l : Nat} (h24 : l < 24) {b b' : Block S Cl}
    {a : Place} (hJ : Joined Z l b b' a) (hsub : (ProofFile.subsOf Z)[l]? = some (subW l))
    (D : PubData) (base : Pub → P × S → Bool) (z : P)
    (hnsA : ∀ X p, Z.p.built.links[l]? = some X → X.kind = 1 → Z.p.X.A[X.g]? = some p →
      D.nsOf l = some p.ns)
    (hnsL : ∀ X hp, Z.p.built.links[l]? = some X → X.kind = 0 → Z.p.X.G[X.g]? = some hp →
      D.nsOf l = some hp.ns)
    {ft : Nat} {s s' : S} (hy : Yes ft b s s') :
    pubAll D base (.ledger l) (z, s') = true ∧ pubAll D base (.freeAbove l) (z, s') = true := by
  obtain ⟨rs, cols, n, e⟩ := hy
  obtain ⟨fs, f, m, hfs, hf, _, _, ho, _, _⟩ := hJ.step e
  obtain ⟨X₀, hX₀, hk₀, _, _⟩ := kinds_of_subs h24 hsub
  rcases framesOf_arms hfs hf with ⟨X, hX, hk, _⟩ | ⟨h0, X, hp, Q, hX, hk, hG, hQ, _, eo, _⟩ |
    ⟨_, X, p, Q, hX, hk, hA, hQ, _, eo, _⟩ | ⟨_, X, hp, Q, hX, hk, hG, hQ, _, eo, _⟩
  · obtain rfl : X₀ = X := Option.some.inj (hX₀.symm.trans hX)
    exact absurd hk hk₀
  · rw [eo] at ho
    refine ⟨by rw [pubAll_ledger]; exact VerifiableInference.Desc.First.ledger_opened_layZero ho,
      ?_⟩
    rw [pubAll_freeAbove, hnsL X hp (by rw [h0]; exact hX) hk hG]
    have := VerifiableInference.Desc.First.freeAbove_opened_layZero ho
    rw [hQ] at this
    exact this
  · rw [eo] at ho
    refine ⟨by rw [pubAll_ledger]; exact ledger_opened_att ho, ?_⟩
    rw [pubAll_freeAbove, hnsA X p hX hk hA]
    have := freeAbove_opened_att ho
    rw [hQ] at this
    exact this
  · rw [eo] at ho
    refine ⟨by rw [pubAll_ledger]; exact ledger_opened_lay ho, ?_⟩
    rw [pubAll_freeAbove, hnsL X hp hX hk hG]
    have := freeAbove_opened_lay ho
    rw [hQ] at this
    exact this

theorem made_ledger_sits {ft : Nat} {b : Block S Cl} {p : VerifiableInference.Desc.First.K2.P2}
    {enter : S → Except String S} {HP : HeadPar}
    (hS : Sits b (VerifiableInference.Desc.First.K2.codeSwitchKind p : Block S Unit) enter
      fun _ t => headOpenQ HP t)
    (D : PubData) (base : Pub → P × S → Bool) (z : P) {m : Nat}
    (hns : D.nsOf m = some HP.hp.ns) {s s' : S} (hy : Yes ft b s s') :
    pubAll D base (.ledger m) (z, s') = true ∧ pubAll D base (.freeAbove m) (z, s') = true := by
  obtain ⟨rs, cols, n, e⟩ := hy
  obtain ⟨t, t', _, _, e3⟩ := hS.step ft s s' rs cols n e
  exact ⟨ledger_made D base m z (headOpenQ_fork e3),
    freeAbove_made D base m z (headOpenQ_fork e3) hns⟩

end P1K2

#print axioms P1K2.made_ledger_first
#print axioms P1K2.made_ledger_sits
