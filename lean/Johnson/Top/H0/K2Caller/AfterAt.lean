-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/AfterAt.lean: the premise `LawAfter` of the code switch's law (LawAt.lean)
brought down to what is asked ONCE of the caller and of the statement in front: a call of
`afterAtYes_paid` (Johnson/Top/H0/K2Hands/TiePaid.lean) at the values of LawAt.lean, with two of the
three clauses that it asks at every yes paid here.

  yesAt_at: `YesAtYes` at `rdOf`, `vN`: its clauses len and reads by PosAt.lean; its clause cols
      (each column shown is the oracles' own at its key and position) stays a premise on the two
      letters shown and orcs
  lawAfter_of: `LawAfter` from: `P2At r p` and p.logN ≤ 32 · `CallerAt` at a public frame W₀ · the
      library's `LdLocD.Lin` · `FrontOn` at every statement with on · the clause cols
Limits: those of LawAt.lean, PosAt.lean and TiePaid.lean. `CallerAt`, `Lin`, `FrontOn` and cols are
premises; no member is named here. It is no soundness of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.PosAt
import Johnson.Top.H0.K2Hands.TiePaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.First.K2Hands
open scoped ENNReal

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (p : K2.P2) {Yt : Type}
  (shown : Rec × Yt → Tr [wT d₁, wT d₂] → Gs) (orcs : Rec × Yt → ℕ → ℕ → List UInt64)

set_option maxHeartbeats 1000000 in
/-- **What is asked at every yes**, at the readings of ReadingRd.lean. -/
theorem yesAt_at (w : K2Wr r d₁ d₂) (hp : P2At r p) (on : Rec × Yt → Prop)
    (hc : ∀ a τ, on a → K2.ColsOf (orcs a) (K2.flat p (shown a τ))) :
    YesAtYes (selR X) (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
      (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) (rdOf (X.withSel iJ iQ) d₁ d₂ ρ) p
      (vN d₁) (vN d₂) shown orcs on :=
  fun a τ _ Qs ha _ hQ =>
    ⟨len_at d₁ d₂ w τ.2.2.1 τ.2.2.2.1, reads_at d₂ hp _ τ.2.2.1 τ.2.2.2.1 Qs hQ, hc a τ ha⟩

variable (strs : Rec × Yt → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)

/-- The typed record of the locations at the caller. -/
noncomputable abbrev selLoc :=
  (closeSel (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
    (baseCount r.set .request r.g) X.w₀).loc

set_option maxHeartbeats 1000000 in
/-- **`LawAfter` from what is asked once.** -/
theorem lawAfter_of (w : K2Wr r d₁ d₂) (hp : P2At r p) (h32 : p.logN ≤ 32)
    (W₀ : OnBytes.SwitchFrame) (mem row : (selR X).Kp → ℕ) (pl : (selR X).Kp → OnBytes.KeptPlace)
    (aOf : (selLoc X iJ iQ).hd.K → ℕ) (iOf : ∀ k, ((selLoc X iJ iQ).hd.o k).Z.S → ℕ)
    (on : Rec × Yt → Prop) (C : CallerAt (selR X) r.cs r.l iJ iQ mem row pl W₀)
    (hL : (selLoc X iJ iQ).Lin
      (fun j : (selR X).Sh.Cf.J => (⟨Sum.inr (iJ j).1, (iJ j).2⟩ : (selLoc X iJ iQ).S.Ent))
      (fun q : (selR X).Sh.Cf.Q => (⟨Sum.inr (iQ q).1, (iQ q).2⟩ : (selLoc X iJ iQ).S.Ent))
      Slf.idf id)
    (F : ∀ a, on a → FrontOn (selR X) (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l
      iJ iQ (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) p strs inX orcs W₀ mem row
      pl aOf iOf a)
    (hc : ∀ a τ, on a → K2.ColsOf (orcs a) (K2.flat p (shown a τ))) :
    LawAfter X iJ iQ d₁ d₂ ρ p strs inX shown on :=
  afterAtYes_paid (selR X) (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
    (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) (rdOf (X.withSel iJ iQ) d₁ d₂ ρ) p
    (vN d₁) (vN d₂) strs inX shown orcs h32 W₀ mem row pl aOf iOf on C hL F
    (yesAt_at X iJ iQ d₁ d₂ ρ p shown orcs w hp on hc)

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.yesAt_at
#print axioms VerifiableInference.Desc.First.K2Caller.lawAfter_of
