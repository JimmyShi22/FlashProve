-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/LawAt.lean: the law of the code switch over its two written rounds, AT THE
KIND's OWN TEXT AND AT A PLACE's RECORD, with its level: a call of `sel_law_at`
(Johnson/Top/H0/K2Hands/TieT.lean) at the caller, the readings, the condition and the written counts
of this folder.

TieT.lean lays the text of the kind K2 over two written rounds (`outT`: nothing where a round's test
of work fails; else the kind's decision at two views), a reading of its statements (`faT`)
and what stands behind (`RbT`), shows the tie hT of `sel_law`, and calls `sel_law` there, with the
caller, the seven readings, the two views, the two tests of work, the kind's condition and the
premise on the written counts as letters. Here these are filled. Nothing new is proved.
Definitions, and theorems with their proofs.

Main names:
  `vN d`: what a kind is shown of a written round. `passOf d`: the round's test of work. `selR X`:
    the group's data with its kept slots.
  `seed_some`, `pos_some`: where a round's test of work passes, the reading of ReadingRd.lean is
    defined.
  `lawOut`, `lawFa`, `lawRb`, `LawAfter`: TieT.lean's `outT`, `faT`, `RbT`, `AfterAtYes` at these
    values.
  `lawOut_yes`: the text over the two written rounds says yes just where both tests of work pass and
    the kind's decision says yes at what a kind is shown of the two rounds.
  `law_at`: `Reduction.Leads` of that text, towards `sel_law`'s conclusion, at the written counts of
    Reading.lean; and these are shares of at most 2⁻¹ ^ target.

What stays a premise: `LawAfter` (at a yes, if all rows that the maker made hold, the typed claim
behind the positions holds); `on` with its two consequences (the joint's condition and the promise
in front). What stays a letter: the two written rounds under `K2Wr`; the kind's parameters p; the
type Yt of what a statement holds beside the record, with strs (the typed strings off it); inX (the
typed statement off the carried record); shown (the columns shown, off a statement and a written
transcript); iJ, iQ; `WordsOf`; the other letters of Member.lean.
Limits: those of TieT.lean, SwitchLeads.lean, ReadingRd.lean and Row.lean. At `on` := never it is
true and says nothing. It is no soundness of the protocol. On hiding nothing.
strs READS THE RECORD TOO (Rec × Yt → the stage's strings): the open word is the fold of the
committed words by elements that earlier rounds drew, and these stand in the record's carried rows,
not in the oracles.

-/
import Johnson.Top.H0.K2Caller.SelAt
import Johnson.Top.H0.K2Hands.TieT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open OnBytes.Tie.Pv.Row (rvOne)
open VerifiableInference.Desc.First.K2Hands
open scoped ENNReal

/-- What a kind is shown of a written round: what the verifier is shown, without the sealed digest.
-/
def vN (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) : Fmt.RoundView :=
  VerifiableInference.Desc.noDigest (rvOne d m c)

/-- A written round's test of work. -/
def passOf (d : RDT) (c : (wT d).Chal) : Bool :=
  GChal.pass (b := d.entry.work) (c : (wRound (toRD d)).Chal)

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁)

/-- The group's data in front, with its kept slots. -/
noncomputable abbrev selR : RowsK (sigOf r.cs r.lo) := (rowsAt r H X.t₀ X.oM X.oZ).keep r.kp

/-- Where the first round's test of work passes, the seed has a reading. -/
theorem seed_some (H : r.OK) (w : K2Wr r d₁ d₂) (m : (wT d₁).Msg) (c : (wT d₁).Chal)
    (hp : passOf d₁ c = true) :
    (seedOfD (bMax r.cs r.l) (shownW d₁ voidE m c).drawn).isSome = true := by
  have hp' : GChal.pass (b := d₁.entry.work) (c : (wRound (toRD d₁)).Chal) = true := hp
  rw [seed_read d₁ _ (K2Wr.nE₁ d₁ d₂ H w) m c]
  unfold chalTo
  rw [if_pos hp']
  rfl

/-- Where the second round's test of work passes, the positions have a reading. -/
theorem pos_some (w : K2Wr r d₁ d₂) (m : (wT d₂).Msg) (c : (wT d₂).Chal)
    (hp : passOf d₂ c = true) :
    (posOfD r.g.main.logN (baseCount r.set .request r.g)
      (shownW d₂ (voidP (baseCount r.set .request r.g)) m c).drawn).isSome = true := by
  have hp' : GChal.pass (b := d₂.entry.work) (c : (wRound (toRD d₂)).Chal) = true := hp
  rw [pos_read d₂ _ _ (K2Wr.nP₂ d₁ d₂ w) m c]
  unfold chalTo
  rw [if_pos hp']
  rfl

variable (p : K2.P2) {Yt : Type} (strs : Rec × Yt → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)
  (shown : Rec × Yt → Tr [wT d₁, wT d₂] → Gs)

/-- The text of the kind over the two written rounds. -/
noncomputable abbrev lawOut :=
  outT (selR X) (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
    (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) (rdOf (X.withSel iJ iQ) d₁ d₂ ρ) p
    (vN d₁) (vN d₂) (passOf d₁) (passOf d₂) strs inX shown

/-- The typed reading of a statement in front. -/
noncomputable abbrev lawFa :=
  faT (selR X) (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
    (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) strs inX

/-- What stands behind. -/
noncomputable abbrev lawRb (Yt : Type) :=
  RbT (Yt := Yt) (selR X) (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
    (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) p

/-- The premise that is left. -/
abbrev LawAfter (on : Rec × Yt → Prop) : Prop :=
  AfterAtYes (selR X) (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
    (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) (rdOf (X.withSel iJ iQ) d₁ d₂ ρ) p
    (vN d₁) (vN d₂) strs inX shown on

set_option maxHeartbeats 1000000 in
/-- **The text says yes just where both tests of work pass and the kind's decision says yes.** -/
theorem lawOut_yes (w : K2Wr r d₁ d₂) (a : Rec × Yt) (τ : Tr [wT d₁, wT d₂]) :
    (lawOut X iJ iQ d₁ d₂ ρ p strs inX shown a τ).isSome = true ↔
      passOf d₁ τ.2.1 = true ∧ passOf d₂ τ.2.2.2.1 = true ∧
        ∃ s', textT p (vN d₁) (vN d₂) shown a τ = .ok s' :=
  outT_yes (selR X) (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
    (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) (rdOf (X.withSel iJ iQ) d₁ d₂ ρ) p
    (vN d₁) (vN d₂) (passOf d₁) (passOf d₂) strs inX shown
    (fun m c hp => seed_some d₁ d₂ H w m c hp) (fun m c hp => pos_some d₁ d₂ w m c hp) a τ

end

set_option maxHeartbeats 2000000 in
/-- **The law of the code switch at the kind's own text, at a place's record, with its level.** -/
theorem law_at {r : SwRow} (h : r.ok = true) (hW : r.writtenOK = true)
    (X : Letters r (r.ok_says h))
    (iJ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (w : K2Wr r d₁ d₂) (p : K2.P2) {Yt : Type}
    (strs : Rec × Yt → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)
    (shown : Rec × Yt → Tr [wT d₁, wT d₂] → Gs) (on : Rec × Yt → Prop)
    (hon : ∀ a, on a → (Cb.Pv.SendLocRide.inJ (selZ X iJ iQ)).on (lawFa X iJ iQ strs inX a))
    (hpr : ∀ a, on a → ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
      (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).on (lawFa X iJ iQ strs inX a))
    (hA : LawAfter X iJ iQ d₁ d₂ ρ p strs inX shown on) :
    (⟨[wT d₁, wT d₂], lawOut X iJ iQ d₁ d₂ ρ p strs inX shown⟩ : Reduction _ _).Leads on
      (fun a b => ∀ wt, lawRb X iJ iQ p Yt a b wt →
        ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
          (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).relR (lawFa X iJ iQ strs inX a)
            (selBk X iJ iQ wt) ∧
        ∀ k : (selHd X iJ iQ).K,
          ((selHd X iJ iQ).o k).decW ((selHd X iJ iQ).sW k (lawFa X iJ iQ strs inX a).2.1.1)
              ((lawFa X iJ iQ strs inX a).1.1.1.2 k) =
            some ((selHd X iJ iQ).msg (cutSel r.cs r.l iJ iQ (selNew X iJ iQ wt)).1 k))
      ((switchMaps (X.withSel iJ iQ) d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps (selZ X iJ iQ))) ∧
    Err.Below ((switchMaps (X.withSel iJ iQ) d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps (selZ X iJ iQ)))
      ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) :=
  ⟨sel_law_at (selR X) (heldAt r (r.ok_says h) X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ
      iQ (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider)
      (rdOf (X.withSel iJ iQ) d₁ d₂ ρ) p (vN d₁) (vN d₂) (passOf d₁) (passOf d₂) strs inX
      shown (Letters.holds h (X.withSel iJ iQ)).1 on hon hpr _
      (rdOf_fits (X.withSel iJ iQ) d₁ d₂ ρ w (logN_of_written hW)) hA,
    switch_written h hW (X.withSel iJ iQ) d₁ d₂ ρ w⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.lawOut_yes
#print axioms VerifiableInference.Desc.First.K2Caller.law_at
