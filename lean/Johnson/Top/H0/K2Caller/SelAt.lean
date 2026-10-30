-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SelAt.lean: the law of the code switch over two written rounds (`sel_law`,
Johnson/Top/H/SwitchLeads.lean) at a place's record: its caller, its seven readings, the kind's
condition and the premise on the written counts are no letters any more, and the written counts are
shares of at most 2⁻¹ ^ target.

`sel_law` stands at the caller `switchSel` (Johnson/Top/H/SwitchSel.lean), which is `switchVec` at
the cut made of two maps of names: so it is the caller of Row.lean at a value of the letter cutN.
Nothing new is proved: a call of `sel_law` at `rdOf` (ReadingRd.lean). Definitions, and theorems
with their proofs.

Main names:
  `Letters.withSel X iJ iQ`: the letters X with the cut made of iJ and iQ. `withSel_caller`: its
    caller is `switchSel` at the record's numbers, by definition.
  `sel_at`: `sel_law` there, at the written counts of Reading.lean; and these are shares of at most
    2⁻¹ ^ target.

What stays a premise: the text `out` over the two written rounds, the reading fa of its statements,
`on` with its two consequences, Rb, and the tie hT: where the text says yes, the seed and the
positions have readings at `rdOf`'s views (so both tests of work have passed), and what stands
behind gives the typed joint behind. The two written rounds under `K2Wr`. iJ, iQ, `WordsOf` and the
other letters of Member.lean.
Limits: those of SwitchLeads.lean, ReadingRd.lean and Row.lean. It is no soundness of the protocol.
On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.ReadingRd
import Johnson.Top.H.SwitchLeads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open scoped ENNReal

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)

/-- The letters with the cut made of two maps of names. -/
noncomputable def Letters.withSel : Letters r H := { X with cutN := cutSel r.cs r.l iJ iQ }

theorem withSel_caller : (X.withSel iJ iQ).caller =
    switchSel (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
      (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) := rfl

end

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)

/-- The caller at the cut made of iJ and iQ. -/
noncomputable abbrev selZ : Cb.Pv.SendLocRide.Size GE := (X.withSel iJ iQ).caller

/-- The held messages' record there. -/
noncomputable abbrev selHd :=
  (closeSel (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
    (baseCount r.set .request r.g) X.w₀).loc.hd

/-- What the block's extractor hands back there. -/
noncomputable abbrev selBk (wt : (Cb.Pv.SendLoc.loc (selZ X iJ iQ).sw).tgt.W) :
    (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).W :=
  selBack (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
    (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) wt

/-- The new messages of a witness behind. -/
noncomputable abbrev selNew (wt : (Cb.Pv.SendLoc.loc (selZ X iJ iQ).sw).tgt.W) :=
  newOf (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
    (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) wt

end

set_option maxHeartbeats 1000000 in
/-- **The law of the code switch over two written rounds, at a place's record.** -/
theorem sel_at {r : SwRow} (h : r.ok = true) (hW : r.writtenOK = true)
    (X : Letters r (r.ok_says h))
    (iJ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (w : K2Wr r d₁ d₂) {A Bt : Type}
    (out : A → Tr [wT d₁, wT d₂] → Option Bt)
    (fa : A → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X ×
      (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
    (on : A → Prop) (hon : ∀ a, on a → (Cb.Pv.SendLocRide.inJ (selZ X iJ iQ)).on (fa a))
    (hpr : ∀ a, on a → ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
      (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).on (fa a))
    (Rb : A → Bt → (Cb.Pv.SendLoc.loc (selZ X iJ iQ).sw).tgt.W → Prop)
    (hT : ∀ a τ b, on a → out a τ = some b → ∃ sd Qs,
      (rdOf (X.withSel iJ iQ) d₁ d₂ ρ).rdSeed
        ((rdOf (X.withSel iJ iQ) d₁ d₂ ρ).view₁ τ.1 τ.2.1).drawn = some sd ∧
      (rdOf (X.withSel iJ iQ) d₁ d₂ ρ).rdPos
        ((rdOf (X.withSel iJ iQ) d₁ d₂ ρ).view₂ τ.2.2.1 τ.2.2.2.1).drawn = some Qs ∧
      ∀ wt, Rb a b wt → (Cb.Pv.SendLocRide.outJ (selZ X iJ iQ)).relR
        ((rdOf (X.withSel iJ iQ) d₁ d₂ ρ).after (fa a) sd Qs
          ((rdOf (X.withSel iJ iQ) d₁ d₂ ρ).answ τ.2.2.1) τ.1) wt) :
    (⟨[wT d₁, wT d₂], out⟩ : Reduction A Bt).Leads on
      (fun a b => ∀ wt, Rb a b wt →
        ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
          (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).relR (fa a) (selBk X iJ iQ wt) ∧
        ∀ k : (selHd X iJ iQ).K,
          ((selHd X iJ iQ).o k).decW ((selHd X iJ iQ).sW k (fa a).2.1.1) ((fa a).1.1.1.2 k) =
            some ((selHd X iJ iQ).msg (cutSel r.cs r.l iJ iQ (selNew X iJ iQ wt)).1 k))
      ((switchMaps (X.withSel iJ iQ) d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps (selZ X iJ iQ))) ∧
    Err.Below ((switchMaps (X.withSel iJ iQ) d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps (selZ X iJ iQ)))
      ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) :=
  ⟨sel_law (heldAt r (r.ok_says h) X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
      (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider)
      (rdOf (X.withSel iJ iQ) d₁ d₂ ρ) (Letters.holds h (X.withSel iJ iQ)).1 out fa on hon hpr _
      (rdOf_fits (X.withSel iJ iQ) d₁ d₂ ρ w (logN_of_written hW)) Rb hT,
    switch_written h hW (X.withSel iJ iQ) d₁ d₂ ρ w⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.withSel_caller
#print axioms VerifiableInference.Desc.First.K2Caller.sel_at
