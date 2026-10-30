-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeepsAt.lean: the code switch: THE LAW THAT ALSO KEEPS THE PROMISE BEHIND,
at the kind's own text, at a place's record; and that the promise behind, like what stands behind
(BehindAt.lean), reads a seed through its matrix alone.

Main names:
  `lawPb`: the promise behind, of a typed statement behind: no open message has a collision at its
    sample's seed; the carried joint's own condition (`SendLocRide.outJP`'s `on`).
  `clash_congr`, `pb_alike`: it does not tell two statements that are `Alike` apart.
  `keeps_at`: `sel_keeps_at` (Johnson/Top/H0/K2Hands/TieKeeps.lean) called at the record: on the
    statements with on the prover has lost towards: whatever the text puts out has the promise
    behind, and every witness of what stands behind gives the relation in front at the witness
    handed back, and the kept messages' decodings. Its three premises on the typed caller
    (`allMeet`, `Hd.Laws`, `G.Fits`) follow from r.ok. It does not ask hon.
Limits. Those of LawAt.lean: hpr and `LawAfter` are premises; on is a letter. It is no soundness of
the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.SeatedAt
import Johnson.Top.H0.K2Hands.TieKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open scoped ENNReal

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)

/-- **The promise behind**, of a typed statement behind: no open message has a collision at its
sample's seed; the carried joint's own condition. -/
def lawPb (b : TB X iJ iQ) : Prop := (Cb.Pv.SendLocRide.outJP (selZ X iJ iQ)).on b

/-- A collision reads a seed through its matrix alone. -/
theorem clash_congr {E : Type} [Field E] (o : OMsg E) (f : o.Str) {ρ ρ' : o.Z.D}
    (hm : o.Z.mat ρ = o.Z.mat ρ') : o.Clash f ρ ↔ o.Clash f ρ' := by
  unfold OMsg.Clash Ood.Clash
  rw [val_of_mat o.Z hm]

/-- **The promise behind does not tell two statements that are alike apart.** -/
theorem pb_alike {b b' : TB X iJ iQ} (h : Alike X iJ iQ b b') (hb : lawPb X iJ iQ b) :
    lawPb X iJ iQ b' := by
  have hb' : (selLoc X iJ iQ).S.CF b.1.2 b.2.1.2 ∧ (selLoc X iJ iQ).A₁.on (b.1.1.2, b.2.1.1) := hb
  show (selLoc X iJ iQ).S.CF b'.1.2 b'.2.1.2 ∧ (selLoc X iJ iQ).A₁.on (b'.1.1.2, b'.2.1.1)
  refine ⟨fun i hc => hb'.1 i ?_, h.carried ▸ hb'.2⟩
  have hc' : ((selLoc X iJ iQ).S.om i).Clash (b'.2.1.2 i) (b'.1.2 i).1 := hc
  show ((selLoc X iJ iQ).S.om i).Clash (b.2.1.2 i) (b.1.2 i).1
  rw [h.words]
  exact (clash_congr _ _ (h.mat i)).2 hc'

end

set_option maxHeartbeats 2000000 in
/-- **The law of the code switch at the kind's own text, THE PROMISE BEHIND KEPT.** -/
theorem keeps_at {r : SwRow} (h : r.ok = true)
    (hW : r.writtenOK = true) (X : Letters r (r.ok_says h))
    (iJ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (w : K2Wr r d₁ d₂) (p : K2.P2) {Yt : Type}
    (strs : Rec × Yt → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)
    (shown : Rec × Yt → Tr [wT d₁, wT d₂] → Gs) (on : Rec × Yt → Prop)
    (hpr : ∀ a, on a → ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
      (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).on (lawFa X iJ iQ strs inX a))
    (hA : LawAfter X iJ iQ d₁ d₂ ρ p strs inX shown on) :
    (⟨[wT d₁, wT d₂], lawOut X iJ iQ d₁ d₂ ρ p strs inX shown⟩ : Reduction _ _).Leads on
      (fun a b => lawPb X iJ iQ b.2 ∧ ∀ wt, lawRb X iJ iQ p Yt a b wt →
        ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
          (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).relR (lawFa X iJ iQ strs inX a)
            (selBk X iJ iQ wt) ∧
        ∀ k : (selHd X iJ iQ).K,
          ((selHd X iJ iQ).o k).decW ((selHd X iJ iQ).sW k (lawFa X iJ iQ strs inX a).2.1.1)
              ((lawFa X iJ iQ strs inX a).1.1.1.2 k) =
            some ((selHd X iJ iQ).msg (cutSel r.cs r.l iJ iQ (selNew X iJ iQ wt)).1 k))
      ((switchMaps (X.withSel iJ iQ) d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps (selZ X iJ iQ))) :=
  sel_keeps_at (selR X) (heldAt r (r.ok_says h) X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ
    iQ (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider)
    (rdOf (X.withSel iJ iQ) d₁ d₂ ρ) p (vN d₁) (vN d₂) (passOf d₁) (passOf d₂) strs inX
    shown (r.ok_says h).meets
    (heldPort_laws r.cs r.lo r.mem (stageOf r.g X.t₀) r.rad X.oM X.oZ ((r.ok_says h).hM X.t₀)
      ((r.ok_says h).hZ X.t₀) r.kp (fun a _ => a.2) (r.ok_says h).h0 X.kq)
    (rowsPort_fits r.cs r.lo r.mem (stageOf r.g X.t₀) r.rad X.oM X.oZ ((r.ok_says h).hM X.t₀)
      ((r.ok_says h).hZ X.t₀) ((r.ok_says h).hA X.t₀) ((r.ok_says h).he X.t₀))
    on hpr _ (rdOf_fits (X.withSel iJ iQ) d₁ d₂ ρ w (logN_of_written hW)) hA

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.pb_alike
#print axioms VerifiableInference.Desc.First.K2Caller.keeps_at
