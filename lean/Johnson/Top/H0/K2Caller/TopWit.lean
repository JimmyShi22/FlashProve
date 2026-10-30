-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TopWit.lean: THE CODE SWITCH's LAW AT A PLACE, ASSEMBLED, WITH THE RELATION
IN FRONT AT THE CHAIN's WITNESS. Why beside TopAt.lean: there the relation in front stands under a
"there is", which is enough for the table of joints' sentence on the carried claim and TOO WEAK for
the pins of the kept members: at a switch the table's extractor lays the pads alone of the copies
that the group in front has kept (`laysPads`, Johnson/Desc/First/Borders.lean), and `pin_ext_pad`
(Johnson/Desc/Sound/World.lean) asks that the witness BEHIND has the message outside the pad
already: that what the old copy decodes to is the new copy's message is the law's own content only
where the typed witness in front is tied to the chain's.

Main names:
  `k02_good_wit`: as `k02_good_top`, over `k2_good_plain` (PlainGood.lean): R a w := at every state
    t that the way in lets in: the relation in front at (t, a.2) and the typed witness inW a w.
    hExt: the piece's extractor is the sub-protocol's, read through inW in front and wtOf behind.
Limits. Those of TopAt.lean; inW, wtOf are letters and hExt a premise here (paid at the makes:
ExtMade.lean). No member. It is no soundness of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.TopAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)
open scoped ENNReal

variable {F : Frame}

set_option maxHeartbeats 4000000 in
/-- **THE CODE SWITCH's LAW AT A PLACE, ASSEMBLED, WITH THE RELATION IN FRONT AT THE CHAIN's
    WITNESS**: as
`k02_good_top` (TopAt.lean), but R a w says the relation in front AT THE TYPED WITNESS inW a w, and
hExt ties the piece's extractor to the sub-protocol's: read through inW in front and wtOf behind. -/
theorem k02_good_wit {W' Cl Cl₀ Cl₁ Xi : Type} {r : SwRow} (h : r.ok = true)
    (hW : r.writtenOK = true) (hz : r.sizedB = true)
    (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM
      (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM
      (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (G : FileDescription Xi) (seat : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT) (p : K2.P2)
    (hp : P2At r p) (he : [d₁, d₂].map (·.entry) = (K2.rounds p).map (·.entry))
    (hk : ∀ d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind)
    (hpl : (K2.codeSwitchKind (Cl := Cl₁) p).planOk = true)
    (hseat : ∀ i, base ≤ (seat i).1 ∧ (seat i).1 - base < d₁.trees.length)
    (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r (r.ok_says h))).held.Smp)
    (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).X ×
      (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str)
    (W₀ : SwitchFrame) (n0 grp rows : ℕ) (aOf : (selLoc (Letters.plain r (r.ok_says h)) iJ iQ).hd.K
        → ℕ)
    (iOf : ∀ k, ((selLoc (Letters.plain r (r.ok_says h)) iJ iQ).hd.o k).Z.S → ℕ)
    (C : CallerAt (selR (Letters.plain r (r.ok_says h))) r.cs r.l iJ iQ memK rowK (plK W₀) W₀)
    (hkeys : KeysFit (F := F) (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ
        iQ G seat base d₁ F) p base
      idExt)
    (b₀ : TB (Letters.plain r (r.ok_says h)) iJ iQ)
    (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec)
    (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) p).rounds)
    (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave)
    (hD : DoorKeeps (F := F) (Letters.plain r (r.ok_says h)) iJ iQ p leave
      (fbOf (Letters.plain r (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ G
          seat)
        (fun _ => ((), ()))))
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W' → W')
    (inW : Rec × F.E.Str → W' → (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ
        iQ).sw).W)
    (wtOf : Rec × F.E.Str → W' → (Cb.Pv.SendLoc.loc (selZ (Letters.plain r (r.ok_says h)) iJ
        iQ).sw).tgt.W)
    (hExt : ∀ a τ b w, (∃ t, enter a.1 = .ok t ∧
        OnTop iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) smp
            d₀ y₀ W₀ n0 grp rows aOf iOf (t, a.2)) →
      (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
          seat base d₁ F) p base
        idExt) B ext').ior.red.out a τ = some b →
      inW a (ext' a τ w) = selBk (Letters.plain r (r.ok_says h)) iJ iQ (wtOf b w)) :
    (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
        seat base d₁ F) p base
      idExt) B ext').GoodIn
      (fun a => ∃ t, enter a.1 = .ok t ∧
        OnTop iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) smp
            d₀ y₀ W₀ n0 grp rows aOf iOf (t, a.2))
      (fun b => lawPb (Letters.plain r (r.ok_says h)) iJ iQ (fbOf (Letters.plain r (r.ok_says h)) iJ
          iQ n0 b₀ (fun _ i => isEmptyElim i)
        (strMadeB iJ iQ G seat) (fun _ => ((), ())) b))
      (fun a w => ∀ t, enter a.1 = .ok t →
        ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).S.over
          (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).A).relR
            (lawFa (Letters.plain r (r.ok_says h)) iJ iQ (strsTop iJ iQ p (fun y => K2.orcS
                (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) smp d₀)
              (inXTop iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂])
                  y) smp d₀ y₀) (t, a.2)) (inW a w))
      (fun b w => ∀ a, OnTop iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base
          [d₁, d₂]) y) smp d₀ y₀ W₀ n0 grp rows aOf iOf a →
        lawRb (Letters.plain r (r.ok_says h)) iJ iQ p F.E.Str a
          (b.1, fbOf (Letters.plain r (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i)
              (strMadeB iJ iQ G seat)
            (fun _ => ((), ())) b) (wtOf b w)) :=
  k2_good_plain h hW iJ iQ G seat base d₁ d₂ (k2Wr_of hp he hk) p hseat _ _ _
    (fun _ ha => ha.2)
    (lawAfter_light (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seat base d₁ F) p
        base idExt _ _
      (k2Wr_of hp he hk) hp hpl hz W₀ memK rowK (plK W₀) aOf iOf _ C
      (frontOnL_top iJ iQ (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y)
          smp d₀ y₀ W₀ aOf iOf _
        (fun _ ha fx hfx => (ha.1 fx hfx).1) (fun _ ha fx hfx => (ha.1 fx hfx).2.1)) hkeys)
    n0 b₀ (fun _ ha fx hfx => ⟨(ha.1 fx hfx).1.codes, (ha.1 fx hfx).2.2.1, (ha.1 fx hfx).2.2.2.1⟩)
    B enter leave hr hs hD ext' inW wtOf hExt

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k02_good_wit
