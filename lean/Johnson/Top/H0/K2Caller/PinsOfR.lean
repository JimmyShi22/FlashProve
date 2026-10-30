-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/PinsOfR.lean: the code switch: THE BRIDGE FROM THE LAW's RELATION IN FRONT
(`k02_place`, PlaceLaw.lean) TO THE TABLE OF JOINTS' PIN AT A KEPT TENANT (`pinJT_kept`,
PinKeptJoin.lean).

Main names:
  `smpTop_is`: the held OOD samples as made off the stored sample rows, at the closed stand-in, are
    the closed definition `smpK2` (SmpK2.lean): by unfolding.
  `pins_of_R`: the law's typed statement in front is `faAt` at the front and its frame
    (`lawFa_top`), read through the file's own columns (`faAt_congr`, `orcS_strs`); the relation's
    clause on the held slots is `pinJT_kept`'s h; the open word's message is read of the witness's
    new messages along the frame's own map of names (`selBk_made_open`, `CallerAt.mapJ`).
Limits. `pinJT_kept`'s other premises are handed through (for `KeptFacts`: KeptFactsAt.lean).
Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.KeptFactsAt
import Johnson.Top.H0.K2Caller.KeptFreeOf
import Johnson.Top.H0.K2Caller.MadeOpen
import Johnson.Top.H0.K2Caller.SmpK2Is
import Johnson.Top.H0.K2Hears.OrcStrs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb IOR
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Strs FileDescription Wit)
open VerifiableInference.Desc.Sound (Frame Mem SitsAt seatOf MsgT msgsOf extAt pinJT smpNamed
  strsOf)
open VerifiableInference.Desc.First.K2Hands
open Johnson.G (smpTop)

variable {F : Frame}

section
variable {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)

/-- The held OOD samples as made, at the closed stand-in, are the closed definition. -/
theorem smpTop_is (t : ℕ) : smpTop r H iJ iQ t (smp₀ r H) = smpK2 r H := rfl

variable {Xi P Cells Tok : Type} (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ)
  (seatN : Fin r.l.length → ℕ × ℕ) (p : K2.P2) (base : ℕ) (d₁ d₂ : RDT) (arr : ℕ → ℕ → ℕ)
  (seats : List (ℕ × ℕ)) (decT : (ℕ → Option (ℕ × List UInt64)) →
    P × VerifiableInference.Desc.First.S → Option Cells) (c₀ : Cells)
  (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).X ×
    (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str)

set_option maxHeartbeats 4000000 in
/-- **THE TABLE's PIN AT A KEPT TENANT, FROM THE LAW's RELATION IN FRONT.** hR: the relation in
    front of
`k02_place` (PlaceLaw.lean) at a witness w' whose new members' messages are w's: so at what the
table's extractor lays of w. The rest: `pinJT_kept`'s own premises (PinKeptJoin.lean). -/
theorem pins_of_R (a' : P × VerifiableInference.Desc.First.S) (t : Rec) (y : F.E.Str)
    (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (h1 : K2.frontAt p t = some fx)
    (P12 : Pub12 (r := r) W₀ fx) (hm : fx.f.rows.masks = 2)
    (C : CallerAt (selR (Letters.plain r H)) r.cs r.l iJ iQ memK rowK (plK W₀) W₀)
    (Ft : Fit r.cs r.l (plainR r H).s W₀ (memK (r := r) (H := H)) rowK (plK W₀)) (q₀ : ℕ)
    (h0 : (K2.longFront p t fx (K2.orcY F.all F.key (strsOf F y)) q₀).isSome = true)
    (w w' : Wit Cells Tok MsgT)
    (hE : msgsOf r.cs r.l seatN arr w' = msgsOf r.cs r.l seatN arr w)
    (hR : ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).S.over
      (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).A).relR
        (lawFa (Letters.plain r H) iJ iQ (strsTop iJ iQ p (fun y => K2.orcS
            (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r H iJ iQ (baseCount
            r.set .request r.g) (smp₀ r H)) d₀)
          (inXTop iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y)
              (smpTop r H iJ iQ (baseCount r.set .request r.g) (smp₀ r H)) d₀ y₀) (t, y))
        (selBk (Letters.plain r H) iJ iQ (wtMade iJ iQ seatN arr w')))
    (ms minePad : List Mem) (hN : (minePad.map seatOf).Nodup) (q : ℕ × ℕ)
    (hex : ∃ x ∈ ms, SitsAt x q.1 q.2)
    (hall : ∀ x ∈ ms, SitsAt x q.1 q.2 → x ∈ minePad ∧
      ∃ (k : {a // (plainHd r H).cl a}) (kk : KeptPlace) (xo : OnBytes.Oracle),
        VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo, seat⟩, k.1.1⟩ ∧ KeptFacts G seat seatN p
            (K2.orcY F.all F.key) arr seats a'
          t fx W₀ (strsOf F y) k kk xo) :
    pinJT r.cs G arr (smpNamed r.cs seats) ms q.1 q.2 a' (strsOf F y)
      (extAt r.cs G arr (smpNamed r.cs seats) decT c₀ [] minePad false none a' (strsOf F y) w) := by
  rw [lawFa_top iJ iQ (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y)
      (smpTop r H iJ iQ (baseCount r.set .request r.g) (smp₀ r H)) d₀ y₀ (t, y) h1 P12.frameIs,
    faAt_congr p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (K2.orcY
        F.all F.key) (smpTop r H iJ iQ (baseCount r.set .request r.g) (smp₀ r H)) (t, fx, W₀) y
        (strsOf F y)
      (K2.orcS_strs F base [d₁, d₂] y)] at hR
  obtain ⟨-, -, h4, -⟩ := hR
  refine pinJT_kept G seat seatN p (K2.orcY F.all F.key) arr seats decT c₀ a' t fx W₀ (strsOf F y)
      hm
    P12.frameIs q₀ h0 Ft w (selBk (Letters.plain r H) iJ iQ (wtMade iJ iQ seatN arr w')).2.1 ?_ h4
        ms minePad hN q
    hex hall
  intro j
  rw [selBk_made_open, hE]
  exact congrArg _ (congrFun (C.mapJ Ft) j)

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.smpTop_is
#print axioms VerifiableInference.Desc.First.K2Caller.pins_of_R
