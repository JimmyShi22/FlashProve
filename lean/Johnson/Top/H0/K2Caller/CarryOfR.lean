-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/CarryOfR.lean: the code switch: THE TABLE OF JOINTS' SENTENCE ON THE CARRIED
CLAIM (`carryK2`, CarryK2.lean) FROM THE LAW's RELATION IN FRONT (`k02_place`, PlaceLaw.lean). One
theorem.

Main names:
  `carry_of_R`: where the list of typed structures has r at m, the way in lets t in, and the text
    makes a front with a frame of t: the relation in front at any typed witness gives `carryK2` at
    the closed held OOD samples and the file's own columns. By `carryK2_front` (TiesFront.lean),
    `lawFa_top`, `faAt_congr`, `orcS_strs`.
Limits. That a front and a frame are there is a premise (an acceptance gives both: SeatYes.lean).
Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.PinsOfR
import Johnson.Top.H0.K2Caller.TiesFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb IOR
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound (Frame strsOf)
open VerifiableInference.Desc.First.K2Hands
open Johnson.G (smpTop)

variable {F : Frame}

set_option maxHeartbeats 4000000 in
/-- **THE TABLE's SENTENCE ON THE CARRIED CLAIM, FROM THE LAW's RELATION IN FRONT**: `carryK2`
(CarryK2.lean) at the closed held OOD samples, where the list of typed structures has r at m, the
numbers are p, and the way in lets t in. hR: the relation in front of `k02_place` at any typed
witness u. -/
theorem carry_of_R {P W : Type} {r : SwRow} (h : r.ok = true)
    (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep
      r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep
      r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (base : ℕ) (d₁ d₂ : RDT)
    (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).X ×
      (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str)
    (rowAt : ℕ → Option SwRow) (pAt : ℕ → K2.P2) (door : ℕ → First.S → Option First.S) (m : ℕ)
    (hr : rowAt m = some r) (z : P) (s t : First.S) (y : F.E.Str) (w : W)
    (hd : door m s = some t) (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame)
    (h1 : K2.frontAt (pAt m) t = some fx) (h2 : K2.frameAt fx = some W₀)
    (u : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).W)
    (hR : ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).S.over
      (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).A).relR
        (lawFa (Letters.plain r (r.ok_says h)) iJ iQ (strsTop iJ iQ (pAt m) (fun y => K2.orcS
            (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ
            (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀)
          (inXTop iJ iQ (pAt m) (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁,
              d₂]) y) (smpTop r (r.ok_says h) iJ iQ (baseCount r.set .request r.g) (smp₀ r
              (r.ok_says h))) d₀ y₀) (t, y)) u) :
    carryK2 rowAt pAt door (K2.orcY F.all F.key) (fun r H => smpK2 r H) m (z, s) (strsOf F y) w :=
  carryK2_front r (K2.orcY F.all F.key) (strsOf F) (fun a => a = (t, y)) h rowAt pAt door
    (fun r H => smpK2 r H) m hr
    (lawFa (Letters.plain r (r.ok_says h)) iJ iQ (strsTop iJ iQ (pAt m) (fun y => K2.orcS
        (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ
        (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀)
      (inXTop iJ iQ (pAt m) (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂])
          y) (smpTop r (r.ok_says h) iJ iQ (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀
          y₀))
    (fun a ha => by subst ha; exact ⟨fx, W₀, h1, h2⟩)
    (fun a fx' W' ha e1 e2 => by
      subst ha
      rw [lawFa_top iJ iQ (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y)
          (smpTop r (r.ok_says h) iJ iQ (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀ y₀
          (t, y) e1 e2,
        faAt_congr (pAt m) (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y)
            (K2.orcY F.all F.key) (smpTop r (r.ok_says h) iJ iQ (baseCount r.set .request r.g) (smp₀
            r (r.ok_says h))) (t, fx', W') y (strsOf F y)
          (K2.orcS_strs F base [d₁, d₂] y)]
      rfl)
    z s t y w hd rfl u hR

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.carry_of_R
