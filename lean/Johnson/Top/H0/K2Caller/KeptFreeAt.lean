-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeptFreeAt.lean: the code switch: THE LAW's PROMISE IN FRONT (`KeptFree`,
PlainGood.lean) FROM THE TABLE OF JOINTS' OWN «no collision» AT THE KEPT TENANTS. One theorem: a
join of `keptFree_of` (KeptFreeOf.lean), `slot_word` (SlotWord.lean), `held_is_named`
(HeldIsNamed.lean) and `clear_of_promise` (ClearKept.lean).

Main names:
  `keptFree_at`: at the made readings and the closed held OOD samples: from: a front with a frame,
    two mask rows, the front's reading of the old group's columns is there · `KeptFacts`
    (PinKeptJoin.lean) at every held member · at every held member a member of the table's list that
    is alike it, at a tenant at which the table promises «no collision».
Limits. All of these are premises here (for `KeptFacts`: KeptFactsAt.lean). Nothing on soundness. On
hiding nothing.

-/
import Johnson.Top.H0.K2Caller.PinsOfR
import Johnson.Top.H0.K2Caller.ClearKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb IOR
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Strs FileDescription)
open VerifiableInference.Desc.Sound (Frame Mem SitsAt smpNamed noCollJT strsOf wordAt)
open VerifiableInference.Desc.First.K2Hands
open Johnson.G (smpTop)

variable {F : Frame}

section
variable {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  {Xi P : Type} (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ)
  (seatN : Fin r.l.length → ℕ × ℕ) (p : K2.P2) (base : ℕ) (d₁ d₂ : RDT) (arr : ℕ → ℕ → ℕ)
  (seats : List (ℕ × ℕ))
  (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).X ×
    (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str)

set_option maxHeartbeats 4000000 in
/-- **THE LAW's PROMISE IN FRONT, FROM THE TABLE OF JOINTS' OWN**: no kept slot of the open word has
    a
collision at its held OOD sample's seed (`KeptFree`, PlainGood.lean), at the made readings and the
closed held OOD samples, from: `KeptFacts` at every held member · at every held member a member of
the table's list that is alike it, at a tenant at which the table promises «no collision». -/
theorem keptFree_at (a' : P × VerifiableInference.Desc.First.S) (t : Rec) (y : F.E.Str)
    (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (h1 : K2.frontAt p t = some fx)
    (hW : K2.frameAt fx = some W₀) (hm : fx.f.rows.masks = 2) (q₀ : ℕ)
    (h0 : (K2.longFront p t fx (K2.orcY F.all F.key (strsOf F y)) q₀).isSome = true)
    (hKF : ∀ k : {a // (plainHd r H).cl a}, ∃ xo, KeptFacts G seat seatN p (K2.orcY F.all F.key) arr
      seats a' t fx W₀ (strsOf F y) k (keptK2 r H W₀ k) xo)
    (ms : List Mem)
    (hcl : ∀ k : {a // (plainHd r H).cl a}, ∃ (q : ℕ × ℕ) (x : Mem), x ∈ ms ∧ SitsAt x q.1 q.2 ∧
      VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo, seat⟩, k.1.1⟩ ∧
      noCollJT r.cs G (smpNamed r.cs seats) ms q.1 q.2 a' (strsOf F y)) :
    KeptFree iJ iQ (strsTop iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base
        [d₁, d₂]) y) (smpTop r H iJ iQ (baseCount r.set .request r.g) (smp₀ r H)) d₀) (inXTop iJ iQ
        p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r H iJ
        iQ (baseCount r.set .request r.g) (smp₀ r H)) d₀ y₀) (t, y) := by
  refine keptFree_of iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂])
      y) (smpTop r H iJ iQ (baseCount r.set .request r.g) (smp₀ r H)) d₀ y₀ (t, y) h1 hW
    (fun k => wordAt G r.cs r.lo seat (strsOf F y) k.1.1) ?_ ?_
  · intro k
    obtain ⟨xo, KF⟩ := hKF k
    rw [faAt_congr p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y)
        (K2.orcY F.all F.key) (smpTop r H iJ iQ (baseCount r.set .request r.g) (smp₀ r H)) (t, fx,
        W₀) y (strsOf F y)
      (K2.orcS_strs F base [d₁, d₂] y)]
    exact slot_word G seat p (K2.orcY F.all F.key) (smpK2 r H) t fx W₀ (strsOf F y) hm hW k _ KF.at'
      KF.rows q₀ h0 KF.seatIs
  · intro k
    obtain ⟨xo, KF⟩ := hKF k
    obtain ⟨q, x, hx, hq, hA, hn⟩ := hcl k
    exact clear_of_promise G seat seats a' (strsOf F y) k.1.1 (smpK2 r H fx W₀ k)
      (held_is_named seat seats a' fx W₀ k KF.st KF.listed KF.num KF.bits xo KF.msg KF.stored
          KF.reads
        KF.fits) ms q hn x hx hq hA

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.keptFree_at
