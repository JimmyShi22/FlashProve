-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchFrontOnTop.lean: code switching: THE LAW's CONDITION IN FRONT (`OnTop`,
Johnson/Top/H0/K2Caller/TopAt.lean) WITH ITS CLAUSE ON THE HELD OUT-OF-DOMAIN (OOD) SAMPLES PAID: at
the held samples as they are made off the verifier's state (`smpTop`,
Johnson/G/SwitchSampleTop.lean), that clause follows from an invariant of the state and tests with
code.

Why. `OnTop` and `frontOnL_top` ask of a letter smp, at every front: each held sample's OOD answers
are the stored sample rows' targets, read, and its OOD seed's rows, carried to the open word's
entries, are the vectors of the stored rows' forms. `sample_top_loc` gives just that at smpTop. Here
Lean holds its end against the two texts that ask it.
  `frontOnL_samples`: `frontOnL_top`'s conclusion with its premise on the held samples replaced: at
  every front, `K2.SampleGoodS` of its statement and the test `storedB`; and three tests on the
  entry r and the frame W₀.
  `onTop_samples`: `OnTop` at smpTop from its other clauses, word for word, with these in the place
  of the clause on the held samples.
  `keptFree_samples`: `OnTop`'s last clause, `KeptFree` (Johnson/Top/H0/K2Caller/PlainGood.lean),
  READS THE OOD SEED OF THE HELD SAMPLE, which at smpTop is taken by choice. It holds there as soon
  as, for each held message, SOME typed OOD seed that fits the stored sample rows has no collision
  at the open word's slot: all seeds that fit collide alike (Johnson/Top/H/SwitchSeedSame.lean).
Limits. LAWS WITH PREMISES: none is shown at a run. W₀ is a letter. `K2.SampleGoodS` is kept by an
accepting run of this sub-protocol where round 1's drawn elements are in canonical form
(`sampleGoodS_kept`); that the other sub-protocols keep it is not typed. That no collision stands at
the OOD seed that was sampled is for the law of the sending that sampled it: not typed here. x₀ is a
placeholder that is read nowhere under the premises. Nothing on soundness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.G.SwitchSampleTop
import Johnson.Top.H.SwitchSeedSame
import Johnson.Top.H0.K2Caller.TopAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Slice OnBytes.Params Cb Iop IOR Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc.Sound (Frame)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K2Caller VerifiableInference.Desc.First.K2Hands
open _root_.Tw.K2 (switchNotices)

section
variable {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (x₀ : (vecD (plainD r H)).held.Smp)
  (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).X ×
    (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).Ex.Str)

/-- The held samples, made, at the number that the law's caller lays. -/
noncomputable abbrev smpK : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp :=
  smpTop r H iJ iQ (baseCount r.set .request r.g) x₀

set_option maxHeartbeats 2000000 in
/-- **`FrontOnL` AT THE MADE READINGS, WITH NO PREMISE ON THE HELD SAMPLES**: from the twelve public
clauses, the invariant and the test on the stored rows at every front, and three tests on r and the
frame. -/
theorem frontOnL_samples {Y : Type} {p : K2.P2} (orc : Y → ℕ → ℕ → List UInt64) (y₀ : Y)
    (W₀ : SwitchFrame) (on : Rec × Y → Prop)
    (h12 : ∀ a, on a → ∀ fx, K2.frontAt p a.1 = some fx → Pub12 (r := r) W₀ fx)
    (hGS : ∀ a, on a → ∀ fx, K2.frontAt p a.1 = some fx →
      K2.SampleGoodS fx.st ∧ storedB r W₀ fx = true)
    (hk : r.keptAt W₀ = true) (hb : keptBitsB r W₀ = true) (hs : keptShapeB r = true)
    (a : Rec × Y) (ha : on a) :
    FrontOnL (selR (Letters.plain r H)) (heldAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM
        (Letters.plain r H).oZ (Letters.plain r H).kq) (Letters.plain r H).Sb (Letters.plain r H).sl
        (Letters.plain r H).Z
      (Letters.plain r H).A₀ r.cs r.l iJ iQ (baseCount r.set .request r.g) (Letters.plain r H).w₀
      (portCode r.cs r.rider) p (strsTop iJ iQ p orc (smpK iJ iQ x₀) d₀)
      (inXTop iJ iQ p orc (smpK iJ iQ x₀) d₀ y₀)
      (fun a => orc a.2) W₀ memK rowK (plK W₀) (aOfK r H) (fun _ _ => 0) a :=
  frontOnL_top iJ iQ orc (smpK iJ iQ x₀) d₀ y₀ W₀ (aOfK r H) (fun _ _ => 0) on h12
    (fun a ha fx hfx => sample_top_loc r H iJ iQ x₀ W₀ fx (hGS a ha fx hfx).1
      (h12 a ha fx hfx).codes hk hb hs (hGS a ha fx hfx).2) a ha

variable {F : Frame}

/-- **`OnTop` AT THE HELD SAMPLES AS MADE**: from its other clauses, word for word, with the
invariant and the test on the stored rows in the place of its clause on the held samples. -/
theorem onTop_samples (p : K2.P2) (orc : F.E.Str → ℕ → ℕ → List UInt64) (y₀ : F.E.Str)
    (W₀ : SwitchFrame) (n0 grp rows : ℕ) (a : Rec × F.E.Str)
    (hf : ∀ fx, K2.frontAt p a.1 = some fx → Pub12 (r := r) W₀ fx ∧
      K2.SampleGoodS fx.st ∧ storedB r W₀ fx = true ∧
      fx.st.oracles.size = n0 ∧ Tied r.l (switchNotices fx.T fx.others) ∧
      fx.f.group = grp ∧ ∃ G, fx.st.groups[grp]? = some G ∧ G.rows.size = rows)
    (hK : KeptFree iJ iQ (strsTop iJ iQ p orc (smpK iJ iQ x₀) d₀)
      (inXTop iJ iQ p orc (smpK iJ iQ x₀) d₀ y₀) a)
    (hk : r.keptAt W₀ = true) (hb : keptBitsB r W₀ = true) (hs : keptShapeB r = true) :
    OnTop iJ iQ p orc (smpK iJ iQ x₀) d₀ y₀ W₀ n0 grp rows (aOfK r H) (fun _ _ => 0) a :=
  ⟨fun fx hfx => by
    obtain ⟨h1, h2, h3, h4⟩ := hf fx hfx
    exact ⟨h1, sample_top_loc r H iJ iQ x₀ W₀ fx h2 h1.codes hk hb hs h3, h4⟩, hK⟩

/-- A typed OOD seed fits the stored sample rows of a held message, at the plain letters. -/
abbrev FitsK (W₀ : SwitchFrame) (St : Statement) (k : (selHd (Letters.plain r H) iJ iQ).K)
    (sd : ((selHd (Letters.plain r H) iJ iQ).o k).Z.D) : Prop :=
  SeedFits (plainR r H) (heldAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM
      (Letters.plain r H).oZ (Letters.plain r H).kq) (Letters.plain r H).Sb (Letters.plain r H).sl
    (Letters.plain r H).Z (Letters.plain r H).A₀ r.cs r.l iJ iQ (baseCount r.set .request r.g)
    (Letters.plain r H).w₀ W₀ k₀Plain memK rowK (aOfK r H) (fun _ _ => 0) St k sd

set_option maxHeartbeats 2000000 in
/-- **`KeptFree` AT THE HELD SAMPLES AS MADE, FROM "NO COLLISION AT SOME OOD SEED THAT FITS"**: the
chosen seed need not be named. -/
theorem keptFree_samples (p : K2.P2) (orc : F.E.Str → ℕ → ℕ → List UInt64) (y₀ : F.E.Str)
    (a : Rec × F.E.Str) {fx : _root_.Tw.K2.Front} {W₀ : SwitchFrame}
    (h1 : K2.frontAt p a.1 = some fx) (h2 : K2.frameAt fx = some W₀)
    (hfree : ∀ k : (selHd (Letters.plain r H) iJ iQ).K, ∃ sd, FitsK iJ iQ W₀ fx.st k sd ∧
      ¬ ((selHd (Letters.plain r H) iJ iQ).o k).ClashW
        ((selHd (Letters.plain r H) iJ iQ).sW k
          (faAt r H p orc (smpK iJ iQ x₀) (a.1, fx, W₀) a.2).2.1.1) sd) :
    KeptFree iJ iQ (strsTop iJ iQ p orc (smpK iJ iQ x₀) d₀)
      (inXTop iJ iQ p orc (smpK iJ iQ x₀) d₀ y₀) a := by
  intro k hc
  rw [lawFa_top iJ iQ orc (smpK iJ iQ x₀) d₀ y₀ a h1 h2] at hc
  obtain ⟨sd, hf, hn⟩ := hfree k
  exact hn ((clash_made_held r.cs r.lo r.mem (stageOf r.g (Letters.plain r H).t₀) r.rad
    (Letters.plain r H).oM (Letters.plain r H).oZ (H.hM _) (H.hZ _) r.kp (fun a _ => a.2) H.h0
    (Letters.plain r H).kq (numAt r) (Letters.plain r H).Sb (Letters.plain r H).sl
    (Letters.plain r H).Z (Letters.plain r H).A₀ r.cs r.l W₀ iJ iQ (baseCount r.set .request r.g)
    (Letters.plain r H).w₀ k₀Plain x₀ fx.st k hf _).1 hc)

end

end Johnson.G

#print axioms Johnson.G.frontOnL_samples
#print axioms Johnson.G.onTop_samples
#print axioms Johnson.G.keptFree_samples
