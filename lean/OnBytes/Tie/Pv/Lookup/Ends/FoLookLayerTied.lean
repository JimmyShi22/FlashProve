-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookLayerTied.lean.
The layers' check: its lookup's claims inside the one equation, at the runs that a whole run holds.

`g_run_tied` (FoTiedG) cuts a run of `Layer.runForkHidG2` that returns into the runs of its named
routines, each from where the one before ended. This file takes the first nine of these run
equations as premises and gives what `layer_look_total` (FoLookLayerRun) asks of the state before
`Forest.objects`, and so that theorem's equation.

Main names:
  `layerMid_eq`: the stretch `layerMid` is `gMid` (FoTiedG).
  `g_claims_ready`: the state from which `Forest.objects` runs is a later state than the one that
    `Layer.hearLook` left; its arrays have their sizes; it has one coefficient for each slot.
  `g_look_at`: there is a function A, chosen before everything but the records P and o, such that at
    these runs the equation of `layer_look_total` holds.

Under: the nine run equations (`g_claims_ready`: the first six); for the equation: `HeardIs` in a
state F0 of which the state that `Layer.hearLook` left is a later one; the shape is lawful; the
three tables' first entries and the world are as in FoLookLayerRun.

Limit: those of FoLookLayerRun. The states behind `Layer.claimsPlanes` are not spoken of.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookLayerRun
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun Cb.Fo

theorem layerMid_eq (P : Layer.Pub) (o : Layer.Own) : layerMid P o = gMid P o := rfl

/-- The state from which `Forest.objects` runs. -/
theorem g_claims_ready {P : Layer.Pub} {hp : Layer.HPlan2} {g : ℕ} {Lc : LinkCtx} {F : Fork}
    {c : Ctx} {iU3 : ℕ} {fo : Forest.Heard} {Fl : Fork} {cl : Ctx} {o : Layer.Own} {Fo : Fork}
    {co : Ctx} {L8 : LinkCtx} {Fa : Fork} {ca : Ctx} {tl1 tl2 : HTailF2} {Lt : LinkCtx} {Gt : Fork}
    {cr : Ctx} {Lb : LinkCtx} {Gb : Fork} {cb : Ctx} {G1 : Fork} {c1 : Ctx}
    (h1 : Layer.hearLook P.y g (F.fillL.slots hp.ns) c = .ok ((fo, Fl), cl))
    (h2 : Layer.hearOwn P hp g fo Fl cl = .ok ((o, Fo), co))
    (h3 : rootInH [iU3] Lc Fo co = .ok ((((), L8), Fa), ca))
    (h4 : tl1.transcriptF L8 Fa ca = .ok (((tl2, Lt), Gt), cr))
    (h5 : t2Batch Gt.next Lt { Gt with planClaimsF := hp.nLin } cr = .ok ((((), Lb), Gb), cb))
    (h6 : (do Layer.note "the element that batches the claims" (← get).theta : SubM Unit) Gb cb =
      .ok (((), G1), c1)) :
    Sized Fl ∧ Later Fl G1 ∧ Sized G1 ∧ G1.LS.size = G1.ns := by
  have s0 : Sized (F.fillL.slots hp.ns) := by
    unfold Sized Fork.slots
    simp
  have z0 : (F.fillL.slots hp.ns).LS.size = (F.fillL.slots hp.ns).ns := by simp [Fork.slots]
  have p1 : Passes (F.fillL.slots hp.ns) Fl := Passes.of h1 fun I _ => by inv
  have p2 : Passes Fl Fo := Passes.of h2 fun I _ => by inv
  have p3 : Passes Fo Fa := Passes.ofL h3 fun I _ => by inv
  have p4 : Passes Fa Gt := Passes.ofL h4 fun I _ => by inv
  have pb : Passes Gt { Gt with planClaimsF := hp.nLin } :=
    fun I _ hI => Prim.book Gt _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hI
  have p5 : Passes { Gt with planClaimsF := hp.nLin } Gb := Passes.ofL h5 fun I _ => by inv
  have p6 : Passes Gb G1 := Passes.of h6 fun I _ => by inv
  have sl := (p1.later s0).2
  have q := p2.trans (p3.trans (p4.trans (pb.trans (p5.trans p6))))
  exact ⟨sl, (q.later sl).1, (q.later sl).2, (p1.trans q).ls s0 z0⟩

/-- **The layers' lookup inside the one equation, at the runs of a whole run.** -/
theorem g_look_at (P : Layer.Pub) (o : Layer.Own) :
    ∃ A : Array E → (ℕ → ℕ) → List Cl,
      ∀ {hp : Layer.HPlan2} {g : ℕ} {Lc : LinkCtx} {F : Fork} {c : Ctx} {iU3 : ℕ}
        {fo : Forest.Heard} {Fl : Fork} {cl : Ctx} {Fo : Fork} {co : Ctx} {L8 : LinkCtx}
        {Fa : Fork} {ca : Ctx} {tl1 tl2 : HTailF2} {Lt : LinkCtx} {Gt : Fork} {cr : Ctx}
        {Lb : LinkCtx} {Gb : Fork} {cb : Ctx} {G1 : Fork} {c1 : Ctx} {G2 : Fork} {c2 : Ctx}
        {G3 : Fork} {c3 : Ctx} {G4 : Fork} {c4 : Ctx},
        Layer.hearLook P.y g (F.fillL.slots hp.ns) c = .ok ((fo, Fl), cl) →
        Layer.hearOwn P hp g fo Fl cl = .ok ((o, Fo), co) →
        rootInH [iU3] Lc Fo co = .ok ((((), L8), Fa), ca) →
        tl1.transcriptF L8 Fa ca = .ok (((tl2, Lt), Gt), cr) →
        t2Batch Gt.next Lt { Gt with planClaimsF := hp.nLin } cr = .ok ((((), Lb), Gb), cb) →
        (do Layer.note "the element that batches the claims" (← get).theta : SubM Unit) Gb cb =
          .ok (((), G1), c1) →
        Forest.objects o.H.fo G1 c1 = .ok (((), G2), c2) →
        gMid P o G2 c2 = .ok (((), G3), c3) →
        Layer.claimsPlanes o.v o.H.fo G3 c3 = .ok (((), G4), c4) →
        Later Fl G1 ∧ Later G1 G4 ∧ Sized G4 ∧ G4.LS.size = G4.ns ∧
        ∀ (K : Type) [CommRing K] (ρ : Reading K) (jLK : ℕ) (rsK : Rounds K) (F0 : Fork),
          HeardIs ρ o.H.fo F0 (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK) → Later F0 Fl →
          FoNums.ok o.H.fo.shape = true →
          ∀ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 → o.v.tabAt "b-bits-1" = some tB1 →
            o.v.tabAt "b-pin" = some tP →
          ∀ H, Later G4 H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K),
            ReadsLaw o.H.fo.shape o.v.y.h.lmb (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb0
              (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb1 ν entry o.v.iU3 o.v.K3 tB0 tB1 tP →
            G4.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
              G1.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
                powSum (ρ.val G1.theta) G1.nClaim
                  ((endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).rows.map (rowRes ν)) +
                clsValue ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (ρ.val G1.theta)
                  (G1.nClaim + ((endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).rows.map
                    (rowRes ν)).length)
                  (A (shownArr G3 o.H.tV.sEnd (nShown P o)) (colsOf G1)) +
                powSum (ρ.val G1.theta)
                  (G1.nClaim + ((endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).rows.map
                    (rowRes ν)).length +
                    (A (shownArr G3 o.H.tV.sEnd (nShown P o)) (colsOf G1)).length)
                  [claimLeaves o.H.fo.shape o.v.y.h.lmb jLK rsK ν
                      (colsK o.H.fo.shape o.v.y.h.lmb
                        (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb0 ν),
                    claimBits o.H.fo.shape o.v.y.h.lmb jLK rsK ν
                      (colsK o.H.fo.shape o.v.y.h.lmb
                        (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb1 ν),
                    Pin.countK o.H.fo.shape o.v.y.h.lmb (Pin.pinColK o.v.y.h.lmb ν)] := by
  obtain ⟨A, hA⟩ := layer_look_total P o
  refine ⟨A, fun h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_⟩
  obtain ⟨_, l1, s1, z1⟩ := g_claims_ready h1 h2 h3 h4 h5 h6
  obtain ⟨lG, sG, zG, hT⟩ := hA _ _ _ _ _ _ _ _ h7 h8 h9 z1 s1
  exact ⟨l1, lG, sG, zG, fun K _ ρ jLK rsK F0 hI h0 =>
    hT K ρ jLK rsK F0 hI (h0.trans l1)⟩

end Fo
