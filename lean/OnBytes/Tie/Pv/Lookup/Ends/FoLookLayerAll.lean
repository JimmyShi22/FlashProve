-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookLayerAll.lean.
The layers' check on a view: its lookup's claims inside the one equation, with no premise on the
lookup's record.

FoLookLayerTied takes as a premise that the lookup's record holds the flat function's end values.
On a run from a context that is a view with no message open (`Clean`) that is a theorem
(`hcOut2V`, FoPadAll). So here the lookup's first slot and the rounds are terms of the run.

Main names:
  `g_look_clean`: at the first nine run equations of `g_run_tied` (FoTiedG), from a context with
    `Clean`: `Forest.pad` has returned the record o.H.fo from the run's own first state and
    context, and has ended where `Layer.hearLook` ended; rv are the rounds of the view that it took;
    the shape is lawful; and the equation of `layer_look_total` holds at the first slot
    `(F.fillL.slots hp.ns).next` and at the rounds rv, each read by ρ (`rdRV`, FoEv).
  `g_look_run`: the same on a run of `Layer.runForkHidG2` that returns: with the whole chain of run
    equations of `g_run_tied`, and: the run's end state is a later state than the one that
    `Layer.claimsPlanes` left.
  In both the function A stands before every state, context, ring, reading and world. In
  `g_look_clean` it stands behind the records P and o. In `g_look_run` it stands behind P alone and
  takes one argument more: the record o that `Layer.hearOwn` returned in the run at hand.

Under: the run returns; `Clean c`; the three tables' first entries and the world are as in
FoLookLayerRun: the world meets the law of the reads (`ReadsLaw`).

Limit: those of FoLookLayerRun, but for the one on the whole check, which `g_look_run` lifts. So the
list can hang on o: that o holds nothing that was drawn with or after theta is not said here.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookLayerTied
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedLook
import OnBytes.Tie.Pv.Lookup.Forest.FoPadAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun Cb.Fo

/-- **At the chain's first nine run equations, on a view.** -/
theorem g_look_clean (P : Layer.Pub) (o : Layer.Own) :
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
        Clean c →
        Forest.pad P.y.cl P.y.fo.pub P.y.h.lidb (F.fillL.slots hp.ns) c = .ok ((o.H.fo, Fl), cl) ∧
        FoNums.ok o.H.fo.shape = true ∧ Later Fl G1 ∧ Later G1 G4 ∧
        ∃ rv : List Fmt.RoundView, Took c rv cl ∧
          ∀ (K : Type) [CommRing K] (ρ : Reading K),
          ∀ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 → o.v.tabAt "b-bits-1" = some tB1 →
            o.v.tabAt "b-pin" = some tP →
          ∀ H, Later G4 H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K),
            ReadsLaw o.H.fo.shape o.v.y.h.lmb
              (endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next (rv.map (rdRV ρ))).zb0
              (endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next (rv.map (rdRV ρ))).zb1 ν
                  entry o.v.iU3 o.v.K3 tB0 tB1
              tP →
            G4.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
              G1.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
                powSum (ρ.val G1.theta) G1.nClaim
                  ((endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next
                      (rv.map (rdRV ρ))).rows.map (rowRes ν)) +
                clsValue ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (ρ.val G1.theta)
                  (G1.nClaim + ((endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next
                      (rv.map (rdRV ρ))).rows.map
                    (rowRes ν)).length)
                  (A (shownArr G3 o.H.tV.sEnd (nShown P o)) (colsOf G1)) +
                powSum (ρ.val G1.theta)
                  (G1.nClaim + ((endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next
                      (rv.map (rdRV ρ))).rows.map
                    (rowRes ν)).length +
                    (A (shownArr G3 o.H.tV.sEnd (nShown P o)) (colsOf G1)).length)
                  [claimLeaves o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next (rv.map (rdRV ρ))
                      ν
                      (colsK o.H.fo.shape o.v.y.h.lmb
                        (endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next
                            (rv.map (rdRV ρ))).zb0 ν),
                    claimBits o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next (rv.map (rdRV ρ))
                        ν
                      (colsK o.H.fo.shape o.v.y.h.lmb
                        (endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next
                            (rv.map (rdRV ρ))).zb1 ν),
                    Pin.countK o.H.fo.shape o.v.y.h.lmb (Pin.pinColK o.v.y.h.lmb ν)] := by
  obtain ⟨A, hA⟩ := g_look_at P o
  refine ⟨A, fun {hp g Lc F c iU3 fo Fl cl Fo co L8 Fa ca tl1 tl2 Lt Gt cr Lb Gb cb G1 c1 G2 c2 G3
    c3 G4 c4} h1 h2 h3 h4 h5 h6 h7 h8 h9 hc => ?_⟩
  have s0 : Sized (F.fillL.slots hp.ns) := by
    unfold Sized Fork.slots
    simp
  have hpad := g_look_exact _ _ _ _ _ _ _ h1
  have hfo : o.H.fo = fo := g_own_fo P hp g fo _ _ _ _ _ h2
  rw [← hfo] at hpad
  obtain ⟨l1, l4, _, _, hT⟩ := hA h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨⟨h0, q1, q2, q3⟩, _, rv, ht, _, _⟩ :=
    hcOut2V Cb.Gl.E Reading.gl _ _ _ o.v.y.h.lmb _ _ _ _ _
    hpad s0 hc
  have hok : FoNums.ok o.H.fo.shape = true := by
    rw [q3]
    exact shape_ok q1 q2
  refine ⟨hpad, hok, l1, l4, rv, ht, fun K _ ρ => ?_⟩
  obtain ⟨_, _, rv', ht', _, hI⟩ := hcOut2V K ρ _ _ _ o.v.y.h.lmb _ _ _ _ _ hpad s0 hc
  obtain rfl := took_unique ht ht'
  exact hT K ρ _ _ Fl hI (Later.refl _) hok

/-- **On a whole run of the layers' check, on a view.** -/
theorem g_look_run (P : Layer.Pub) :
    ∃ A : Layer.Own → Array E → (ℕ → ℕ) → List Cl,
      ∀ (hp : Layer.HPlan2) (g : ℕ) (Lc : LinkCtx) (F : Fork) (c : Ctx)
        (r : ((WsForkOut × LinkCtx) × Fork) × Ctx),
        Layer.runForkHidG2 P hp g Lc F c = .ok r → Clean c →
    ∃ (iU3 : ℕ) (fo : Forest.Heard) (Fl : Fork) (cl : Ctx) (o : Layer.Own) (Fo : Fork) (co : Ctx)
      (L8 : LinkCtx) (Fa : Fork) (ca : Ctx) (tl1 tl2 tl3 : HTailF2) (Lt : LinkCtx) (Gt : Fork)
      (cr : Ctx) (Lb : LinkCtx) (Gb : Fork) (cb : Ctx) (G1 : Fork) (c1 : Ctx) (G2 : Fork) (c2 : Ctx)
      (G3 : Fork) (c3 : Ctx) (G4 : Fork) (c4 : Ctx) (G5 : Fork) (c5 : Ctx) (G6 : Fork) (c6 : Ctx)
      (G7 : Fork) (c7 : Ctx) (G8 : Fork) (c8 : Ctx) (n : ℕ),
      hp.tl.ix.U.getD 2 none = some iU3 ∧
      Layer.hearLook P.y g (F.fillL.slots hp.ns) c = .ok ((fo, Fl), cl) ∧
      Layer.hearOwn P hp g fo Fl cl = .ok ((o, Fo), co) ∧
      rootInH [iU3] Lc Fo co = .ok ((((), L8), Fa), ca) ∧
      hp.tl.closeFuns o.funs = some tl1 ∧
      tl1.transcriptF L8 Fa ca = .ok (((tl2, Lt), Gt), cr) ∧
      t2Batch Gt.next Lt { Gt with planClaimsF := hp.nLin } cr = .ok ((((), Lb), Gb), cb) ∧
      (do Layer.note "the element that batches the claims" (← get).theta : SubM Unit) Gb cb =
        .ok (((), G1), c1) ∧
      Forest.objects o.H.fo G1 c1 = .ok (((), G2), c2) ∧
      gMid P o G2 c2 = .ok (((), G3), c3) ∧
      Layer.claimsPlanes o.v o.H.fo G3 c3 = .ok (((), G4), c4) ∧
      gEmb g o G4 c4 = .ok (((), G5), c5) ∧
      tl2.objectsF o.funs G5 c5 = .ok ((tl3, G6), c6) ∧
      gLast g hp o G6 c6 = .ok (((), G7), c7) ∧
      (G7.nClaim == hp.nLin) = true ∧
      gTests hp tl3 G7 c7 = .ok (((), G8), c8) ∧
      tl3.equationsLaidF = some n ∧
      doorH n Lb G8 c8 = .ok ((((), r.1.1.2), r.1.2), r.2) ∧ r.1.1.1 = o.wo ∧
      Later G4 r.1.2 ∧
        Forest.pad P.y.cl P.y.fo.pub P.y.h.lidb (F.fillL.slots hp.ns) c = .ok ((o.H.fo, Fl), cl) ∧
        FoNums.ok o.H.fo.shape = true ∧ Later Fl G1 ∧ Later G1 G4 ∧
        ∃ rv : List Fmt.RoundView, Took c rv cl ∧
          ∀ (K : Type) [CommRing K] (ρ : Reading K),
          ∀ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 → o.v.tabAt "b-bits-1" = some tB1 →
            o.v.tabAt "b-pin" = some tP →
          ∀ H, Later G4 H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K),
            ReadsLaw o.H.fo.shape o.v.y.h.lmb
              (endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next (rv.map (rdRV ρ))).zb0
              (endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next (rv.map (rdRV ρ))).zb1 ν
                  entry o.v.iU3 o.v.K3 tB0 tB1
              tP →
            G4.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
              G1.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
                powSum (ρ.val G1.theta) G1.nClaim
                  ((endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next
                      (rv.map (rdRV ρ))).rows.map (rowRes ν)) +
                clsValue ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (ρ.val G1.theta)
                  (G1.nClaim + ((endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next
                      (rv.map (rdRV ρ))).rows.map
                    (rowRes ν)).length)
                  (A o (shownArr G3 o.H.tV.sEnd (nShown P o)) (colsOf G1)) +
                powSum (ρ.val G1.theta)
                  (G1.nClaim + ((endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next
                      (rv.map (rdRV ρ))).rows.map
                    (rowRes ν)).length +
                    (A o (shownArr G3 o.H.tV.sEnd (nShown P o)) (colsOf G1)).length)
                  [claimLeaves o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next (rv.map (rdRV ρ))
                      ν
                      (colsK o.H.fo.shape o.v.y.h.lmb
                        (endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next
                            (rv.map (rdRV ρ))).zb0 ν),
                    claimBits o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next (rv.map (rdRV ρ))
                        ν
                      (colsK o.H.fo.shape o.v.y.h.lmb
                        (endsOf o.H.fo.shape o.v.y.h.lmb (F.fillL.slots hp.ns).next
                            (rv.map (rdRV ρ))).zb1 ν),
                    Pin.countK o.H.fo.shape o.v.y.h.lmb (Pin.pinColK o.v.y.h.lmb ν)] := by
  choose A hA using fun o => g_look_clean P o
  refine ⟨A, fun hp g Lc F c r h hc => ?_⟩
  obtain ⟨iU3, fo, Fl, cl, o, Fo', co, L8, Fa, ca, tl1, tl2, tl3, Lt, Gt, cr, Lb, Gb, cb, G1, c1,
    G2, c2, G3, c3, G4, c4, G5, c5, G6, c6, G7, c7, G8, c8, n, e0, e1, e2, e3, ec, e4, e5, e6, e7,
    e8, e9, e10, e11, e12, e13, e14, e15, e16, e17⟩ := g_run_tied P hp g Lc F c r h
  obtain ⟨_, _, s1, _⟩ := g_claims_ready e1 e2 e3 e4 e5 e6
  have p7 : Passes G1 G2 := Passes.of e7 fun I _ => by inv
  have p8 : Passes G2 G3 := Passes.of e8 fun I _ => by unfold gMid gLedger; inv
  have p9 : Passes G3 G4 := Passes.of e9 fun I _ => by inv
  have s4 : Sized G4 := ((p7.trans (p8.trans p9)).later s1).2
  have p10 : Passes G4 G5 := Passes.of e10 fun I _ => by unfold gEmb gEmb0; inv
  have p11 : Passes G5 G6 := Passes.of e11 fun I _ => by inv
  have p12 : Passes G6 G7 := Passes.of e12 fun I _ => by unfold gLast; inv
  have p14 : Passes G7 G8 := Passes.of e14 fun I _ => by unfold gTests; inv
  have p16 : Passes G8 r.1.2 := Passes.ofL e16 fun I _ => by inv
  exact ⟨iU3, fo, Fl, cl, o, Fo', co, L8, Fa, ca, tl1, tl2, tl3, Lt, Gt, cr, Lb, Gb, cb, G1, c1,
    G2, c2, G3, c3, G4, c4, G5, c5, G6, c6, G7, c7, G8, c8, n, e0, e1, e2, e3, ec, e4, e5, e6, e7,
    e8, e9, e10, e11, e12, e13, e14, e15, e16, e17,
    ((p10.trans (p11.trans (p12.trans (p14.trans p16)))).later s4).1,
    hA o e1 e2 e3 e4 e5 e6 e7 e8 e9 hc⟩

end Fo
