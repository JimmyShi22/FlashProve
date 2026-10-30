-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookLayerReads.lean.
The layers' lookup inside the one equation, under the law of the reads at the sub-proof's own list
of tables.

`g_look_run` (OnBytes/Tie/Pv/Lookup/Ends/FoLookLayerAll.lean; under the name `LayerLookOf` in
OnBytes/Tie/Pv/Lookup/Ends/FoPassedLayerLook.lean) asks of the world the law of the reads at the
three tables of the lookup's planes (`ReadsLaw`). `layer_readsLaw`
(OnBytes/Tie/Pv/Lookup/Ends/FoReadsLayer.lean) gives that law from the law at all tables of the list
that the check itself closes (`ReadsAll` at `o.funs`). This file joins the two.

Main names:
  `planeMatB y mats`: a test on public numbers: the layout's record of the lookup is what
    `Forest.shape` makes of its calls (`madeB`, OnBytes/Tie/Pv/Lookup/Ends/FoShapesBDefs.lean); the
    planes' matrix has its rows in one block of 2^lmb; it has at least the planes' columns.
  `LayerLookAll`: `LayerLookOf`, word for word, but for what it asks of the world: the cells of the
    planes' matrix are the lookup's cells, and `ReadsAll` at the plan's matrices and `o.funs`. The
    three first entries of the tables are no letters of it.
  `layer_lookAll`: `LayerLookOf` gives it, on a view, under `planeMatB`.
  `passed_layer_look_all`: `passed_layer_look` with `LayerLookAll`, each group under `planeMatB` at
    the call's own layout and the group's plan.
Limits: those of OnBytes/Tie/Pv/Lookup/Ends/FoPassedLayerLook.lean: the equation is on the total
behind Layer.claimsPlanes, not on the total at the run's end; of the list A neither the length nor
the claims are said. Not shown here: that any run's world meets `ReadsAll`. `planeMatB` holds at
every group's plan of a record that publicOf returns (`public_planeMatB`,
OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPubG.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPassedLayerLook
import OnBytes.Tie.Pv.Lookup.Ends.FoReadsLayer
import OnBytes.Tie.Pv.Lookup.Ends.FoShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.Model.Verify
open OnBytes.Model.Stages Cb.Fo

/-- The test on public numbers. -/
def planeMatB (y : Layer.Lay) (mats : Array TMat) : Bool :=
  madeB y.cl y.h.lidb y.fo && decide ((mats.getD (Layer.matIx y).iB {}).m / 2 ^ y.h.lmb = 1) &&
    decide (planeCols y.fo y.h.lmb ≤ (mats.getD (Layer.matIx y).iB {}).k)

/-- What g_look_run concludes of a run of the layers' check, under the law at all its tables. -/
def LayerLookAll (A : Layer.Own → Array E → (ℕ → ℕ) → List Cl) (P : Layer.Pub) (hp : Layer.HPlan2)
    (g : ℕ) (Lc : LinkCtx) (F : Fork) (c : Ctx) (r : ((WsForkOut × LinkCtx) × Fork) × Ctx) : Prop :=
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
          ∀ H, Later G4 H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K) (cellM : ℕ → ℕ → ℕ → K),
            (∀ r < 2 ^ P.y.h.lmb, ∀ c < planeCols P.y.fo P.y.h.lmb,
              cellM (Layer.matIx P.y).iB r c = ν (.cell r c)) →
            ReadsAll ρ hp.tl.mats o.funs entry o.v.iU3 o.v.K3 cellM →
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
                    Pin.countK o.H.fo.shape o.v.y.h.lmb (Pin.pinColK o.v.y.h.lmb ν)]

theorem layer_lookAll {A : Layer.Own → Array E → (ℕ → ℕ) → List Cl} {P : Layer.Pub}
    {hp : Layer.HPlan2} {g : ℕ} {Lc : LinkCtx} {F : Fork} {c : Ctx}
    {r : ((WsForkOut × LinkCtx) × Fork) × Ctx} (h : LayerLookOf A P hp g Lc F c r) (hc : Clean c)
    (hB : planeMatB P.y hp.tl.mats = true) : LayerLookAll A P hp g Lc F c r := by
  obtain ⟨iU3, fo, Fl, cl, o, Fo', co, L8, Fa, ca, tl1, tl2, tl3, Lt, Gt, cr, Lb, Gb, cb, G1, c1,
    G2, c2, G3, c3, G4, c4, G5, c5, G6, c6, G7, c7, G8, c8, n, e0, e1, e2, e3, ec, e4, e5, e6, e7,
    e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, l1, hpad, hok, l2, l3, rv, ht, hT⟩ := h
  refine ⟨iU3, fo, Fl, cl, o, Fo', co, L8, Fa, ca, tl1, tl2, tl3, Lt, Gt, cr, Lb, Gb, cb, G1, c1,
    G2, c2, G3, c3, G4, c4, G5, c5, G6, c6, G7, c7, G8, c8, n, e0, e1, e2, e3, ec, e4, e5, e6, e7,
    e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, l1, hpad, hok, l2, l3, rv, ht,
    fun K _ ρ H hH ν entry cellM h4 hA => ?_⟩
  simp only [planeMatB, Bool.and_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨b1, b2⟩, b3⟩ := hB
  obtain ⟨tB0, tB1, tP, t0, t1, t2, _⟩ := g_planes_exact _ _ _ _ _ _ e9
  have ey : o.v.y = P.y := (own_tables P hp g fo _ _ _ _ _ e2).1
  have ef : o.H.fo = fo := g_own_fo P hp g fo _ _ _ _ _ e2
  have es : o.H.fo.shape = P.y.fo := by
    rw [ef]
    exact g_shape_is P.y g _ _ _ _ fo e1 (made_of_test b1)
  obtain ⟨_, _, rv', ht', _, hI⟩ :=
    hcOut2V K ρ _ _ _ o.v.y.h.lmb _ _ _ _ _ hpad (sized_slots F.fillL hp.ns) hc
  obtain rfl := took_unique ht ht'
  refine hT K ρ tB0 tB1 tP t0 t1 t2 H hH ν entry
    (layer_readsLaw ρ P hp g fo _ _ _ _ o e2 Fl _ _ hI hp.tl.mats cellM ν ?_ ?_ ?_ entry _ _ hA tB0
      tB1 tP t0 t1 t2)
  · rw [ey]
    exact b2
  · rw [ey, es]
    exact b3
  · rw [ey, es]
    exact h4

/-- From an accepted call to the layers' lookups inside their one equations. -/
theorem passed_layer_look_all :
    ∃ A : Layer.Pub → Layer.Own → Array E → (ℕ → ℕ) → List Cl,
      ∀ {o : Options} {f : Files} {k : Nat} {entry : FileIn}, entryNumber o f = .ok k →
      (wholeCall o { f with entry := entry }).passing = true →
    ∃ (r : Read) (ent : ByteArray) (p : Planned) (C : Common) (table further : Params.TableName)
      (so : Head.StOwn) (cov : Head.Covered) (item : ByteArray) (links : Array LinkH)
      (rd : Proof.ProofRead) (x : Proof.LinksResult × Ctx) (check check2 : ChainCheck)
      (c1 c2 : Ctx),
      PassedRan o f k entry r ent p C table further so cov item links rd x check check2 c1 c2 ∧
      publicOf r.pol r.KL r.layout = .ok C.X ∧
      (∀ (g : Nat) (hp : Layer.HPlan2), C.X.G[g]? = some hp →
        planeMatB C.X.layers.y hp.tl.mats = true →
        ∃ (i : Nat) (hb : i < C.built.links.size) (hi : i < links.size) (q' : ChainCheck)
          (d1 d2 : Ctx) (D : LinkCtx) (F : Fork) (w : WsForkOut),
          CutAt C.X cov links C.built.links p.chains.proof.first C.X.layers.wsLay check c1
            ((check2, x.1), c2) i hb hi q' d1 d2 D F ∧
          links[i] = (layersPlanOf C.X cov.tokv g hp).link ("G" ++ toString g) (1 + g) 0 g true ∧
          Layer.runForkHidG2 { C.X.layers with tokv := cov.tokv } hp g
            { check := q', link := i, arrayOf := (C.built.links[i]).arrayOf, list := hp.Tp }
            hp.Fp d1 = .ok (((w, D), F), d2) ∧
          LayerLookAll (A { C.X.layers with tokv := cov.tokv }) { C.X.layers with tokv := cov.tokv }
            hp g { check := q', link := i, arrayOf := (C.built.links[i]).arrayOf, list := hp.Tp }
            hp.Fp d1 (((w, D), F), d2)) := by
  obtain ⟨A, hA⟩ := passed_layer_look
  refine ⟨A, ?_⟩
  intro o f k entry hk h
  obtain ⟨r, ent, p, C, table, further, so, cov, item, links, rd, x, check, check2, c1, c2, hP, hX,
    hG⟩ := hA hk h
  refine ⟨r, ent, p, C, table, further, so, cov, item, links, rd, x, check, check2, c1, c2, hP, hX,
    fun g hp hg hB => ?_⟩
  obtain ⟨i, hb, hi, q', d1, d2, D, F, w, hc, el, hr, hL⟩ := hG g hp hg
  have hcl : Clean d1 := by
    obtain ⟨_, _, _, _, _, hcl, _⟩ := hc
    exact hcl
  exact ⟨i, hb, hi, q', d1, d2, D, F, w, hc, el, hr, layer_lookAll hL hcl hB⟩

end Fo
