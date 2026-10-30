-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPassedLayerLook.lean.
The layers' lookups inside their one equations, from a call that the byte-level verifier accepts.

passed_places (OnBytes/Tie/Pv/Lookup/Ends/FoPassedPlaces.lean) goes from the verifier's whole call
on a set of files, if its
result is a passing one, to the run of each sub-proof's routine inside it. g_look_run
(OnBytes/Tie/Pv/Lookup/Ends/FoLookLayerAll.lean) goes from a run of the layers' check on a view to
the equation on its total.
This file puts the two together, at every group of layers.

States:
  LayerLookOf A P hp g Lc F c r: under one name, what g_look_run concludes of a run of
    Layer.runForkHidG2 P hp g from (Lc, F, c) to r, letter for letter: the chain of run equations of
    g_run_tied; the run's end state is later than the one that Layer.claimsPlanes left; Forest.pad
    has returned the lookup's record from the run's own first state and context; the shape is
    lawful; rv are the rounds of the view that it took; and, in the world of every later state that
    meets the law of the reads, the total behind Layer.claimsPlanes is the total before
    Forest.objects plus: powSum of the flat function's rows; the list A; powSum of claimLeaves,
    claimBits and the counts' sum. There is no member on the keys: the layers add no claim on the
    keys in this stretch (see OnBytes/Tie/Pv/Lookup/Ends/FoStartClaim.lean). A reads what
    Layer.hearOwn returned, the values under the end slots of the first token sumcheck in the state
    before Layer.claimsPlanes, and the arrays' numbers of columns; its length is not said.
  layer_lookOf: g_look_run in that word.
  passed_layer_look: if the whole call on the files with the entry returns a passing result:
    PassedRan and the public record, as in passed_places, on the same witnesses; and for each group
    g with a plan hp for its layers: the place i, CutAt, the link and the run of Layer.runForkHidG2,
    as passed_places has them, and of that very run: LayerLookOf.
  In the last two the function A stands first: before the files, every state, context, record and
    world; in passed_layer_look it reads the layers' public record too.
Premises, sorted. On the call: the entry's number is read; the whole call's result is a passing one.
On the world (inside LayerLookOf, as a condition): ReadsLaw.
Limits: those of OnBytes/Tie/Pv/Lookup/Ends/FoLookLayerAll.lean. Not said: passed_places' clauses on
attention and on the head.
Not shown: that any run's world meets ReadsLaw.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookLayerAll
import OnBytes.Tie.Pv.Lookup.Ends.FoPassedPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.Model.Verify
open OnBytes.Model.Stages Cb.Fo

/-- What g_look_run concludes of a run of the layers' check. -/
def LayerLookOf (A : Layer.Own → Array E → (ℕ → ℕ) → List Cl) (P : Layer.Pub) (hp : Layer.HPlan2)
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
                    Pin.countK o.H.fo.shape o.v.y.h.lmb (Pin.pinColK o.v.y.h.lmb ν)]

/-- g_look_run, in that word. -/
theorem layer_lookOf (P : Layer.Pub) :
    ∃ A : Layer.Own → Array E → (ℕ → ℕ) → List Cl,
      ∀ (hp : Layer.HPlan2) (g : ℕ) (Lc : LinkCtx) (F : Fork) (c : Ctx)
        (r : ((WsForkOut × LinkCtx) × Fork) × Ctx),
        Layer.runForkHidG2 P hp g Lc F c = .ok r → Clean c → LayerLookOf A P hp g Lc F c r :=
  g_look_run P

/-- From an accepted call to the layers' lookups inside their one equations. -/
theorem passed_layer_look :
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
        ∃ (i : Nat) (hb : i < C.built.links.size) (hi : i < links.size) (q' : ChainCheck)
          (d1 d2 : Ctx) (D : LinkCtx) (F : Fork) (w : WsForkOut),
          CutAt C.X cov links C.built.links p.chains.proof.first C.X.layers.wsLay check c1
            ((check2, x.1), c2) i hb hi q' d1 d2 D F ∧
          links[i] = (layersPlanOf C.X cov.tokv g hp).link ("G" ++ toString g) (1 + g) 0 g true ∧
          Layer.runForkHidG2 { C.X.layers with tokv := cov.tokv } hp g
            { check := q', link := i, arrayOf := (C.built.links[i]).arrayOf, list := hp.Tp }
            hp.Fp d1 = .ok (((w, D), F), d2) ∧
          LayerLookOf (A { C.X.layers with tokv := cov.tokv }) { C.X.layers with tokv := cov.tokv }
            hp g { check := q', link := i, arrayOf := (C.built.links[i]).arrayOf, list := hp.Tp }
            hp.Fp d1 (((w, D), F), d2)) := by
  choose A hA using layer_lookOf
  refine ⟨A, ?_⟩
  intro o f k entry hk h
  obtain ⟨r, ent, p, C, table, further, so, cov, item, links, rd, x, check, check2, c1, c2, hP, hX,
    hG, _, _⟩ := passed_places hk h
  refine ⟨r, ent, p, C, table, further, so, cov, item, links, rd, x, check, check2, c1, c2, hP, hX,
    fun g hp hg => ?_⟩
  obtain ⟨i, hb, hi, q', d1, d2, D, F, w, hc, el, hr⟩ := hG g hp hg
  have hcl : Clean d1 := by
    obtain ⟨_, _, _, _, _, hcl, _⟩ := hc
    exact hcl
  exact ⟨i, hb, hi, q', d1, d2, D, F, w, hc, el, hr, hA _ _ _ _ _ _ _ hr hcl⟩

end Fo
