-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookDigitsRun.lean.
The smallness test's lookup on the digits inside the one equation, at the runs that a whole check
holds.

`z_look_at` (FoLookDigits) takes the run equations of `HTailF2.transcriptF` and `HTailF2.objectsF`
and some facts on the states around them. The tied cuts of the three checks (FoTiedG, FoTiedA,
FoTiedH) hand on these two equations inside one chain. This file pays the facts on the states from
the chain's other equations.

Main names:
  `ZTests tl2 tl3 Fc`: the ten premises of `z_look_at` on public numbers, as one record.
  `ZLook J tl tl2 tl3 L Lt F Gt Fb G' c cr cb Fc`: the conclusion of `z_look_at`, word for word,
    under a name.
  `z_look_pass`: `ZLook` where every property that the steps keep passes from the state that
    `transcriptF` left to the state from which `objectsF` runs; under the two runs, `Sized F`,
    F.LS.size = F.ns, c on a view, and `ZTests`.
  `z_look_G`, `z_look_A`, `z_look_H`: `ZLook` at the run equations of the layers' check
    (`g_run_tied`), of the attention check (`a_run_tied`) and of the head's check (`h_run_tied` with
    `h_walk_exact`).
  `lay_mask`, `lay_cell`: at the places of a lay's addresses (FoLookLay) the mask row and the cells
    of which `ZLook` speaks are `Lay.maskAt` and `Lay.cellAt`.

Under: the chain's run equations; the run starts on a view (dry = false); `ZTests`.

Limit: those of FoLookDigits. Fc is free: that it is the state from which the check's own
`coefficients` runs is not said here.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookDigits
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedZ
import OnBytes.Tie.Pv.Lookup.Ends.FoLookLay
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp
open OnBytes.Road.Rows

/-- The premises of `z_look_at` on public numbers. -/
structure ZTests (tl2 tl3 : HTailF2) (Fc : Fork) : Prop where
  t1 : tailTest tl2 = true
  t2 : ∀ q < 2, pieceTest tl2 q = true
  t3 : ∀ q < 2, apartTest tl2 q = true
  t4 : callsTest tl2 = true
  t5 : ∀ h0, Forest.shape #[tl2.z1.call, tl2.z2.call] tl2.lidb = .ok h0 →
    { h0 with pub := tl2.f9.pub } = tl2.f9
  t6 : 2 ^ tl2.f9.cK = tl2.f9.NC
  t7 : 5 ≤ tl2.f9.kT + tl2.f9.cK
  t8 : ∀ q < 2, (tl2.zOf q).call.n ≤ 63
  t9 : coefTest tl3 Fc = true
  t10 : ∀ a ∈ allPieces tl2, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R

/-- The conclusion of `z_look_at`. -/
def ZLook (J : Type) [Fintype J] [DecidableEq J] (tl tl2 tl3 : HTailF2) (L Lt : LinkCtx)
    (F Gt Fb G' : Fork) (c cr cb : Ctx) (Fc : Fork) : Prop :=
    ∃ (tl' : HTailF2) (F1 : Fork) (c5 c1 : Ctx) (g : Heard) (rv : List Fmt.RoundView) (Fa : Fork)
      (ca : Ctx) (tlA : HTailF2) (G1 : Fork) (d1 : Ctx) (tlB : HTailF2) (G2 : Fork) (d2 : Ctx),
      tl.drawMatrixF F c = .ok ((tl', F), c5) ∧
      rootInH [tl.ix.ZZ, tl.ix.BZ] L F c5 = .ok ((((), Lt), F1), c1) ∧
      Forest.pad #[tl2.z1.call, tl2.z2.call] tl2.f9.pub tl2.lidb F1 c1 = .ok ((g, Gt), cr) ∧
      tl2.heard = some g ∧ tl2.f9 = g.shape ∧ tl2.slotA = F1.next ∧ Took c1 rv cr ∧
      Forest.objects g Fb cb = .ok (((), Fa), ca) ∧
      tl2.linJoin9 Fa ca = .ok ((tlA, G1), d1) ∧ tlA.linBits9 G1 d1 = .ok ((tlB, G2), d2) ∧
      Passes G2 G' ∧
      ∀ (K : Type) [Field K] (ρ : Reading K) (en : Ent3 → Option J) (mk : ℕ → Option J)
        (m : J → K) (entry : ℕ → ℕ → ℕ → K) (H : Fork), Later G2 H →
        RowsLaw ρ (coefAll tl3 g Fc) (H.worldOf ρ (fun j => zext m (mk j)) entry)
          (fun t r i => zext m (en (t, r, i))) →
        G2.total ρ (H.worldOf ρ (fun j => zext m (mk j)) entry) =
          Fb.total ρ (H.worldOf ρ (fun j => zext m (mk j)) entry) +
            (batchAt (ρ.val Fb.theta) (lookLed Fb.nClaim
              (digForms tl2 en mk g.shape F1.next (rv.map (rdRV ρ))))).gap m

variable {J : Type} [Fintype J] [DecidableEq J]

/-- Where every property that the steps keep passes on between the two routines. -/
theorem z_look_pass {tl tl2 tl3 : HTailF2} {L Lt : LinkCtx} {F Gt Fb G' : Fork}
    {c cr cb c' : Ctx} {funs : Array HFun}
    (hT : tl.transcriptF L F c = .ok (((tl2, Lt), Gt), cr))
    (hO : tl2.objectsF funs Fb cb = .ok ((tl3, G'), c')) (hp : Passes Gt Fb) (hS : Sized F)
    (hl : F.LS.size = F.ns) (hd : c.ch.dry = false) {Fc : Fork} (T : ZTests tl2 tl3 Fc) :
    ZLook J tl tl2 tl3 L Lt F Gt Fb G' c cr cb Fc := by
  have pT : Passes F Gt := Passes.ofL hT fun I _ => by inv
  have sT := (pT.later hS).2
  exact z_look_at tl tl2 tl3 L Lt F Gt Fb G' c cr cb c' funs hT hS hd hO (hp.later sT).1
    (hp.later sT).2 ((pT.trans hp).ls hS hl) T.t1 T.t2 T.t3 T.t4 T.t5 T.t6 T.t7 T.t8 Fc T.t9 T.t10

/-- **At the layers' check.** -/
theorem z_look_G {P : Layer.Pub} {hp : Layer.HPlan2} {g : ℕ} {Lc : LinkCtx} {F : Fork} {c : Ctx}
    {iU3 : ℕ} {fo : Forest.Heard} {Fl : Fork} {cl : Ctx} {o : Layer.Own} {Fo : Fork} {co : Ctx}
    {L8 : LinkCtx} {Fa : Fork} {ca : Ctx} {tl1 tl2 tl3 : HTailF2} {Lt : LinkCtx} {Gt : Fork}
    {cr : Ctx} {Lb : LinkCtx} {Gb : Fork} {cb : Ctx} {G1 : Fork} {c1 : Ctx} {G2 : Fork} {c2 : Ctx}
    {G3 : Fork} {c3 : Ctx} {G4 : Fork} {c4 : Ctx} {G5 : Fork} {c5 : Ctx} {G6 : Fork} {c6 : Ctx}
    (h1 : Layer.hearLook P.y g (F.fillL.slots hp.ns) c = .ok ((fo, Fl), cl))
    (h2 : Layer.hearOwn P hp g fo Fl cl = .ok ((o, Fo), co))
    (h3 : rootInH [iU3] Lc Fo co = .ok ((((), L8), Fa), ca))
    (h4 : tl1.transcriptF L8 Fa ca = .ok (((tl2, Lt), Gt), cr))
    (h5 : t2Batch Gt.next Lt { Gt with planClaimsF := hp.nLin } cr = .ok ((((), Lb), Gb), cb))
    (h6 : (do Layer.note "the element that batches the claims" (← get).theta : SubM Unit) Gb cb =
      .ok (((), G1), c1))
    (h7 : Forest.objects o.H.fo G1 c1 = .ok (((), G2), c2))
    (h8 : gMid P o G2 c2 = .ok (((), G3), c3))
    (h9 : Layer.claimsPlanes o.v o.H.fo G3 c3 = .ok (((), G4), c4))
    (h10 : gEmb g o G4 c4 = .ok (((), G5), c5))
    (h11 : tl2.objectsF o.funs G5 c5 = .ok ((tl3, G6), c6)) (hd : c.ch.dry = false) {Fc : Fork}
    (T : ZTests tl2 tl3 Fc) : ZLook J tl1 tl2 tl3 L8 Lt Fa Gt G5 G6 ca cr c5 Fc := by
  obtain ⟨s0, z0⟩ := start_ok F.fillL hp.ns
  have pT := g_pass_T h1 h2 h3
  have d1 : cl.ch.dry = false := (stays_Model_Layer_hearLook _ _ _).out _ _ _ h1 hd
  have d2 : co.ch.dry = false := (stays_Model_Layer_hearOwn _ _ _ _ _).out _ _ _ h2 d1
  have d3 : ca.ch.dry = false := (DryL.rootInH _ _ _).out _ _ _ h3 d2
  exact z_look_pass h4 h11 (g_pass_O h5 h6 h7 h8 h9 h10) (pT.later s0).2 (pT.ls s0 z0) d3 T

/-- **At the attention check.** -/
theorem z_look_A {P : Attention.Plan} {Lc : LinkCtx} {F : Fork} {c : Ctx} {f : Attention.First}
    {t : Attention.Tables} {Fh : Fork} {ch : Ctx} {L2 : LinkCtx} {Ft : Fork} {ct cr : Ctx}
    {tl1 tl2 tl3 : HTailF2} {Lt : LinkCtx} {Gt : Fork} {cr' : Ctx} {Lb : LinkCtx} {Gb : Fork}
    {cb : Ctx} {Gc : Fork} {cc : Ctx} {Go : Fork} {co : Ctx}
    (h1 : Attention.hear P (F.fillL.slots P.ns) c = .ok ((f, Fh), ch))
    (h2 : rootInH [P.iU3] Lc Fh ch = .ok ((((), L2), Ft), ct))
    (h3 : Attention.tables P.S P.mats P.nW f.g f.planes f.scores f.d f.x ct = .ok (t, cr))
    (h4 : tl1.transcriptF L2 Ft cr = .ok (((tl2, Lt), Gt), cr'))
    (h5 : Attention.Seam.batch Gt.next Lt { Gt with planClaimsF := P.nLin } cr' =
      .ok ((((), Lb), Gb), cb))
    (h6 : Attention.claims P (aHeard P f t) Gb cb = .ok (((), Gc), cc))
    (h7 : tl2.objectsF t.funs Gc cc = .ok ((tl3, Go), co)) (hd : c.ch.dry = false) {Fc : Fork}
    (T : ZTests tl2 tl3 Fc) : ZLook J tl1 tl2 tl3 L2 Lt Ft Gt Gc Go cr cr' cc Fc := by
  obtain ⟨s0, z0⟩ := start_ok F.fillL P.ns
  have pT := a_pass_T h1 h2
  have d1 : ch.ch.dry = false := (stays_Attention_hear _ _).out _ _ _ h1 hd
  have d2 : ct.ch.dry = false := (DryL.rootInH _ _ _).out _ _ _ h2 d1
  have d3 : cr.ch.dry = false := (dry_tables _ _ _ _ _ _ _ _).out _ _ _ h3 d2
  exact z_look_pass h4 h7 (a_pass_O h5 h6) (pT.later s0).2 (pT.ls s0 z0) d3 T

/-- **At the head's check.** -/
theorem z_look_H {s : Head.Shape} {Y : Head.HL} {b : Head.Border} {hp : Head.HPlanH2}
    {cov : Head.Covered} {wsLay : WsLay} {Lc : LinkCtx} {F : Fork} {c : Ctx} {x : Head.Heard}
    {t : Head.Tables} {iU3 : ℕ} {Fh : Fork} {ch : Ctx} {L9 : LinkCtx} {Fa : Fork} {ca : Ctx}
    {Ga : Fork} {ca' : Ctx} {tl1 tl2 tl3 : HTailF2} {Lt : LinkCtx} {Gt : Fork} {cr : Ctx}
    {claim : WsClaim} {Gw : Fork} {cw : Ctx} {wo : WsForkOut} {Ge : Fork} {ce : Ctx} {Lb : LinkCtx}
    {Gb : Fork} {cb : Ctx} {F1 : Fork} {c1 : Ctx} {F2 : Fork} {c2 : Ctx} {F3 : Fork} {c3 : Ctx}
    {F4 : Fork} {c4 : Ctx} {F5 : Fork} {c5 : Ctx} {F6 : Fork} {c6 : Ctx} {F7 : Fork} {c7 : Ctx}
    (h1 : Head.hear s Y hp cov Lc.check.plain ({ trees := F.trees } : Fork).fillL c =
      .ok ((x, Fh), ch))
    (h2 : rootInH [iU3] Lc Fh ch = .ok ((((), L9), Fa), ca))
    (h3 : Head.tablesOf s Y hp cov x Fa ca = .ok ((t, Ga), ca'))
    (h4 : tl1.transcriptF L9 Ga ca' = .ok (((tl2, Lt), Gt), cr))
    (h5 : Head.weightsClaim (hRun s Y b hp cov x t iU3) wsLay Gt cr = .ok ((claim, Gw), cw))
    (h6 : wsForkEnd wsLay #[claim] #[x.sV] Gw cw = .ok ((wo, Ge), ce))
    (h7 : t2Batch Ge.next Lt { Ge with planClaimsF := hp.nLin } ce = .ok ((((), Lb), Gb), cb))
    (w1 : Forest.objects (hRun s Y b hp cov x t iU3).x.g1 Gb cb = .ok (((), F1), c1))
    (w2 : hMid1 (hRun s Y b hp cov x t iU3) F1 c1 = .ok (((), F2), c2))
    (w3 : Head.claimJoin (hRun s Y b hp cov x t iU3) F2 c2 = .ok (((), F3), c3))
    (w4 : hMid2 (hRun s Y b hp cov x t iU3) F3 c3 = .ok (((), F4), c4))
    (w5 : Head.claimPlanes (hRun s Y b hp cov x t iU3) F4 c4 = .ok (((), F5), c5))
    (w6 : Head.noteConstant "the look-up's planes" F5 c5 = .ok (((), F6), c6))
    (w7 : tl2.objectsF (hRun s Y b hp cov x t iU3).t.funs F6 c6 = .ok ((tl3, F7), c7))
    (hd : c.ch.dry = false) {Fc : Fork} (T : ZTests tl2 tl3 Fc) :
    ZLook J tl1 tl2 tl3 L9 Lt Ga Gt F6 F7 ca' cr c6 Fc := by
  obtain ⟨F', cp, hpad, p0⟩ := h_hear_exact _ _ _ _ _ _ _ _ _ _ h1
  obtain ⟨s0, z0⟩ := start_ok ({ trees := F.trees } : Fork).fillL hp.ns
  have pp : Passes (({ trees := F.trees } : Fork).fillL.slots hp.ns) F' :=
    Passes.of hpad fun I _ => Inv.pad _ _ _
  have pT := pp.trans (h_pass_T p0 h2 h3)
  have d1 : ch.ch.dry = false := ((by stays : DryS (Head.hear s Y hp cov Lc.check.plain)) _).out
    _ _ _ h1 hd
  have d2 : ca.ch.dry = false := (DryL.rootInH _ _ _).out _ _ _ h2 d1
  have d3 : ca'.ch.dry = false := (stays_Model_Head_tablesOf _ _ _ _ _ _).out _ _ _ h3 d2
  exact z_look_pass h4 w7 (h_pass_O h5 h6 h7 w1 w2 w3 w4 w5 w6) (pT.later s0).2 (pT.ls s0 z0) d3 T

section
variable {K : Type} [Field K] (Y : Lay J) (m : J → K)

omit [DecidableEq J] in
theorem lay_mask : (fun j => zext m (entryOf Y (.mask j))) = Y.maskAt m :=
  funext fun j => zext_mask Y m j

omit [DecidableEq J] in
theorem lay_cell :
    (fun t r i => zext m (entryOf Y (.cell t r i))) = fun t r i => Y.cellAt m t r i :=
  funext fun t => funext fun r => funext fun i => zext_cell Y m t r i

end
end Fo
