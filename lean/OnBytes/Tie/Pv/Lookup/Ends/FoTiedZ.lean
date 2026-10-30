-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTiedZ.lean.
The smallness test's lookup on the digits, from its messages to its claims.

`z_chain`: its premises are two run equations that each of the three whole checks hands on
(a_run_tied, h_run_tied with h_walk_exact, g_run_tied): transcriptF's and objectsF's, for the state
tl2 of the test that transcriptF returned; that every kept property passes from where transcriptF
ended to where objectsF began; and of the state and context from which transcriptF ran: the slots'
arrays have their sizes, the one equation has a coefficient for each slot, the run is on a view.
Then: Forest.pad has returned, from a state with the arrays at their sizes and a context with no
message open, and it ended where transcriptF ended; tl2 keeps its record g; Forest.objects g has
returned from where objectsF began; linJoin9 from where objects ended; linBits9 from where linJoin9
ended; the state from which linJoin9 ran is a later state than the one that pad left, has the arrays
at their sizes and a coefficient for each slot; from the state that linBits9 left to the one that
objectsF left every kept property passes on.
`pass_plan`: setting the number of planned claims keeps every kept property.
`a_pass_T`, `a_pass_O`, `h_pass_T`, `h_pass_O`, `g_pass_T`, `g_pass_O`: at the three checks, from
the run equations that the tied statements hand on: every kept property passes from the check's
first state to where transcriptF begins, and from where transcriptF ended to where objectsF begins.
`start_ok`: behind Fork.slots the arrays have their sizes and there is a coefficient for each slot.
Dropped in z_chain, though site_Z (OnBytes/Tie/Pv/Lookup/Ends/FoSite.lean) has them on the same
premise: the run equations of
drawMatrixF, from where transcriptF began, and of rootInH, which ends where Forest.pad began: so
z_chain ties the state and the context from which pad ran only by the three properties named.
Forest.pad stands at the calls, public numbers and bound of a record tl', of which it is said that
tl2 is tl' with four fields set; that tl' comes from tl1 is said by site_Z and site_Z_own
(OnBytes/Tie/Pv/Lookup/Ends/FoSiteOwn.lean). The record tl3 that objectsF returns is tied to
nothing. z_chain and site_Z_own
meet in g: both say that tl2 keeps it.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedLook
import OnBytes.Tie.Pv.Lookup.Ends.FoSite

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem start_ok (F : Fork) (n : ℕ) : Sized (F.slots n) ∧ (F.slots n).LS.size = (F.slots n).ns :=
  ⟨sized_slots F n, Fork.slots_sized F n⟩

theorem pass_plan (F : Fork) (n : ℕ) : Passes F { F with planClaimsF := n } :=
  fun _ _ h => Prim.book F _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h

theorem z_chain {tl1 tl2 tl3 : HTailF2} {L L' : LinkCtx} {Ft Gt Fz Gz : Fork}
    {cr cr' cz cz' : Ctx} {funs : Array HFun}
    (hT : tl1.transcriptF L Ft cr = .ok (((tl2, L'), Gt), cr'))
    (hO : tl2.objectsF funs Fz cz = .ok ((tl3, Gz), cz')) (hp : Passes Gt Fz) (hS : Sized Ft)
    (hl : Ft.LS.size = Ft.ns) (hd : cr.ch.dry = false) :
    ∃ (tl' : HTailF2) (F1 : Fork) (c1 : Ctx) (g : Forest.Heard) (Fa : Fork) (ca : Ctx)
      (tlJ : HTailF2) (G1 : Fork) (cJ : Ctx) (tlB : HTailF2) (G2 : Fork) (cB : Ctx),
      Forest.pad #[tl'.z1.call, tl'.z2.call] tl'.f9.pub tl'.lidb F1 c1 = .ok ((g, Gt), cr') ∧
      Sized F1 ∧ Later Ft F1 ∧ Clean c1 ∧
      tl2 = { tl' with foldDrawn := tl'.foldDrawn + 1, slotA := Ft.next, slotB := Gt.next,
                       heard := some g } ∧
      Forest.objects g Fz cz = .ok (((), Fa), ca) ∧
      tl2.linJoin9 Fa ca = .ok ((tlJ, G1), cJ) ∧ tlJ.linBits9 G1 cJ = .ok ((tlB, G2), cB) ∧
      Later Gt Fa ∧ Sized Fa ∧ Fa.LS.size = Fa.ns ∧ Passes G2 Gz := by
  obtain ⟨tl', F5, F1, c5, c1, L6, g, -, -, hpad, hr, s1, l1, k1⟩ := site_Z _ _ _ _ _ hT hS hd
  have e2 : tl2 =
      { tl' with
        foldDrawn := tl'.foldDrawn + 1, slotA := Ft.next, slotB := Gt.next, heard := some g } :=
    (Prod.mk.inj hr).1
  obtain ⟨g', Fa, ca, tlJ, G1, cJ, tlB, G2, cB, hg, ho, hJ, hB, pE⟩ :=
    z_objects_exact _ _ _ _ _ _ _ hO
  have eg : g' = g := by
    rw [e2] at hg
    exact (Option.some.inj hg).symm
  subst eg
  have pT : Passes Ft Gt := Passes.ofL hT (fun I _ => by inv)
  have pA : Passes Gt Fa := hp.trans (Passes.of ho (fun I _ => by inv))
  have sG := (pT.later hS).2
  exact ⟨tl', F1, c1, g', Fa, ca, tlJ, G1, cJ, tlB, G2, cB, hpad, s1, l1, k1, e2, ho, hJ, hB,
    (pA.later sG).1, (pA.later sG).2, (pT.trans pA).ls hS hl, pE⟩

/-! ### the three checks -/

theorem a_pass_T {P : Attention.Plan} {F0 Fh Ft : Fork} {c ch ct : Ctx} {f : Attention.First}
    {Lc L2 : LinkCtx} (h1 : Attention.hear P F0 c = .ok ((f, Fh), ch))
    (h2 : rootInH [P.iU3] Lc Fh ch = .ok ((((), L2), Ft), ct)) : Passes F0 Ft :=
  (Passes.of h1 (fun I _ => by inv)).trans (Passes.ofL h2 (fun I _ => by inv))

theorem a_pass_O {P : Attention.Plan} {hd : Attention.Heard} {Gt Gb Gc : Fork} {cr cb cc : Ctx}
    {Lt Lb : LinkCtx}
    (h1 : Attention.Seam.batch Gt.next Lt { Gt with planClaimsF := P.nLin } cr =
      .ok ((((), Lb), Gb), cb))
    (h2 : Attention.claims P hd Gb cb = .ok (((), Gc), cc)) : Passes Gt Gc :=
  (pass_plan Gt _).trans ((Passes.ofL h1 (fun I _ => by inv)).trans
    (Passes.of h2 (fun I _ => by inv)))

theorem g_pass_T {P : Layer.Pub} {hp : Layer.HPlan2} {g iU3 : ℕ} {F0 Fl Fo Fa : Fork}
    {c cl co ca : Ctx} {fo : Forest.Heard} {o : Layer.Own} {Lc L8 : LinkCtx}
    (h1 : Layer.hearLook P.y g F0 c = .ok ((fo, Fl), cl))
    (h2 : Layer.hearOwn P hp g fo Fl cl = .ok ((o, Fo), co))
    (h3 : rootInH [iU3] Lc Fo co = .ok ((((), L8), Fa), ca)) : Passes F0 Fa :=
  (Passes.of h1 (fun I _ => by inv)).trans ((Passes.of h2 (fun I _ => by inv)).trans
    (Passes.ofL h3 (fun I _ => by inv)))

theorem h_pass_T {s : Head.Shape} {Y : Head.HL} {hp : Head.HPlanH2} {cov : Head.Covered}
    {iU3 : ℕ} {x : Head.Heard} {t : Head.Tables} {F' Fh Fa Ga : Fork} {ch ca ca' : Ctx}
    {Lc L9 : LinkCtx} (h0 : Passes F' Fh)
    (h2 : rootInH [iU3] Lc Fh ch = .ok ((((), L9), Fa), ca))
    (h3 : Head.tablesOf s Y hp cov x Fa ca = .ok ((t, Ga), ca')) : Passes F' Ga :=
  h0.trans ((Passes.ofL h2 (fun I _ => by inv)).trans (Passes.of h3 (fun I _ => by inv)))

theorem g_pass_O {P : Layer.Pub} {hp : Layer.HPlan2} {g : ℕ} {o : Layer.Own}
    {Gt Gb G1 G2 G3 G4 G5 : Fork} {cr cb c1 c2 c3 c4 c5 : Ctx} {Lt Lb : LinkCtx}
    (h1 : t2Batch Gt.next Lt { Gt with planClaimsF := hp.nLin } cr = .ok ((((), Lb), Gb), cb))
    (h2 : (do Layer.note "the element that batches the claims" (← get).theta : SubM Unit) Gb cb =
      .ok (((), G1), c1))
    (h3 : Forest.objects o.H.fo G1 c1 = .ok (((), G2), c2))
    (h4 : gMid P o G2 c2 = .ok (((), G3), c3))
    (h5 : Layer.claimsPlanes o.v o.H.fo G3 c3 = .ok (((), G4), c4))
    (h6 : gEmb g o G4 c4 = .ok (((), G5), c5)) : Passes Gt G5 :=
  (pass_plan Gt _).trans ((Passes.ofL h1 (fun I _ => by inv)).trans
    ((Passes.of h2 (fun I _ => by inv)).trans ((Passes.of h3 (fun I _ => by inv)).trans
      ((Passes.of h4 (fun I _ => by unfold gMid gLedger; inv)).trans
        ((Passes.of h5 (fun I _ => by inv)).trans
          (Passes.of h6 (fun I _ => by unfold gEmb gEmb0; inv)))))))

theorem h_pass_O {R : Head.Run} {wsLay : WsLay} {hp : Head.HPlanH2} {claim : WsClaim}
    {sV : Array ℕ} {wo : WsForkOut} {Gt Gw Ge Gb F1 F2 F3 F4 F5 F6 : Fork}
    {cr cw ce cb c1 c2 c3 c4 c5 c6 : Ctx} {Lt Lb : LinkCtx}
    (h1 : Head.weightsClaim R wsLay Gt cr = .ok ((claim, Gw), cw))
    (h2 : wsForkEnd wsLay #[claim] sV Gw cw = .ok ((wo, Ge), ce))
    (h3 : t2Batch Ge.next Lt { Ge with planClaimsF := hp.nLin } ce = .ok ((((), Lb), Gb), cb))
    (h4 : Forest.objects R.x.g1 Gb cb = .ok (((), F1), c1))
    (h5 : hMid1 R F1 c1 = .ok (((), F2), c2))
    (h6 : Head.claimJoin R F2 c2 = .ok (((), F3), c3))
    (h7 : hMid2 R F3 c3 = .ok (((), F4), c4))
    (h8 : Head.claimPlanes R F4 c4 = .ok (((), F5), c5))
    (h9 : Head.noteConstant "the look-up's planes" F5 c5 = .ok (((), F6), c6)) : Passes Gt F6 :=
  (Passes.of h1 (fun I _ => by inv)).trans ((Passes.of h2 (fun I _ => by inv)).trans
    ((pass_plan Ge _).trans ((Passes.ofL h3 (fun I _ => by inv)).trans
      ((Passes.of h4 (fun I _ => by inv)).trans
        ((Passes.of h5 (fun I _ => by unfold hMid1; inv)).trans
          ((Passes.of h6 (fun I _ => by inv)).trans
            ((Passes.of h7 (fun I _ => by unfold hMid2; inv)).trans
              ((Passes.of h8 (fun I _ => by inv)).trans
                (Passes.of h9 (fun I _ => by inv))))))))))

end Fo
