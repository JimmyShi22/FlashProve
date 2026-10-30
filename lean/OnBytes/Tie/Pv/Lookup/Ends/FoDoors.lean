-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoDoors.lean.
The doors of the lookups in the three kinds of sub-proof: at each call of the lookup's routine, what
the law at a lookup's place takes from the caller.

The law at a lookup's place takes four things from the caller: a run of the lookup's routine
(OnBytes.Model.Forest.pad) from a state Fk and a context cx; that the record's shape is made of the
calls, the public numbers and the bound by the byte-level verifier's own routines (`ShapeOf`);
`Sized Fk`; `Clean cx`. Each sub-proof calls the routine twice: for its own calls, first of all, and
for the digits of its smallness test. The law is `Fo.look_place`
(OnBytes/Tie/Pv/Lookup/Peel/FoPeelPlace.lean); `Fo.Peel.look_yesT`
(OnBytes/Tie/Pv/Lookup/Forest/FoPeelT.lean) takes the same four.
Mind: a door, here, is the entry of a lookup. It is another thing than the closing routine `doorH`
(OnBytes/Model/Trees.lean) and the mark `doorShutF` of a sub-proof's state.

 * `Door calls pub lid Fk cx g F' cx'`: these four, under one name. `door_of`: the run, `Sized` and
   `Clean` give the fourth (`hcOut2V`, OnBytes/Tie/Pv/Lookup/Forest/FoPadAll.lean).
 * `DoorZ tl L F c tl2 Lt Gt c'`: the door of the digits inside a run of `HTailF2.transcriptF` from
   (L, F, c) to ((tl2, Lt), Gt, c'): the draw of the matrix has run from (F, c), the commitment from
   where it ended, to (Lt, F1, c1); `Door` at tl's own two calls, public numbers and bound, from
   (F1, c1) to (Gt, c'); tl2 keeps the lookup's record. `door_Z`: it holds if `Sized F` and c is on
   a view (`site_Z_own`, OnBytes/Tie/Pv/Lookup/Ends/FoSiteOwn.lean).
 * `DoorsA P Lc F c`, `DoorsG P hp g Lc F c`, `DoorsH s Y hp cov Lc F c`: both doors of a sub-proof,
   with the run equations that lead from the routine's own start (Lc, F, c) to the smallness test,
   each from where the one before ended, as the tied statements on the three routines hand them on
   (OnBytes/Tie/Pv/Lookup/Ends/FoTiedA.lean, OnBytes/Tie/Pv/Lookup/Ends/FoTiedG.lean,
     OnBytes/Tie/Pv/Lookup/Ends/FoTiedH.lean). The first door stands at the routine's own context c,
   and at the state with the slots laid: `F.fillL.slots P.ns`; `F.fillL.slots hp.ns`; `(({ trees :=
   F.trees } : Fork).fillL).slots hp.ns`.
 * `doors_A`, `doors_G`, `doors_H`: they hold on a run of the routine that returns from a context
   with `Clean`.
 * `slots_next`: the first free slot at the first door is that of the state before the slots were
   laid. `slots_nextH`: at the head's first door it is 0.

Every witness is the value of a run equation whose start is named. The shape is that of the record
that the run returned; that it is the plan's record is not said here.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedZ
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedA
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedG
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedH
import OnBytes.Tie.Pv.Lookup.Forest.FoPadAll
import OnBytes.Tie.Pv.Lookup.Ends.FoSiteOwn
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysTop

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- What the law at a lookup's place takes from the caller. -/
structure Door (calls : Array Call) (pub : Array Nat) (lid : ℕ) (Fk : Fork) (cx : Ctx)
    (g : Forest.Heard) (F' : Fork) (cx' : Ctx) : Prop where
  run : Forest.pad calls pub lid Fk cx = .ok ((g, F'), cx')
  shape : ShapeOf calls pub lid g.shape
  sized : Sized Fk
  clean : Clean cx

theorem door_of {calls : Array Call} {pub : Array Nat} {lid : ℕ} {Fk F' : Fork} {cx cx' : Ctx}
    {g : Forest.Heard} (hr : Forest.pad calls pub lid Fk cx = .ok ((g, F'), cx'))
    (hF : Sized Fk) (hc : Clean cx) : Door calls pub lid Fk cx g F' cx' :=
  ⟨hr, (hcOut2V Cb.Gl.E Reading.gl calls pub lid 0 Fk F' cx cx' g hr hF hc).1, hF, hc⟩

/-- The door of the digits inside a run of the smallness test's messages. -/
def DoorZ (tl : HTailF2) (L : LinkCtx) (F : Fork) (c : Ctx) (tl2 : HTailF2) (Lt : LinkCtx)
    (Gt : Fork) (c' : Ctx) : Prop :=
  ∃ (tl' : HTailF2) (c5 : Ctx) (F1 : Fork) (c1 : Ctx) (gz : Forest.Heard),
    tl.drawMatrixF F c = .ok ((tl', F), c5) ∧
    rootInH [tl.ix.ZZ, tl.ix.BZ] L F c5 = .ok ((((), Lt), F1), c1) ∧
    Door #[tl.z1.call, tl.z2.call] tl.f9.pub tl.lidb F1 c1 gz Gt c' ∧
    tl2.heard = some gz

theorem door_Z {tl tl2 : HTailF2} {L Lt : LinkCtx} {F Gt : Fork} {c c' : Ctx}
    (h : tl.transcriptF L F c = .ok (((tl2, Lt), Gt), c')) (hF : Sized F)
    (hd : c.ch.dry = false) : DoorZ tl L F c tl2 Lt Gt c' := by
  obtain ⟨tl', F1, c5, c1, gz, a1, a2, a3, a4, a5, _, a7⟩ := site_Z_own tl L F c _ h hF hd
  exact ⟨tl', c5, F1, c1, gz, a1, a2, door_of a3 a5 a7, a4⟩

theorem slots_next (F : Fork) (n : ℕ) : (F.fillL.slots n).next = F.next := rfl

theorem slots_nextH (F : Fork) (n : ℕ) :
    ((({ trees := F.trees } : Fork).fillL).slots n).next = 0 := rfl

/-- Attention's two doors. -/
def DoorsA (P : Attention.Plan) (Lc : LinkCtx) (F : Fork) (c : Ctx) : Prop :=
  ∃ (f : Attention.First) (t : Attention.Tables) (Fh : Fork) (ch : Ctx) (L2 : LinkCtx)
    (Ft : Fork) (ct cr : Ctx) (tl1 tl2 : HTailF2) (Lt : LinkCtx) (Gt : Fork) (cr' : Ctx)
    (Fq : Fork) (cq : Ctx),
    Door (P.S.calls.map (·.call)) P.fs.pub P.lid (F.fillL.slots P.ns) c f.g Fq cq ∧
    Attention.hear P (F.fillL.slots P.ns) c = .ok ((f, Fh), ch) ∧
    rootInH [P.iU3] Lc Fh ch = .ok ((((), L2), Ft), ct) ∧
    Attention.tables P.S P.mats P.nW f.g f.planes f.scores f.d f.x ct = .ok (t, cr) ∧
    ({ P.seam.tl with funClosed := false, foldDrawn := 0 } : HTailF2).closeFuns t.funs =
      some tl1 ∧
    tl1.transcriptF L2 Ft cr = .ok (((tl2, Lt), Gt), cr') ∧
    DoorZ tl1 L2 Ft cr tl2 Lt Gt cr'

theorem doors_A (P : Attention.Plan) (Lc : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((Unit × LinkCtx) × Fork) × Ctx) (h : Attention.run P Lc F c = .ok r) (hc : Clean c) :
    DoorsA P Lc F c := by
  obtain ⟨f, t, Fh, ch, L2, Ft, ct, cr, tl1, tl2, _, Lt, Gt, cr', _, _, _, _, _, _, _, _, _,
    h1, h2, h3, h4, h5, _⟩ := a_run_tied P Lc F c r h
  obtain ⟨Fq, cq, hp, _⟩ := a_hear_exact _ _ _ _ _ _ h1
  have s0 : Sized (F.fillL.slots P.ns) := sized_slots _ _
  have sT : Sized Ft := ((a_pass_T h1 h2).later s0).2
  have d1 := (stays_Attention_hear P _).out _ _ _ h1 hc.1
  have d2 := ((shutL_rootInH _).dry _ _).out _ _ _ h2 d1
  have d3 := (dry_tables _ _ _ _ _ _ _ _).out _ _ _ h3 d2
  exact ⟨f, t, Fh, ch, L2, Ft, ct, cr, tl1, tl2, Lt, Gt, cr', Fq, cq, door_of hp s0 hc,
    h1, h2, h3, h4, h5, door_Z h5 sT d3⟩

/-- The two doors of a group of layers. -/
def DoorsG (P : Layer.Pub) (hp : Layer.HPlan2) (g : ℕ) (Lc : LinkCtx) (F : Fork) (c : Ctx) :
    Prop :=
  ∃ (iU3 : ℕ) (fo : Forest.Heard) (Fl : Fork) (cl : Ctx) (o : Layer.Own) (Fo : Fork) (co : Ctx)
    (L8 : LinkCtx) (Fa : Fork) (ca : Ctx) (tl1 tl2 : HTailF2) (Lt : LinkCtx) (Gt : Fork)
    (cr : Ctx),
    Door P.y.cl P.y.fo.pub P.y.h.lidb (F.fillL.slots hp.ns) c fo Fl cl ∧
    hp.tl.ix.U.getD 2 none = some iU3 ∧
    Layer.hearLook P.y g (F.fillL.slots hp.ns) c = .ok ((fo, Fl), cl) ∧
    Layer.hearOwn P hp g fo Fl cl = .ok ((o, Fo), co) ∧
    rootInH [iU3] Lc Fo co = .ok ((((), L8), Fa), ca) ∧
    hp.tl.closeFuns o.funs = some tl1 ∧
    tl1.transcriptF L8 Fa ca = .ok (((tl2, Lt), Gt), cr) ∧
    DoorZ tl1 L8 Fa ca tl2 Lt Gt cr

theorem doors_G (P : Layer.Pub) (hp : Layer.HPlan2) (g : ℕ) (Lc : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((WsForkOut × LinkCtx) × Fork) × Ctx) (h : Layer.runForkHidG2 P hp g Lc F c = .ok r)
    (hc : Clean c) : DoorsG P hp g Lc F c := by
  obtain ⟨iU3, fo, Fl, cl, o, Fo, co, L8, Fa, ca, tl1, tl2, _, Lt, Gt, cr, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, h0, h1, h2, h3, h4, h5, _⟩ :=
    g_run_tied P hp g Lc F c r h
  have s0 : Sized (F.fillL.slots hp.ns) := sized_slots _ _
  have sT : Sized Fa := ((g_pass_T h1 h2 h3).later s0).2
  have d1 := (stays_Model_Layer_hearLook _ _ _).out _ _ _ h1 hc.1
  have d2 := (stays_Model_Layer_hearOwn _ _ _ _ _).out _ _ _ h2 d1
  have d3 := ((shutL_rootInH _).dry _ _).out _ _ _ h3 d2
  exact ⟨iU3, fo, Fl, cl, o, Fo, co, L8, Fa, ca, tl1, tl2, Lt, Gt, cr,
    door_of (g_look_exact _ _ _ _ _ _ _ h1) s0 hc, h0, h1, h2, h3, h4, h5, door_Z h5 sT d3⟩

/-- The output head's two doors. -/
def DoorsH (s : Head.Shape) (Y : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (Lc : LinkCtx) (F : Fork) (c : Ctx) : Prop :=
  ∃ (x : Head.Heard) (t : Head.Tables) (iU3 : ℕ) (Fh : Fork) (ch : Ctx) (L9 : LinkCtx)
    (Fa : Fork) (ca : Ctx) (Ga : Fork) (ca' : Ctx) (tl1 tl2 : HTailF2) (Lt : LinkCtx)
    (Gt : Fork) (cr : Ctx) (Fq : Fork) (cq : Ctx),
    Door Y.cl Y.fs.pub s.LIDB ((({ trees := F.trees } : Fork).fillL).slots hp.ns) c x.g1 Fq cq ∧
    hp.tl.ix.U.getD 2 none = some iU3 ∧
    Head.hear s Y hp cov Lc.check.plain ({ trees := F.trees } : Fork).fillL c =
      .ok ((x, Fh), ch) ∧
    rootInH [iU3] Lc Fh ch = .ok ((((), L9), Fa), ca) ∧
    Head.tablesOf s Y hp cov x Fa ca = .ok ((t, Ga), ca') ∧
    hp.tl.closeFuns t.funs = some tl1 ∧
    tl1.transcriptF L9 Ga ca' = .ok (((tl2, Lt), Gt), cr) ∧
    DoorZ tl1 L9 Ga ca' tl2 Lt Gt cr

theorem doors_H (s : Head.Shape) (Y : Head.HL) (b : Head.Border) (hp : Head.HPlanH2)
    (O : Head.Owner) (cov : Head.Covered) (wsLay : WsLay) (Lc : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((WsForkOut × LinkCtx) × Fork) × Ctx)
    (h : Head.runForkHidH2 s Y b hp O cov wsLay Lc F c = .ok r) (hc : Clean c) :
    DoorsH s Y hp cov Lc F c := by
  obtain ⟨x, t, iU3, Fh, ch, L9, Fa, ca, Ga, ca', tl1, tl2, _, Lt, Gt, cr, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, h0, h1, h2, h3, h4, h5, _⟩ := h_run_tied s Y b hp O cov wsLay Lc F c r h
  obtain ⟨Fq, cq, hq, pq⟩ := h_hear_exact _ _ _ _ _ _ _ _ _ _ h1
  have s0 : Sized ((({ trees := F.trees } : Fork).fillL).slots hp.ns) := sized_slots _ _
  have sq : Sized Fq := (Keeps.pad _ _ _ _ _ _ _ _ hq s0).2
  have sT : Sized Ga := ((h_pass_T pq h2 h3).later sq).2
  have d1 := (stays_hearH _ _ _ _ _ _).out _ _ _ h1 hc.1
  have d2 := ((shutL_rootInH _).dry _ _).out _ _ _ h2 d1
  have d3 := (stays_Model_Head_tablesOf _ _ _ _ _ _).out _ _ _ h3 d2
  exact ⟨x, t, iU3, Fh, ch, L9, Fa, ca, Ga, ca', tl1, tl2, Lt, Gt, cr, Fq, cq,
    door_of hq s0 hc, h0, h1, h2, h3, h4, h5, door_Z h5 sT d3⟩

end Fo
