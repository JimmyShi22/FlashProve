-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadsReturn.lean: CONDITIONAL: the quiet step behind an attention
segment's sending of its reads (`readsAtSO`, Johnson/Desc/First/Att/ReadsO.lean) RETURNS at a state
in which the segment's own rounds have laid what they heard, the lookup has laid what it returned,
the list of tables is open, and the points and the tables can be made.

Main names:
  `order_any`: the guard of order reads neither the list of tables nor the mark "closed".
  `reads_return_of`: from the returns of the points' and the tables' functions, outright: the
    step says yes and the state behind it is written out.
  `reads_return_ret`: the two returns taken from the library's structure of the gathering's
    returns (`Returns`, Johnson/Desc/First/Att/K05GatheredZero.lean).
  `reads_return`: **the two returns paid by the library's law** `returns_at_lk`
    (Johnson/Desc/First/Att/K05ReturnsLk.lean), under that law's own premises at the plan's numbers
    and the state's values.

TWO NAMED PREMISES on the smallness test's own texts, in all three: hshp: there is one shape a
matrix (`tl.shp.size = tl.NM`); hord: the guard of order says yes. In `reads_return_of` hord stands
at the closed list; in the other two at the state's own part of the smallness test, which is the
same by `order_any`. Whoever keeps the smallness test's part of the state pays them.

Limits. All three are conditional, and no premise is shown to be met here. `reads_return` takes
over the whole list of premises of `returns_at_lk`: among them that the key points are the
lookup's (`K3Pts`), that what was heard was said at the state's ledger (`Said`, `Sized`), and that
the claims' dry run on the plan says yes (`claimsOk`).
THE STATE s IS THE ONE IN FRONT OF THE QUIET STEP. In the verifier's chain that step is joined
behind the sending of the reads, so between the block of the segment's own rounds and s stands that
sending. What the block of the own rounds lays (what was heard, the ledger with `Said` and `Sized`)
and what stood in front of it (what the lookup returned, the open list) hold at s only if the
sending leaves these fields: that is not shown here; `k1_leaves`
(Johnson/Desc/K5/Honest/Law/ReadsAfter.lean) shows what the sending's yes leaves.
The law that is called fixes numbers: four lookup calls, two messages of planes. A plan with other
numbers is not reached. It also takes typed parameters Pp with the plan's dimensions as data: the
theorem says nothing unless there are such; no term of that type is named here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.ReadsStep
import Johnson.Desc.First.Att.K05ReturnsLk
import Johnson.Desc.First.Att.Claims.LeftIsBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
  Inst.Model.AttSeg
open VerifiableInference.Desc.First (S AttOwn K8.Order.orderOk)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (UnitG UnitsAll K3Pts Returns claimsOk Said Lists
  returns_at_lk)
open VerifiableInference.Desc.Part
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Road.L5 (dimOf)

/-- The guard of order reads neither the list of tables nor the mark "closed". -/
theorem order_any (tl : HTailF2) (L : LinkCtx) (St : Statement) (b : Bool) (funs : Array HFun) :
    K8.Order.orderOk { tl with funClosed := b, funs := funs } L St = K8.Order.orderOk tl L St :=
  rfl

/-- The state behind the quiet step's yes: the tables laid, the list closed over them. -/
def behindReads (s : S) (a : AttOwn) (t : P.TablesP) : S :=
  { s with here := .att { a with
      t := some (tabsBack t), tl := { a.tl with funClosed := true, funs := (tabsBack t).funs } } }

/-- **The quiet step returns where the points' and the tables' functions do.** Conditional:
hs, h5, hg, ho: an attention segment is open, what its own rounds heard and what the lookup
returned are laid, the list of tables is open (whoever carries the state through the blocks in
front pays the four); hp, ht: the two returns; hshp, hord: the two named premises on the smallness
test's texts. -/
theorem reads_return_of (A : Attention.Plan) {s : S} {a : AttOwn} {hh : P.Heard}
    {g : Forest.Heard} {p : P.Pts} {t : P.TablesP} (hs : s.here = .att a)
    (h5 : a.heard5 = some hh) (hg : a.g = some g) (ho : a.tl.funClosed = false)
    (hp : P.ptsFrom (P.parCOf A).geo g.zk hh a.F = some p)
    (ht : P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
      (P.lookOfO (P.parCOf A).geo.lmb g) p = some t)
    (hshp : a.tl.shp.size = a.tl.NM)
    (hord : K8.Order.orderOk { a.tl with funClosed := true, funs := (tabsBack t).funs } a.L s.st =
      true) :
    readsAtSO A s = .ok (behindReads s a t) := by
  refine (readsAtSO_iff A s _).2 ⟨a, hh, g, p, t, hs, ?_, hg, ho, hp, ht, hshp, hord, rfl⟩
  unfold S.heard5?
  rw [hs]
  exact h5

/-- The same with the two returns taken from the library's structure of the gathering's returns,
at the plan's shape, the plan's smallness test's numbers, the state's ledger and what the state
holds of the lookup. -/
theorem reads_return_ret (A : Attention.Plan) {s : S} {a : AttOwn} {hh : P.Heard}
    {g : Forest.Heard} (hs : s.here = .att a) (h5 : a.heard5 = some hh) (hg : a.g = some g)
    (ho : a.tl.funClosed = false) {zx : Array E} {zk : Array (Array E)} {l : P.Left}
    {i : P.Runs.In} {Kc : ℕ} {l₁ l₂ : List Aff} {jn : P.Runs.JoinsP} {k3 : P.Runs.PadIn}
    {kf : Array Aff} {Fj : Fork} {tj : OnBytes.K.Kc.Tape} {xj : Aff × Fork × OnBytes.K.Kc.Tape}
    (R : Returns A.S zx zk a.F hh l A g i Kc l₁ l₂ jn k3 kf Fj tj xj A.seam.tl A.nW
      (P.lookOfO (P.parCOf A).geo.lmb g))
    (hshp : a.tl.shp.size = a.tl.NM) (hord : K8.Order.orderOk a.tl a.L s.st = true) :
    readsAtSO A s = .ok (behindReads s a i.t) := by
  have hp : P.pointsOf (P.geoOf A.S) zk hh l = some i.p := by
    rw [← R.geo]
    exact R.points
  have ht : P.tablesP (P.geoOf A.S) (K5Law.matsOf A.seam.tl.mats) A.nW
      (P.lookOfO (P.parCOf A).geo.lmb g) i.p = some i.t := by
    rw [← R.geo]
    exact R.tables
  refine reads_return_of A hs h5 hg ho ?_ ht hshp ((order_any _ _ _ _ _).trans hord)
  rw [R.zkL]
  exact K5Law.ptsFrom_of_is R.left hp

section At
variable {fs : Model.Forest.Shape} {lid : ℕ} {cf : Attention.Cfg} {r1 r2 u1 u2 wl ix wh : UnitG}
variable {K M X : Type} [Field K] [Fintype K]

/-- **The quiet step returns at a state behind the segment's own rounds.** Conditional:
  hs, h5, hg, ho: as in `reads_return_of`;
  hid, PL, U, hmf, hd, hlm, hN: on the plan alone (the plan's maker pays them; for hd the library
    has `claims_of_atO`, Johnson/Desc/First/Att/K05PublicB.lean, from the block's own test on the
    plan);
  H3, hz4, hsh, he, hpl: on what the lookup returned (the lookup's side pays them);
  Pp, hD, hn, b2, b3: what was heard was said at the state's ledger. The yes of the block of the
    segment's own rounds gives that at the state behind that block; at s it holds only if the
    sending of the reads, which stands between, leaves the ledger and what was heard;
  hshp, hord: the two named premises on the smallness test's texts. -/
theorem reads_return (A : Attention.Plan) {s : S} {a : AttOwn} {hh : P.Heard} {g : Forest.Heard}
    (hs : s.here = .att a) (h5 : a.heard5 = some hh) (hg : a.g = some g)
    (ho : a.tl.funClosed = false)
    (hid : Attention.shapeHid lid cf = Except.ok (A.S, fs)) (PL : K5Law.PlanLaw cf A.S fs)
    (U : UnitsAll A.S fs r1 r2 u1 u2 wl ix wh) (hmf : OnBytes.Road.Rows.MatsFit A.S A.seam.tl)
    {Kc : ℕ} {k3 : P.Runs.PadIn} {nzx : ℕ}
    (hd : claimsOk ⟨P.geoOf A.S, A.iU3, A.nW, K5Law.matsOf A.seam.tl.mats⟩ Kc k3 true nzx = true)
    {zy : Array E} {z : ℕ → Cb.Gl.E} (H3 : K3Pts fs g.zx zy g.zk z) (hz4 : g.zk.size = 4)
    (hlm : ∀ f : Fam, Cb.Pv.Att.End.IsPlane f → A.S.cf.lmS ≤ f.l (dimOf A.S))
    (Pp : OwnPar K M X) (hD : Pp.D = dimOf A.S) (hn : Pp.npl = 2) (rows : ℕ)
    {L : Lists} (b2 : Said (recOf Pp rows) hh a.F L) (b3 : OnBytes.Model.Road.Sized a.F)
    (hN : A.NC = A.S.calls.size) (hsh : g.shape.calls.size = 4) (he : g.e.size = 4)
    (hpl : VerifiableInference.Desc.First.Look.planesOk g.shape (P.parCOf A).geo.lmb = true)
    (hshp : a.tl.shp.size = a.tl.NM) (hord : K8.Order.orderOk a.tl a.L s.st = true) :
    ∃ t, readsAtSO A s = .ok (behindReads s a t) := by
  obtain ⟨l, i, l₁, l₂, jn, kf, xj, R⟩ := returns_at_lk hid PL U A.seam.tl hmf A.iU3 A.nW hd H3 hz4
    hlm Pp hD hn rows b2 b3 A hN rfl g rfl hsh he a.F [] (P.lookOfO (P.parCOf A).geo.lmb g) rfl hpl
  exact ⟨i.t, reads_return_ret A hs h5 hg ho R hshp hord⟩

end At

end H2K5.Honest

#print axioms H2K5.Honest.order_any
#print axioms H2K5.Honest.reads_return_of
#print axioms H2K5.Honest.reads_return_ret
#print axioms H2K5.Honest.reads_return
