-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Planes.lean: the forms that an attention segment hands the lookup for
its three claims on the planes of the counts (`readersOfO`, Johnson/Desc/First/Att/SeatO.lean):
CONDITIONAL, under premises on the plan and the state that are not shown here: they are there, and
in a world that reads the array of the segment's tables as the stated function of the committed
cells each is worth the sum, over the rows of the planes' matrix, of weight times cell.

The three tables. The last three tables that the verifier's text makes
(Johnson/Desc/First/Att/TablesP.lean) lie on the planes' matrix, number NAs + 2 of the segment's
list: two under the lookup's weights for the two bits, one under its weights for the pin. A reader
hands out the form that names one entry of one of them: the entry of a column.

Main names:
  `ReadsStated A s Dt cN W`: a NAMED PREMISE on a world W: each entry of the array of the tables
    is the stated function `uAtt A (funsAt A)` (Johnson/Desc/First/Att/K05WorldTieAt.lean) at the
    state s and the committed data Dt.
  `readsStated_own`: the premise at the world in which the library's sentence on forms that name
    a later array evaluates them (`worldOwn` at `St.at1`, Johnson/Desc/Sound/FormsQ.lean), under
    three premises: the stated function's law at the state; the open link names the array of the
    tables; that array is of the segment's second sending.
  `attAt_stated`: in such a world every table of the verifier's list is true of the matrices read
    off the data (`AttAt`, Johnson/Road/Rows/AttRead.lean): by `uAtt_is_sum`.
  `planeSum`: the sum over the rows of the planes' matrix of weight times cell, at a column.
  `planes_say`: **what the readers' forms are worth in such a world**: for a bit e and a column:
    `planeSum` under the bit's weights; for the pin: under the pin's weights.
  `readers_return`: the two readers are there, at a state in which the points and the tables are
    made and the array of the tables is in the ledger.
  `readers_all`: each reader returns a form at every column of the planes' matrix.

Limits. All are conditional; who is meant to pay each premise stands at the statement. What the
lookup's three vectors of weights are is not said here: they are taken as the lookup hands them in.
The cells are those read off the committed data (`matsAt`): that they are the honest witness's is
not said here. That the committed array holds these entries, and what the lookup's claims make of
the forms, are not in this file.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05StatedArm
import Johnson.Desc.First.Att.K05HostPlanesPlan
import Johnson.Desc.First.Att.K05ReadersRet
import Johnson.Desc.First.Att.Claims.PlanesWorth
import Johnson.Desc.First.Att.Claims.FunsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open OnBytes.Road (Mats)
open OnBytes.Road.Rows (AttAt MatsFit)
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ matsOfData Stated second worldOwn)

/-- The matrices as they are read off the committed data at a state. -/
noncomputable def matsAt (A : Attention.Plan) (s : First.S) (Dt : Bound GQ) : Mats GQ :=
  matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[]) Dt

/-- A NAMED PREMISE on a world: each entry of the array of the segment's tables is the stated
function of the committed cells, at the state s and the data Dt. Whoever lays the world pays it. -/
def ReadsStated (A : Attention.Plan) (s : First.S) (Dt : Bound GQ) (cN : ℕ × String)
    (W : World GQ) : Prop :=
  ∀ r i, W.entry A.iU3 r i = P.uAtt A (K5Law.funsAt A) s Dt cN r i

/-- **The named premise at the world in which the library's sentence on forms that name a later
array evaluates them.** Conditional: hSt: the letter St reads the array of the tables as the stated
function at s (paid by `hSt_of_arm`, Johnson/Desc/First/Att/K05StatedArm.lean); hb: the open link
names the array of the tables, as b; h2: that array is of the segment's second sending. The last
two are facts on the open link's frame; no lemma that pays them is called here. -/
theorem readsStated_own {St : Stated} {A : Attention.Plan} {s : First.S}
    (hSt : P.StatedAtt St A (K5Law.funsAt A) s) {a : VerifiableInference.Desc.K9.Part}
    {b : ℕ × String} (hb : a.L.arrayOf[A.iU3]? = some b) (h2 : second s b = true)
    (late : List (ℕ × E × E)) (Dt : Bound GQ) :
    ReadsStated A s Dt b (worldOwn a late (St.at1 s Dt)) := by
  intro r i
  show (match a.L.arrayOf[A.iU3]? with
    | some b => (St.at1 s Dt).cell b.1 b.2 r i
    | none => 0) = _
  rw [hb]
  exact hSt.cell Dt b r i h2

/-- **In a world that reads the array as the stated function every table of the verifier's list
is true of the matrices read off the data.** Conditional: hin: the claims' reading at the state
returns, and the number of columns that it reads off the ledger is the planned one (the equation
fixes both); gL: free: of what the lookup returned no clause of the conclusion's tables reads
anything; hid, hmf: two facts on the plan (paid by
`K5Law.ofPlan_shape` and `K5Law.ofPlan_matsFit` at a plan that the planner returned); hW. -/
theorem attAt_stated (A : Attention.Plan) {s : First.S} {i : P.Runs.In}
    (hin : P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) s = some (i, P.plannedK A)) {lid : ℕ}
    {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (hid : Attention.shapeHid lid cf = .ok (A.S, fs)) (hmf : MatsFit A.S A.seam.tl)
    (gL : Forest.Heard) {W : World GQ} {Dt : Bound GQ} {cN : ℕ × String}
    (hW : ReadsStated A s Dt cN W) :
    AttAt Reading.gl W A.seam.tl (P.plannedK A) (matsAt A s Dt) (K5Law.oldOf A.S gL i) lid cf
      fs := by
  refine ⟨OnBytes.Road.gl_numerals, hid, hmf, fun Fn hFn c sg pos hpos => ?_⟩
  have eu : i.iU3 = A.iU3 := (K5Law.inOf_some _ _ _ _ _ hin).2.1
  have hF : Fn ∈ K5Law.funsAt A s := by
    unfold K5Law.funsAt
    rw [hin]
    exact hFn
  show W.entry i.iU3 _ _ = _
  rw [eu, hW]
  exact P.uAtt_is_sum A s Dt cN hF hpos

/-- The sum over the rows of the planes' matrix of weight times cell, at a column. -/
noncomputable def planeSum (Sh : Attention.Shape) (M : Mats GQ) (phi : Array E) (col : ℕ) : GQ :=
  ∑ j ∈ Finset.range (2 ^ Sh.cf.lmb), Reading.gl.val (phi.getD j zeroE) * M (Sh.cf.NAs + 2) j col

/-- **What the forms for the planes are worth where the array is read as the stated function.**
Conditional:
  hA: the plan is one that the planner returned, but for one field (paid by
    `K5Law.public_ofPlan` at every attention plan of the public parameters);
  hp: six numbers of the shape are not 0 (a test of the block's guard on the plan);
  hr: the readers are there (`readers_return`);
  hK: the array of the tables has the planned number of columns in the state's ledger: a fact on
    the ledger's tree, true where the link's frame lays the plan's trees; no lemma that pays it is
    called here;
  hW: `ReadsStated`.
lk: what the lookup hands in, as the state holds it. e: every number but 0 reads the second bit's
weights, as the reader's text has it. In the proof a blank stands for what the lookup returned in
the library's older structure of what was heard: the tables' truth reads nothing of it. -/
theorem planes_say (A : Attention.Plan) (hA : K5Law.OfPlan A) (hp : K5Law.PosG (P.geoOf A.S))
    {s : First.S} {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} (hr : P.readersOfO A s = some r)
    (hK : (P.seatCO (P.parCOf A)).cols s = some (P.plannedK A)) {W : World GQ} {Dt : Bound GQ}
    {cN : ℕ × String} (hW : ReadsStated A s Dt cN W) :
    ∃ lk, (P.seatCO (P.parCOf A)).look s = some lk ∧
      (∀ e col f, r.1 e col = some f → f.value Reading.gl W =
        planeSum A.S (matsAt A s Dt) (if e == 0 then lk.phiB0 else lk.phiB1) col) ∧
      ∀ col f, r.2 col = some f →
        f.value Reading.gl W = planeSum A.S (matsAt A s Dt) lk.phiP col := by
  obtain ⟨lid, cf, hid⟩ := K5Law.ofPlan_shape hA
  obtain ⟨i, K, lk, hin, hlk, H⟩ := K5Law.planes_worth (Kf := GQ) (tl := A.seam.tl) (S := A.S)
    (gL := default) (lid := lid) (cf := cf) (fs := A.fs) (P.seatCO (P.parCOf A)) (P.parCOf A) s rfl
    rfl hp hr
  obtain rfl : K = P.plannedK A :=
    Option.some.inj ((K5Law.inOf_some _ _ _ _ _ hin).2.2.2.2.1.symm.trans hK)
  obtain ⟨h1, h2⟩ := H Reading.gl W (matsAt A s Dt)
    (attAt_stated A hin hid (K5Law.ofPlan_matsFit hA) default hW)
  have one : (A.seam.tl.mats.getD (A.S.cf.NAs + 2) {}).m / 2 ^ A.S.cf.lmb = 1 := by
    rw [K5Law.ofPlan_rows hA]
    exact Nat.div_self (Nat.two_pow_pos _)
  rw [one] at h1 h2
  simp only [Nat.mod_one, Nat.zero_mul, Nat.zero_add, Nat.div_one] at h1 h2
  exact ⟨lk, hlk, h1, h2⟩

/-- **The two readers are there.** Conditional: hs, hg, h5: an attention segment is open, what the
lookup returned and what the segment's own rounds heard are laid; hl, hpt, ht: the rows that the
sumchecks leave, the points and the tables are made (paid as in
Johnson/Desc/K5/Honest/Law/ReadsReturn.lean); hT: the array of the tables is in the ledger. -/
theorem readers_return (A : Attention.Plan) {s : First.S} {a : First.AttOwn} {gL : Forest.Heard}
    {hh : P.Heard} {l : P.Left} {p : P.Pts} {t : P.TablesP} {T : HTree} (hs : s.here = .att a)
    (hg : a.g = some gL) (h5 : a.heard5 = some hh)
    (hl : P.LeftIs (P.parCOf A).geo gL.zk hh a.F l)
    (hpt : P.pointsOf (P.parCOf A).geo gL.zk hh l = some p)
    (ht : P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
      (P.lookOfO (P.parCOf A).geo.lmb gL) p = some t)
    (hT : a.F.trees[(P.parCOf A).iU3]? = some T) :
    P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) s =
        some ({ g := (P.parCOf A).geo, p := p, t := t, zk := gL.zk, iU3 := (P.parCOf A).iU3 },
          T.K) ∧
      ∃ r, P.readersOfO A s = some r := by
  have hin : P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) s =
      some ({ g := (P.parCOf A).geo, p := p, t := t, zk := gL.zk, iU3 := (P.parCOf A).iU3 },
        T.K) := by
    rw [K5Law.inOf_isAt hs, hg, h5]
    exact K5Law.inAt_of_is hl hpt ht hT
  refine ⟨hin, ?_⟩
  unfold P.readersOfO P.readersOfK
  rw [hin]
  exact ⟨_, rfl⟩

/-- **Each reader returns a form at every column of the planes' matrix.** Conditional: hA, hp as
in `planes_say`; hin: the claims' reading at the state returns; hr: the readers; hwide: the array
of the tables has at least the planned length of columns in the ledger. -/
theorem readers_all (A : Attention.Plan) (hA : K5Law.OfPlan A) (hp : K5Law.PosG (P.geoOf A.S))
    {s : First.S} {i : P.Runs.In} {K : ℕ}
    (hin : P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) s = some (i, K))
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} (hr : P.readersOfO A s = some r)
    (hwide : A.nW ≤ K) :
    (∀ e col, col < (A.seam.tl.mats.getD (A.S.cf.NAs + 2) {}).k → ∃ f, r.1 e col = some f) ∧
      ∀ col, col < (A.seam.tl.mats.getD (A.S.cf.NAs + 2) {}).k → ∃ f, r.2 col = some f := by
  obtain ⟨eg, _, _, _, _, lk, _, ht⟩ := K5Law.inOf_some _ _ _ _ _ hin
  have ht' : P.tablesP i.g (K5Law.matsOf A.seam.tl.mats) A.nW lk i.p = some i.t := by
    rw [eg]
    exact ht
  refine P.readers_ret_plan (S := A.S) (tl := A.seam.tl) hin hr (K5Law.len_in ht') hwide eg ht'
    (by rw [eg]; exact hp) ?_
  rw [K5Law.ofPlan_rows hA, Nat.div_self (Nat.two_pow_pos _), Nat.mul_one]

end H2K5.Honest

#print axioms H2K5.Honest.readsStated_own
#print axioms H2K5.Honest.attAt_stated
#print axioms H2K5.Honest.planes_say
#print axioms H2K5.Honest.readers_return
#print axioms H2K5.Honest.readers_all
