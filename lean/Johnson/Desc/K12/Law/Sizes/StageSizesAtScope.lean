-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/StageSizesAtScope.lean: at every three public files in the scope of the
goals, the sized stages of three of a proof file's four proximity tests in what the program computes
are three typed lists, and the setting is the typed setting.

The scope (VerifierAndGoals.InScope, Ladder.lean) fixes the layout file and the parameter file but for eight
numbers, and leaves the scale file free. The stages of the folded row's test, of Omega's test and of
the request's own test read none of these: Params.proofSized sizes them by Params.linSized at the
parameter file's first 32 lines, the table's sizes, the rows of the committed matrix and the number
of rows that a request's sub-proofs leave on the table. Here that is proved along the program's own
text, in the way of Johnson/Goal/PlanValues/ScopeAtPlan.lean and KeyFullAtScope.lean for a key's
sizes; the sizing itself is evaluated turn by turn in the four files Turns...Full.lean of this
folder.
Main names:
  `linFinish_stages`: what linSized's closing text returns holds the three lists that it was given.
  `three_stages`: whatever linSized returns at the typed lines is sized as the three typed lists.
  `wsLay_of_polLayout`, `wsLay_at_policy`, `m0_full`: the layout of the committed matrix in the
    public part is that of the ten written sizes; it has 3076096 rows.
  `AtFull M`: ten equations of fields of what the planner has made with closed terms.
  `PubFull X`: four facts on a public part: all that the sizing reads of it. `pubFull_of_layout`: a
    public part has them if its scan and layers' layout are polLayout's at a parameter file in scope
    and its layout of the committed matrix is wsLayOf's of these: no maker is named.
    `public_at_scope`: what publicOf returns at files in scope has them.
  `batch_of_public`, `atFull_of_public`: THE STATEMENT, from `PubFull X` and configure's yes: no
    planner's name, no maker of the public part, no scope occur in it.
  `batch_of_configure`, `atFull_of_configure`: the same at what publicOf returns at files in scope.
  `atFull_at_scope`, `atFull_at_made`: the same from `planned` and from `madeOf`; `batch_at_scope`,
    `three_at_scope`, `three_at_made`, `sets_at_scope`: its parts.
Limits: one direction: from a program that returns. That Model.Verify.planned or madeOf returns at
any file in scope is not shown: no member of the two premises together is exhibited in Lean. THE
FOURTH LIST, of the first chain's last test, is not here. Of a place of the kind K12 only the stages
and the setting are pinned: its rows, its work, its first and free trees, its index, its oracle
messages, its answers and what stands before it are not spoken of. That a description of the
protocol takes its numbers from a call of configure of that form is not said. Nothing on soundness.
Nothing on hiding.
-/
import Johnson.Goal.PlanValues.KeyPlansAtScope
import Johnson.Goal.Meaning.PlanShapes
import OnBytes.Params.Fit.SizedParts
import Johnson.Desc.K12.Law.Sizes.TurnsThreeFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Sizes
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open H2K.Member Lk6.AtPlan

/-! ## 1. The sizing at the typed lines -/

/-- The setting of the written lines is the typed setting. -/
theorem set_eq : recordSet = setAt := by decide +kernel

/-- What linSized's closing text returns holds the three lists of stages that it was given. -/
theorem linFinish_stages {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x y z : Sizing} {stU stO stW : List StageSize} {r : LinSized}
    (h : linFinish s L T codes x y z stU stO stW = some (r, c)) :
    r.folded.stages = stU ∧ r.omega.stages = stO ∧ r.own.stages = stW := by
  unfold linFinish at h
  dsimp only at h
  split at h
  · obtain rfl := (Prod.mk.inj (Option.some.inj h)).1
    exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- The folded row and Omega have groups of their own at the typed lines. -/
theorem split_full : linSplit prLin = true := by decide +kernel

/-- **Whatever linSized returns at the typed lines, the written table and any codes has the three
typed lists of stages.** -/
theorem three_stages {codes c : Codes} {x : LinSized}
    (h : linSized recordSet prLin recordTable codes = some (x, c)) :
    x.folded.stages = szUFull ∧ x.omega.stages = szOFull ∧ x.own.stages = szWFull := by
  obtain ⟨X, Y, Z, stU, stO, stW, hT, hU, hO, hW, hF⟩ := linSized_named h
  rw [if_pos split_full] at hO
  have e0 := Option.some.inj (hT.symm.trans prTurns)
  obtain ⟨rfl, e1⟩ := Prod.mk.inj e0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  obtain rfl : stU = szUFull := Option.some.inj (hU.symm.trans U_stages)
  obtain rfl : stO = szOFull := Option.some.inj (hO.symm.trans O_stages)
  obtain rfl : stW = szWFull := Option.some.inj (hW.symm.trans W_stages)
  exact linFinish_stages hF

/-! ## 2. The two numbers that the sizing takes from the sub-proofs -/

/-- The rows of the committed matrix, by the planner's step. -/
def m0Of (l : Lines) (w : WsShape) (p3 : Bool) : Option Nat :=
  match wsLayOf w p3 l.blockLog with
  | .error _ => none
  | .ok Y => some Y.m0

set_option maxRecDepth 1000000 in
theorem m0Of_full : m0Of recordLines wsFull true = some 3076096 := by decide +kernel

/-- The layout of the ten written sizes has 3076096 rows. -/
theorem m0_full {Y : WsLay} (hY : wsLayOf wsFull true recordLines.blockLog = .ok Y) :
    Y.m0 = 3076096 := by
  have h := m0Of_full
  unfold m0Of at h
  rw [hY] at h
  exact Option.some.inj h

/-- At the parameter file at any values of the eight free numbers: the 32 lines of the scan are the
written lines, and the layout of the committed matrix that is made of the scan and the layers'
layout is that of the ten written sizes. -/
theorem wsLay_of_polLayout {v : VerifierAndGoals.FreeLines} {P : PolScan} {y : Layer.Lay} {W : WsLay}
    (hy : polLayout (VerifierAndGoals.policyFile v) = .ok (P, y))
    (hw : wsLayOf (weightShape P y) y.h.p3 P.lkW = .ok W) :
    P.frame = recordLines ∧ wsLayOf wsFull true recordLines.blockLog = .ok W := by
  have hS := polLayout_scan hy
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, bD⟩ := scan_sizes hS
  have hf := scan_frame hS
  obtain ⟨c1, c2, c3⟩ := layout_sizes (polLayout_layout hy)
  have hq : y.dq = 5120 := by
    rw [c2]
    show P.h.H * P.h.dh = 5120
    rw [b3, b5]
  have hkv : y.dkv = 1024 := by
    rw [c3]
    show P.h.Gk * P.h.dh = 1024
    rw [b4, b5]
  have h3 : y.h.p3 = true := by
    rw [c1]
    show (P.h.prof == 3 || (P.h.prof == 4 && decide (0 < P.h.NE))) = true
    rw [b0, b8]
    rfl
  have hws : weightShape P y = wsFull := by
    unfold weightShape wsFull
    simp only [bD, b1, b2, b5, hkv, hq, b6, b7, b8, b9]
  have hlk : P.lkW = recordLines.blockLog := by
    show P.frame.blockLog = _
    rw [hf]
  rw [hws, h3, hlk] at hw
  exact ⟨hf, hw⟩

/-- The same of what publicOf returns there. -/
theorem wsLay_at_policy {v : VerifierAndGoals.FreeLines} {KL : ByteArray} {layout : Option ByteArray}
    {X : Public} (hX : publicOf (VerifierAndGoals.policyFile v) KL layout = .ok X) :
    X.P.frame = recordLines ∧ wsLayOf wsFull true recordLines.blockLog = .ok X.layers.wsLay := by
  obtain ⟨y, hy, hw⟩ := publicOf_wsLay hX
  exact wsLay_of_polLayout hy hw

/-- In scope the goals' reader returns. -/
theorem inScope_readFiles {Z : VerifierAndGoals.PublicFiles} (h : VerifierAndGoals.InScope Z = true) :
    ∃ pp, VerifierAndGoals.readFiles Z = .ok pp := by
  unfold VerifierAndGoals.InScope at h
  rw [Bool.and_eq_true] at h
  have h2 := h.2
  split at h2
  · rename_i pp hpp
    exact ⟨pp, hpp⟩
  · cases h2

/-- The mask rows of the request's mask message at 13 rows on the table. -/
theorem maskRows_full : Send.maskRowsFor
    (13 + (if 1 < 13 then Batt.masksOf recordLines.blockLog else 0))
    (2 ^ recordLines.own.maskLogL) recordLines.answers = 1 := by decide +kernel

/-! ## 3. From configure's yes -/

/-- What linSized's closing text returns has these fields of the shape, and the lines. -/
theorem linFinish_shape {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x y z : Sizing} {stU stO stW : List StageSize} {r : LinSized}
    (h : linFinish s L T codes x y z stU stO stW = some (r, c)) :
    r.shape.fold.index = indexShapeOf s T ∧ r.shape.fold.columns = linColumnsOf s L T ∧
      r.shape.masksAhead = true ∧ r.shape.choice = ⟨true⟩ := by
  unfold linFinish at h
  dsimp only at h
  split at h
  · obtain rfl := (Prod.mk.inj (Option.some.inj h)).1
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

/-- **What the planner has made is sized as at the full size**: ten equations of fields of M with
closed terms: the two settings, the stages of three tests, that the test on the table is no one-time
test, and four fields of its shape. -/
structure AtFull (M : Configured) : Prop where
  /-- read for a place's work, rows and answers -/
  set : M.sized.set = setAt
  /-- read for the radii -/
  setP : M.sized.proof.set = setAt
  /-- read for the stages and radii of the folded row's place -/
  U : M.sized.proof.batch.folded.stages = szUFull
  /-- of Omega's place -/
  O : M.sized.proof.batch.omega.stages = szOFull
  /-- of the place of the request's own test -/
  W : M.sized.proof.batch.own.stages = szWFull
  /-- read for the scope under which a place's work is taken -/
  later : M.sized.proof.batch.lines.oneTime = false
  /-- read, with the next, for the rows of the folded row's place -/
  index : M.sized.proof.batch.shape.fold.index = indexShapeOf recordSet recordTable
  columns : M.sized.proof.batch.shape.fold.columns = linColumnsOf recordSet prLin recordTable
  /-- read for the own mask of two places -/
  ahead : M.sized.proof.batch.shape.masksAhead = true
  /-- read for whether the masks come early -/
  choice : M.sized.proof.batch.shape.choice = ⟨true⟩

/-- **A public part as at the full size**: all that the sizing of a proof's tests reads of it: the
written lines, the layout of the ten written sizes, profile 4 and twelve groups of layers. -/
structure PubFull (X : Public) : Prop where
  frame : X.P.frame = recordLines
  wsLay : wsLayOf wsFull true recordLines.blockLog = .ok X.layers.wsLay
  p4 : X.p4 = true
  groups : X.NGr = 12

/-- **A public part whose scan and layers' layout are polLayout's at a parameter file in scope, and
whose layout of the committed matrix is wsLayOf's of these, is as at the full size.** No maker of
the public part is named: the two premises are two lines of its text, and neither reads a hash. -/
theorem pubFull_of_layout {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {X : Public}
    (hl : polLayout Z.pol = .ok (X.P, X.layers.y))
    (hw : wsLayOf (weightShape X.P X.layers.y) X.layers.y.h.p3 X.P.lkW = .ok X.layers.wsLay) :
    PubFull X := by
  obtain ⟨pp, hR⟩ := inScope_readFiles hZ
  have hv := Road.Hd.policy_of_scope hZ hR
  have hl' := hl
  rw [hv] at hl'
  obtain ⟨hfr, hw'⟩ := wsLay_of_polLayout hl' hw
  obtain ⟨S, hS, hh⟩ := Flat.settingsAtRef_held hR
  have hX := polLayout_scan hl
  have e : S = X.P := Except.ok.inj (hS.symm.trans hX)
  rw [hv] at hX
  have A : Road.Hd.PublicCore X.P := Road.Hd.core_of_stored hX (e ▸ hh)
  have Ad := Road.admitted_of_layout (Road.Hd.layerLayout_of_polLayout hl)
    (Road.Hd.switches_of_core A).p3
  have e1 : X.P.h.L = 48 := A.num 2
  have e2 : X.P.h.ll = 2 := A.num 3
  refine ⟨hfr, hw', ?_, ?_⟩
  · show X.layers.y.h.p4 = true
    rw [Ad.shape]
    exact Road.Hd.p4_of_core A
  · show X.layers.y.NGr = 12
    rw [Ad.NGr]
    show X.P.h.L / 2 ^ X.P.h.ll = 12
    rw [e1, e2]
    norm_num

/-- **The public part in scope**, from publicOf's yes. -/
theorem public_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {lay : Option ByteArray} {X : Public} (hX : publicOf Z.pol Z.KL lay = .ok X) : PubFull X := by
  obtain ⟨pp, hR⟩ := inScope_readFiles hZ
  obtain ⟨v, hv⟩ := inScope_policy hZ
  obtain ⟨h4, hN, _, _⟩ := Meaning.scope_plans hZ hR hX
  rw [hv] at hX
  obtain ⟨hfr, hw⟩ := wsLay_at_policy hX
  exact ⟨hfr, hw, h4, hN⟩

section
variable {X : Public} (hP0 : PubFull X) {shapes : Shapes} {cfg : ByteArray} {bits : Nat}
  {made : Configured} (hc : configure X.P.frame shapes cfg bits = .ok made) {rl : List ReqLink}
  (he : shapes.sub = subproofsWith X rl)
include hP0 hc he

/-- **From configure's yes at a public part as at the full size: the sizes of a proof's test on the
table are what linSized returns at the typed lines and the written table**, at some list of codes.
-/
theorem batch_of_public :
    ∃ codes1, linSized recordSet prLin recordTable codes1 =
      some (made.sized.proof.batch, made.sized.proof.codes) := by
  obtain ⟨hfr, hw, _, hN⟩ := hP0
  have hP := (configure_proof_sizes hc).1
  rw [hfr] at hP
  obtain ⟨load, shape, K, T, codes1, _, _, _, _, _, _, hT, hL⟩ := proofSized_parts hP
  obtain rfl : T = recordTable := Option.some.inj (hT.symm.trans record_table)
  have e1 : shapes.sub.matrixRows = 3076096 := by
    rw [he]
    exact m0_full hw
  have e2 : shapes.sub.pendingRows = 13 := by
    rw [he]
    show X.NGr + 1 = 13
    rw [hN]
  rw [e1, e2, maskRows_full] at hL
  exact ⟨codes1, hL⟩

/-- **From configure's yes at a public part as at the full size.** No planner's name, no maker of
the public part and no scope occur: whoever calls configure on such a public part's lines and on
shapes whose sub-proofs are subproofsWith's has it. The request's links rl are a free letter: none
of the ten fields hangs on them (the first chain's last test does: LastAtScope.lean pins them
there). The requested bits are free too: no field reads them. -/
theorem atFull_of_public : AtFull made := by
  have hfr := hP0.frame
  obtain ⟨_, hL⟩ := batch_of_public hP0 hc he
  obtain ⟨t1, t2, t3⟩ := three_stages hL
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hF⟩ := linSized_named hL
  obtain ⟨a1, a2, a3, a4⟩ := linFinish_shape hF
  obtain ⟨_, s2, hot⟩ := configure_proof_sizes hc
  have s1 := (sized_link (configure_plans hc).1).1
  rw [hfr] at s1 s2
  exact ⟨s1.trans set_eq, s2.trans set_eq, t1, t2, t3, hot, a1, a2, a3, a4⟩

end

section
variable {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {lay : Option ByteArray} {X : Public}
  (hX : publicOf Z.pol Z.KL lay = .ok X) {shapes : Shapes} {cfg : ByteArray} {bits : Nat}
  {made : Configured} (hc : configure X.P.frame shapes cfg bits = .ok made) {rl : List ReqLink}
  (he : shapes.sub = subproofsWith X rl)
include hZ hX hc he

/-- The same where the public part is what publicOf returns at files in scope. -/
theorem batch_of_configure :
    ∃ codes1, linSized recordSet prLin recordTable codes1 =
      some (made.sized.proof.batch, made.sized.proof.codes) :=
  batch_of_public (public_at_scope hZ hX) hc he

/-- **From configure's yes at what publicOf returns at files in scope.** -/
theorem atFull_of_configure : AtFull made :=
  atFull_of_public (public_at_scope hZ hX) hc he

end

/-! ## 4. At the scope, from Model.Verify.planned -/

/-- **At every three public files in the goals' scope**, from `planned`. -/
theorem atFull_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Verify.Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) : AtFull p.chains.made := by
  obtain ⟨_, shapes, _, _, _, rl, _, hX, _, _, _, _, hc, _, _, _, he⟩ := planned_parts hp
  exact atFull_of_configure hZ hX hc he

/-- The same from the record that Johnson.G.OfPlan.madeOf makes of the three files. -/
theorem atFull_at_made {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {m : Johnson.G.OfPlan.Made} (h : Johnson.G.OfPlan.madeOf Z.pol Z.lay Z.KL = .ok m) :
    AtFull m.p.chains.made :=
  atFull_at_scope hZ (madeOf_planned h)

/-- The sizes of a proof's test on the table, from `planned`. -/
theorem batch_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Verify.Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    ∃ codes1, linSized recordSet prLin recordTable codes1 =
      some (p.chains.made.sized.proof.batch, p.chains.made.sized.proof.codes) := by
  obtain ⟨_, shapes, _, _, _, rl, _, hX, _, _, _, _, hc, _, _, _, he⟩ := planned_parts hp
  exact batch_of_configure hZ hX hc he

/-- **At every three public files in the goals' scope the stages of the folded row's test, of
Omega's test and of the request's own test are the three typed lists.** -/
theorem three_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Verify.Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.proof.batch.folded.stages = szUFull ∧
      p.chains.made.sized.proof.batch.omega.stages = szOFull ∧
      p.chains.made.sized.proof.batch.own.stages = szWFull :=
  ⟨(atFull_at_scope hZ hp).U, (atFull_at_scope hZ hp).O, (atFull_at_scope hZ hp).W⟩

/-- The same from madeOf. -/
theorem three_at_made {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {m : Johnson.G.OfPlan.Made} (h : Johnson.G.OfPlan.madeOf Z.pol Z.lay Z.KL = .ok m) :
    m.p.chains.made.sized.proof.batch.folded.stages = szUFull ∧
      m.p.chains.made.sized.proof.batch.omega.stages = szOFull ∧
      m.p.chains.made.sized.proof.batch.own.stages = szWFull :=
  three_at_scope hZ (madeOf_planned h)

/-- **Both settings in what the program computes are the typed setting**: that of all sizes, at
which the work is read, and that of the proof's sizes, at which the radii are read. -/
theorem sets_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Verify.Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.set = setAt ∧ p.chains.made.sized.proof.set = setAt :=
  ⟨(atFull_at_scope hZ hp).set, (atFull_at_scope hZ hp).setP⟩

end H2K.Sizes

#print axioms H2K.Sizes.three_stages
#print axioms H2K.Sizes.wsLay_at_policy
#print axioms H2K.Sizes.pubFull_of_layout
#print axioms H2K.Sizes.public_at_scope
#print axioms H2K.Sizes.atFull_of_public
#print axioms H2K.Sizes.atFull_of_configure
#print axioms H2K.Sizes.atFull_at_scope
#print axioms H2K.Sizes.batch_at_scope
#print axioms H2K.Sizes.three_at_scope
#print axioms H2K.Sizes.three_at_made
#print axioms H2K.Sizes.sets_at_scope
