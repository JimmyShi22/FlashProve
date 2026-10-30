-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean: what a run of the public part that returns says of
what it returns, with the second hash function as an argument: the library's `publicOf_cut` and
`public_reads`, and what `config_at` walks, at `publicOfO o` and `Attention.configO o`
(Johnson/Desc/Ok/PlanWritten/PublicAt.lean), at every o; and one statement on the record alone that
both `publicOf` and `publicOfO o` pay.

Many laws of the library take "`publicOf pol KL layout = .ok X`" as a premise and spend of it only
what three laws draw from it: `Fo.Pub.publicOf_cut` (OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean),
`Fo.Pub.public_A` (FoPublicA.lean) and `Fit.public_reads` (OnBytes/Model/Fit/LayerCaps.lean). Where
the record comes from `publicOfO o`, that premise is not at hand. None of the three conclusions
names a hash but in one place: `publicOf_cut` names the attention sub-proofs' `config`, whose text
tests a table's digest. `PublicCut` has, in that place, what a yes of `config` says that does not
hang on a hash (`ConfigCut`), which is more than `public_A` reads of it.

Row or tool. Every declaration here is a tool: rules for all files, all o and all records. No
description of the protocol is named.

What is here. The proofs are the library's own, step for step, with the twins' names.
  `pubOf_set`, `publicOfO_cut`: the statement of `publicOf_cut` with `publicOfO o` in the premise
    and `Attention.configO o` in the clause on attention: all its clauses, and one more: the layers'
    record has the scan's settings.
  `publicOfO_reads`: the statement of `public_reads` with `publicOfO o` in the premise.
  `ConfigCut P y sc mq A0`: of the plans A0: the lines on attention's calls are read; the two tests
    on the shape pass; `Attention.group` makes a plan for each group, in order; there is at least
    one; A0 are these plans. `Attention.configO_cut`, `Attention.config_cut`: a yes of
    `Attention.configO o`, at any o, and a yes of the library's `Attention.config`, give it of their
    plans. `ConfigCut.at`, `configO_at`: so member number g is what `Attention.group` returns at g:
    the conclusion of `config_at`.
  `PublicCut pol KL X`: the clauses of `publicOfO_cut`, with `ConfigCut` for the run of `config`,
    and the equation of `public_reads`. It names no hash.
  `publicCut_of_O`, `publicCut_of`: where `publicOfO o` at any o, or the library's `publicOf`,
    returns X, `PublicCut pol KL X` holds. The second is the first at the second hash function
    (`publicOfO_older`, Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean).
  `cut_A`: the conclusion of `public_A` from `PublicCut pol KL X`.

What of OnBytes/Model/ is used: what the three laws name.

Limits. One direction: from a run that returns. At no o is `publicOfO o` shown to return.
`PublicCut` keeps what the three laws keep, and of `config` what is named above: not its test on the
table of exponentials, and not its digest of the lines. Of the other tests of the public part, of
the head's layout and of the three digests of the lists of calls it says nothing. The twins are a
copy of the library's text; if that text turns, the copy and these proofs turn with it. Nothing on
soundness.


-/
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA
import OnBytes.Model.Fit.LayerCaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes OnBytes.Model Fo.BatRows Fo.Pub

variable {o : Nat → ByteArray → ByteArray}

/-! ## The three laws at the twins -/

/-- `Layer.Pub.of` keeps the settings. -/
theorem pubOf_set {y : Layer.Lay} {sc : Layer.Scales} {rope : Array Nat} {wsLay : WsLay} {V : Nat}
    {tokv : Array Nat} {set : Settings} {L : Layer.Pub}
    (h : Layer.Pub.of y sc rope wsLay V tokv set = .ok L) : L.set = set := by
  unfold Layer.Pub.of at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨rd, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  rfl

/-- A run of `publicOfO o` that returns, in X's own fields. -/
theorem publicOfO_cut {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : publicOfO o pol KL layout = .ok X) :
    Verify.polLayout pol = .ok (X.P, X.layers.y) ∧
    X.hS = Verify.headShape X.P X.layers.y ∧
    Layer.plansG X.layers = .ok X.G ∧
    Verify.ownerOf X.layers.y X.G = .ok X.owner ∧
    (∃ H0, Head.planH2 X.P.settings X.hS X.HLy (Verify.borderOf X.layers.y) X.owner
        X.layers.y.NGr X.P.lkW = .ok H0 ∧ X.H = { H0 with Fp := H0.Fp.trimL }) ∧
    X.layers.set = X.P.settings ∧
    ∃ (sc : Layer.Scales) (A0 : Array OnBytes.Attention.Plan) (seen : Array Verify.SubPlan),
      Layer.scalesOf X.layers.y.h (fileWords KL) = .ok sc ∧
      ((X.layers.y.h.p4 = true ∧
          ∃ c, Attention.configO o X.P X.layers.y sc (midQ X.layers.y) = .ok c ∧ A0 = c.plans) ∨
        (X.layers.y.h.p4 = false ∧ A0 = #[])) ∧
      Verify.attentionOwners X.layers.y.h.p4 X.layers.y.NGr (seenG X.G) (seenA0 A0) = .ok seen ∧
      X.A = A0.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } }) seen := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, k1, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, k2, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨wsLay, _, h⟩ := bindE_ok h
  obtain ⟨rope, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, _, h⟩ := bindE_ok h
  obtain ⟨y2, k3, h⟩ := ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, k5, h⟩ := bindE_ok h
  obtain ⟨seen, k6, h⟩ := bindE_ok h
  obtain ⟨owner, k7, h⟩ := bindE_ok h
  obtain ⟨H0, k8, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  have hy : layers.y = y := pubOf_y k4
  dsimp only
  rw [hy]
  refine ⟨k1, rfl, k5, k7, ⟨H0, k8, rfl⟩, pubOf_set k4, sc, y2.1, seen, k2, ?_, k6, rfl⟩
  rcases k3 with ⟨hp, c, k9, e⟩ | ⟨hp, e⟩
  · exact .inl ⟨hp, c, k9, by rw [e]⟩
  · exact .inr ⟨by simpa using hp, by rw [e]⟩

/-- The tables of reads in what `publicOfO o` returns are `readsOf`'s at its layout. -/
theorem publicOfO_reads {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : publicOfO o pol KL layout = .ok X) : Layer.readsOf X.layers.y = .ok X.layers.rd := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, _, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨wsLay, _, h⟩ := bindE_ok h
  obtain ⟨rope, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, _, h⟩ := bindE_ok h
  obtain ⟨y2, _, h⟩ := ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, _, h⟩ := bindE_ok h
  obtain ⟨seen, _, h⟩ := bindE_ok h
  obtain ⟨owner, _, h⟩ := bindE_ok h
  obtain ⟨H0, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  exact Fit.pubOf_reads k4

/-- **What a yes of the attention sub-proofs' config says that does not hang on a hash**, of its
plans A0: the lines on attention's calls are read; the two tests on the shape pass; a plan is made
for each group, in order; there is at least one; A0 are these plans. -/
def ConfigCut (P : PolScan) (y : Layer.Lay) (sc : Layer.Scales) (mq : Nat → Nat)
    (A0 : Array OnBytes.Attention.Plan) : Prop :=
  ∃ (lines : List OnBytes.Attention.Line) (plans : List OnBytes.Attention.Plan),
    OnBytes.Attention.readLines P.polCallsA = .ok lines ∧
    refuseIf (P.h.Gk &&& (P.h.Gk - 1) != 0) "af-shape-heads" = .ok () ∧
    refuseIf (P.h.lmh < P.h.lt || P.h.lmh > 24 || P.h.lmo < P.h.lt || P.h.lmo > 24 ||
      P.h.lmbA > 24 || P.h.lmS > 24 || P.h.NAs == 0 || P.h.NAs > 64)
      "shape-request-matrix-A" = .ok () ∧
    (List.range y.NGr).mapM (OnBytes.Attention.group P y sc mq lines) = .ok plans ∧
    plans ≠ [] ∧ A0 = plans.toArray

/-- A yes of `Attention.configO o`, at any o, gives it. -/
theorem Attention.configO_cut {P : PolScan} {y : Layer.Lay} {s : Layer.Scales} {mq : Nat → Nat}
    {c : OnBytes.Attention.Config} (h : Attention.configO o P y s mq = .ok c) :
    ConfigCut P y s mq c.plans := by
  unfold Attention.configO at h
  obtain ⟨lines, h1, h⟩ := bindE_ok h
  obtain ⟨_, t1, h⟩ := bindE_ok h
  obtain ⟨_, t2, h⟩ := bindE_ok h
  obtain ⟨plans, h2, h⟩ := bindE_ok h
  cases plans with
  | nil => cases h
  | cons X0 rest =>
    obtain ⟨_, _, h⟩ := bindE_ok h
    obtain rfl := Except.ok.inj h
    exact ⟨lines, X0 :: rest, h1, t1, t2, h2, List.cons_ne_nil _ _, rfl⟩

/-- So does a yes of the library's `Attention.config`. -/
theorem Attention.config_cut {P : PolScan} {y : Layer.Lay} {s : Layer.Scales} {mq : Nat → Nat}
    {c : OnBytes.Attention.Config} (h : OnBytes.Attention.config P y s mq = .ok c) :
    ConfigCut P y s mq c.plans := by
  rw [← Attention.configO_older] at h
  exact Attention.configO_cut h

/-- Member number g of the plans is what `Attention.group` returns at g: the conclusion of
`config_at`. -/
theorem ConfigCut.at {P : PolScan} {y : Layer.Lay} {sc : Layer.Scales} {mq : Nat → Nat}
    {A0 : Array OnBytes.Attention.Plan} (C : ConfigCut P y sc mq A0) :
    ∃ lines, OnBytes.Attention.readLines P.polCallsA = .ok lines ∧
      ∀ (g : Nat) (a : OnBytes.Attention.Plan), A0[g]? = some a →
        OnBytes.Attention.group P y sc mq lines g = .ok a := by
  obtain ⟨lines, plans, h1, _, _, h2, _, rfl⟩ := C
  refine ⟨lines, h1, fun g a hg => ?_⟩
  obtain ⟨x, hx, hf⟩ := mapM_at _ _ _ h2 g a (by simpa using hg)
  have hx' : x = g := by
    obtain ⟨_, e⟩ := List.getElem?_eq_some_iff.1 hx
    rw [List.getElem_range] at e
    exact e.symm
  rw [hx'] at hf
  exact hf

/-- Member number g of the plans of `Attention.configO o`: the like of `config_at`. -/
theorem configO_at {P : PolScan} {y : Layer.Lay} {s : Layer.Scales} {mq : Nat → Nat}
    {c : OnBytes.Attention.Config} (h : Attention.configO o P y s mq = .ok c) :
    ∃ lines, OnBytes.Attention.readLines P.polCallsA = .ok lines ∧
      ∀ (g : Nat) (a : OnBytes.Attention.Plan), c.plans[g]? = some a →
        OnBytes.Attention.group P y s mq lines g = .ok a :=
  (Attention.configO_cut h).at

/-! ## One statement on the record, which both roads pay -/

/-- **The clauses of `publicOf_cut`, with `ConfigCut` for the run of `config`, and the equation of
`public_reads`.** It names no hash. -/
def PublicCut (pol KL : ByteArray) (X : Verify.Public) : Prop :=
  (Verify.polLayout pol = .ok (X.P, X.layers.y) ∧
    X.hS = Verify.headShape X.P X.layers.y ∧
    Layer.plansG X.layers = .ok X.G ∧
    Verify.ownerOf X.layers.y X.G = .ok X.owner ∧
    (∃ H0, Head.planH2 X.P.settings X.hS X.HLy (Verify.borderOf X.layers.y) X.owner
        X.layers.y.NGr X.P.lkW = .ok H0 ∧ X.H = { H0 with Fp := H0.Fp.trimL }) ∧
    X.layers.set = X.P.settings ∧
    ∃ (sc : Layer.Scales) (A0 : Array OnBytes.Attention.Plan) (seen : Array Verify.SubPlan),
      Layer.scalesOf X.layers.y.h (fileWords KL) = .ok sc ∧
      ((X.layers.y.h.p4 = true ∧
          ConfigCut X.P X.layers.y sc (midQ X.layers.y) A0) ∨
        (X.layers.y.h.p4 = false ∧ A0 = #[])) ∧
      Verify.attentionOwners X.layers.y.h.p4 X.layers.y.NGr (seenG X.G) (seenA0 A0) = .ok seen ∧
      X.A = A0.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } }) seen) ∧
    Layer.readsOf X.layers.y = .ok X.layers.rd

/-- **Where `publicOfO o` returns X, at any o, it holds.** -/
theorem publicCut_of_O {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : publicOfO o pol KL layout = .ok X) : PublicCut pol KL X := by
  obtain ⟨c1, c2, c3, c4, c5, c6, sc, A0, seen, k2, k3, k6, k7⟩ := publicOfO_cut h
  refine ⟨⟨c1, c2, c3, c4, c5, c6, sc, A0, seen, k2, ?_, k6, k7⟩, publicOfO_reads h⟩
  rcases k3 with ⟨hp, c, k9, rfl⟩ | k3
  · exact .inl ⟨hp, Attention.configO_cut k9⟩
  · exact .inr k3

/-- **Where the library's `publicOf` returns X, it holds**: `publicOf` is `publicOfO` at the second
hash function. -/
theorem publicCut_of {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) : PublicCut pol KL X :=
  publicCut_of_O (o := secondHashFunction) ((publicOfO_older pol KL layout).trans h)

/-- **A member of X.A**: the conclusion of `public_A`, from `PublicCut`. -/
theorem cut_A {pol KL : ByteArray} {X : Verify.Public} (C : PublicCut pol KL X) (g : Nat)
    (a : OnBytes.Attention.Plan) (hg : X.A[g]? = some a) :
    ∃ (sc : Layer.Scales) (lines : List OnBytes.Attention.Line) (cf : OnBytes.Attention.Cfg)
      (a0 : OnBytes.Attention.Plan),
      Layer.scalesOf X.layers.y.h (fileWords KL) = .ok sc ∧
      OnBytes.Attention.readLines X.P.polCallsA = .ok lines ∧
      OnBytes.Attention.fill X.P X.layers.y sc lines g = .ok cf ∧
      OnBytes.Attention.plan X.P.settings
        (OnBytes.Attention.inOf X.P.settings X.layers.y (midQ X.layers.y g) g) cf = .ok a0 ∧
      a = { a0 with seam := { a0.seam with tl := a.seam.tl } } ∧
      a.seam.tl.mats = a0.seam.tl.mats ∧ a.seam.tl.tau = a0.seam.tl.tau := by
  obtain ⟨⟨_, _, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩, _⟩ := C
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_keeps k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, kc⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := kc.at
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    refine ⟨sc, lines, cf, a0, k2, l1, m1, m2, rfl, ?_, ?_⟩
    · show s.tl.mats = _
      rw [f2.1, f3]
    · show s.tl.tau = _
      rw [f2.2, f3]
  · simp at e1

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.pubOf_set
#print axioms VerifiableInference.PlanWritten.publicOfO_cut
#print axioms VerifiableInference.PlanWritten.publicOfO_reads
#print axioms VerifiableInference.PlanWritten.Attention.configO_cut
#print axioms VerifiableInference.PlanWritten.Attention.config_cut
#print axioms VerifiableInference.PlanWritten.ConfigCut.at
#print axioms VerifiableInference.PlanWritten.configO_at
#print axioms VerifiableInference.PlanWritten.publicCut_of_O
#print axioms VerifiableInference.PlanWritten.publicCut_of
#print axioms VerifiableInference.PlanWritten.cut_A
