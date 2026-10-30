-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean: every step of the text that makes the public part of
a stage which takes no hash, as an equation in the fields of the record that is returned.

Many laws of the library have "`publicOf pol KL layout = .ok X`" as a premise and open the text of
`publicOf` (OnBytes/Model/VerifyPublic.lean) to draw one or another of its steps from it. Where the
record comes from `publicOfO o` (Johnson/Desc/Ok/PlanWritten/PublicAt.lean), that premise is not at
hand. `PublicSteps pol KL X` is a premise that both roads pay, and it does not have to grow: it
holds every step that does not take the second hash function, so whatever a law draws from the text,
but for a digest, is a field of it or a step from one.

The text has twenty-one steps. Kept, each as a field: the scan and the layout (`layout`); the scales
(`scales`) and the test on them (`held`); that no sum wraps (`noWrap`); the widths of the weights
(`widths`); the head's shape (`hS`) and the test on the vocabulary (`vocab`); the layout of the
committed matrix (`wsLay`); the rotary table (`rope`); the head's layout (`head`); the layers'
record (`layers`); the layers' plans (`plans`); the owner (`owner`); and, in the field `attention`:
attention's plans, the filling of their owners, the head's plan, and the tests across plans.

Not kept, because they take the second hash function: the three tests of a public table against its
digest in the parameter file (the gate's, the sigmoid's, the rotary table's); the digest of the
three files, of which the text asks only that it is made; and the three digests of the lists of
calls in the record. These are five steps. A sixth, the attention sub-proofs' config, is kept but
for what takes the hash in it: its test on the table of exponentials and its digest of the lines
(`ConfigCut`, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).

Row or tool. Every declaration here is a tool: rules for all files, all o and all records. No
description of the protocol is named.

What is here.
  `pubOf_fields`: what `Layer.Pub.of` returns, field by field.
  `PublicSteps pol KL X`: the structure. It names no hash and no o.
  `publicSteps_of_O`: where `publicOfO o` returns X, at any o, it holds. The proof is the walk of
    `publicOfO_cut` with every equation kept. `publicSteps_of`: where the library's `publicOf`
    returns X, it holds: `publicOf` is `publicOfO` at the second hash function (`publicOfO_older`,
    Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean).
  `PublicSteps.cut`: it gives `PublicCut pol KL X`. `cut_hS`, `cut_plans`, `cut_owner`, `cut_set`,
    `cut_attention`: the clauses of `PublicCut` that had no name, so that nobody has to spend that
    statement by the places of its clauses (the others:
    Johnson/Desc/Ok/PlanWritten/PublicAtCutMore.lean).
  `PublicSteps.tails`, `PublicSteps.set`, `PublicSteps.reads`, `PublicSteps.V`, `PublicSteps.tokv`:
    five steps from the field `layers`: the lists of matrices are `tailsOf` of the layout; the
    settings are the scan's; the tables of reads are `readsOf`'s; the size of the vocabulary is the
    scan's; there is no token yet.
  `mapM_size`, `ConfigCut.NAs`, `ConfigCut.size`, `ConfigCut.groups`: what else laws of the library
    read of a yes of attention's config, from `ConfigCut`: the conclusions of `config_NAs`
    (OnBytes/Tie/Pv/Lookup/Ends/FoPublicAMats.lean) and of `config_groups`
    (Johnson/Road/HeadL5Grp.lean).

What of OnBytes/Model/ is used: the routines that `publicOf` calls.

Limits. One direction: from a run that returns. At no o is `publicOfO o` shown to return, and
`PublicSteps` does not give back that it does: the five steps that are not kept may refuse. It says
nothing of `X.digests`. `publicOfO` is a copy of the library's text; if that text turns, the copy,
the structure and the walk turn with it. Nothing on soundness.


-/
import Johnson.Desc.Ok.PlanWritten.PublicAtCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes OnBytes.Model Fo.BatRows Fo.Pub

variable {o : Nat → ByteArray → ByteArray}

/-- What `Layer.Pub.of` returns, field by field. -/
theorem pubOf_fields {y : Layer.Lay} {sc : Layer.Scales} {rope : Array Nat} {wsLay : WsLay}
    {V : Nat} {tokv : Array Nat} {set : Settings} {L : Layer.Pub}
    (h : Layer.Pub.of y sc rope wsLay V tokv set = .ok L) :
    L.y = y ∧ L.sc = sc ∧ L.rope = rope ∧ L.wsLay = wsLay ∧ L.V = V ∧ L.tokv = tokv ∧
      L.tails = Layer.tailsOf y ∧ L.set = set ∧ Layer.readsOf y = .ok L.rd := by
  unfold Layer.Pub.of at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨rd, hr, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hr⟩

/-- **Every step of the public part's text that takes no hash**, in X's own fields. -/
structure PublicSteps (pol KL : ByteArray) (X : Verify.Public) : Prop where
  /-- the scan of the parameter file and the layers' layout -/
  layout : Verify.polLayout pol = .ok (X.P, X.layers.y)
  /-- the scales, off the scale file -/
  scales : Layer.scalesOf X.layers.y.h (fileWords KL) = .ok X.layers.sc
  /-- the test on the scales -/
  held : Layer.scalesHeld X.layers.y.h X.layers.sc = .ok ()
  /-- no sum wraps -/
  noWrap : Layer.noWrap X.layers.y.h X.layers.sc X.layers.y.dq = .ok ()
  /-- the widths of the weights -/
  widths : Layer.weightWidthsHeld X.layers.y.h X.layers.y.kinds = .ok ()
  /-- the head's shape -/
  hS : X.hS = Verify.headShape X.P X.layers.y
  /-- the test on the vocabulary -/
  vocab : Head.vocabulary X.hS = .ok ()
  /-- the layout of the committed matrix of weights -/
  wsLay : wsLayOf (Verify.weightShape X.P X.layers.y) X.layers.y.h.p3 X.P.lkW = .ok X.layers.wsLay
  /-- the rotary table -/
  rope : Layer.ropeOf X.layers.y.h = .ok X.layers.rope
  /-- the head's layout -/
  head : Head.layout X.hS X.layers.y.tauFC = .ok X.HLy
  /-- the layers' record -/
  layers : Layer.Pub.of X.layers.y X.layers.sc X.layers.rope X.layers.wsLay X.P.h.V #[]
    X.P.settings = .ok X.layers
  /-- the layers' plans -/
  plans : Layer.plansG X.layers = .ok X.G
  /-- what the head reads of the last group's plan -/
  owner : Verify.ownerOf X.layers.y X.G = .ok X.owner
  /-- attention's plans, the filling of their owners, the head's plan, the tests across plans -/
  attention : ∃ (A0 : Array OnBytes.Attention.Plan) (seen : Array Verify.SubPlan),
    ((X.layers.y.h.p4 = true ∧ ConfigCut X.P X.layers.y X.layers.sc (midQ X.layers.y) A0) ∨
      (X.layers.y.h.p4 = false ∧ A0 = #[])) ∧
    Verify.attentionOwners X.layers.y.h.p4 X.layers.y.NGr (seenG X.G) (seenA0 A0) = .ok seen ∧
    X.A = A0.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } }) seen ∧
    ∃ H0, Head.planH2 X.P.settings X.hS X.HLy (Verify.borderOf X.layers.y) X.owner
        X.layers.y.NGr X.P.lkW = .ok H0 ∧ X.H = { H0 with Fp := H0.Fp.trimL } ∧
      Verify.crossPlans (X.G.size - 1 + X.A.size + 1) X.layers.y.NGr X.layers.y.h.p4
        (Layer.tailsOf X.layers.y) (seenG X.G) seen ⟨H0.tl, H0.Fp, H0.Tp⟩ = .ok ()

/-- **Where `publicOfO o` returns X, at any o, it holds.** -/
theorem publicSteps_of_O {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : publicOfO o pol KL layout = .ok X) : PublicSteps pol KL X := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, k1, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, k2, h⟩ := bindE_ok h
  obtain ⟨_, t3, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := ite_unit_ok h
  obtain ⟨_, t6, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, t8, h⟩ := bindE_ok h
  obtain ⟨_, t9, h⟩ := bindE_ok h
  obtain ⟨wsLay, t10, h⟩ := bindE_ok h
  obtain ⟨rope, t11, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, t13, h⟩ := bindE_ok h
  obtain ⟨y2, k3, h⟩ := ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, k5, h⟩ := bindE_ok h
  obtain ⟨seen, k6, h⟩ := bindE_ok h
  obtain ⟨owner, k7, h⟩ := bindE_ok h
  obtain ⟨H0, k8, h⟩ := bindE_ok h
  obtain ⟨_, t20, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  obtain ⟨ey, esc, erope, ews, -, -, -, -, -⟩ := pubOf_fields k4
  subst ey esc erope ews
  have ka : (layers.y.h.p4 = true ∧ ConfigCut P layers.y layers.sc (midQ layers.y) y2.1) ∨
      (layers.y.h.p4 = false ∧ y2.1 = #[]) := by
    rcases k3 with ⟨hp, c, k9, e⟩ | ⟨hp, e⟩
    · exact .inl ⟨hp, by rw [e]; exact Attention.configO_cut k9⟩
    · exact .inr ⟨by simpa using hp, by rw [e]⟩
  exact
    { layout := k1, scales := k2, held := t3, noWrap := t6, widths := t8, hS := rfl, vocab := t9,
      wsLay := t10, rope := t11, head := t13, layers := k4, plans := k5, owner := k7,
      attention := ⟨y2.1, seen, ka, k6, rfl, H0, k8, rfl, t20⟩ }

/-- **Where the library's `publicOf` returns X, it holds**: `publicOf` is `publicOfO` at the second
hash function. -/
theorem publicSteps_of {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) : PublicSteps pol KL X :=
  publicSteps_of_O (o := secondHashFunction) ((publicOfO_older pol KL layout).trans h)

variable {pol KL : ByteArray} {X : Verify.Public}

/-- The lists of matrices in the layers' record are `tailsOf` of the layout. -/
theorem PublicSteps.tails (C : PublicSteps pol KL X) : X.layers.tails = Layer.tailsOf X.layers.y :=
  (pubOf_fields C.layers).2.2.2.2.2.2.1

/-- The settings in the layers' record are the scan's. -/
theorem PublicSteps.set (C : PublicSteps pol KL X) : X.layers.set = X.P.settings :=
  (pubOf_fields C.layers).2.2.2.2.2.2.2.1

/-- The tables of reads in the layers' record are `readsOf`'s at the layout. -/
theorem PublicSteps.reads (C : PublicSteps pol KL X) :
    Layer.readsOf X.layers.y = .ok X.layers.rd :=
  (pubOf_fields C.layers).2.2.2.2.2.2.2.2

/-- The size of the vocabulary in the layers' record is the scan's. -/
theorem PublicSteps.V (C : PublicSteps pol KL X) : X.layers.V = X.P.h.V :=
  (pubOf_fields C.layers).2.2.2.2.1

/-- The layers' record holds no token yet. -/
theorem PublicSteps.tokv (C : PublicSteps pol KL X) : X.layers.tokv = #[] :=
  (pubOf_fields C.layers).2.2.2.2.2.1

/-- **It gives `PublicCut`.** -/
theorem PublicSteps.cut (C : PublicSteps pol KL X) : PublicCut pol KL X := by
  obtain ⟨A0, seen, k3, k6, k7, H0, k8, e8, _⟩ := C.attention
  exact ⟨⟨C.layout, C.hS, C.plans, C.owner, ⟨H0, k8, e8⟩, C.set, X.layers.sc, A0, seen, C.scales,
    k3, k6, k7⟩, C.reads⟩

/-! ## What else is read of a yes of attention's config -/

/-- The list of the values of a function that may refuse is as long as the list. -/
theorem mapM_size {ε α β : Type} (f : α → Except ε β) : ∀ (l : List α) (r : List β),
    l.mapM f = .ok r → r.length = l.length
  | [], r, h => by
    rw [List.mapM_nil] at h
    obtain rfl : [] = r := Except.ok.inj h
    rfl
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, _, h⟩ := bindE_ok h
    obtain ⟨bs, hbs, h⟩ := bindE_ok h
    obtain rfl : b :: bs = r := Except.ok.inj h
    rw [List.length_cons, List.length_cons, mapM_size f l bs hbs]

variable {P : PolScan} {y : Layer.Lay} {sc : Layer.Scales} {mq : Nat → Nat}
  {A0 : Array OnBytes.Attention.Plan}

/-- The number of parts of the matrix `as` is not 0: the conclusion of `config_NAs`
(OnBytes/Tie/Pv/Lookup/Ends/FoPublicAMats.lean). -/
theorem ConfigCut.NAs (C : ConfigCut P y sc mq A0) : 0 < P.h.NAs := by
  obtain ⟨_, _, _, _, hr, _, _, _⟩ := C
  by_contra hn
  have h0 : P.h.NAs = 0 := by omega
  simp [refuseIf, h0] at hr

/-- There are as many plans as groups of layers. -/
theorem ConfigCut.size (C : ConfigCut P y sc mq A0) : A0.size = y.NGr := by
  obtain ⟨_, plans, _, _, _, h2, _, rfl⟩ := C
  have k := mapM_size _ _ _ h2
  rw [List.length_range] at k
  rw [List.size_toArray]
  exact k

/-- **One plan for each group of layers, and it is what `Attention.group` returns**: the conclusion
of `config_groups` (Johnson/Road/HeadL5Grp.lean). -/
theorem ConfigCut.groups (C : ConfigCut P y sc mq A0) :
    ∃ lines, A0.size = y.NGr ∧ ∀ g, g < y.NGr →
      ∃ Xg, A0[g]? = some Xg ∧ OnBytes.Attention.group P y sc mq lines g = .ok Xg := by
  obtain ⟨lines, _, hat⟩ := C.at
  refine ⟨lines, C.size, fun g hg => ?_⟩
  have hlt : g < A0.size := by rw [C.size]; exact hg
  exact ⟨A0[g], Array.getElem?_eq_getElem hlt, hat g A0[g] (Array.getElem?_eq_getElem hlt)⟩

/-! ## The clauses of `PublicCut`, by name -/

/-- The head's shape. -/
theorem cut_hS (C : PublicCut pol KL X) : X.hS = Verify.headShape X.P X.layers.y := C.1.2.1

/-- The layers' plans. -/
theorem cut_plans (C : PublicCut pol KL X) : Layer.plansG X.layers = .ok X.G := C.1.2.2.1

/-- What the head reads of the last group's plan. -/
theorem cut_owner (C : PublicCut pol KL X) : Verify.ownerOf X.layers.y X.G = .ok X.owner :=
  C.1.2.2.2.1

/-- The settings in the layers' record are the scan's. -/
theorem cut_set (C : PublicCut pol KL X) : X.layers.set = X.P.settings := C.1.2.2.2.2.2.1

/-- The clause on the scales and on attention, whole. -/
theorem cut_attention (C : PublicCut pol KL X) :
    ∃ (sc : Layer.Scales) (A0 : Array OnBytes.Attention.Plan) (seen : Array Verify.SubPlan),
      Layer.scalesOf X.layers.y.h (fileWords KL) = .ok sc ∧
      ((X.layers.y.h.p4 = true ∧ ConfigCut X.P X.layers.y sc (midQ X.layers.y) A0) ∨
        (X.layers.y.h.p4 = false ∧ A0 = #[])) ∧
      Verify.attentionOwners X.layers.y.h.p4 X.layers.y.NGr (seenG X.G) (seenA0 A0) = .ok seen ∧
      X.A = A0.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } }) seen :=
  C.1.2.2.2.2.2.2

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.pubOf_fields
#print axioms VerifiableInference.PlanWritten.publicSteps_of_O
#print axioms VerifiableInference.PlanWritten.publicSteps_of
#print axioms VerifiableInference.PlanWritten.PublicSteps.tails
#print axioms VerifiableInference.PlanWritten.PublicSteps.set
#print axioms VerifiableInference.PlanWritten.PublicSteps.reads
#print axioms VerifiableInference.PlanWritten.PublicSteps.V
#print axioms VerifiableInference.PlanWritten.PublicSteps.tokv
#print axioms VerifiableInference.PlanWritten.PublicSteps.cut
#print axioms VerifiableInference.PlanWritten.mapM_size
#print axioms VerifiableInference.PlanWritten.ConfigCut.NAs
#print axioms VerifiableInference.PlanWritten.ConfigCut.size
#print axioms VerifiableInference.PlanWritten.ConfigCut.groups
#print axioms VerifiableInference.PlanWritten.cut_hS
#print axioms VerifiableInference.PlanWritten.cut_plans
#print axioms VerifiableInference.PlanWritten.cut_owner
#print axioms VerifiableInference.PlanWritten.cut_set
#print axioms VerifiableInference.PlanWritten.cut_attention
