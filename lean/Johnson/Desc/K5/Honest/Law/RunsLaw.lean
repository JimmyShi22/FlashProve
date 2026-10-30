-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RunsLaw.lean: THREE OF THE FOUR RUNS OF CLAIMS THAT STAND IN THE BLOCK OF
AN ATTENTION SEGMENT's OWN ROUNDS ("first", "keys", "second"), ON THE FIRST CHAIN's SHAPE, IN THE
FORM `RunLaw` (Johnson/Desc/First/Batch/Shape/ClaimShape.lean). The run on shapes is THE RUN ITSELF
AT THE BLANK OF THE SHAPE, behind the one Bool of Johnson/Desc/K5/Honest/Law/TabsChain.lean.
Definitions, and statements with their proofs.

Main names:
  `inAt_sh`, `blank_sh`, `real_in`   the runs' input at a state's parts and at the blank of their
    shapes
  `bareSh`, `claimSh_ofForm`   a bare form's claim, on shapes
  `partsOf`, `parts_at`, `inBlank`   the three components that the runs read; the input at their
    blank
  `k5FirstG`, `k5KeysG`, `k5SecondG`   **the runs on shapes**
  `preK5`   **the runs' one premise on values**: the two tests of the tables' maker
  `firstK_at`, `keysK_at`, `secondK_at`   the three runs as functions of the state's parts
  `firstLaw`, `keysLaw`, `secondLaw`   **the laws**
  `pre_of_first`, `pre_of_keys`, `pre_of_second`   a return of the run gives its premise on values

Limits. THE RUN ON SHAPES RUNS THE RUN AT ZEROS: whoever evaluates it at the full size pays that.
The one Bool is sufficient; it is not shown to be necessary: where it says no the run on shapes
refuses though the run may return. THE ONE BOOL IS NOT ENOUGH FOR A RUN ON SHAPES TO RETURN: the run
at the blank has tests of its own (the tables' array must be in the ledger, with its number of
columns; the runs' own tests on numbers and lengths). NO STATEMENT HERE SAYS THAT A RUN ON SHAPES
RETURNS ANYWHERE, NOR THAT THE PREMISE ON VALUES HOLDS ANYWHERE. The runs on shapes have been seen
to return at one state that is laid by hand, by evaluation
(Johnson/Desc/K5/Honest/Law/RunsLawToy.lean); no run of the chain reaches that state. Who pays the
premise on values is not said; a return of the run itself gives it (`pre_of_first`, `pre_of_keys`,
`pre_of_second`). Shapes alone: nothing on a claim's worth. "join" is not here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Batch.Shape.ClaimShape
import Johnson.Desc.First.Att.Claims.K5Still
import Johnson.Desc.First.Att.Claims.InAt
import Johnson.Desc.K5.Honest.Law.TabsChain
import Johnson.Desc.K5.Honest.Law.RunsIn
import Johnson.Desc.K5.Honest.Law.RunsBlank

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S First.AttOwn Claim named)
open VerifiableInference.Desc.K9.Shape (Run RunLaw)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Heard)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh ClaimSh claimSh AffSh affSh Heard5Sh
  heard5Sh HeardAll heardAll LedSh ledSh attOf attOwnSh)
open K5Law (OptRel)

/-! ## 1 The runs' input at two hearings of one shape -/

/-- What a return of the runs' input holds. -/
theorem inAt_holds {c : ParC} {gl : Forest.Heard} {h : Heard} {F : Fork} {x : P.Runs.In × Nat}
    (hx : K5Law.inAt c gl h F = some x) :
    ∃ p t, P.ptsFrom c.geo gl.zk h F = some p ∧
      P.tablesP c.geo c.mats c.nW (P.lookOfO c.geo.lmb gl) p = some t ∧
      (F.trees[c.iU3]?).map (·.K) = some x.2 ∧
      x.1 = { g := c.geo, p := p, t := t, zk := gl.zk, iU3 := c.iU3 } := by
  unfold K5Law.inAt at hx
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hx
  obtain ⟨p, hp, t, ht, K, hK, rfl⟩ := hx
  exact ⟨p, t, hp, ht, hK, rfl⟩

/-- And back. -/
theorem inAt_of {c : ParC} {gl : Forest.Heard} {h : Heard} {F : Fork} {p : P.Pts} {t : P.TablesP}
    {K : Nat} (hp : P.ptsFrom c.geo gl.zk h F = some p)
    (ht : P.tablesP c.geo c.mats c.nW (P.lookOfO c.geo.lmb gl) p = some t)
    (hK : (F.trees[c.iU3]?).map (·.K) = some K) :
    K5Law.inAt c gl h F = some ({ g := c.geo, p := p, t := t, zk := gl.zk, iU3 := c.iU3 }, K) := by
  unfold K5Law.inAt
  simp only [Option.bind_eq_bind, hp, ht, hK, Option.bind_some, Option.pure_def]

/-- Both inputs are made, at hearings, key points and ledgers of one shape: they meet ShIn, at one
number of columns. -/
theorem inAt_sh {c : ParC} {gl gl' : Forest.Heard} {h h' : Heard} {F F' : Fork}
    {x x' : P.Runs.In × Nat} (ez : gl.zk.toList.map (·.size) = gl'.zk.toList.map (·.size))
    (eH : heard5Sh h = heard5Sh h')
    (eT : (F.trees[c.iU3]?).map (·.K) = (F'.trees[c.iU3]?).map (·.K))
    (hx : K5Law.inAt c gl h F = some x) (hx' : K5Law.inAt c gl' h' F' = some x') :
    ShIn x.1 x'.1 ∧ x.2 = x'.2 := by
  obtain ⟨p, t, hp, ht, hK, e⟩ := inAt_holds hx
  obtain ⟨p', t', hp', ht', hK', e'⟩ := inAt_holds hx'
  rw [e, e']
  refine ⟨shIn_of c ez eH hp hp' ht ht', ?_⟩
  rw [hK, hK'] at eT
  exact Option.some.inj eT

/-- At a state's parts and at the blank of their shapes. -/
theorem blank_sh {c : ParC} {gl : Forest.Heard} {h : Heard} {F : Fork} {x x' : P.Runs.In × Nat}
    (hx : K5Law.inAt c gl h F = some x)
    (hx' : K5Law.inAt c (heardAll gl).blank (heard5Blank (heard5Sh h)) (ledBlank (ledSh F)) =
      some x') : ShIn x.1 x'.1 ∧ x.2 = x'.2 :=
  inAt_sh (by rw [look_zk]; rfl) (heard5Sh_blank _).symm (by rw [led_K, fork_K]) hx hx'

/-- **The real input is made** where the one Bool and the two tests on values say yes and the
blank's is made. -/
theorem real_in (A : Attention.Plan) {gl : Forest.Heard} {h : Heard} {F : Fork}
    {x' : P.Runs.In × Nat}
    (hG : tabsG A (heard5Sh h) (heardAll gl) (ledSh F) = true) (hV : valsT A gl h F = true)
    (hx' : K5Law.inAt (P.parCOf A) (heardAll gl).blank (heard5Blank (heard5Sh h))
      (ledBlank (ledSh F)) = some x') : ∃ x, K5Law.inAt (P.parCOf A) gl h F = some x := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 (tabs_returns A hG hV)
  unfold tabsOf at hT
  obtain ⟨p, hp, hT⟩ := Option.bind_eq_some_iff.1 hT
  obtain ⟨t, ht, -⟩ := Option.map_eq_some_iff.1 hT
  obtain ⟨_, _, _, _, hK', _⟩ := inAt_holds hx'
  rw [led_K, ← fork_K] at hK'
  exact ⟨_, inAt_of hp ht hK'⟩

/-! ## 2 The runs on shapes -/

/-- A bare form's claim, on shapes. -/
def bareSh (f : AffSh) : ClaimSh := ClaimSh.mk none f []

theorem claimSh_ofForm (f : Aff) : claimSh ({ form := f } : Claim) = bareSh (affSh f) := rfl

/-- The three components that the runs read. -/
def partsOf (a : ChainSh) : Option (Heard5Sh × HeardAll × LedSh) :=
  match a.att.bind (·.heard5), a.look, a.led with
  | some H, some K, some L => some (H, K, L)
  | _, _, _ => none

/-- At a state in an attention link in which both are laid. -/
theorem parts_at {s : First.S} {a : First.AttOwn} {h : Heard} {gl : Forest.Heard}
    (hh : s.here = .att a) (h5 : a.heard5 = some h) (hg : a.g = some gl) :
    partsOf (chainSh s) = some (heard5Sh h, heardAll gl, ledSh a.F) := by
  have e1 : (chainSh s).att = attOf s.here := rfl
  have e2 : (chainSh s).look = s.look?.map heardAll := rfl
  have e3 : (chainSh s).led = s.fork?.map ledSh := rfl
  have f1 : attOf s.here = some (attOwnSh a) := by rw [hh]; rfl
  have f2 : s.look? = a.g := by
    unfold First.S.look?
    rw [hh]
  have f3 : s.fork? = some a.F := by
    unfold First.S.fork?
    rw [hh]
  have k5 : (attOwnSh a).heard5 = some (heard5Sh h) := by
    show a.heard5.map heard5Sh = _
    rw [h5]
    rfl
  unfold partsOf
  rw [e1, e2, e3, f1, f2, f3, hg]
  simp only [Option.bind_some, k5, Option.map_some]

/-- The runs' input at the blank of the shape. -/
def inBlank (A : Attention.Plan) (a : ChainSh) : Option (P.Runs.In × Nat) :=
  (partsOf a).bind fun x => K5Law.inAt (P.parCOf A) x.2.1.blank (heard5Blank x.1) (ledBlank x.2.2)

/-- **"first" on shapes.** -/
def k5FirstG (A : Attention.Plan) (_ : Nat) (a : ChainSh) :
    Except String (List ClaimSh × ChainSh) :=
  if tabsGC A a then
    match (inBlank A a).bind fun x => P.Runs.firstRun x.1 x.2 with
    | some y => .ok (y.1.map fun f => bareSh (affSh f), a)
    | none => .error "K5.first on shapes"
  else .error "K5.first on shapes: the tables' test"

/-- **"second" on shapes.** -/
def k5SecondG (A : Attention.Plan) (_ : Nat) (a : ChainSh) :
    Except String (List ClaimSh × ChainSh) :=
  if tabsGC A a then
    match (inBlank A a).bind fun x => P.Runs.secondRun x.1 x.2 with
    | some y => .ok (y.map fun f => bareSh (affSh f), a)
    | none => .error "K5.second on shapes"
  else .error "K5.second on shapes: the tables' test"

/-- The calls' key forms at the blank of the shape: "first" reckoned anew, then "keys"' tests. -/
def keysBlank (A : Attention.Plan) (a : ChainSh) : Option (Array Aff) :=
  (partsOf a).bind fun q => (inBlank A a).bind fun x =>
    (P.Runs.firstRun x.1 x.2).bind fun y => P.Runs.keysRun x.1 (P.padOfO q.2.1.shape) y.2

/-- **"keys" on shapes**: no claim. -/
def k5KeysG (A : Attention.Plan) (_ : Nat) (a : ChainSh) :
    Except String (List ClaimSh × ChainSh) :=
  if tabsGC A a then
    match keysBlank A a with
    | some _ => .ok ([], a)
    | none => .error "K5.keys on shapes"
  else .error "K5.keys on shapes: the tables' test"

/-- **THE RUNS' ONE PREMISE ON VALUES**: the two tests of the tables' maker. -/
def preK5 (A : Attention.Plan) (_ : Nat) (s : First.S) : Prop := valsTS A s = true

/-! ## 3 The runs as functions of the state's parts -/

section
variable {c : ParC} {s : First.S} {a : First.AttOwn} {h : Heard} {gl : Forest.Heard}

theorem inOf_at (hh : s.here = .att a) (h5 : a.heard5 = some h) (hg : a.g = some gl) :
    P.inOf (P.seatCO c) c s = K5Law.inAt c gl h a.F := by
  rw [K5Law.inOf_isAt hh, hg, h5]
  rfl

theorem firstK_at (hh : s.here = .att a) (h5 : a.heard5 = some h) (hg : a.g = some gl) :
    P.firstK (P.seatCO c) c s =
      (K5Law.inAt c gl h a.F).bind fun x => (P.Runs.firstRun x.1 x.2).map fun y => (y.1, s) := by
  unfold P.firstK
  rw [inOf_at hh h5 hg]
  cases K5Law.inAt c gl h a.F with
  | none => rfl
  | some x => cases hf : P.Runs.firstRun x.1 x.2 <;> simp [hf]

theorem secondK_at (hh : s.here = .att a) (h5 : a.heard5 = some h) (hg : a.g = some gl) :
    P.secondK (P.seatCO c) c s =
      (K5Law.inAt c gl h a.F).bind fun x => (P.Runs.secondRun x.1 x.2).map fun y => (y, s) := by
  unfold P.secondK
  rw [inOf_at hh h5 hg]
  cases K5Law.inAt c gl h a.F with
  | none => rfl
  | some x => cases hf : P.Runs.secondRun x.1 x.2 <;> simp [hf]

theorem keysK_at (hh : s.here = .att a) (h5 : a.heard5 = some h) (hg : a.g = some gl) :
    P.keysOfK (P.seatCO c) c s =
      (K5Law.inAt c gl h a.F).bind fun x => (P.Runs.firstRun x.1 x.2).bind fun y =>
        P.Runs.keysRun x.1 (P.padOfO gl.shape) y.2 := by
  have hpad : (P.seatCO c).pad s = some (P.padOfO gl.shape) := by
    unfold P.seatCO
    simp only [hh, hg, Option.map_some]
  unfold P.keysOfK
  rw [inOf_at hh h5 hg, hpad]
  cases K5Law.inAt c gl h a.F with
  | none => rfl
  | some x => cases hf : P.Runs.firstRun x.1 x.2 <;> simp [hf]

end

/-! ## 4 The laws -/

section
variable (A : Attention.Plan)

/-- What the runs on shapes' common front gives at a state's shape. -/
theorem front_of {s : First.S} (hG : tabsGC A (chainSh s) = true) :
    ∃ a h gl, s.here = .att a ∧ a.heard5 = some h ∧ a.g = some gl ∧
      tabsG A (heard5Sh h) (heardAll gl) (ledSh a.F) = true ∧
      inBlank A (chainSh s) = K5Law.inAt (P.parCOf A) (heardAll gl).blank
        (heard5Blank (heard5Sh h)) (ledBlank (ledSh a.F)) := by
  obtain ⟨a, h, gl, hh, h5, hg, hT⟩ := parts_of_GC A hG
  refine ⟨a, h, gl, hh, h5, hg, hT, ?_⟩
  unfold inBlank
  rw [parts_at hh h5 hg]
  rfl

/-- The two tests on values, at the state's parts. -/
theorem vals_at {s : First.S} {a : First.AttOwn} {h : Heard} {gl : Forest.Heard}
    (hh : s.here = .att a) (h5 : a.heard5 = some h) (hg : a.g = some gl) :
    valsTS A s = valsT A gl h a.F := by
  unfold valsTS
  rw [hh]
  simp only [h5, hg]

/-- A return of the runs' input holds the two tests on values. -/
theorem vals_of_in {gl : Forest.Heard} {h : Heard} {F : Fork} {x : P.Runs.In × Nat}
    (hx : K5Law.inAt (P.parCOf A) gl h F = some x) : valsT A gl h F = true := by
  obtain ⟨p, t, hp, ht, _, _⟩ := inAt_holds hx
  have hok : K5Law.placeOk (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
      (P.lookOfO (P.parCOf A).geo.lmb gl) p = true := by
    rw [← K5Law.tablesP_isSome, ht]
    rfl
  unfold K5Law.placeOk at hok
  simp only [Bool.and_eq_true] at hok
  unfold valsT
  rw [hp]
  simp only [Bool.and_eq_true]
  exact ⟨hok.1.1.1.1.1, hok.1.1.1.1.2⟩

/-- What a return of "first" as a run of claims holds. -/
theorem first_ok_is {n : Nat} {s s' : First.S} {cs : List Claim}
    (h : K5Law.runFirst (P.parCOf A) n s = .ok (cs, s')) :
    s' = s ∧ ∃ l, P.firstK (P.seatCO (P.parCOf A)) (P.parCOf A) s = some (l, s) ∧
      cs = l.map fun f => ({ form := f } : Claim) := by
  obtain ⟨e, l, hl, rfl⟩ := K5Law.runOfForms_hands (P.seatCO (P.parCOf A)) (P.parCOf A) _
    (K5Law.rFirst_mem _) n s cs s' h
  exact ⟨e, l, K5Law.named_ok hl, rfl⟩

theorem second_ok_is {n : Nat} {s s' : First.S} {cs : List Claim}
    (h : K5Law.runSecond (P.parCOf A) n s = .ok (cs, s')) :
    s' = s ∧ ∃ l, P.secondK (P.seatCO (P.parCOf A)) (P.parCOf A) s = some (l, s) ∧
      cs = l.map fun f => ({ form := f } : Claim) := by
  obtain ⟨e, l, hl, rfl⟩ := K5Law.runOfForms_hands (P.seatCO (P.parCOf A)) (P.parCOf A) _
    (K5Law.rSecond_mem _) n s cs s' h
  exact ⟨e, l, K5Law.named_ok hl, rfl⟩

theorem keys_ok_is {n : Nat} {s s' : First.S} {cs : List Claim}
    (h : K5Law.runKeys (P.parCOf A) n s = .ok (cs, s')) :
    s' = s ∧ ∃ l, P.keysK (P.seatCO (P.parCOf A)) (P.parCOf A) s = some (l, s) ∧
      cs = l.map fun f => ({ form := f } : Claim) := by
  obtain ⟨e, l, hl, rfl⟩ := K5Law.runOfForms_hands (P.seatCO (P.parCOf A)) (P.parCOf A) _
    (K5Law.rKeys_mem _) n s cs s' h
  exact ⟨e, l, K5Law.named_ok hl, rfl⟩

/-- The claims' shapes, of the forms' shapes. -/
theorem claims_sh (l : List Aff) :
    (l.map fun f => ({ form := f } : Claim)).map claimSh = (l.map affSh).map bareSh := by
  rw [List.map_map, List.map_map]
  rfl

/-- **"first".** -/
def firstLaw : RunLaw (K5Law.runFirst (P.parCOf A)) where
  runG := k5FirstG A
  pre := preK5 A
  carries := by
    intro n s s' cs y _ hr hg
    unfold k5FirstG at hg
    split at hg
    · rename_i hG
      obtain ⟨a, h, gl, hh, h5, hgl, _, eB⟩ := front_of A hG
      obtain ⟨rfl, l, hl, rfl⟩ := first_ok_is A hr
      rw [firstK_at hh h5 hgl] at hl
      obtain ⟨x, hx, hl⟩ := Option.bind_eq_some_iff.1 hl
      obtain ⟨z, hz, ez⟩ := Option.map_eq_some_iff.1 hl
      obtain rfl : z.1 = l := (Prod.mk.inj ez).1
      rw [eB] at hg
      split at hg
      · rename_i y' hy'
        obtain ⟨x', hx', hz'⟩ := Option.bind_eq_some_iff.1 hy'
        obtain ⟨S, eK⟩ := blank_sh hx hx'
        have r := first_shapes S x.2
        rw [hz, eK, hz'] at r
        rw [← Except.ok.inj hg, claims_sh, r.1, List.map_map]
        rfl
      · cases hg
    · cases hg
  returns := by
    intro n s y hg hp
    unfold k5FirstG at hg
    split at hg
    · rename_i hG
      obtain ⟨a, h, gl, hh, h5, hgl, hT, eB⟩ := front_of A hG
      have hV : valsT A gl h a.F = true := by
        rw [← vals_at A hh h5 hgl]
        exact hp
      rw [eB] at hg
      split at hg
      · rename_i y' hy'
        obtain ⟨x', hx', hz'⟩ := Option.bind_eq_some_iff.1 hy'
        obtain ⟨x, hx⟩ := real_in A hT hV hx'
        obtain ⟨S, eK⟩ := blank_sh hx hx'
        have r := first_shapes S x.2
        rw [eK, hz'] at r
        cases hz : P.Runs.firstRun x.1 x'.2 with
        | none =>
          rw [hz] at r
          exact r.elim
        | some z =>
          refine ⟨(z.1.map fun f => ({ form := f } : Claim), s), ?_⟩
          show (VerifiableInference.Desc.K9.runOfForms (K5Law.rFirst (P.parCOf A))).2 n s = _
          unfold VerifiableInference.Desc.K9.runOfForms K5Law.rFirst
          simp only [firstK_at hh h5 hgl, hx, eK, hz, Option.bind_some, Option.map_some, named]
          rfl
      · cases hg
    · cases hg

/-- **"second".** -/
def secondLaw : RunLaw (K5Law.runSecond (P.parCOf A)) where
  runG := k5SecondG A
  pre := preK5 A
  carries := by
    intro n s s' cs y _ hr hg
    unfold k5SecondG at hg
    split at hg
    · rename_i hG
      obtain ⟨a, h, gl, hh, h5, hgl, _, eB⟩ := front_of A hG
      obtain ⟨rfl, l, hl, rfl⟩ := second_ok_is A hr
      rw [secondK_at hh h5 hgl] at hl
      obtain ⟨x, hx, hl⟩ := Option.bind_eq_some_iff.1 hl
      obtain ⟨z, hz, ez⟩ := Option.map_eq_some_iff.1 hl
      obtain rfl : z = l := (Prod.mk.inj ez).1
      rw [eB] at hg
      split at hg
      · rename_i y' hy'
        obtain ⟨x', hx', hz'⟩ := Option.bind_eq_some_iff.1 hy'
        obtain ⟨S, eK⟩ := blank_sh hx hx'
        have r := second_shapes S x.2
        rw [hz, eK, hz'] at r
        have r' : z.map affSh = y'.map affSh := r
        rw [← Except.ok.inj hg, claims_sh, r', List.map_map]
        rfl
      · cases hg
    · cases hg
  returns := by
    intro n s y hg hp
    unfold k5SecondG at hg
    split at hg
    · rename_i hG
      obtain ⟨a, h, gl, hh, h5, hgl, hT, eB⟩ := front_of A hG
      have hV : valsT A gl h a.F = true := by
        rw [← vals_at A hh h5 hgl]
        exact hp
      rw [eB] at hg
      split at hg
      · rename_i y' hy'
        obtain ⟨x', hx', hz'⟩ := Option.bind_eq_some_iff.1 hy'
        obtain ⟨x, hx⟩ := real_in A hT hV hx'
        obtain ⟨S, eK⟩ := blank_sh hx hx'
        have r := second_shapes S x.2
        rw [eK, hz'] at r
        cases hz : P.Runs.secondRun x.1 x'.2 with
        | none =>
          rw [hz] at r
          exact r.elim
        | some z =>
          refine ⟨(z.map fun f => ({ form := f } : Claim), s), ?_⟩
          show (VerifiableInference.Desc.K9.runOfForms (K5Law.rSecond (P.parCOf A))).2 n s = _
          unfold VerifiableInference.Desc.K9.runOfForms K5Law.rSecond
          simp only [secondK_at hh h5 hgl, hx, eK, hz, Option.bind_some, Option.map_some, named]
          rfl
      · cases hg
    · cases hg

/-- The key forms at the blank of a state's shape. -/
theorem keysBlank_at {s : First.S} {a : First.AttOwn} {h : Heard} {gl : Forest.Heard}
    (hh : s.here = .att a) (h5 : a.heard5 = some h) (hg : a.g = some gl) :
    keysBlank A (chainSh s) =
      (K5Law.inAt (P.parCOf A) (heardAll gl).blank (heard5Blank (heard5Sh h))
        (ledBlank (ledSh a.F))).bind fun x => (P.Runs.firstRun x.1 x.2).bind fun y =>
          P.Runs.keysRun x.1 (P.padOfO gl.shape) y.2 := by
  unfold keysBlank inBlank
  rw [parts_at hh h5 hg]
  rfl

/-- **The key forms at two inputs of the runs: both are refused, or both are made, of one shape.**
CONDITIONAL on: the two inputs meet `ShIn`, at one number of columns; one input of the lookup's at
both. It is called at a state's parts and at the blank of their shapes. -/
theorem keys_both {gl : Forest.Heard} {x x' : P.Runs.In × Nat} (S : ShIn x.1 x'.1)
    (eK : x.2 = x'.2) :
    OptRel (fun k k' => formsSh k = formsSh k')
      ((P.Runs.firstRun x.1 x.2).bind fun y => P.Runs.keysRun x.1 (P.padOfO gl.shape) y.2)
      ((P.Runs.firstRun x'.1 x'.2).bind fun y => P.Runs.keysRun x'.1 (P.padOfO gl.shape) y.2) := by
  have r := first_shapes S x.2
  rw [← eK]
  cases hz : P.Runs.firstRun x.1 x.2 with
  | none =>
    cases hz' : P.Runs.firstRun x'.1 x.2 with
    | none => trivial
    | some z' =>
      rw [hz, hz'] at r
      exact r.elim
  | some z =>
    cases hz' : P.Runs.firstRun x'.1 x.2 with
    | none =>
      rw [hz, hz'] at r
      exact r.elim
    | some z' =>
      rw [hz, hz'] at r
      exact keys_shapes S.same.g _ r.2

/-- **"keys".** -/
def keysLaw : RunLaw (K5Law.runKeys (P.parCOf A)) where
  runG := k5KeysG A
  pre := preK5 A
  carries := by
    intro n s s' cs y _ hr hg
    unfold k5KeysG at hg
    split at hg
    · obtain ⟨rfl, l, hl, rfl⟩ := keys_ok_is A hr
      obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.1 hl
      obtain rfl : [] = l := (Prod.mk.inj e).1
      split at hg
      · rw [← Except.ok.inj hg]
        rfl
      · cases hg
    · cases hg
  returns := by
    intro n s y hg hp
    unfold k5KeysG at hg
    split at hg
    · rename_i hG
      obtain ⟨a, h, gl, hh, h5, hgl, hT, _⟩ := front_of A hG
      have hV : valsT A gl h a.F = true := by
        rw [← vals_at A hh h5 hgl]
        exact hp
      rw [keysBlank_at A hh h5 hgl] at hg
      split at hg
      · rename_i k' hk'
        obtain ⟨x', hx', hz'⟩ := Option.bind_eq_some_iff.1 hk'
        obtain ⟨x, hx⟩ := real_in A hT hV hx'
        obtain ⟨S, eK⟩ := blank_sh hx hx'
        have r := keys_both (gl := gl) S eK
        rw [hz'] at r
        cases hk : ((P.Runs.firstRun x.1 x.2).bind fun y =>
            P.Runs.keysRun x.1 (P.padOfO gl.shape) y.2) with
        | none =>
          rw [hk] at r
          exact r.elim
        | some k =>
          refine ⟨([], s), ?_⟩
          show (VerifiableInference.Desc.K9.runOfForms (K5Law.rKeys (P.parCOf A))).2 n s = _
          unfold VerifiableInference.Desc.K9.runOfForms K5Law.rKeys P.keysK
          simp only [keysK_at hh h5 hgl, hx, Option.bind_some, hk, Option.map_some, named]
          rfl
      · cases hg
    · cases hg

/-! ## 5 A return of the run gives its premise on values -/

/-- A return of the runs' input at a state gives the premise. -/
theorem pre_of_inOf {n : Nat} {s : First.S} {x : P.Runs.In × Nat}
    (hx : P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) s = some x) : preK5 A n s := by
  obtain ⟨a, hh⟩ := K5Law.att_of_inOf hx
  rw [K5Law.inOf_isAt hh] at hx
  obtain ⟨gl, hg, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨h, h5, hx⟩ := Option.bind_eq_some_iff.1 hx
  unfold preK5
  rw [vals_at A hh h5 hg]
  exact vals_of_in A hx

theorem pre_of_first {n : Nat} {s : First.S} {z : List Claim × First.S}
    (h : K5Law.runFirst (P.parCOf A) n s = .ok z) : preK5 A n s := by
  obtain ⟨_, l, hl, _⟩ := first_ok_is A (cs := z.1) (s' := z.2) h
  unfold P.firstK at hl
  obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.1 hl
  exact pre_of_inOf A hx

theorem pre_of_second {n : Nat} {s : First.S} {z : List Claim × First.S}
    (h : K5Law.runSecond (P.parCOf A) n s = .ok z) : preK5 A n s := by
  obtain ⟨_, l, hl, _⟩ := second_ok_is A (cs := z.1) (s' := z.2) h
  unfold P.secondK at hl
  obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.1 hl
  exact pre_of_inOf A hx

theorem pre_of_keys {n : Nat} {s : First.S} {z : List Claim × First.S}
    (h : K5Law.runKeys (P.parCOf A) n s = .ok z) : preK5 A n s := by
  obtain ⟨_, l, hl, _⟩ := keys_ok_is A (cs := z.1) (s' := z.2) h
  obtain ⟨k, hk, _⟩ := Option.map_eq_some_iff.1 hl
  unfold P.keysOfK at hk
  obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.1 hk
  exact pre_of_inOf A hx

end

end H2K5.Honest

#print axioms H2K5.Honest.inAt_holds
#print axioms H2K5.Honest.inAt_of
#print axioms H2K5.Honest.inAt_sh
#print axioms H2K5.Honest.blank_sh
#print axioms H2K5.Honest.real_in
#print axioms H2K5.Honest.claimSh_ofForm
#print axioms H2K5.Honest.parts_at
#print axioms H2K5.Honest.inOf_at
#print axioms H2K5.Honest.firstK_at
#print axioms H2K5.Honest.secondK_at
#print axioms H2K5.Honest.keysK_at
#print axioms H2K5.Honest.front_of
#print axioms H2K5.Honest.vals_at
#print axioms H2K5.Honest.vals_of_in
#print axioms H2K5.Honest.first_ok_is
#print axioms H2K5.Honest.second_ok_is
#print axioms H2K5.Honest.keys_ok_is
#print axioms H2K5.Honest.claims_sh
#print axioms H2K5.Honest.firstLaw
#print axioms H2K5.Honest.secondLaw
#print axioms H2K5.Honest.keysBlank_at
#print axioms H2K5.Honest.keys_both
#print axioms H2K5.Honest.keysLaw
#print axioms H2K5.Honest.pre_of_inOf
#print axioms H2K5.Honest.pre_of_first
#print axioms H2K5.Honest.pre_of_second
#print axioms H2K5.Honest.pre_of_keys
