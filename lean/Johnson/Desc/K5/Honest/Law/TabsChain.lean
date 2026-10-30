-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/TabsChain.lean: CONDITIONAL: THE QUIET STEP BEHIND AN ATTENTION SEGMENT's
SENDING OF ITS READS (readsAtSO, Johnson/Desc/First/Att/ReadsO.lean) AS A STEP ON THE FIRST CHAIN's
SHAPE ALONE, WHERE ONE BOOL ON THAT SHAPE AND TWO TESTS ON VALUES SAY YES. Over the library, the
shapes of Johnson/Desc/First/Shape/ and the step's own law on the shape
(Johnson/Desc/First/Att/ReadsOShape.lean). Definitions, and statements with their proofs.

Why. `att_sh` (Att/ReadsOShape.lean) has the decision, seen through the chain's shape, as the step
`attG` at the shapes of the tables that are made; these are read off the state there.
Johnson/Desc/K5/Honest/Law/TabsReturns.lean has these shapes as `attFuns A`, a function of the plan
alone, under a Bool on three shapes and two tests on values. Here the two are joined.

Main names:
  `tabsGC`   **the one Bool on the chain's shape**
  `valsTS`   **the two tests on values, on the state**
  `tabsAt_is`, `parts_of_GC`, `tabsAt_shape`   the shapes of the tables that the step makes at a
    state are attFuns A
  `reads_sh`   **the decision, seen through the shape, is attG (some (attFuns A))**
  `reads_carries`, `reads_returns`   **carries and returns**
  `tabsGC_bites`   three controls: the Bool can say no

EVERY STATEMENT ON THE STEP IS CONDITIONAL. `tabsAt_shape`, `reads_sh`: the Bool's yes at the
state's shape; the two tests on values at the state. `reads_carries`: the step's yes; the Bool's
yes. `reads_returns`: the Bool's yes; the step on the shape returns; the two tests on values.
Limits. THE QUIET STEP ALONE: in the first chain's blocksInOrder list it stands joined behind the sending of
the reads, inside wrappers: nothing is said of these. The Bool is sufficient, not necessary. NO
STATEMENT OF THIS FILE ENDS IN THE BOOL's YES: that `tabsG` and the two tests say yes together is an
evaluation (Law/TabsReturnsToy.lean: at parts laid by hand; Law/TabsChainToy.lean: with `attG`'s
return, at a state laid by hand, which no run of the chain reaches and at which the guard of order
has no matrix to ask after). No theorem here says whether `attG` returns (the list of tables is
open; the guard of order).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.ReadsOShape
import Johnson.Desc.K5.Honest.Law.TabsReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Shape (ChainSh chainSh FunSh funSh heardAll heard5Sh ledSh attOf
  attOwnSh)

/-! ## 1 The names, on the chain's shape and on the state -/

/-- **THE ONE BOOL ON THE CHAIN's SHAPE** for the tables of the quiet step behind the reads at an
attention link: `tabsG` (Johnson/Desc/K5/Honest/Law/TabsReturns.lean) at three components of the
first chain's shape (Johnson/Desc/First/Shape/Chain.lean): what the link's own rounds handed on
(att), what the lookup returned (look), the ledger (led). No where one of the three is not laid. -/
def tabsGC (A : Attention.Plan) (a : ChainSh) : Bool :=
  match a.att.bind (·.heard5), a.look, a.led with
  | some H, some K, some L => tabsG A H K L
  | _, _, _ => false

/-- **THE TWO TESTS ON VALUES, ON THE STATE**: `valsT` at the state's own parts. No where the chain
stands in no attention link, or where what the link's own rounds handed on or what the lookup
returned is not laid. -/
def valsTS (A : Attention.Plan) (s : First.S) : Bool :=
  match s.here with
  | .att a =>
    match a.heard5, a.g with
    | some h, some gl => valsT A gl h a.F
    | _, _ => false
  | _ => false

/-! ## 2 The tables that the step makes -/

/-- The step's tables at a state are the two makers in a row at the state's own parts. CONDITIONAL
on: an attention link stands open in which both are laid. -/
theorem tabsAt_is (A : Attention.Plan) {s : First.S} {a : First.AttOwn} {h : P.Heard}
    {gl : Forest.Heard} (hh : s.here = .att a) (h5 : a.heard5 = some h) (hg : a.g = some gl) :
    tabsAt A s = tabsOf A gl h a.F := by
  have e5 : s.heard5? = some h := by
    unfold First.S.heard5?
    rw [hh]
    exact h5
  unfold tabsAt tabsOf
  rw [hh]
  show (s.heard5?.bind fun h => a.g.bind fun g => _) = _
  rw [e5, hg]
  rfl

/-- What the Bool's yes at a state's shape says of the state. -/
theorem parts_of_GC (A : Attention.Plan) {s : First.S} (hG : tabsGC A (chainSh s) = true) :
    ∃ a h gl, s.here = .att a ∧ a.heard5 = some h ∧ a.g = some gl ∧
      tabsG A (heard5Sh h) (heardAll gl) (ledSh a.F) = true := by
  have e1 : (chainSh s).att = attOf s.here := rfl
  have e2 : (chainSh s).look = s.look?.map heardAll := rfl
  have e3 : (chainSh s).led = s.fork?.map ledSh := rfl
  unfold tabsGC at hG
  rw [e1, e2, e3] at hG
  cases hh : s.here with
  | att a =>
    have f1 : attOf s.here = some (attOwnSh a) := by rw [hh]; rfl
    have f2 : s.look? = a.g := by
      unfold First.S.look?
      rw [hh]
    have f3 : s.fork? = some a.F := by
      unfold First.S.fork?
      rw [hh]
    rw [f1, f2, f3] at hG
    cases h5 : a.heard5 with
    | none =>
      have : (attOwnSh a).heard5 = none := by
        show a.heard5.map heard5Sh = none
        rw [h5]
        rfl
      simp [this] at hG
    | some h =>
      have k5 : (attOwnSh a).heard5 = some (heard5Sh h) := by
        show a.heard5.map heard5Sh = _
        rw [h5]
        rfl
      cases hg : a.g with
      | none => simp [k5, hg] at hG
      | some gl =>
        simp only [Option.bind_some, k5, hg, Option.map_some] at hG
        exact ⟨a, h, gl, rfl, h5, hg, hG⟩
  | _ =>
    have f1 : attOf s.here = none := by rw [hh]; rfl
    simp [f1] at hG

/-- **THE SHAPES OF THE TABLES THAT THE STEP MAKES AT A STATE ARE attFuns A**, where the Bool says
yes at the state's shape and the two tests on values say yes at the state. CONDITIONAL on these two.
-/
theorem tabsAt_shape (A : Attention.Plan) {s : First.S} (hG : tabsGC A (chainSh s) = true)
    (hV : valsTS A s = true) :
    (tabsAt A s).map (fun t => t.funs.toList.map funSh) = some (attFuns A) := by
  obtain ⟨a, h, gl, hh, h5, hg, hT⟩ := parts_of_GC A hG
  have hV' : valsT A gl h a.F = true := by
    unfold valsTS at hV
    rw [hh] at hV
    simp only [h5, hg] at hV
    exact hV
  rw [tabsAt_is A hh h5 hg]
  exact tabs_shape A hT hV'

/-! ## 3 The quiet step, on the shape alone -/

/-- **THE QUIET STEP IS A STEP ON THE SHAPE ALONE**: the decision, seen through the chain's shape,
is `attG` (Johnson/Desc/First/Att/ReadsOShape.lean) at the plan's own list of shapes: it says yes
just where that step returns, and then the shape behind is what it returns. CONDITIONAL on the
Bool's yes at the state's shape and the two tests on values at the state. -/
theorem reads_sh (A : Attention.Plan) {s : First.S} (hG : tabsGC A (chainSh s) = true)
    (hV : valsTS A s = true) :
    (readsAtSO A s).toOption.map chainSh = attG (some (attFuns A)) (chainSh s) := by
  rw [att_sh, tabsAt_shape A hG hV]

/-- **CARRIES**: where the quiet step says yes and the Bool says yes in front, the step on the shape
returns the shape behind. The tests on values are not asked. -/
theorem reads_carries (A : Attention.Plan) {s s' : First.S} (h : readsAtSO A s = .ok s')
    (hG : tabsGC A (chainSh s) = true) :
    attG (some (attFuns A)) (chainSh s) = some (chainSh s') := by
  obtain ⟨a, h5v, gl, hh, h5, hg, hT⟩ := parts_of_GC A hG
  have e := att_sh A s
  rw [h] at e
  have e' : attG ((tabsAt A s).map fun t => t.funs.toList.map funSh) (chainSh s) =
      some (chainSh s') := e.symm
  cases hT' : tabsAt A s with
  | none =>
    rw [hT'] at e'
    unfold attG at e'
    split at e'
    · cases e'
    · cases e'
  | some T =>
    rw [hT'] at e'
    rw [tabsAt_is A hh h5 hg] at hT'
    rw [← tabs_carries_G A hT' hT]
    exact e'

/-- **RETURNS**: where the Bool says yes at the shape in front, the step on the shape returns, and
the two tests on values say yes, the quiet step says yes, and the shape behind is what the step on
the shape returned. -/
theorem reads_returns (A : Attention.Plan) {s : First.S} {t : ChainSh}
    (hG : tabsGC A (chainSh s) = true) (ht : attG (some (attFuns A)) (chainSh s) = some t)
    (hV : valsTS A s = true) : ∃ s', readsAtSO A s = .ok s' ∧ chainSh s' = t := by
  have e := reads_sh A hG hV
  rw [ht] at e
  cases hr : readsAtSO A s with
  | error x =>
    rw [hr] at e
    cases e
  | ok s' =>
    rw [hr] at e
    exact ⟨s', rfl, Option.some.inj e⟩

/-- Three controls: the Bool on the chain's shape says no where no attention link's own fields are
there, where the lookup has laid nothing, and where no ledger is there. -/
theorem tabsGC_bites (A : Attention.Plan) (a : ChainSh) :
    (a.att = none → tabsGC A a = false) ∧ (a.look = none → tabsGC A a = false) ∧
      (a.led = none → tabsGC A a = false) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp [tabsGC, h]
  · unfold tabsGC
    rw [h]
    cases a.att.bind (·.heard5) <;> rfl
  · unfold tabsGC
    rw [h]
    cases a.att.bind (·.heard5) <;> cases a.look <;> rfl

end H2K5.Honest

#print axioms H2K5.Honest.tabsAt_is
#print axioms H2K5.Honest.parts_of_GC
#print axioms H2K5.Honest.tabsAt_shape
#print axioms H2K5.Honest.reads_sh
#print axioms H2K5.Honest.reads_carries
#print axioms H2K5.Honest.reads_returns
#print axioms H2K5.Honest.tabsGC_bites
