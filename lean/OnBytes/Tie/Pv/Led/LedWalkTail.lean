-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedWalkTail.lean: routines of the smallness test in the shipped Lean verifier
that add plain claims or none, each with the list that it adds.

Statements in the form Walks r P ol (LedWalk.lean).

Main names.
  Still r: whenever r returns, the state is as it was. still_pure, still_bind, still_ask, still_get,
    still_must, still_lift, still_liftT; still_walks: such a routine adds nothing.
  still_selfTestF, still_tileSelfTestF: the two tests of the smallness test's own weights leave the
    state as it was.
  bitsL tl g, walks_linBits9: the three claims that read the planes of the lookup's counts: each is
    a form and one run of entries of the array BZ.

What this file does not claim. What a form says. The claim on the key vectors (linJoin9), the ties
and the reads are not treated here. Nothing where a routine does not return.


-/
import OnBytes.Tie.Pv.Led.LedWalkSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

/-- Whenever the routine returns, the state is as it was. -/
def Still {α : Type} (r : Model.SubM α) : Prop :=
  ∀ (F G : Model.Fork) (c c' : Ctx) (a : α), r F c = .ok ((a, G), c') → G = F

theorem still_walks {α : Type} {r : Model.SubM α} (h : Still r) :
    Walks r (fun _ => True) (some []) :=
  walks_still fun F G c c' a hr => ⟨h F G c c' a hr, trivial⟩

theorem still_pure {α : Type} (a : α) : Still (pure a : Model.SubM α) := fun F G c c' x hr => by
  have e := (PscRun.pure_ok a F c _).1 hr
  simp only [Prod.mk.injEq] at e
  exact e.1.2

theorem still_bind {α β : Type} {r : Model.SubM α} {k : α → Model.SubM β} (hr : Still r)
    (hk : ∀ x, Still (k x)) : Still (r >>= k) := fun F G c c' y h => by
  obtain ⟨x, F1, c1, h1, h2⟩ := (PscRun.bind_ok _ _ _ _ _).1 h
  rw [hk x F1 G c1 c' y h2, hr F F1 c c1 x h1]

theorem still_ask {α : Type} (f : Model.Fork → Option α) : Still (Model.SubM.ask f) :=
  fun F G c c' a hr => by
    obtain ⟨a', _, e⟩ := (PscRun.ask_ok f F c _).1 hr
    simp only [Prod.mk.injEq] at e
    exact e.1.2

theorem still_get {α : Type} (x : Option α) : Still (Model.SubM.get x) :=
  fun F G c c' a hr => by
    obtain ⟨a', _, e⟩ := (PscRun.get_ok x F c _).1 hr
    simp only [Prod.mk.injEq] at e
    exact e.1.2

theorem still_must (b : Bool) : Still (Model.SubM.must b) := fun F G c c' a hr => by
  obtain ⟨_, e⟩ := (PscRun.must_ok b F c _).1 hr
  simp only [Prod.mk.injEq] at e
  exact e.1.2

theorem still_lift {α : Type} (b : Blk α) : Still (StateT.lift b : Model.SubM α) :=
  fun F G c c' x hr => by
    obtain ⟨a, c1, _, e⟩ := (PscRun.lift_ok b F c _).1 hr
    simp only [Prod.mk.injEq] at e
    exact e.1.2

theorem still_liftT {α : Type} (b : Blk α) : Still (monadLift b : Model.SubM α) := still_lift b

/-- The test that every column which a virtual row is meant to read has a weight. -/
theorem still_selfTestF (tl : Model.HTailF2) (nU : Array Nat) : Still (tl.selfTestF nU) := by
  unfold Model.HTailF2.selfTestF
  exact still_bind (still_ask _) fun _ => still_bind (still_must _) fun _ =>
    still_bind (still_liftT _) fun _ => still_bind (still_liftT _) fun _ => still_liftT _

/-- The second computation of part of the smallness test's weights. -/
theorem still_tileSelfTestF (tl : Model.HTailF2) : Still tl.tileSelfTestF := by
  unfold Model.HTailF2.tileSelfTestF
  refine still_bind (still_get _) fun g => still_bind (still_get _) fun jo =>
    still_bind (still_get _) fun x => ?_
  obtain ⟨nbW, W⟩ := x
  exact still_bind (still_ask _) fun _ => still_bind (still_liftT _) fun _ =>
    still_bind (still_ask _) fun _ => still_bind (still_liftT _) fun _ =>
    still_bind (still_liftT _) fun _ =>
    still_bind (still_ask _) fun _ => still_bind (still_liftT _) fun _ =>
    still_bind (still_ask _) fun _ => still_bind (still_liftT _) fun _ =>
    still_bind (still_ask _) fun _ => still_bind (still_liftT _) fun _ =>
    still_bind (still_ask _) fun _ => still_bind (still_liftT _) fun _ =>
    still_bind (still_ask _) fun _ => still_liftT _

/-- The run of a claim on the planes: the whole of virtual row number row of the array BZ. -/
def runOnBZ (tl : Model.HTailF2) (row : Nat) (coef : E) (w : Array E) : Model.Run2 :=
  { tree := tl.ix.BZ, row := row, first := 0, coef := coef, w := w, n := tl.bzColumns }

/-- The three claims that read the planes of the lookup's counts. -/
def bitsL (tl : Model.HTailF2) (g : Model.Forest.Heard) : List Model.Aff :=
  [claimForm (g.leaves.rowForm oneE {})
      #[runOnBZ tl 0 (mulE g.leaves.eps g.leavesA)
        (Model.eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))],
    claimForm (Model.Aff.slot g.sBit)
      #[runOnBZ tl 1 (subE zeroE oneE) (Model.eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))],
    claimForm (Model.Aff.ofConst (subE zeroE (Model.ofNat (2 ^ tl.f9.v - tl.f9.padding))))
      #[runOnBZ tl 2 oneE ((Array.range tl.bzColumns).map fun u => Model.ofNat (2 ^ (u % 32)))]]

theorem walks_linBits9 (tl : Model.HTailF2) :
    Walks tl.linBits9 (fun _ => True) (tl.heard.bind fun g => some (bitsL tl g)) := by
  unfold Model.HTailF2.linBits9
  refine walks_get_bind tl.heard fun g => ?_
  refine walks_after (walks_pscRow g.leaves oneE {}) fun x hx => ?_
  obtain ⟨row, p'⟩ := x
  obtain rfl : row = g.leaves.rowForm oneE {} := hx
  exact walks_bind (walks_t2Lin _ _) fun _ _ => walks_bind (walks_t2Lin _ _) fun _ _ =>
    walks_bind (walks_t2Lin _ _) fun _ _ =>
      walks_after (walks_planesAdded g) fun _ _ => walks_pure _ trivial

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.still_selfTestF
#print axioms OnBytes.Road.Rows.still_tileSelfTestF
#print axioms OnBytes.Road.Rows.walks_linBits9
