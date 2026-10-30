-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean.
What it means that the byte-level verifier's lookup routine returns the flat function's end values:
a statement. Its proof is Fo.hcOut2 (OnBytes/Tie/Pv/Lookup/Forest/FoPadAll.lean).

The routine OnBytes.Model.Forest.pad runs in the state of a sub-proof (Fork) and of the channel
(Ctx): it takes rounds off the view and returns a record Heard. This file says, for every reading ρ
of the byte-level field in a commutative ring K (OnBytes.Model.Reading), when a Heard with the state
that the run leaves holds the end values `Fo.Ends K`.

* `HeardIs ρ g F En`: field by field. Scalars, points and lists of scalars are equal after reading.
  A form of Heard is compared in the words of OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean: a claim is
  the flat function's row (`RowIs`); a form has the flat function's target as its public part and,
  on the mask row, the flat function's form (`FormIs`). Both speak of the form's value in every
  later state of the sub-proof. The sumcheck over the leaves is held as a record: the routine
  returns it before its claim is made, so its variables (equality weights, with their points and
  numbers of coefficients), its three flags and the invariant of its state (`Ran`,
  OnBytes/Tie/Pv/Psc/PscWhole.lean) are fields too; so is what lies under the slot of the planes'
  shown value.
* `PadLeft h F F' g`: what a run leaves in the state of the sub-proof: the slots taken; every slot
  that was filled stays filled and keeps what stands under it; of the run's own slots all are filled
  but those of the hiding polynomial of the sumcheck over the leaves, which the run does not touch;
  three entries more in the list of owed claims, whose numbers the record holds; the other fields
  are untouched.
* `Sized F` (OnBytes/Tie/Pv/Psc/PscFork.lean): the three arrays under the slots are as long as there
  are slots. A hypothesis on the state before the run: the routine that fills a slot does not test
  it, and in a state with shorter arrays what is shown would be lost.
* `HCout2`: a closed proposition: on every run of Forest.pad that returns and takes the rounds rv
  off a view (`Took`, OnBytes/Tie/Pv/Psc/PscView.lean: not a dry run; no message open before or
  after), the record's shape is the one that Forest.shape makes of the calls, with the numbers of
  padding keys filled in (`ShapeOf`); the record holds `endsOf` at that shape, at the first free
  slot before the run, and at the rounds that the run took off the view; and the run leaves the
  state as `PadLeft` says.

Nothing is proved in this file.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoForm

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The record that the byte-level routine returns, with the state that its run leaves, holds these
end values. -/
structure HeardIs (g : Forest.Heard) (F : Fork) (En : Ends K) : Prop where
  theta : ρ.val g.theta = En.theta
  alpha : ρ.val g.alpha = En.alpha
  a : ρ.val g.a = En.a
  nRows : g.rows.size = En.rows.length
  rows : ∀ i, i < g.rows.size → RowIs ρ F (g.rows.getD i {}) (En.rows.getD i ⟨[], 0⟩)
  lvEps : ρ.val g.leaves.eps = En.lvEps
  lvFin : ρ.val g.leaves.claim = En.lvFin
  lvXs : rdA ρ g.leaves.r = En.lvXs
  lvVars : ∃ zd : List (OnBytes.E × ℕ),
    g.leaves.vars.toList = zd.map (fun p => OnBytes.Psc.Weight.equality p.1 p.2) ∧
    zd.map (fun p => ρ.val p.1) = En.lvZs ∧ zd.map (fun p => p.2) = En.lvDg.map (· + 1)
  lvRan : ∃ (mu : OnBytes.E) (zd : List (OnBytes.E × ℕ)) (rs : List (List OnBytes.E × OnBytes.E)),
    Ran g.leaves En.lvFirst mu g.leaves.eps zd rs ∧ zd.map (fun p => ρ.val p.1) = En.lvZs ∧
      zd.map (fun p => p.2) = En.lvDg.map (· + 1)
  lvSize : g.leaves.r.size = g.leaves.vars.size
  lvFlags : g.leaves.started = true ∧ g.leaves.ended = false ∧ g.leaves.rowMade = false
  lvTg : ρ.val g.leaves.target = En.lvTg
  lvStart : FormIs ρ F g.leaves.start En.lvTg En.lvInc
  lvFirst : g.leaves.first = En.lvFirst
  leavesA : ρ.val g.leavesA = En.leavesA
  sBit : g.sBit = En.sBit
  sBitAt : FormIs ρ F (Aff.slot g.sBit) En.bitV [(Pl.mask En.sBit, En.bitBe)]
  zx : rdA ρ g.zx = En.zx
  zy : rdA ρ g.zy = En.zy
  e : rdA ρ g.e = En.e
  cEnd : FormIs ρ F g.cEnd En.cEndC En.cEndInc
  zb0 : rdA ρ g.zb0 = En.zb0
  zb1 : rdA ρ g.zb1 = En.zb1
  tT : rdA ρ g.tT = En.tT
  zk : g.zk.toList.map (rdA ρ) = En.zk

end

/-- What a run of the routine leaves in the state of the sub-proof. 1 + 2 * h.d + 5: the number of
coefficients of the hiding polynomial of the sumcheck over the leaves. -/
structure PadLeft (h : Forest.Shape) (F F' : Fork) (g : Forest.Heard) : Prop where
  next : F'.next = F.next + Forest.elems h
  fit : Sized F'
  keep : ∀ j, Filled F j → Filled F' j ∧ F'.vp.getD j zeroE = F.vp.getD j zeroE ∧
    F'.mf.getD j zeroE = F.mf.getD j zeroE
  filled : ∀ j, F.next ≤ j → j < F.next + Forest.elems h →
    ¬ (g.leaves.first ≤ j ∧ j < g.leaves.first + (1 + 2 * h.d + 5)) → Filled F' j
  leaves : ∀ j, g.leaves.first ≤ j → j < g.leaves.first + (1 + 2 * h.d + 5) →
    (Filled F' j ↔ Filled F j) ∧ F'.vp.getD j zeroE = F.vp.getD j zeroE ∧
      F'.mf.getD j zeroE = F.mf.getD j zeroE
  beyond : ∀ j, F.next + Forest.elems h ≤ j → (Filled F' j ↔ Filled F j)
  owed : F'.owed = ((F.owed.push { what := "look-up-mask-claims" }).push
    { what := "look-up-plane-claims" }).push { what := "look-up-join" }
  owedAt : g.owedObjects = F.owed.size ∧ g.owedPlanes = F.owed.size + 1 ∧ g.owedJoin = F.owed.size +
      2
  rest : F'.trees = F.trees ∧ F'.ns = F.ns ∧ F'.LS = F.LS ∧ F'.c0 = F.c0 ∧ F'.nClaim = F.nClaim ∧
    F'.theta = F.theta ∧ F'.thetaDrawnF = F.thetaDrawnF ∧ F'.planClaimsF = F.planClaimsF ∧
    F'.kapMapF = F.kapMapF ∧ F'.doorShutF = F.doorShutF

/-- The record's shape is made of the calls by the byte-level verifier's own routines. -/
def ShapeOf (calls : Array Call) (pub : Array Nat) (lid : ℕ) (h : Forest.Shape) : Prop :=
  ∃ h0, Forest.shape calls lid = .ok h0 ∧ Forest.pubAsk h0 pub = .ok () ∧ h = { h0 with pub := pub }

/-- On every run on a view that returns, the byte-level routine's record holds the flat function's
end values. -/
def HCout2 : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : Reading K) (calls : Array Call) (pub : Array Nat) (lid lm : ℕ)
    (F F' : Fork) (c c' : Ctx) (g : Forest.Heard) (rv : List Fmt.RoundView),
    Forest.pad calls pub lid F c = .ok ((g, F'), c') → Sized F →
    Took c rv c' →
    ShapeOf calls pub lid g.shape ∧ PadLeft g.shape F F' g ∧
    HeardIs ρ g F' (endsOf g.shape lm F.next (rv.map (rdRV ρ)))

end Fo
