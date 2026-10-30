-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ClaimBody.lean: the hypothesis of `core_own`
(Sim/CoreOwn.lean) on the claim that is left at the last stage of a proximity test (`EndOk`, in that
file) is proved from `BehindFirst`: the invariant of the later stages, no clause of which says that
a part of the verifier accepts (`BodyInv`, Johnson/Prover/Link/BodyInv.lean), taken after the first
switch. And the equation of `core_own` is stated with `BehindFirst` in the place of that hypothesis
(`core_inv`). A fact on the text's own run, on the side of completeness, and then the same equation
of two texts' laws. No property is claimed, and it is no sentence on a simulator. p, s, next, rest,
l, tB, P₀, hide, colR, colF, D, dep, n and asks are free parameters.

In the list: the test's stages (`Fmt.M1.Stage`) are s, next and the list rest. Every stage but the
last is a fold and then a switch into the next stage. The text is `restText` (Sim/Text.lean): all
that a prover shows from the first switch on. The text at rows 0 with one item laid anew is
`zeroText` (Sim/Sims.lean). P₀ (`PS`) is the prover's state at the first stage: its rows. Coins by
number are a function c from ℕ to the extension field. `coinsOf`
(Johnson/Desc/ProofFile/Honest/K12/Coins.lean) reads the random values that the text takes
(`BCoins`) from c and from hide, the first fold's coefficients. `OwnCs s (next :: rest)`
(Sim/CoreOwn.lean) is the type of the coins that the second part takes: as many as `restPart`
(Johnson/Desc/ProofFile/Honest/K12/Parts.lean) takes at these stages. `(stretchOf c).e` gives such
coins by number, 0 beyond the count. D gives the sampled challenges by the round's number.

  `core_inv`: the equation of `core_own`: over the second part's own numbered coins, sampled
    uniformly: what is shown of a proximity test's text from the first switch on at given rows, and
    what is shown of the text at rows 0 with one item laid anew, have one law. In Lean: over
    `Prob.unif (OwnCs s (next :: rest))`, `PMF.map` of `realOwn` (the left side) is `PMF.map` of
    `zeroOwn` (the right side; both Sim/CoreOwn.lean), each at `(stretchOf c).e`. `BehindFirst` at
    every coin is in the place of the hypothesis of `core_own` on the last claim
  `endOk_of_body`: where each stage from next on fits the next (`FitAll next rest`), `BehindFirst`
    at c gives `EndOk` at c, by the second of its two alternatives: the claim that is left at the
    last stage is true on the last message
  `BehindFirst`: a definition: `BodyInv` at `PlanAll p` (Johnson/Prover/Link/BodyCloseB.lean),
    before the stage next, at coins by number, and at the two states and the column that the first
    stage leaves
  `ownAsks`: for each round from the first switch on: of the tree that it sends, just the positions
    at which that tree is opened. A definition, for n rounds, by `openedTr` (Sim/CoreText.lean)
  `ownAsks_in`: `ownAsks` meets the hypothesis `hasks` of `core_inv` and of `core_own`

By what. `endOk_of_body`: `inv_end` takes `BodyInv` on to the last stage, and `claimTrue_of_inv`
gives the claim there (both Johnson/LinkSim/AtText/SeamClaim.lean; they are called); `claim_iff`
(Sim/CoreOwn.lean) and `stagesEnd_eq` (Sim/CoreText.lean) bring it into the form of `EndOk`.
`core_inv`: `core_own`, at `endOk_of_body` and `fitAll_of_fits` (Sim/CoreText.lean). `ownAsks_in`:
by unfolding.

Hypotheses. `core_inv` has five.
- `hF`: `FitsBody D (next :: rest) s 1` (Johnson/LinkSim/AtText/SpecShift.lean): each stage fits the
  next; no list of sampled positions is longer than a row's tail; the packing has room; the last
  stage has h = g = 0
- `hlow`: h ≤ k at every stage from next on
- `hcol`: colR and colF agree at the positions of `openedAt D (next :: rest) s 1`
  (Johnson/LinkSim/AtText/SpecStage.lean)
- `hbody`: `BehindFirst` at `(stretchOf c).e`, for every c of `OwnCs s (next :: rest)`
- `hasks`: for every i, each position in the first list of asks at i is among
  `openedTr D (next :: rest) s 1` at the round number 1 + (h + g) + i, with h and g those of
  `sgOf s`

Limits.
- On the right side the rows and the first fold's coefficients still stand, through the verifier's
  state behind the first fold alone (`entryOf`, Sim/CoreLaw.lean): a function of the state tB behind
  the batching and of the first fold's rounds as they are shown.
- The invariant is asked at every coin.
- `BehindFirst` is proved at no parameters in this file.
- `BehindFirst` can hold only where `p.nums.ownMask = false`: `PlanAll` has `PlanFrom`
  (Johnson/Prover/Link/FormStepPlan.lean), which has that clause at every stage. So at a place whose
  first fold sends its own table (`p.nums.ownMask = true`) `BehindFirst` is false at every coin,
  `hbody` fails, and `core_inv` is vacuous. The other limits on where `BodyInv` can hold are in the
  head of its file.
- `BehindFirst` holds further hypotheses on the plan and on the challenges' form, inside its
  definition. `PlanFrom` has `p.nums.stages.drop 1 = next :: rest`, and `Dealt`
  (Johnson/Desc/K12/OpenLaws.lean) at `l.drop (s.k + 3)` and the lists of trees of `p.nums`;
  `PlanAll` has `SortsFrom` (Johnson/Prover/Link/BodySorts.lean) at `l.drop (s.k + 3)`, next and
  rest; `BodyInv` has `FitFrom D` (Johnson/Prover/Link/BodyFit.lean) at `l.drop (s.k + 3)`, from
  round number 1 + (h + g) + 3 on. So `hbody` binds p, l and D to next :: rest, though each is a
  free parameter of `core_inv`.
- `EndOk` holds by a default too where the last stage's first round sampled no element, and it reads
  the claim by a definition that has a default: see the limits in the head of Sim/CoreOwn.lean.
- The five hypotheses of `core_inv` have no values that meet them together in the library yet, and
  no file in the library shows that the two sides differ.
- The other limits are `core_own`'s. Nothing on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.CoreOwn
import Johnson.LinkSim.AtText.SeamClaim
import Johnson.Desc.K12.Honest.FirstYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (FitsBody openedAt)
open OnBytes.LinkSim.Seam (inv_end claimTrue_of_inv)

attribute [local instance] csNonempty

section Body
variable (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (tB : T12)
  (P₀ : PS) (hide : ℕ → GE) (colR colF : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) (dep : ℕ → Option ℕ)
  (n : ℕ) (asks : List (List (List ℕ)))

/-- `BodyInv` (Johnson/Prover/Link/BodyInv.lean) at `PlanAll p`, before the stage next, which has
the number 1, at the random values that `coinsOf` reads from hide and from the coins c by number.
Its other arguments are what the first stage leaves, from the state tB, the rows P₀ and one tree of
depth `(sgOf s).C.a` with the column colR: the declared rounds from number s.k + 3 on; the number of
that stage's first round; the verifier's state after the first switch and the batching that follows
it (`t3At`); the prover's state after the switch (`qAt`; both
Johnson/Desc/K12/Honest/FirstYes.lean); the column of the tree that the switch sends (`aCol`,
Johnson/Desc/K12/Honest/Stages.lean). It can hold only where `p.nums.ownMask = false` and
`p.nums.stages.drop 1 = next :: rest`: see the limits in the head of this file. -/
def BehindFirst (c : ℕ → GE) : Prop :=
  BodyInv p (coinsOf (s :: next :: rest) hide c) (PlanAll p) D rest 1 next (l.drop (s.k + 3))
    (1 + ((sgOf s).h + (sgOf s).g) + 3)
    (t3At p (coinsOf (s :: next :: rest) hide c) rest 0 s next l 1 tB P₀ [((sgOf s).C.a, colR)] D)
    (qAt (coinsOf (s :: next :: rest) hide c) rest 0 s next 1 P₀ D)
    (aCol rest.isEmpty next (qAt (coinsOf (s :: next :: rest) hide c) rest 0 s next 1 P₀ D))

/-- The hypothesis of `core_own` on the last claim (`EndOk`, Sim/CoreOwn.lean) follows from
`BehindFirst`, where each stage from next on fits the next. The proof gives the second alternative
of `EndOk`: the claim is true. -/
theorem endOk_of_body (hf : FitAll next rest) (c : ℕ → GE)
    (h : BehindFirst p s next rest l tB P₀ hide colR D c) :
    EndOk p s next rest l tB P₀ hide colR D c := by
  have h1 := (claim_iff p _).1 (claimTrue_of_inv p _ D _ (inv_end p _ D _ _ _ _ _ _ _ _ h))
  rw [← stagesEnd_eq p _ rest 1 next _ _ _ _ _ D hf] at h1
  exact Or.inr h1

/-- For each of n rounds from the first switch on: of the tree that it sends, just the positions at
which that tree is opened. These are `openedTr`'s (Sim/CoreText.lean). -/
def ownAsks : List (List (List ℕ)) :=
  (List.range n).map fun i =>
    [openedTr D (next :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + i)]

theorem ownAsks_in (i : ℕ) (q : ℕ)
    (h : q ∈ ((((ownAsks s next rest D n)[i]?).getD [])[0]?).getD []) :
    q ∈ openedTr D (next :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + i) := by
  unfold ownAsks at h
  by_cases hi : i < n
  · simpa [List.getElem?_map, List.getElem?_range hi] using h
  · have e : (List.range n)[i]? = none := by
      rw [List.getElem?_eq_none]
      simpa using hi
    simp [List.getElem?_map, e] at h

variable (hF : FitsBody D (next :: rest) s 1) (hlow : ∀ st ∈ next :: rest, st.h ≤ st.k)
  (hcol : ∀ x ∈ Fmt.listOf (openedAt D (next :: rest) s 1), colR x = colF x)
  (hbody : ∀ c : OwnCs s (next :: rest),
    BehindFirst p s next rest l tB P₀ hide colR D (stretchOf c).e)
  (hasks : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
    q ∈ openedTr D (next :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + i))

include hF hlow hcol hbody hasks in
/-- **The equation of `core_own` (Sim/CoreOwn.lean), from `BehindFirst` at every coin.** `hbody` is
in the place of the hypothesis `hcl` of `core_own`, which is `EndOk` at every coin; the other four
hypotheses are those of `core_own`. No property is claimed, and it is no sentence on a simulator. -/
theorem core_inv :
    PMF.map (fun c : OwnCs s (next :: rest) =>
        realOwn p s next rest l tB P₀ hide colR D dep n asks (stretchOf c).e)
        (Prob.unif (OwnCs s (next :: rest))) =
      PMF.map (fun c : OwnCs s (next :: rest) =>
        zeroOwn p s next rest l tB P₀ hide colF D dep n asks (stretchOf c).e)
        (Prob.unif (OwnCs s (next :: rest))) :=
  core_own p s next rest l tB P₀ hide colR colF D dep n asks hF hlow hcol
    (fun c => endOk_of_body p s next rest l tB P₀ hide colR D (fitAll_of_fits _ _ _ hF).2
      (stretchOf c).e (hbody c)) hasks

end Body

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.endOk_of_body
#print axioms ProofFile.Honest.K12.ownAsks_in
#print axioms ProofFile.Honest.K12.core_inv
#print axioms ProofFile.Honest.K12.BehindFirst
#print axioms ProofFile.Honest.K12.ownAsks
