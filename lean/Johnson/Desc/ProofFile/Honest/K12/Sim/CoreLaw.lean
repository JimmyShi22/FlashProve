-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/CoreLaw.lean: over a finite type of a proximity test's random
values from the first switch on, sampled uniformly: what is shown of the text at given rows and what
is shown of the text at rows 0, with one item laid anew, have one law. An equation of two texts'
laws. No property is claimed, and it is no sentence on a simulator: the state tB, the first fold's
coefficients W0 and the column in front colF are letters: nothing here says that they are made of
public things. Definitions and theorems. The two main theorems hold at all numbers of a place p
(`P12`), at every list of two or more stages s :: next :: rest, and at all values of the other
parameters that meet the four hypotheses below. `core_own` (Sim/CoreOwn.lean) calls `core_body`.

In this head: a law is a distribution, a letter is a free parameter, a premise is a hypothesis, and
who pays a premise is who proves it. In front of means before and behind means after, in the order
of the rounds. Laid means built or placed. A member of the finite type is an element of it. A text
is a Lean term with a value in `BOut` (Johnson/Prover/Link/BodyAll.lean): the rounds, for each round
the written column of the tree that it sends, and groups of columns. The text at given rows is
`restText` (Sim/Text.lean). The text at rows 0 with one item laid anew is `zeroTextK`
(Sim/Sims.lean): `restText` at rows 0, with the last round but one replaced by a round whose only
item is `tauSim`. Rows are a prover's state at a stage (`PS`, Johnson/Prover/Link/BodyState.lean);
the given rows are P₀; at rows 0 every entry of the state is 0 (`zeroPS`, Sim/Sims.lean). What is
shown is `shownFrom` (Sim/Sims.lean): of each of the first n rounds of a text's output the round's
items and, where dep gives a depth at the round's number, the columns of the round's tree at the
positions in the first list of asks at that number. The left side is `realView`, the right side
`zeroView`. The texts read their random values from a value of `BCoins` (BodyAll.lean): functions on
all natural numbers, in the fields `W` (the folds' coefficients, by the fold's number from 0), `new`
and `fr`. The finite type is `BodyK GE s (next :: rest)` (Johnson/Prover/Link/LinkCoin.lean): for
each switch, finite functions at the sizes of the message that the switch sends and of what goes
with it. Sections 1 and 2 are at `BodyK GE s rest`, for every list rest. `LaidFrom s rest k 0 K`
(Johnson/LinkSim/AtText/CoinsPlaces.lean) says that `K.fr`, `K.new` and, from fold number 1 on,
`K.W` are the images of k under `bodyFr`, `bodyNew` and `bodyW` (LinkCoin.lean). The places are the
arguments inside the sizes: `InBody s rest 0 K` (Johnson/LinkSim/AtText/Places.lean) says that these
three are 0 outside them. tB has the type `T12` (Johnson/Desc/K12/Join.lean), the type of the
verifier's state inside a test. colR and colF, "the column in front", are free parameters in the
place of the written column of the tree that holds the first stage's rows, on the left and on the
right side. l: declared rounds with their oracle messages (`Laid`, Johnson/Desc/K12/Frame.lean). D:
the challenges by the round's number; the first fold's first round has the number 1. A reading round
is a round whose challenge samples positions.

  `core_body`: under the four hypotheses below: over `BodyK GE s (next :: rest)`, sampled uniformly
    (`Prob.unif`), `realView` and `zeroView` have the same distribution
  `core_upTo`: under the same hypotheses: the two are one up to a change of the coins that can be
    undone. In Lean: `UpToShift` (Johnson/LinkSim/UpTo.lean) at the sum `addBody`
    (Johnson/LinkSim/AtText/SpecCoins.lean)
  `realView`: a definition: what is shown of the text at the rows P₀. In Lean: `shownFrom` of
    `restText` at `layBody` of k, the state `entryOf`, the rows P₀ and one tree with the column colR
  `zeroView`: a definition: what is shown of the text at rows 0, with the one item laid anew. In
    Lean: `shownFrom` of `zeroTextK` at `layBody` of k, the state `entryOf` and one tree with the
    column colF
  `entryOf`: a definition: the verifier's state behind the first fold: from tB, over the text's own
    first fold's rounds at the rows P₀ and the coefficients W0. In Lean: `aRec1`
    (Johnson/Desc/K12/Honest/Stages.lean) at tB over `foldShown`
    (Johnson/Desc/K12/Honest/Fold.lean): the state that the description's fold returns, or tB where
    it rejects
  `layBody s rest W0 k`: a definition: the value of `BCoins` whose `W` is W0 at fold number 0 and
    `bodyW` of k at j for fold number j + 1, whose `new` is `bodyNew` of k and whose `fr` is
    `bodyFr` of k. `restText` and `zeroTextK` are the same at two values of `BCoins` that agree from
    fold number 1 on (`restText_congr`, Sim/Text.lean; `zeroTextK_congr`, Sim/CoreText.lean)
  `laid_lay`, `laid_unique`: `LaidFrom s rest k 0` holds of `layBody s rest W0 k`; if it holds of
    one K at k and at k', then k = k'
  `backOf`, `backOf_spec`: a definition: where `InBody s rest 0 K` holds, a k that `body_onto`
    gives; elsewhere some element of the finite type. Where `InBody s rest 0 K` holds,
    `LaidFrom s rest (backOf s rest K) 0 K`
  `lay_add`: where `LaidFrom s rest k' 0 K'`: `layBody` of the sum `addBody s rest k k'` agrees from
    fold number 1 on (`SameFrom 1`, Sim/Text.lean) with the sum `addB`
    (Johnson/LinkSim/AtText/Defs.lean) of `layBody` of k and K'
  `virt_add`: with the first fold's coefficients set by `virtK` (Sim/CoreText.lean), the two sides
    of `lay_add` are equal
  `bc_ext`: two values of `BCoins` with equal fields are equal
  `addPS_cancel`, `body_cancel`: `addPS` (Defs.lean) and `addBody` cancel on the right
  `bodyFintype`, `bodyNonempty`: the finite type is finite and not empty; local instances, in this
    file only

By what. The following, up to `UpToShift.law_eq`, are definitions and lemmas of Johnson/LinkSim/:
they are called, not proved anew. `shB` (AtText/ShiftDefs.lean): the shift of the random values.
`inBody_sh` (AtText/PlacesProof.lean): under `FitsBody` the shift is 0 outside the places.
`walkSame` (AtText/Induct.lean): computed along the other run, the shift is the same. `bodyW_add`,
`bodyFr_add`, `bodyNew_add` (AtText/CoinsAdd.lean): the three maps out of the finite type take a sum
to the sum. `body_inj` (CoinsAdd.lean) and `body_onto` (AtText/CoinsPlaces.lean): together the three
maps are one to one, and onto the values that are 0 outside the places. `UpToShift.law_eq`
(UpTo.lean): one law under a change that can be undone. What is shown under the change: `rest_view`
(Sim/CoreText.lean). `core_upTo` also calls `atStage_first` and `zeroTextK_congr`
(Sim/CoreText.lean); `addPS_cancel` calls `ps_ext` (AtText/State.lean); the two instances come from
`BodyK.finite` and `BodyK.nonempty` (LinkCoin.lean).

Hypotheses of `core_upTo` and `core_body`. hF: `FitsBody D (next :: rest) s 1`
(Johnson/LinkSim/AtText/SpecShift.lean): for every stage, the reading round that opens the tree with
the stage's rows samples no more positions, counted with repeats, than `C.r` and than `Z.r` of the
stage's sizes, the lengths of its rows' tails; at every stage but the last, h + 2 g + 1 is at most
`Z.l` and the stage fits the next (`CsFit`); the last stage has h = 0 and g = 0. hcol: colR and colF
agree at the positions that the first reading round samples, in the tree's range (`openedAt`,
Johnson/LinkSim/AtText/SpecStage.lean). hcl: at every k of the finite type, the element that the
last stage's first round samples is 0 (`LamZero`, Johnson/LinkSim/AtText/SpecShiftIn.lean), or the
claim that is left at the last stage is true at the prover's last message (`ClaimTrue`, Defs.lean);
both are read at `bodyEnd` (Johnson/Prover/Link/BodyEnd.lean) of the run from tB at the rows P₀, the
column colR and `layBody` of k. hasks: for every i, each position in the first list of asks at i is
among those at which the tree that round number i from the first switch on sends is opened
(`openedTr`, Sim/CoreText.lean).

Limits.
- On the right side the rows P₀ and the coefficients W0 still stand, through `entryOf` alone: the
  verifier's state behind the first fold, which is a function of tB and of the first fold's rounds
  as they are shown.
- The column colF is read just at the positions at which the premise makes it colR.
- How it stands to `Spec.core` (Sim/Spec.lean). No theorem says that it is an instance. It is
  narrower, or other, in these:
  (i) the state behind the first fold is the one that the description's fold leaves from a letter tB
      over the text's own first fold's rounds;
  (ii) one tree in front, of the first stage's depth;
  (iii) the positions asked of a tree are among those that the next reading round samples, and
      these, counted with repeats, are no more than a row's tail is long (`FitsBody`): `budRest`
      allows more, and counts different points;
  (iv) the coins are another finite type: `BodyK` (Johnson/Prover/Link/LinkCoin.lean), laid into the
      letters with written zeros outside the sizes; not the second part's own numbered coins
      (`coinsOf`, Johnson/Desc/ProofFile/Honest/K12/Coins.lean);
  (v) how many rounds are shown is a letter n, not the text's own count;
  (vi) `FitsBody`'s first clause holds the first reading round's positions against the first stage's
      tails, which are no rows of this text's own trees; and it asks h = g = 0 at the last stage:
      neither stands among `Spec.core`'s premises.
- The premise on the claim that is left at the real text's last stage is asked at every member of
  the finite type (or the last sampled element is 0). Nothing says who pays it.
- `LamZero` holds by a default too. It is `toE ((D o).elems.headD (0, 0, 0)) = 0` at the o of
  `bodyEnd`: where that round sampled no element, `headD` gives (0, 0, 0), `toE` of that is 0
  (`toE_zeroE`, OnBytes/Slice/Field.lean), and `LamZero` holds: it does not say that a 0 was
  sampled. `ClaimTrue` reads the claim by `claimEnd` (Defs.lean): where `stageAt` or `claimAt`
  gives `none`, that is the claim with no coefficients and the target (0, 0, 0). Nothing in this
  file tests for either case.
- That the four hypotheses hold together at any values is not shown in this file. They have no
  values that meet them together in the library yet, and no file in the library shows that the two
  sides differ.
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.CoreText
import Johnson.LinkSim.AtText.CoinsPlaces
import Johnson.LinkSim.UpTo

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim (UpToShift)
open OnBytes.LinkSim.AtText (zPS addPS addB shB AtStage FitsBody openedAt LamZero InBody LaidFrom
  inBody_sh body_onto body_inj addBody bodyW_add bodyFr_add bodyNew_add walkSame ps_ext)

/-! ## 1 From the finite type to `BCoins`, and back -/

/-- The value of `BCoins` that is built from an element k of the finite type: `W` is W0 at fold
number 0 and `bodyW` of k from fold number 1 on; `new` is `bodyNew` of k; `fr` is `bodyFr` of k. W0:
the first fold's coefficients, which are no part of it. -/
def layBody (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (W0 : ∀ σ : Sg, HIdx (sVars GE 2 (σ.h + σ.g)) → GE) (k : BodyK GE s rest) : BCoins where
  W := fun σ j =>
    match j with
    | 0 => W0 σ
    | j + 1 => bodyW s rest k σ j
  new := bodyNew s rest k
  fr := bodyFr s rest k

variable {s : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}

theorem laid_lay (W0 : ∀ σ : Sg, HIdx (sVars GE 2 (σ.h + σ.g)) → GE) (k : BodyK GE s rest) :
    LaidFrom s rest k 0 (layBody s rest W0 k) :=
  ⟨fun i => by rw [Nat.zero_add]; rfl, fun i => by rw [Nat.zero_add]; rfl, fun σ i => by
    rw [show 0 + 1 + i = i + 1 by omega]
    rfl⟩

theorem laid_unique {k k' : BodyK GE s rest} {K : BCoins} (h : LaidFrom s rest k 0 K)
    (h' : LaidFrom s rest k' 0 K) : k = k' :=
  body_inj s rest k k' (fun j => (h.1 j).symm.trans (h'.1 j))
    (fun j => (h.2.1 j).symm.trans (h'.2.1 j)) fun σ j => (h.2.2 σ j).symm.trans (h'.2.2 σ j)

open Classical in
/-- Where K is 0 outside the places (`InBody s rest 0 K`): an element k of the finite type with
`LaidFrom s rest k 0 K`, as `body_onto` gives it. Elsewhere: some element. -/
def backOf (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (K : BCoins) : BodyK GE s rest :=
  if h : InBody s rest 0 K then (body_onto s rest 0 K h).choose
  else (BodyK.nonempty (0 : GE) s rest).some

theorem backOf_spec {K : BCoins} (h : InBody s rest 0 K) :
    LaidFrom s rest (backOf s rest K) 0 K := by
  unfold backOf
  rw [dif_pos h]
  exact (body_onto s rest 0 K h).choose_spec

/-! ## 2 Small facts -/

theorem bc_ext {K K' : BCoins} (h1 : K.W = K'.W) (h2 : K.new = K'.new) (h3 : K.fr = K'.fr) :
    K = K' := by
  cases K
  cases K'
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- `layBody` of a sum agrees with the sum of `layBody` of k and K', from fold number 1 on. -/
theorem lay_add (W0 : ∀ σ : Sg, HIdx (sVars GE 2 (σ.h + σ.g)) → GE) (k k' : BodyK GE s rest)
    {K' : BCoins} (h : LaidFrom s rest k' 0 K') :
    SameFrom 1 (layBody s rest W0 (addBody s rest k k')) (addB (layBody s rest W0 k) K') where
  W := fun σ j hj => by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
    funext x
    have e := h.2.2 σ i
    rw [show 0 + 1 + i = 1 + i by omega] at e
    show (layBody s rest W0 (addBody s rest k k')).W σ (1 + i) x =
      (layBody s rest W0 k).W σ (1 + i) x + K'.W σ (1 + i) x
    rw [e, show 1 + i = i + 1 by omega]
    exact bodyW_add s rest k k' σ i x
  new := funext fun j => by
    have e := h.2.1 j
    rw [Nat.zero_add] at e
    show bodyNew s rest (addBody s rest k k') j = addPS (bodyNew s rest k j) (K'.new j)
    rw [e]
    exact bodyNew_add s rest k k' j
  fr := funext fun j => funext fun i => by
    have e := h.1 j
    rw [Nat.zero_add] at e
    show bodyFr s rest (addBody s rest k k') j i = bodyFr s rest k j i + K'.fr j i
    rw [e]
    exact bodyFr_add s rest k k' j i

/-- With the first fold's coefficients set by `virtK` (Sim/CoreText.lean), the two sides of
`lay_add` are equal. -/
theorem virt_add (W0 : ∀ σ : Sg, HIdx (sVars GE 2 (σ.h + σ.g)) → GE) (k k' : BodyK GE s rest)
    {K' : BCoins} (h : LaidFrom s rest k' 0 K') (tB : T12) (P₀ : PS) (D : ℕ → Fmt.Drawn) :
    virtK (layBody s rest W0 (addBody s rest k k')) (layBody s rest W0 (addBody s rest k k')) tB P₀
        D =
      virtK (addB (layBody s rest W0 k) K') (layBody s rest W0 k) tB P₀ D := by
  have hs := lay_add W0 k k' h
  refine bc_ext (funext fun σ => funext fun j => ?_) hs.new hs.fr
  cases j with
  | zero => rfl
  | succ j => exact hs.W σ (j + 1) (by omega)

theorem addPS_cancel {P Q R : PS} (h : addPS P R = addPS Q R) : P = Q :=
  ps_ext (funext fun i => add_right_cancel (congrFun (congrArg PS.tabM h) i))
    (funext fun i => add_right_cancel (congrFun (congrArg PS.tabZ h) i))
    (funext fun b => funext fun q => add_right_cancel (congrFun (congrFun (congrArg PS.tM h) b) q))
    (funext fun b => funext fun q => add_right_cancel (congrFun (congrFun (congrArg PS.tZ h) b) q))
    (funext fun b => funext fun q => add_right_cancel (congrFun (congrFun (congrArg PS.fM h) b) q))
    (funext fun b => funext fun q => add_right_cancel (congrFun (congrFun (congrArg PS.fT h) b) q))
    (funext fun i => add_right_cancel (congrFun (congrArg PS.sM h) i))
    (funext fun i => add_right_cancel (congrFun (congrArg PS.sT h) i))

theorem body_cancel (a b d : BodyK GE s rest) (h : addBody s rest a d = addBody s rest b d) :
    a = b :=
  body_inj s rest a b
    (fun j => funext fun i => add_right_cancel (b := bodyFr s rest d j i) (by
      rw [← bodyFr_add, ← bodyFr_add, h]))
    (fun j => addPS_cancel (R := bodyNew s rest d j) (by rw [← bodyNew_add, ← bodyNew_add, h]))
    fun σ j => funext fun x => add_right_cancel (b := bodyW s rest d σ j x) (by
      rw [← bodyW_add, ← bodyW_add, h])

/-! ## 3 The two views, and the statement -/

/-- The finite type is finite, by `BodyK.finite` (Johnson/Prover/Link/LinkCoin.lean). A local
instance, in this file only: the type is defined in another folder. -/
@[reducible] def bodyFintype (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) :
    Fintype (BodyK GE s rest) :=
  haveI := BodyK.finite (α := GE) s rest
  Fintype.ofFinite _

theorem bodyNonempty (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) : Nonempty (BodyK GE s rest) :=
  BodyK.nonempty 0 s rest

attribute [local instance] bodyFintype bodyNonempty

section Core
variable (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (tB : T12)
  (P₀ : PS) (W0 : ∀ σ : Sg, HIdx (sVars GE 2 (σ.h + σ.g)) → GE) (colR colF : ℕ → List UInt64)
  (D : ℕ → Fmt.Drawn) (dep : ℕ → Option ℕ) (n : ℕ) (asks : List (List (List ℕ)))

/-- The verifier's state behind the first fold: from tB, over the text's own first fold's rounds at
the rows P₀ and the coefficients W0. tB is a free parameter: nothing here says that it is the
verifier's state before the first fold. -/
def entryOf : T12 :=
  aRec1 p 0 s l tB (foldShown (sgOf s) (vecG (sgOf s) (rowOf tB)) (μOf (sgOf s) P₀) (W0 (sgOf s))
    fun i => D (1 + i))

/-- What is shown of the text at the rows P₀. -/
def realView (k : BodyK GE s (next :: rest)) : List Shown :=
  shownFrom (restText p (layBody s (next :: rest) W0 k) s next rest l 1 (entryOf p s l tB P₀ W0 D)
    P₀ [((sgOf s).C.a, colR)] D) dep n asks

/-- What is shown of the text at rows 0, with the one item laid anew. -/
def zeroView (k : BodyK GE s (next :: rest)) : List Shown :=
  shownFrom (zeroTextK p (layBody s (next :: rest) W0 k) s next rest l (entryOf p s l tB P₀ W0 D)
    [((sgOf s).C.a, colF)] D) dep n asks

variable (hF : FitsBody D (next :: rest) s 1)
  (hcol : ∀ x ∈ Fmt.listOf (openedAt D (next :: rest) s 1), colR x = colF x)
  (hcl : ∀ k : BodyK GE s (next :: rest),
    LamZero D (bodyEnd p (layBody s (next :: rest) W0 k) D (next :: rest) 0 s l 1 tB P₀ colR) ∨
      OnBytes.LinkSim.AtText.ClaimTrue p
        (bodyEnd p (layBody s (next :: rest) W0 k) D (next :: rest) 0 s l 1 tB P₀ colR))
  (hasks : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
    q ∈ openedTr D (next :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + i))

include hF hcol hcl hasks in
/-- **The two are one up to a change of the coins that can be undone.** -/
theorem core_upTo :
    UpToShift (addBody s (next :: rest)) (realView p s next rest l tB P₀ W0 colR D dep n asks)
      (zeroView p s next rest l tB P₀ W0 colF D dep n asks) := by
  refine ⟨fun k => backOf s (next :: rest)
      (shB p (layBody s (next :: rest) W0 k) D (next :: rest) 0 s l 1 tB P₀ colR P₀),
    fun k => backOf s (next :: rest)
      (shB p (virtK (layBody s (next :: rest) W0 k) (layBody s (next :: rest) W0 k) tB P₀ D) D
        (next :: rest) 0 s l 1 tB zPS colF P₀), fun k => ?_⟩
  have hb := backOf_spec (inBody_sh p (layBody s (next :: rest) W0 k) D (next :: rest) 0 s l 1 tB P₀
    colR P₀ hF)
  refine ⟨?_, ?_⟩
  · have hv := rest_view p s next rest l tB P₀ colR colF D (layBody s (next :: rest) W0 k) dep n
      asks hF hcol (hcl k) hasks
    unfold realView zeroView
    rw [zeroTextK_congr p (lay_add W0 k _ hb)]
    exact hv
  · show backOf _ _ _ = backOf _ _ _
    rw [virt_add W0 k _ hb tB P₀ D]
    exact congrArg _ (walkSame p D (next :: rest) 0 s l 1 tB _ _ P₀ zPS P₀ colR colF hF
      (atStage_first p s next rest l tB P₀ colR colF D _ hcol))

include hF hcol hcl hasks in
/-- **Over the finite type, sampled uniformly, the two views have the same distribution.**
An equation of two texts' laws. It is no sentence on a simulator. -/
theorem core_body :
    (Prob.unif (BodyK GE s (next :: rest))).map
        (realView p s next rest l tB P₀ W0 colR D dep n asks) =
      (Prob.unif (BodyK GE s (next :: rest))).map
        (zeroView p s next rest l tB P₀ W0 colF D dep n asks) :=
  UpToShift.law_eq body_cancel
    (core_upTo p s next rest l tB P₀ W0 colR colF D dep n asks hF hcol hcl hasks)

end Core

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.laid_lay
#print axioms ProofFile.Honest.K12.laid_unique
#print axioms ProofFile.Honest.K12.backOf_spec
#print axioms ProofFile.Honest.K12.bc_ext
#print axioms ProofFile.Honest.K12.lay_add
#print axioms ProofFile.Honest.K12.virt_add
#print axioms ProofFile.Honest.K12.addPS_cancel
#print axioms ProofFile.Honest.K12.body_cancel
#print axioms ProofFile.Honest.K12.bodyNonempty
#print axioms ProofFile.Honest.K12.core_upTo
#print axioms ProofFile.Honest.K12.core_body
#print axioms ProofFile.Honest.K12.layBody
#print axioms ProofFile.Honest.K12.backOf
#print axioms ProofFile.Honest.K12.bodyFintype
#print axioms ProofFile.Honest.K12.entryOf
#print axioms ProofFile.Honest.K12.realView
#print axioms ProofFile.Honest.K12.zeroView
