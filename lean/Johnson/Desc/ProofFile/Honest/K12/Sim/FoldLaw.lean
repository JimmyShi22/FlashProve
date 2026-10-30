-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FoldLaw.lean: over uniform coefficients of its hiding
polynomial, what a fold's rounds show is 2k + 1 uniform field elements, laid in the rounds' order:
at every claim, every message and all challenges. A theorem on a text: the definition `foldShown`
(Johnson/Desc/K12/Honest/Fold.lean). `fold_law` has no hypothesis and holds at every stage.
Sim/ExactFirst.lean calls `fold_law`, `shown_prefix` and `foldShown_shown`;
Sim/ExactFirstOwnLaw.lean calls `foldVals_inj`, `hideAt_inj`, `showRV_congr`, `valsOf_fst` and
`valsOf_snd`. Definitions and theorems.

In the list: a fold is a step of the proximity test at a stage s (`Sg`, OnBytes/Slice/Stage.lean). k
is s.h + s.g, the number of the stage's row variables; in an entry without s it is any number. v:
the claim's coefficients. μ: the stage's message. W: the hiding polynomial's coefficients; their
names (`HIdx`, Cb/Ld/LdHide.lean) have the numbers below 2k + 1 (`wNo`,
Johnson/Prover/Link/LinkCoinNo.lean). D: the challenges, by the round's number.
`foldShown s v μ W D` is a list of rounds (`Fmt.RoundView`): the first has the hiding polynomial's sum
(`hMu`, LdHide.lean), each of the k others the coefficients 0 and 2 of one round polynomial
(`foldPoly`, Fold.lean). A text is a Lean term that computes what a prover sends; in `shown_prefix`
its output is a `BOut` (Johnson/Prover/Link/BodyAll.lean), whose field `rs` lists the rounds.
`Shown`, in the frame (Johnson/Desc/ProofFile/Honest/Frame.lean), is what is shown of one round: the
items in the clear and, for each root, a list of columns. Coins are a `Cs d` (the frame), whose type
states their count d (`Due`): f elements of the base field and e of the extension field.
`stretchOf c` (Johnson/Desc/ProofFile/Honest/K12/Coins.lean) gives them by number, and 0 beyond the
count. `hideAt k x` (Coins.lean) takes the coefficients W from numbered values x.

  `fold_law`: the theorem. At every s, v, μ and D two distributions are equal, both over uniform c
    of the type `Cs ⟨0, 2 * k + 1⟩`: that of `laidAs k` at the fold's values (`foldVals`) where W is
    `hideAt k (stretchOf c).e`, and that of `laidAs k (stretchOf c).e`
  `foldShown_shown`, `showRV_shown`: the fold's rounds are shown as `laidAs` lays its values. In
    Lean: `showOne`, mapped over a round without an item followed by `foldShown s v μ W D`, gives
    `laidAs k (foldVals s v μ D W)`; mapped over `showRV k q D` (Johnson/Prover/Link/FoldSay.lean),
    it gives, for each i below k, the two elements of `pairAt k q i` and no list of columns
  `foldVals_inj`: the values fix the coefficients. If `foldVals s v μ D W` and `foldVals s v μ D W'`
    agree at every number below 2k + 1, then W = W'
  `hideAt_inj`: the coefficients fix the coins below 2k + 1. If `hideAt k c = hideAt k c'`, then c
    and c' agree at every number below 2k + 1
  `reLay k F c`: a definition: coins ↦ values, on coins of the type `Cs ⟨0, 2 * k + 1⟩`: element
    number i of the extension field becomes `F (stretchOf c).e i`
  `reLay_at`: at every number n below 2k + 1, `(stretchOf (reLay k F c)).e n` is
    `F (stretchOf c).e n`
  `reLay_bij`: where F x is `foldVals s v μ D (hideAt k x)`, `reLay k F` is a bijection
  `csSome`: a local instance: the type `Cs d` is not empty
  `laidAs k x`, `laidAs_congr`: 2k + 1 values laid as a fold's rounds show them, behind a round that
    shows nothing; it reads the values below 2k + 1. In Lean: `laidAs k x` is a definition: a
    `Shown` without an item; one with x 0; then, for each i below k, one with x (1 + 2 i) and
    x (2 + 2 i); none has a list of columns. `laidAs_congr`: x and y that agree at every number
    below 2k + 1 give the same list
  `foldVals s v μ D W`: a definition: a fold's 2k + 1 values: `valsOf k` at the sum of W (`hMu`) and
    at `foldPoly s v μ W`, with the challenges that `drawnE` (FoldSay.lean) reads off D
  `valsOf k sum q n`, `valsOf_fst`, `valsOf_snd`: a definition: the values by number: at 0 the sum;
    by the two theorems, at 1 + 2 i the first and at 2 + 2 i the second element of `pairAt k q i`
  `pairAt k q i`: a definition: the coefficients 0 and 2 of round polynomial number i of q; (0, 0)
    where i is not below k
  `showRV_congr`: if `pairAt k q` and `pairAt k q'` agree at every number below k, then
    `showRV k q D = showRV k q' D`
  `showOne`, `shown_prefix`, `showOne_one`, `showOne_two`: a round as it is shown where it sends no
    tree; the first rounds of a text's output, where none of them sends a tree, are shown so; at one
    and at two elements. In Lean: `showOne r` has the items of r but the roots (`saidOf`,
    Johnson/Desc/ProofFile/Honest/K12/Parts.lean), written by `Said.got` (the frame), and no list of
    columns. `shown_prefix`: if `O.rs` begins with the list A and `dep` is `none` below `A.length`,
    then `shownFrom O dep A.length asks` (Sim/Sims.lean) is `A.map showOne`

By what. What the rounds show is a list laid of 2k + 1 values: the polynomial's sum, and each round
polynomial's coefficients 0 and 2. These values determine the coefficients: `foldVals_inj` calls
`foldRV_inj` (Johnson/LinkSim/AtText/FoldInjAt.lean), and `foldRV` (FoldSay.lean) is `foldShown` by
unfolding (stated as `foldRV_eq`, Fold.lean). Every number below 2k + 1 is the number of a
coefficient's name (`wNo_onto`, LinkCoinNo.lean), and the coefficient of `hideAt k c` at a name is c
at the name's number (`hideAt_eq`, Sim/Bridge.lean): that gives `hideAt_inj`. So "coins ↦ values" is
a one-to-one map of a finite type into itself: it is onto, and carries the uniform law to itself.
The first step is `Finite.injective_iff_bijective` (Mathlib), in `reLay_bij`; the second is
`Prob.map_unif_of_bijective` (Prob/Linear.lean), in `fold_law`.

Limits.
- The claim's coefficients, the message and the challenges are fixed, and hang on no coin of the
  polynomial.
- It speaks of these rounds alone: the same coefficients, packed into a table that is sent and
  opened elsewhere, are not spoken of.
- `fold_law` is stated of `laidAs` at `foldVals`. `foldShown_shown` ties these to `foldShown`,
  through `showOne`. No job, part or play of the frame is named in this file.
- What `fold_law` samples is c of the type `Cs ⟨0, 2 * k + 1⟩`, and the coefficients are
  `hideAt k (stretchOf c).e`. That this map reaches every W is not stated in this file.
- At the level of oracle messages: no root, salt or hash.
- No property of a protocol is claimed. Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Bridge
import Johnson.Desc.ProofFile.Honest.K12.Sim.Sims
import Johnson.LinkSim.AtText.FoldInjAt
import Prob.Linear

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open OnBytes.LinkSim.AtText (foldRV_inj)

/-! ## 1 Rounds that send no tree, as they are shown -/

/-- A round as it is shown where it sends no tree. It has the round's items but the roots
(`saidOf`), written by `Said.got`, and no list of columns. -/
def showOne (r : Fmt.RoundView) : Shown := ⟨(r.vals.filterMap saidOf).map Said.got, []⟩

/-- The first rounds of a text's output, where none of them sends a tree. If `O.rs` begins with A
and `dep` is `none` below `A.length`, then `shownFrom` at these rounds is `A.map showOne`, at every
`asks`. -/
theorem shown_prefix (O : BOut) (A Bs : List Fmt.RoundView) (hO : O.rs = A ++ Bs) (dep : ℕ → Option ℕ)
    (hdep : ∀ i, i < A.length → dep i = none) (asks : List (List (List ℕ))) :
    shownFrom O dep A.length asks = A.map showOne := by
  unfold shownFrom
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < A.length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [hdep i hi]
  unfold shownAs sendingOf showOne
  simp only [hO, List.getElem?_append_left hi, List.getElem?_eq_getElem hi, Option.map_some,
    Option.getD_some, Option.toList_none, List.map_nil, List.zipIdx_nil]

theorem showOne_one (a : GE) (d : Fmt.Drawn) : showOne ⟨[.e (ofE a)], d⟩ = ⟨[.e (ofE a)], []⟩ := by
  simp [showOne, saidOf, Said.got, toE_ofE]

theorem showOne_two (a b : GE) (d : Fmt.Drawn) :
    showOne ⟨[.e (ofE a), .e (ofE b)], d⟩ = ⟨[.e (ofE a), .e (ofE b)], []⟩ := by
  simp [showOne, saidOf, Said.got, toE_ofE]

/-! ## 2 The 2k + 1 values -/

/-- The coefficients 0 and 2 of the round polynomial number i; (0, 0) where i is not below k. -/
def pairAt : (k : ℕ) → (RIdx (sVars GE 2 k) → GE) → ℕ → GE × GE
  | 0, _, _ => (0, 0)
  | _ + 1, q, 0 => (q (Sum.inl (0 : Fin 3)), q (Sum.inl (2 : Fin 3)))
  | k + 1, q, i + 1 => pairAt k (fun x => q (Sum.inr x)) i

/-- The values by number: the sum; then, round by round, the coefficients 0 and 2. -/
def valsOf (k : ℕ) (sum : GE) (q : RIdx (sVars GE 2 k) → GE) (n : ℕ) : GE :=
  if n = 0 then sum
  else if (n - 1) % 2 = 0 then (pairAt k q ((n - 1) / 2)).1 else (pairAt k q ((n - 1) / 2)).2

theorem valsOf_fst (k : ℕ) (sum : GE) (q : RIdx (sVars GE 2 k) → GE) (i : ℕ) :
    valsOf k sum q (1 + 2 * i) = (pairAt k q i).1 := by
  unfold valsOf
  rw [if_neg (by omega), if_pos (by omega)]
  congr 2
  omega

theorem valsOf_snd (k : ℕ) (sum : GE) (q : RIdx (sVars GE 2 k) → GE) (i : ℕ) :
    valsOf k sum q (2 + 2 * i) = (pairAt k q i).2 := by
  unfold valsOf
  rw [if_neg (by omega), if_neg (by omega)]
  congr 2
  omega

/-- 2k + 1 values laid as a fold's rounds show them, behind a round that shows nothing. x is read at
0 and, for each i below k, at 1 + 2 i and 2 + 2 i. -/
def laidAs (k : ℕ) (x : ℕ → GE) : List Shown :=
  ⟨[], []⟩ :: ⟨[.e (ofE (x 0))], []⟩ ::
    (List.range k).map fun i => ⟨[.e (ofE (x (1 + 2 * i))), .e (ofE (x (2 + 2 * i)))], []⟩

theorem laidAs_congr (k : ℕ) (x y : ℕ → GE) (h : ∀ n, n < 2 * k + 1 → x n = y n) :
    laidAs k x = laidAs k y := by
  unfold laidAs
  rw [h 0 (by omega)]
  refine congrArg _ (congrArg _ (List.map_congr_left fun i hi => ?_))
  have hi' := List.mem_range.1 hi
  rw [h (1 + 2 * i) (by omega), h (2 + 2 * i) (by omega)]

theorem showRV_shown : ∀ (k : ℕ) (q : RIdx (sVars GE 2 k) → GE) (D : ℕ → Fmt.Drawn),
    (showRV k q D).map showOne =
      (List.range k).map fun i => ⟨[.e (ofE (pairAt k q i).1), .e (ofE (pairAt k q i).2)], []⟩
  | 0, _, _ => rfl
  | k + 1, q, D => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show showOne ⟨[.e (ofE (q (Sum.inl (0 : Fin 3)))), .e (ofE (q (Sum.inl (2 : Fin 3))))], D 0⟩ ::
      (showRV k (fun i => q (Sum.inr i)) fun n => D (n + 1)).map showOne = _
    rw [showOne_two, showRV_shown k]
    rfl

theorem showRV_congr : ∀ (k : ℕ) (q q' : RIdx (sVars GE 2 k) → GE) (D : ℕ → Fmt.Drawn),
    (∀ i, i < k → pairAt k q i = pairAt k q' i) → showRV k q D = showRV k q' D
  | 0, _, _, _, _ => rfl
  | k + 1, q, q', D, h => by
    have h0 : (q (Sum.inl (0 : Fin 3)), q (Sum.inl (2 : Fin 3))) =
        (q' (Sum.inl (0 : Fin 3)), q' (Sum.inl (2 : Fin 3))) := h 0 (by omega)
    show (⟨[.e (ofE (q (Sum.inl (0 : Fin 3)))), .e (ofE (q (Sum.inl (2 : Fin 3))))], D 0⟩ :
        Fmt.RoundView) :: showRV k (fun i => q (Sum.inr i)) (fun n => D (n + 1)) =
      ⟨[.e (ofE (q' (Sum.inl (0 : Fin 3)))), .e (ofE (q' (Sum.inl (2 : Fin 3))))], D 0⟩ ::
        showRV k (fun i => q' (Sum.inr i)) fun n => D (n + 1)
    rw [(Prod.mk.inj h0).1, (Prod.mk.inj h0).2,
      showRV_congr k _ (fun i => q' (Sum.inr i)) _ fun i hi => h (i + 1) (by omega)]

section Fold
variable (s : Sg) (v μ : s.cIn.J → GE) (D : ℕ → Fmt.Drawn)

/-- A fold's 2k + 1 values, where k is s.h + s.g: `valsOf` at the sum of W (`hMu`) and at the round
polynomials `foldPoly`, with the challenges that `drawnE` reads off D. -/
def foldVals (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) : ℕ → GE :=
  valsOf (s.h + s.g) (hMu (sVars GE 2 (s.h + s.g)) W)
    (foldPoly s v μ W (Johnson.Prover.Link.drawnE (D 0))
      (ptK (s.h + s.g) fun n => Johnson.Prover.Link.drawnE (D (n + 1))))

/-- The fold's rounds, behind a round that shows nothing, are shown as its values are laid. -/
theorem foldShown_shown (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (d : Fmt.Drawn) :
    ((⟨[], d⟩ : Fmt.RoundView) :: foldShown s v μ W D).map showOne =
      laidAs (s.h + s.g) (foldVals s v μ D W) := by
  unfold foldShown laidAs
  rw [List.map_cons, List.map_cons, showOne_one, showRV_shown]
  refine congrArg₂ _ rfl (congrArg₂ _ rfl (List.map_congr_left fun i _ => ?_))
  unfold foldVals
  rw [valsOf_fst, valsOf_snd]

/-- **The values fix the coefficients.** -/
theorem foldVals_inj (W W' : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (h : ∀ n, n < 2 * (s.h + s.g) + 1 → foldVals s v μ D W n = foldVals s v μ D W' n) : W = W' := by
  refine foldRV_inj s v μ W W' D ?_
  show foldShown s v μ W D = foldShown s v μ W' D
  unfold foldShown
  have h0 : hMu (sVars GE 2 (s.h + s.g)) W = hMu (sVars GE 2 (s.h + s.g)) W' := h 0 (by omega)
  rw [h0]
  refine congrArg _ (showRV_congr _ _ _ _ fun i hi => ?_)
  have h1 := h (1 + 2 * i) (by omega)
  have h2 := h (2 + 2 * i) (by omega)
  unfold foldVals at h1 h2
  rw [valsOf_fst, valsOf_fst] at h1
  rw [valsOf_snd, valsOf_snd] at h2
  exact Prod.ext h1 h2

end Fold

/-- The coefficients fix the coins below 2k + 1. -/
theorem hideAt_inj (k : ℕ) (c c' : ℕ → GE) (h : hideAt k c = hideAt k c') (n : ℕ)
    (hn : n < 2 * k + 1) : c n = c' n := by
  obtain ⟨x, hx⟩ := wNo_onto k n hn
  have := congrFun h x
  rwa [hideAt_eq, hideAt_eq, hx] at this

/-! ## 3 The theorem -/

/-- The type `Cs d` of coins is not empty. A local instance, made of the frame's `default`. -/
local instance csSome (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-- Coins ↦ values, on coins of the type `Cs ⟨0, 2 * k + 1⟩`: element number i of the extension
field becomes `F (stretchOf c).e i`. -/
def reLay (k : ℕ) (F : (ℕ → GE) → ℕ → GE) (c : Cs ⟨0, 2 * k + 1⟩) : Cs ⟨0, 2 * k + 1⟩ :=
  ⟨c.f, fun i => F (stretchOf c).e i.val⟩

theorem reLay_at (k : ℕ) (F : (ℕ → GE) → ℕ → GE) (c : Cs ⟨0, 2 * k + 1⟩) (n : ℕ)
    (hn : n < 2 * k + 1) : (stretchOf (reLay k F c)).e n = F (stretchOf c).e n := by
  show (if h : n < 2 * k + 1 then (reLay k F c).e ⟨n, h⟩ else 0) = _
  rw [dif_pos hn]
  rfl

theorem reLay_bij (s : Sg) (v μ : s.cIn.J → GE) (D : ℕ → Fmt.Drawn) :
    Function.Bijective (reLay (s.h + s.g) fun x => foldVals s v μ D (hideAt (s.h + s.g) x)) := by
  refine Finite.injective_iff_bijective.1 fun c c' h => ?_
  have hv : ∀ n, n < 2 * (s.h + s.g) + 1 →
      foldVals s v μ D (hideAt (s.h + s.g) (stretchOf c).e) n =
        foldVals s v μ D (hideAt (s.h + s.g) (stretchOf c').e) n := fun n hn => by
    rw [← reLay_at _ (fun x => foldVals s v μ D (hideAt (s.h + s.g) x)) c n hn, h,
      reLay_at _ _ _ _ hn]
  have hW := foldVals_inj s v μ D _ _ hv
  have hf : c.f = c'.f := by
    have := congrArg Cs.f h
    exact this
  have he : c.e = c'.e := funext fun i => by
    have := hideAt_inj _ _ _ hW i.val i.isLt
    have e1 : ∀ y : Cs ⟨0, 2 * (s.h + s.g) + 1⟩, (stretchOf y).e i.val = y.e i := fun y => by
      show (if h : i.val < 2 * (s.h + s.g) + 1 then y.e ⟨i.val, h⟩ else 0) = _
      rw [dif_pos i.isLt]
    rwa [e1, e1] at this
  cases c
  cases c'
  simp only at hf he
  rw [hf, he]

/-- **The law: what a fold's rounds show, over uniform coefficients, is 2k + 1 uniform elements,
laid in the rounds' order.** In Lean, with k for s.h + s.g: over uniform c of the type
`Cs ⟨0, 2 * k + 1⟩`, `laidAs k` at the fold's values where W is `hideAt k (stretchOf c).e` has the
distribution of `laidAs k (stretchOf c).e`. -/
theorem fold_law (s : Sg) (v μ : s.cIn.J → GE) (D : ℕ → Fmt.Drawn) :
    (Prob.unif (Cs ⟨0, 2 * (s.h + s.g) + 1⟩)).map (fun c =>
        laidAs (s.h + s.g) (foldVals s v μ D (hideAt (s.h + s.g) (stretchOf c).e))) =
      (Prob.unif (Cs ⟨0, 2 * (s.h + s.g) + 1⟩)).map fun c =>
        laidAs (s.h + s.g) (stretchOf c).e := by
  have e : (fun c : Cs ⟨0, 2 * (s.h + s.g) + 1⟩ =>
      laidAs (s.h + s.g) (foldVals s v μ D (hideAt (s.h + s.g) (stretchOf c).e))) =
      (fun c => laidAs (s.h + s.g) (stretchOf c).e) ∘
        reLay (s.h + s.g) fun x => foldVals s v μ D (hideAt (s.h + s.g) x) := by
    funext c
    exact (laidAs_congr _
      (stretchOf (reLay (s.h + s.g) (fun x => foldVals s v μ D (hideAt (s.h + s.g) x)) c)).e
      (foldVals s v μ D (hideAt (s.h + s.g) (stretchOf c).e)) fun n hn =>
        reLay_at _ (fun x => foldVals s v μ D (hideAt (s.h + s.g) x)) c n hn).symm
  rw [e, ← PMF.map_comp, Prob.map_unif_of_bijective (reLay_bij s v μ D)]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.shown_prefix
#print axioms ProofFile.Honest.K12.showOne_one
#print axioms ProofFile.Honest.K12.showOne_two
#print axioms ProofFile.Honest.K12.valsOf_fst
#print axioms ProofFile.Honest.K12.valsOf_snd
#print axioms ProofFile.Honest.K12.laidAs_congr
#print axioms ProofFile.Honest.K12.showRV_shown
#print axioms ProofFile.Honest.K12.showRV_congr
#print axioms ProofFile.Honest.K12.foldShown_shown
#print axioms ProofFile.Honest.K12.foldVals_inj
#print axioms ProofFile.Honest.K12.hideAt_inj
#print axioms ProofFile.Honest.K12.reLay_at
#print axioms ProofFile.Honest.K12.reLay_bij
#print axioms ProofFile.Honest.K12.fold_law
#print axioms ProofFile.Honest.K12.showOne
#print axioms ProofFile.Honest.K12.pairAt
#print axioms ProofFile.Honest.K12.valsOf
#print axioms ProofFile.Honest.K12.laidAs
#print axioms ProofFile.Honest.K12.foldVals
#print axioms ProofFile.Honest.K12.csSome
#print axioms ProofFile.Honest.K12.reLay
