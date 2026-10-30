-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/MatrixAtBatch.lean: THE SMALLNESS TEST: THE MATRIX IN THE STATE IN FRONT OF A
SEGMENT's BATCHING IS THE ONE THAT THE ROUND OF THE DRAW HAS DRAWN, WITH THE PLACE's SIZES. LEMMAS;
NONE OF THE LIBRARY's GOALS. No prover stands in them; nothing on completeness, soundness or hiding.

The letters are those of an opening of the description (IM.Open). AT ALL 25 SEGMENTS, of all three
sorts, in the goals' scope: (l, i, n) runs over the written list `stretches`
(Johnson/P1K8R/WideAtSeat.lean): the draw's block is number 14 l + i + 2 of the flat list, n blocks
stand between it and the batching.
  `keeps4_wideM`   the reading "with the drawn matrix" reads none of the four fields that the lookup
      on the digits lays
  `k_of_list`   a matrix's number of columns off the list of these numbers
  `typed_of_means`   behind a yes of the draw's decision at a round whose matrix entries are those
      of a typed matrix β, at sizes that fit the place: `TypedAt`
      (Johnson/Desc/ProofFile/Honest/K8/FrontTyped.lean)
  `typed_of_wideM`   `TypedAt` reads that reading alone
  **`matrix_at_batch`**   from a yes of the seated draw's step, over the n blocks behind it: the
      state that they hand on holds data tl with `TypedAt sz β tl`: so `allLive tl` says no just if
      some column of β is all 0, and `cols tl` is the sizes' number of columns
  `reach_back`, `leaves_step`, `reach_stretch`   a reached state, one border back; over blocks that
      leave a reading
  **`matrix_at_reached`**   the same along "reached" (Johnson/Top/H0/Walk/Reach.lean): for a state s
      reached in front of a segment's batching there are a state reached in front of the draw's
      block and a step of that block from it at SOME round r, such that s holds `TypedAt sz β` for
      every typed matrix β whose entries r has drawn. (That s is reached from what that step returns
      is not a clause of it.)
By: SitsAt, sitsAt_open (Johnson/P1K8R/Sits.lean, OrderAtSeat.lean) · MeansAtS
(Johnson/Desc/First/K8/HearMeans.lean) · staysAt_open (WideAtSeat.lean) with foldLeaves ·
firstColumns_get (Johnson/Desc/First/K8/Law.lean).
Limits. That a written challenge of the draw's round gives the entries of a typed matrix, and with
which weight, is not said here. No sum over rounds. No number is evaluated.
-/
import Johnson.P1K8R.WideAtSeat
import Johnson.Desc.ProofFile.Honest.K8.FrontTyped
import Johnson.Desc.First.K8.Law
import Johnson.Desc.Sound.RunIsDecide
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8
open ProofFile.Honest.K8 (TypedAt allLive cols allLive_iff cols_eq)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

theorem keeps4_wideM : Keeps4 wideMOf := fun _ _ _ _ _ => rfl

/-- Column counts off the list of the matrices' numbers of columns. -/
theorem k_of_list (tl : HTailF2) (ks : List Nat) (h : tl.mats.toList.map (·.k) = ks) (i : Nat)
    (hi : i < ks.length) : (tl.mats.getD i {}).k = ks.getD i 0 := by
  subst h
  rw [List.length_map, Array.length_toList] at hi
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList, Array.getElem?_eq_getElem hi]
  rfl

/-- Behind a yes of the draw's decision. -/
theorem typed_of_means (p : K8.Par) (sz : Size) (β : Dr sz) (hf : Fits p sz) (s s' : S) (r : Fmt.RoundView)
    (hm : MeansAtS p s r s') (hr : r.drawn.trits.toArray = listOf β) :
    ∃ tl, s'.tl? = some tl ∧ TypedAt sz β tl := by
  obtain ⟨tl, ht, -, -, -, hNM, hk, -, htau, -, rfl⟩ := hm
  refine ⟨_, putTl_tl s tl _ ht, ⟨hr, htau.trans hf.tau.symm, hNM.trans hf.nm.symm,
    fun μ => firstColumns_get hf μ, fun μ => ?_⟩⟩
  have hμ : μ.val < p.ks.length := by
    rw [← hf.nm]
    exact μ.isLt
  show (tl.mats.getD μ.val {}).k = sz.k μ
  rw [k_of_list tl p.ks hk μ.val hμ, hf.k μ.val hμ]

/-- `TypedAt` reads the reading "with the drawn matrix" alone. -/
theorem typed_of_wideM {sz : Size} {β : Dr sz} {a b : HTailF2} (h : wideMOf b = wideMOf a)
    (H : TypedAt sz β a) : TypedAt sz β b := by
  simp only [wideMOf, wideOf, Ready.seven, Prod.mk.injEq] at h
  obtain ⟨⟨⟨-, -, -, -, a5, -, a7⟩, a8, -, -⟩, a11, a12⟩ := h
  exact ⟨a11.trans H.cfF, a8.trans H.tau, a5.trans H.NM, fun μ => by rw [a12]; exact H.first μ,
    fun μ => by rw [a7]; exact H.k μ⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The matrix in front of the batching.** -/
theorem matrix_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ x ∈ P1K8S.stretches, ∃ (b8 : Block S Claim) (Xl : LinkH),
      c.blocksInOrder[14 * x.1 + x.2.1 + 2]? = some b8 ∧ Bs.G₀.built[x.1]? = some Xl ∧
      ∀ (ft : Nat) (s₆ s₇ : S) (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (k : Nat) (rs' : List Fmt.RoundView)
        (cols' : List Desc.OpenedColumn) (out : S × List Fmt.RoundView × List Desc.OpenedColumn) (sz : Size) (β : Dr sz),
        Fits (ProofFile.k8ParW Z Bs.G₀ Xl x.1).toPar sz →
        b8.step ft s₆ [r] cols = .ok (s₇, k) → r.drawn.trits.toArray = listOf β →
        foldBlocks ft ((c.blocksInOrder.drop (14 * x.1 + x.2.1 + 3)).take x.2.2) s₇ rs' cols' = .ok out →
        ∃ tl, out.1.tl? = some tl ∧ TypedAt sz β tl ∧
          (allLive tl = false ↔ ∃ (μ : Fin sz.NM) (c : Fin (sz.k μ)), ∀ u, (β μ u c).val = 0) ∧
          ProofFile.Honest.K8.cols tl = sz.columns := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hp : (l, if l = 24 then 5 else 4) ∈ P1K8S.places := List.mem_map.2 ⟨l, hl, rfl⟩
  obtain ⟨Lk, b8, Xl, -, -, hf8, hXl, -, -, -, hstep⟩ := P1K8S.sitsAt_open hS hR O _ hp
  obtain ⟨-, hstay⟩ := P1K8S.staysAt_open hS hR O _ hx
  refine ⟨b8, Xl, hf8, hXl, ?_⟩
  intro ft s₆ s₇ r cols k rs' cols' out sz β hfit hst hr hfold
  obtain ⟨r', hr', -, hm, -, -⟩ := (hstep ft s₆ s₇ k [r] cols).1 hst
  obtain rfl : r = r' := List.head_eq_of_cons_eq hr'
  obtain ⟨tl₇, ht7, hT7⟩ := typed_of_means _ sz β hfit s₆ s₇ r hm hr
  have hleave : ∀ b ∈ (c.blocksInOrder.drop (14 * l + (if l = 24 then 5 else 4) + 3)).take
      (if l = 24 then 3 else 2), b.Leaves (readTl wideMOf) := by
    intro b hb
    obtain ⟨j, hj, hbj⟩ := P1K8S.mem_stretch hb
    exact hstay j hj b hbj _ wideMOf keeps4_wideM
  have hw : readTl wideMOf out.1 = readTl wideMOf s₇ :=
    Desc.foldLeaves S Claim _ (readTl wideMOf) ft _ s₇ rs' cols' out hleave hfold
  unfold readTl at hw
  rw [ht7] at hw
  cases hto : out.1.tl? with
  | none =>
    rw [hto] at hw
    exact absurd hw (by simp)
  | some tl =>
    rw [hto] at hw
    have hT := typed_of_wideM (Option.some.inj hw) hT7
    exact ⟨tl, rfl, hT, allLive_iff hT, cols_eq hT⟩

/-! ## Along "reached" -/

/-- A reached state, one border back. -/
theorem reach_back {σ Cl Pz : Type} {ft : ℕ} {bs : List (Block σ Cl)} {start : Pz → σ} {k : ℕ}
    {z : Pz} {s' : σ} (h : Reach ft bs start (k + 1) (z, s')) :
    ∃ s b, Reach ft bs start k (z, s) ∧ bs[k]? = some b ∧ StepYes ft b s s' := by
  cases h with
  | succ hr hb hy => exact ⟨_, _, hr, hb, hy⟩

/-- A step of a block that leaves a reading leaves it. -/
theorem leaves_step {σ Cl α : Type} {ft : ℕ} {b : Block σ Cl} {f : σ → α} (hl : b.Leaves f)
    {s s' : σ} (h : StepYes ft b s s') : f s' = f s := by
  obtain ⟨R, cs, -, e⟩ := h
  exact hl _ _ _ _ ((Sound.step_ok_iff ft b s s' R cs cs.length).1 e).2.2.2

/-- Over n blocks each of which leaves a reading. -/
theorem reach_stretch {σ Cl Pz α : Type} {ft : ℕ} {bs : List (Block σ Cl)} {start : Pz → σ}
    {f : σ → α} {k : ℕ} {z : Pz} : ∀ (n : ℕ) (s : σ), Reach ft bs start (k + n) (z, s) →
      (∀ j, j < n → ∀ b, bs[k + j]? = some b → b.Leaves f) →
      ∃ s₀, Reach ft bs start k (z, s₀) ∧ f s = f s₀
  | 0, s, h, _ => ⟨s, h, rfl⟩
  | n + 1, s, h, hl => by
    obtain ⟨s₁, b, hr, hb, hy⟩ := reach_back (k := k + n) h
    obtain ⟨s₀, h0, e0⟩ := reach_stretch n s₁ hr fun j hj b' hb' => hl j (by omega) b' hb'
    exact ⟨s₀, h0, (leaves_step (hl n (by omega) b hb) hy).trans e0⟩

/-- **The matrix in a state reached in front of the batching.** -/
theorem matrix_at_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ x ∈ P1K8S.stretches, ∃ (b8 : Block S Claim) (Xl : LinkH),
      c.blocksInOrder[14 * x.1 + x.2.1 + 2]? = some b8 ∧ Bs.G₀.built[x.1]? = some Xl ∧
      ∀ (z : ProofFile.InstPub) (s : S),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 3 + x.2.2) (z, s) →
        ∃ (s₆ s₇ : S) (r : Fmt.RoundView) (cols : List Desc.OpenedColumn),
          Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 2) (z, s₆) ∧
          b8.step 0 s₆ [r] cols = .ok (s₇, cols.length) ∧
          ∀ (sz : Size) (β : Dr sz), Fits (ProofFile.k8ParW Z Bs.G₀ Xl x.1).toPar sz →
            r.drawn.trits.toArray = listOf β →
            ∃ tl, s.tl? = some tl ∧ TypedAt sz β tl ∧
              (allLive tl = false ↔
                ∃ (μ : Fin sz.NM) (c : Fin (sz.k μ)), ∀ u, (β μ u c).val = 0) ∧
              ProofFile.Honest.K8.cols tl = sz.columns := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hp : (l, if l = 24 then 5 else 4) ∈ P1K8S.places := List.mem_map.2 ⟨l, hl, rfl⟩
  obtain ⟨Lk, b8, Xl, -, -, hf8, hXl, -, -, -, hstep⟩ := P1K8S.sitsAt_open hS hR O _ hp
  obtain ⟨-, hstay⟩ := P1K8S.staysAt_open hS hR O _ hx
  refine ⟨b8, Xl, hf8, hXl, fun z s hr => ?_⟩
  obtain ⟨s₇, h7, e7⟩ := reach_stretch (f := readTl wideMOf) _ s hr
    fun j hj b hb => hstay j hj b hb _ wideMOf keeps4_wideM
  obtain ⟨s₆, b, h6, hb, R, cs, -, hst⟩ :=
    reach_back (k := 14 * l + (if l = 24 then 5 else 4) + 2) h7
  obtain rfl : b8 = b := Option.some.inj (hf8.symm.trans hb)
  obtain ⟨r, rfl, -, hm, -, -⟩ := (hstep 0 s₆ s₇ cs.length R cs).1 hst
  refine ⟨s₆, s₇, r, cs, h6, hst, fun sz β hfit hrβ => ?_⟩
  obtain ⟨tl₇, ht7, hT7⟩ := typed_of_means _ sz β hfit s₆ s₇ r hm hrβ
  unfold readTl at e7
  rw [ht7] at e7
  cases hto : s.tl? with
  | none =>
    rw [hto] at e7
    exact absurd e7 (by simp)
  | some tl =>
    rw [hto] at e7
    have hT := typed_of_wideM (Option.some.inj e7) hT7
    exact ⟨tl, rfl, hT, allLive_iff hT, cols_eq hT⟩

end

end P1K8

#print axioms P1K8.reach_stretch
#print axioms P1K8.matrix_at_reached
#print axioms P1K8.typed_of_means
#print axioms P1K8.typed_of_wideM
#print axioms P1K8.matrix_at_batch
#print axioms P1K8.keeps4_wideM
#print axioms P1K8.k_of_list
#print axioms P1K8.reach_back
#print axioms P1K8.leaves_step
