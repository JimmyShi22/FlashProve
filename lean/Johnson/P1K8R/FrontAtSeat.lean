-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FrontAtSeat.lean: THE SMALLNESS TEST: ITS ONE THEOREM AT THE FOLD:
AT EVERY STATE THAT THE FOLD HANDS ON IN FRONT OF A DRAW THE TEST `frontB` SAYS YES. NO SOUNDNESS.

`Ready.frontB` (Johnson/Desc/First/K8/Front.lean): a link is open; the list of tables is closed;
every table lies on the third vector of reads; the smallness test's part of the verifier's state
passes `planFitsB`. `cond_of_front` (LawFront.lean) turns a yes into what the law of the draw reads
of that part.
  `PlanFitsAll W`: THE NAMED TEST ON THE PLAN: `planFitsB` at the frame's own 25 values: each
    layers' entry's, each attention entry's seam's, the head's.
  `reads_under`: at each place the entry in front of the draw's is under the lot's block of the
    reads' sending with the step without a round joined behind.
  `own_head`, `own_layers`: the head's link and the 12 layers' links: by the laws
    of that block (K1PenR/AtK1Seat.lean), and at a layers' link the law of the feed-forward caller's
    block in front of it (Johnson/Road/K4/FunsTree.lean).
  `own_att`: the 12 attention links: behind the link's first entry the state's value is the plan's
    seam's but for two marks (`att_tl_at_fold`, Johnson/P1L20R/FrameFold.lean); the lookup
    on the calls and the attention's own block leave the seven fields
    (Johnson/Desc/First/K8/LawWideK3.lean; Johnson/Desc/First/Att/K05Leaves.lean); the step behind
    the reads' sending keeps them.
  `LaidFront W s`: WHAT THE THREE ARMS END IN: there is a planned value tlP of the public parameters
    (`PlanVal`: a layers' entry's, an attention entry's seam's, the head's) whose seven fields the
    state's value has (`lay7B`), and `onThirdB` says yes. NO PREMISE ON THE PLAN.
  `LaidOwn W l s`: THE SAME WITH THE LINK's OWN PLANNED VALUE NAMED (`PlanAt W l tlP`: the head's at
    link 24; group g's layers' entry's at link 2 g; group g's attention entry's seam's at link
    2 g + 1): what the three arms end in. `planAt_built`: it is
    the built link's own field tl.
  `own_at_place`, `k8LaidOwn`: that, at all 25 places along the fold from the first state, and at
    every reached statement.
  `laid_head`, `laid_layers`, `laid_att`, `laid_at_place`, `k8Laid`: further statements.

  `front_of_laid`, `front_head`, `front_layers`, `front_att`, `front_at_place`: the one test
    `frontB`, under `PlanFitsAll`.
  `k8Front`: **AT EVERY STATEMENT THAT IS REACHED AT THE NUMBER OF A DRAW'S ENTRY (`RchAt`,
    Johnson/Top/H0/Walk/ReachAt.lean): `frontB` SAYS YES AT ITS STATE.** The witnesses of "some
    rounds and columns" stay inside the proof.
Limits. `PlanFitsAll` is a premise: evaluated at no plan.
The fold starts at the first state.

-/
import Johnson.P1K8R.RowAtSeat
import Johnson.K1PenR.AtK1Seat
import Johnson.IMR.K4Seat
import Johnson.IMR.K8Seat
import Johnson.IMR.PureJoin
import Johnson.Desc.First.K8.LawFront
import Johnson.Road.K4.FunsTree
import Johnson.P1K8R.WideAtSeat
import Johnson.P1K8R.NamedOfReach
import Johnson.P1L20R.FrameFold
import Johnson.IMR.K5Seat
import Johnson.Desc.First.Att.K05Leaves

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8S

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready
open ProofFile (Cl)

/-- The named test on the plan. -/
def PlanFitsAll (W : Verify.Public) : Prop :=
  (∀ (g : ℕ) (hp : Layer.HPlan2), W.G[g]? = some hp → planFitsB hp.tl = true) ∧
  (∀ (g : ℕ) (a : Attention.Plan), W.A[g]? = some a → planFitsB a.seam.tl = true) ∧
  planFitsB W.H.tl = true

/-- A planned value of the smallness test's part: a layers' entry's, an attention entry's seam's, or
the head's. -/
def PlanVal (W : Verify.Public) (tlP : HTailF2) : Prop :=
  (∃ (g : ℕ) (hp : Layer.HPlan2), W.G[g]? = some hp ∧ tlP = hp.tl) ∨
  (∃ (g : ℕ) (a : Attention.Plan), W.A[g]? = some a ∧ tlP = a.seam.tl) ∨ tlP = W.H.tl

/-- THE LINK's OWN planned value: the head's at link 24; group g's layers' entry's at link 2 g;
group g's attention entry's seam's at link 2 g + 1. -/
def PlanAt (W : Verify.Public) (l : ℕ) (tlP : HTailF2) : Prop :=
  (l = 24 ∧ tlP = W.H.tl) ∨
  (∃ (g : ℕ) (hp : Layer.HPlan2), g < 12 ∧ l = 2 * g ∧ W.G[g]? = some hp ∧ tlP = hp.tl) ∨
  ∃ (g : ℕ) (a : Attention.Plan), g < 12 ∧ l = 2 * g + 1 ∧ W.A[g]? = some a ∧ tlP = a.seam.tl

/-- It is a planned value. -/
theorem planVal_of_at {W : Verify.Public} {l : ℕ} {tlP : HTailF2} (h : PlanAt W l tlP) :
    PlanVal W tlP := by
  rcases h with ⟨-, rfl⟩ | ⟨g, hp, -, -, e, rfl⟩ | ⟨g, a, -, -, e, rfl⟩
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl ⟨g, hp, e, rfl⟩
  · exact Or.inr (Or.inl ⟨g, a, e, rfl⟩)

/-- The named test holds at every planned value. -/
theorem planFits_of_val {W : Verify.Public} (hW : PlanFitsAll W) {tlP : HTailF2}
    (h : PlanVal W tlP) : planFitsB tlP = true := by
  rcases h with ⟨g, hp, e, rfl⟩ | ⟨g, a, e, rfl⟩ | rfl
  · exact hW.1 g hp e
  · exact hW.2.1 g a e
  · exact hW.2.2

/-- What the fold hands on in front of a draw, with the planned value named. -/
def LaidFront (W : Verify.Public) (s : S) : Prop :=
  ∃ tlP, PlanVal W tlP ∧ lay7B tlP s = true ∧ onThirdB s = true

/-- The same with THE LINK's OWN planned value named. -/
def LaidOwn (W : Verify.Public) (l : ℕ) (s : S) : Prop :=
  ∃ tlP, PlanAt W l tlP ∧ lay7B tlP s = true ∧ onThirdB s = true

theorem laidFront_of_own {W : Verify.Public} {l : ℕ} {s : S} (h : LaidOwn W l s) :
    LaidFront W s := by
  obtain ⟨tlP, hv, h7, h3⟩ := h
  exact ⟨tlP, planVal_of_at hv, h7, h3⟩

/-- A link of the list that is run has the built link's group number. -/
theorem zipped_g {Bl : Stages.LinksH} {ls : Array LinkH} {j : ℕ} {x : LinkH}
    (h : (OnBytes.L5.LinksOrder.zipped Bl ls)[j]? = some x) :
    ∃ b, Bl.links[j]? = some b ∧ b.g = x.g := by
  unfold OnBytes.L5.LinksOrder.zipped at h
  rw [Array.getElem?_zipWith] at h
  cases hb : Bl.links[j]? with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    cases hl : ls[j]? with
    | none => rw [hl] at h; cases h
    | some y =>
      rw [hl] at h
      obtain rfl := Option.some.inj h
      exact ⟨b, rfl, rfl⟩

/-- It gives the one test, under the named test on the plan. -/
theorem front_of_laid {W : Verify.Public} (hW : PlanFitsAll W) {s : S} (h : LaidFront W s) :
    frontB s = true := by
  obtain ⟨tlP, hv, h7, h3⟩ := h
  exact frontB_of_tests h7 (planFits_of_val hW hv) h3

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- One place: the entry of the reads' sending is under the lot's block. -/
theorem reads_under (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl24 : l ≤ 24)
    (sub : ModelPart) (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K1) (hi : i = 3 ∨ i = 4) :
    ∃ b Xl pr reads, c.blocksInOrder[14 * l + i + 2]? = some b ∧ Bs.G₀.built[l]? = some Xl ∧
      b.Under (IM.k1Reads Z Bs.G₀ l Xl pr reads) := by
  obtain ⟨Lk, b, Xl, pr, pd, reads, digits, e1, e2, e3, hn, harm⟩ :=
    IM.k1_later O l sub hl i hk (by omega)
  have hf : c.blocksInOrder[14 * l + i + 2]? = some b := by
    have := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope hS hR O hl24 i] at this
  rcases harm with ⟨_, h⟩ | ⟨e, _⟩
  · exact ⟨b, Xl, pr, reads, hf, e3, alone_retype_under h⟩
  · exfalso
    rcases IM.numbers_pieces hn with ⟨-, h'⟩ | ⟨-, h'⟩ <;> omega

/-- **The head's link.** -/
theorem own_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take 343) (ProofFile.startS Z p) R C = .ok out) :
    LaidOwn Bs.G₀.W 24 out.1 := by
  obtain ⟨b, Xl, pr, reads, hf, e3, hu⟩ := reads_under hS hR O (l := 24) (by omega) .head
    (IM.subs_head hS hR O.pub O.blank) 4 (by unfold kindsBeforeBatching; rfl) (Or.inr rfl)
  obtain ⟨_, X', e3', hk, _⟩ := IM.ground_named hS hR O.pub O.blank
  obtain rfl : X' = Xl := Option.some.inj (e3'.symm.trans e3)
  obtain ⟨t₄, R₄, C₄⟩ := out
  obtain ⟨t₃, R₃, C₃, f₃⟩ := Meaning.K2.fold_back (k := 342) f
  obtain ⟨rs, gs, d⟩ := Meaning.K2.fold_next (k := 342) hf f₃ f
  obtain ⟨h7, h3⟩ := K1Pen.k1Reads_makes_head Z Bs.G₀ 24 X' pr reads e3 hk (hu _ _ _ _ d)
  exact ⟨_, Or.inl ⟨rfl, rfl⟩, h7, h3⟩

/-- **A layers' link.** -/
theorem own_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {g : ℕ} (hg : g < 12) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * (2 * g) + 6)) (ProofFile.startS Z p) R C = .ok out) :
    LaidOwn Bs.G₀.W (2 * g) out.1 := by
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, e3, hk, hXg, _, hla⟩ :=
    IM.k1_reads_layers hS hR O g hg
  have hf : c.blocksInOrder[14 * (2 * g) + 5]? = some b := by
    have := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope hS hR O (by omega) 3] at this
  obtain ⟨Lk', b2, x, e1', e2', _, hla2, _⟩ := IM.k4_of hS hR O g hg
  have hf2 : c.blocksInOrder[14 * (2 * g) + 4]? = some b2 := by
    have := IM.hear_at_flat e1' e2'
    rwa [IM.flatIx_scope hS hR O (by omega) 2] at this
  obtain ⟨t₄, R₄, C₄⟩ := out
  obtain ⟨t₃, R₃, C₃, f₃⟩ := Meaning.K2.fold_back (k := 14 * (2 * g) + 5) f
  obtain ⟨t₂, R₂, C₂, f₂⟩ := Meaning.K2.fold_back (k := 14 * (2 * g) + 4) f₃
  obtain ⟨rs, gs, d⟩ := Meaning.K2.fold_next hf f₃ f
  obtain ⟨rs2, gs2, d2⟩ := Meaning.K2.fold_next hf2 f₂ f₃
  have d2' : (OnBytes.Desc.First.K4.blockAtS { x.2 with k3Runs := true }).decide t₂ rs2 gs2 =
      .ok t₃ := (IM.alone_underR hla2).2 _ _ _ _ d2
  obtain ⟨funs, hfu, htr⟩ := OnBytes.Road.K4.funs_tree_atS d2'
  obtain ⟨hp, ehp, h7, h3⟩ := K1Pen.k1Reads_makes_layers Z Bs.G₀ (2 * g) Xl 4 reads e3 hk
    (alone_retype_under hla _ _ _ _ d)
  rw [hXg] at ehp
  refine ⟨hp.tl, Or.inr (Or.inl ⟨g, hp, hg, rfl, ehp, rfl⟩), h7, ?_⟩
  rw [h3]
  exact (funsThirdB_iff t₃).2 ⟨funs, hfu, htr⟩

/-- The seven fields are none of the four that the lookup lays. -/
theorem keeps4_seven : Keeps4 seven := fun _ _ _ _ _ => rfl

/-- The first test from the reading. -/
theorem lay7B_of_lay7 {tlP : HTailF2} {s : S} (h : lay7 s = some (seven tlP)) :
    lay7B tlP s = true := by
  unfold lay7 at h
  cases ht : s.tl? with
  | none => simp [ht] at h
  | some tl =>
    rw [ht] at h
    have e : seven tl = seven tlP := Option.some.inj h
    simp only [seven, Prod.mk.injEq] at e
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := e
    unfold lay7B
    rw [ht]
    simp [a1, a2, a3, a4, a5, a6, a7]

/-- **An attention link.** -/
theorem own_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {g : ℕ} (hg : g < 12) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * (2 * g + 1) + 6)) (ProofFile.startS Z p) R C = .ok out) :
    LaidOwn Bs.G₀.W (2 * g + 1) out.1 := by
  obtain ⟨b, Xl, pr, reads, hf, e3, hu⟩ := reads_under hS hR O (l := 2 * g + 1) (by omega)
    .attention (IM.subs_att hS hR O.pub O.blank (g := g) hg) 3
    (by unfold kindsBeforeBatching; cases (2 * g + 1 == 0) <;> rfl) (Or.inl rfl)
  obtain ⟨hN, _⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨_, X', _, _, _, _, e3', hk, hXg, _⟩ := hN g hg
  obtain rfl : X' = Xl := Option.some.inj (e3'.symm.trans e3)
  obtain ⟨Lk, b1, b1', eL, e1, k3, la1⟩ := IM.k3_of hS hR O (2 * g + 1) (by omega) false
  have ix1 : IM.k3Ix (2 * g + 1) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g + 1 = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ 2 * g + 1 = 24)]
    rfl
  rw [ix1] at e1
  have i1 : c.blocksInOrder[14 * (2 * g + 1) + 3]? = some b1 := by
    have k := IM.hear_at_flat eL e1
    rwa [IM.flatIx_scope hS hR O (by omega) 1] at k
  obtain ⟨Lk', b2, b2', a, eL', e2, k5, la2, _⟩ := IM.k5_of hS hR O g hg
  have i2 : c.blocksInOrder[14 * (2 * g + 1) + 4]? = some b2 := by
    have k := IM.hear_at_flat eL' e2
    rwa [IM.flatIx_scope hS hR O (by omega) 2] at k
  obtain ⟨t₄, R₄, C₄⟩ := out
  obtain ⟨t₃, R₃, C₃, f₃⟩ := Meaning.K2.fold_back (k := 14 * (2 * g + 1) + 5) f
  obtain ⟨t₂, R₂, C₂, f₂⟩ := Meaning.K2.fold_back (k := 14 * (2 * g + 1) + 4) f₃
  obtain ⟨t₁, R₁, C₁, f₁⟩ := Meaning.K2.fold_back (k := 14 * (2 * g + 1) + 3) f₂
  obtain ⟨rs1, gs1, d1⟩ := Meaning.K2.fold_next i1 f₁ f₂
  obtain ⟨rs2, gs2, d2⟩ := Meaning.K2.fold_next i2 f₂ f₃
  obtain ⟨rs3, gs3, d3⟩ := Meaning.K2.fold_next hf f₃ f
  have ha : IM.subAt (2 * g + 1) = ModelPart.attention := by
    unfold IM.subAt
    rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨X, q, eX, _, eq, ht1⟩ := P1L20.att_tl_at_fold hS hR O (l := 2 * g + 1) (by omega) ha f₁
  have hg' : X.g = g := by
    obtain ⟨ls, _, _, eB, _⟩ := IM.blank_ground O.blank
    rw [eB] at e3
    obtain ⟨b', hb', hbg⟩ := zipped_g e3
    obtain rfl : b' = X := Option.some.inj (hb'.symm.trans eX)
    rw [hbg]
    exact hXg
  rw [hg'] at eq
  have h1 : lay7 t₁ = some (seven q.seam.tl) := by
    unfold lay7
    rw [ht1]
    rfl
  have h2 : lay7 t₂ = lay7 t₁ :=
    leaves_of_under (IM.alone_underR la1).2 (theStated_leaves_tl keeps4_seven k3) _ _ _ _ d1
  have h3 : t₃.tl? = t₂.tl? :=
    VerifiableInference.Desc.First.Att.P.k5AtN_leaves_tl k5 _ _ _ _
      ((IM.alone_underR la2).2 _ _ _ _ d2)
  have h7 : lay7B q.seam.tl t₃ = true := by
    refine lay7B_of_lay7 ?_
    unfold lay7
    rw [h3]
    exact h2.trans h1
  obtain ⟨hT, hK⟩ := K1Pen.k1Reads_makes_att Z Bs.G₀ (2 * g + 1) X' pr reads hk (hu _ _ _ _ d3)
  refine ⟨q.seam.tl, Or.inr (Or.inr ⟨g, q, hg, rfl, ?_, rfl⟩), (hK q.seam.tl).trans h7, hT⟩
  rw [O.W]
  exact eq

/-- **AT ALL 25 PLACES, ALONG THE FOLD FROM THE FIRST STATE: NO PREMISE ON THE PLAN.** -/
theorem own_at_place (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ} (hx : x ∈ places) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * x.1 + x.2 + 2)) (ProofFile.startS Z p) R C = .ok out) :
    LaidOwn Bs.G₀.W x.1 out.1 := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hl' : l < 25 := List.mem_range.1 hl
  by_cases h24 : l = 24
  · subst h24
    exact own_head hS hR O p R C out f
  · simp only [h24, if_false] at f
    by_cases he : l % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
      exact own_layers hS hR O (g := g) (by omega) p R C out f
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
      exact own_att hS hR O (g := g) (by omega) p R C out f

/-- Further names. -/
theorem laid_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take 343) (ProofFile.startS Z p) R C = .ok out) :
    LaidFront Bs.G₀.W out.1 :=
  laidFront_of_own (own_head hS hR O p R C out f)

theorem laid_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {g : ℕ} (hg : g < 12) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * (2 * g) + 6)) (ProofFile.startS Z p) R C = .ok out) :
    LaidFront Bs.G₀.W out.1 :=
  laidFront_of_own (own_layers hS hR O hg p R C out f)

theorem laid_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {g : ℕ} (hg : g < 12) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * (2 * g + 1) + 6)) (ProofFile.startS Z p) R C = .ok out) :
    LaidFront Bs.G₀.W out.1 :=
  laidFront_of_own (own_att hS hR O hg p R C out f)

theorem laid_at_place (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ} (hx : x ∈ places) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * x.1 + x.2 + 2)) (ProofFile.startS Z p) R C = .ok out) :
    LaidFront Bs.G₀.W out.1 :=
  laidFront_of_own (own_at_place hS hR O hx p R C out f)

/-- **k8LaidOwn: AT EVERY REACHED STATE IN FRONT OF A DRAW, WITH THE LINK's OWN PLANNED VALUE.** -/
theorem k8LaidOwn (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ} (hx : x ∈ places) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (14 * x.1 + x.2 + 2) a) : LaidOwn Bs.G₀.W x.1 a.1.2 := by
  obtain ⟨_, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.rchAt_fold h
  exact own_at_place hS hR O hx a.1.1 rs cols _ f

/-- The link's own planned value is the built link's. -/
theorem planAt_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} {Xl : LinkH}
    (e3 : Bs.G₀.built[l]? = some Xl) {tlP : HTailF2} (h : PlanAt Bs.G₀.W l tlP) : tlP = Xl.tl := by
  obtain ⟨hT, Xh, eh, th, _⟩ := IM.ground_tails hS hR O.pub O.blank
  rcases h with ⟨rfl, rfl⟩ | ⟨g, hp, hg, rfl, e, rfl⟩ | ⟨g, a, hg, rfl, e, rfl⟩
  · obtain rfl : Xh = Xl := Option.some.inj (eh.symm.trans e3)
    exact th.symm
  · obtain ⟨hp', _, x, _, e1, _, e2, t2, _⟩ := hT g hg
    obtain rfl : hp' = hp := Option.some.inj (e1.symm.trans e)
    obtain rfl : x = Xl := Option.some.inj (e2.symm.trans e3)
    exact t2.symm
  · obtain ⟨_, a', _, x', _, e1, _, _, _, _, _, _, e2, t2, _⟩ := hT g hg
    obtain rfl : a' = a := Option.some.inj (e1.symm.trans e)
    obtain rfl : x' = Xl := Option.some.inj (e2.symm.trans e3)
    exact t2.symm

/-- The three arms, by name. -/
theorem front_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hW : PlanFitsAll Bs.G₀.W)
    (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take 343) (ProofFile.startS Z p) R C = .ok out) :
    frontB out.1 = true :=
  front_of_laid hW (laid_head hS hR O p R C out f)

theorem front_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hW : PlanFitsAll Bs.G₀.W)
    {g : ℕ} (hg : g < 12) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * (2 * g) + 6)) (ProofFile.startS Z p) R C = .ok out) :
    frontB out.1 = true :=
  front_of_laid hW (laid_layers hS hR O hg p R C out f)

theorem front_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hW : PlanFitsAll Bs.G₀.W)
    {g : ℕ} (hg : g < 12) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * (2 * g + 1) + 6)) (ProofFile.startS Z p) R C = .ok out) :
    frontB out.1 = true :=
  front_of_laid hW (laid_att hS hR O hg p R C out f)

/-- The one test at all 25 places, under the named test on the plan. -/
theorem front_at_place (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hW : PlanFitsAll Bs.G₀.W)
    {x : ℕ × ℕ} (hx : x ∈ places) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * x.1 + x.2 + 2)) (ProofFile.startS Z p) R C = .ok out) :
    frontB out.1 = true :=
  front_of_laid hW (laid_at_place hS hR O hx p R C out f)

/-- **k8Laid: AT EVERY REACHED STATE IN FRONT OF A DRAW, WITH THE PLANNED VALUE NAMED.** -/
theorem k8Laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ} (hx : x ∈ places) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (14 * x.1 + x.2 + 2) a) : LaidFront Bs.G₀.W a.1.2 := by
  obtain ⟨_, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.rchAt_fold h
  exact laid_at_place hS hR O hx a.1.1 rs cols _ f

/-- **k8Front: AT EVERY REACHED STATE IN FRONT OF A DRAW.** -/
theorem k8Front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hW : PlanFitsAll Bs.G₀.W)
    {x : ℕ × ℕ} (hx : x ∈ places) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (14 * x.1 + x.2 + 2) a) : frontB a.1.2 = true := by
  obtain ⟨_, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.rchAt_fold h
  exact front_at_place hS hR O hW hx a.1.1 rs cols _ f

end P1K8S

#print axioms P1K8S.own_head
#print axioms P1K8S.own_layers
#print axioms P1K8S.own_att
#print axioms P1K8S.own_at_place
#print axioms P1K8S.k8LaidOwn
#print axioms P1K8S.planAt_built
#print axioms P1K8S.laid_att
#print axioms P1K8S.laid_at_place
#print axioms P1K8S.k8Laid
#print axioms P1K8S.front_head
#print axioms P1K8S.front_layers
#print axioms P1K8S.front_att
#print axioms P1K8S.front_at_place
#print axioms P1K8S.k8Front
#print axioms P1K8S.laid_head
#print axioms P1K8S.laid_layers
