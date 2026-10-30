-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/ShareAtTheG.lean: the smallness test's three shares of the clause on the rows toward zero
knowledge, at the lists of all kinds' rows by their name (`theGOfReturn`, E2E/TheG.lean): `KindPays`,
`KindBud`, `KindOnAtEveryRun`, under one premise on the kinds' rows K: the kind's lot with its simulators is
among the lots that K lays. The road of Johnson/Desc/ProofFile/Honest/K13/Term/KindPaysAtTheG.lean.

  `k8LotAtBase`                    the kind's lot with its simulators
  `otherLotsLayNoSideOfK8`         of the base filling's lots each is the kind's or lays no side of the kind
  `k8_places_elsewhere`            no member of the two later chains stands at a place of the kind
  `k8_none_elsewhere`              nor does a side of these chains
  `k8KindPays_at_theGOfReturn`     **KindPays G .K8**
  `k8ListsBear_at_theGOfReturn`    each list of the kind at that G is a row of the lot, in the first chain
  `k8KindBud_at_theGOfReturn`, `k8OnAtEveryRun_at_theGOfReturn`   the other two
  `k8_named`, `k8_lots_fit`         what K's maker owes at this lot
  `K8Stands`, `k8Stands_at_theGOfReturn`   the row stands, with a side, at each of the 25 members
  `k8Share_at_theGOfReturn`        **the three in one record**

One limit is raised, file-wide, as in the file it follows: maxRecDepth 100000; and at the two kernel facts on
the written lists 1000000.

Limits. Of the measure of the 25 private stops nothing is said here: KindOnAtEveryRun and exact speak off
them; it is bounded in Johnson/P1K8R/WindowAtTerm.lean, under that file's premises. h, T and K are
arguments. `laid` is a premise on K: whoever lays K owes it. The kind's On and bud ask
nothing: exact holds at every state of its part. Nothing is claimed on completeness, soundness or hiding.
-/
import E2E.TheG
import E2E.KindPaysOfALot
import Johnson.M1.BudGather
import Johnson.Desc.ProofFile.Honest.Law.UseByKind
import Johnson.Desc.ProofFile.Honest.Law.FillPairs
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsByKind
import AtFullSide.K8.SimAtFill
import Johnson.Desc.ProofFile.Honest.K7.AtFill
import Johnson.P1K8R.PinAtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open VerifiableInference.Desc (Chain KindName FileDescription)
open VerifiableInference.Compilation (KindPays)
open ProofFile.Honest.Term (matrixInput theGAtBase baseMaker baseFilling)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.TheSides (Letters theSides overlaySlots overlayLot find_name Narrows narrows_of_bare KindRows
  castSides castSides_of kindPays_of_rows rows_of_overlay block_of_seated)
open AtPublicFiles.TheG (ThreadParts theLetters theG theGOfReturn)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open P2Law.ProofPlan (WP)
open ProofFile.Honest.K14 (planAlike_at_head)
open OnBytes.HonestTrace (Sz)
open P5J (TS)

/-- **The kind's lot with its simulators.** -/
noncomputable abbrev k8LotAtBase :
    SLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst :=
  smallSLot id matsO

theorem k8FillLot_pair {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) :
    (smallLot (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := Inst) (X := Unit) id matsO, KindName.K8) ∈
      widerPairs I o S O := by
  unfold widerPairs
  exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))

/-- **Of the base filling's lots each is the kind's or lays no side at a place of the kind.** -/
theorem otherLotsLayNoSideOfK8 {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      M.name = (smallLot (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := Inst) (X := Unit) id matsO).name ∨
        ∀ x ∈ M.halves Zq G, x.place.kind ≠ .K8 := by
  intro M hM
  rcases lot_alone I o S O (pair_only I o S O (k8FillLot_pair I o S O) (by decide)) Zq G M hM with
    rfl | none
  · exact Or.inl rfl
  · exact Or.inr none

theorem small_on_at {W₀ Rc X : Type} (Zq : Pub) (G : Ground) :
    ∀ r ∈ (smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) (Pb := Inst) id matsO).rows Zq G,
      (∀ u ca m front, r.On u ca m front) ∧ ∀ n ds asks, r.bud n ds asks := by
  intro r hr
  obtain ⟨l, Xl, hX, rfl⟩ := smallSLot_rows_mem hr
  exact ⟨fun _ _ _ _ => trivial, fun _ _ _ => trivial⟩

set_option maxRecDepth 1000000 in
theorem wp_shared_no_K8 : WP.shared.blocksInOrder.all (fun b => b.place.kind != .K8) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem wp_second_no_K8 : WP.second.blocksInOrder.all (fun b => b.place.kind != .K8) = true := by
  decide +kernel

section Places
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **No member of the two later chains stands at a place of the kind.** -/
theorem k8_places_elsewhere (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (∀ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder, b.place.kind ≠ .K8) ∧
      ∀ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder, b.place.kind ≠ .K8 := by
  have A := planAlike_at_head h
  refine ⟨fun b hb hk => ?_, fun b hb hk => ?_⟩
  · have hm : b.place ∈ WP.shared.blocksInOrder.map (·.place) := by
      rw [VerifiableInference.Desc.alike₂_place _ _ A.shared]
      exact List.mem_map.2 ⟨b, hb, rfl⟩
    obtain ⟨w, hw, hwp⟩ := List.mem_map.1 hm
    have q : (w.place.kind != .K8) = true := List.all_eq_true.1 wp_shared_no_K8 w hw
    rw [hwp, hk] at q
    cases q
  · have hm : b.place ∈ WP.second.blocksInOrder.map (·.place) := by
      rw [VerifiableInference.Desc.alike₂_place _ _ A.second]
      exact List.mem_map.2 ⟨b, hb, rfl⟩
    obtain ⟨w, hw, hwp⟩ := List.mem_map.1 hm
    have q : (w.place.kind != .K8) = true := List.all_eq_true.1 wp_second_no_K8 w hw
    rw [hwp, hk] at q
    cases q

/-- **No side of the two later chains stands at a place of the kind.** -/
theorem k8_none_elsewhere {W₁ Rc Tr X₀ X : Type} {P : OnlineProverParts W₁ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₁ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (∀ g ∈ A.H.shared, g.place.kind ≠ .K8) ∧ ∀ g ∈ A.H.second, g.place.kind ≠ .K8 := by
  obtain ⟨-, s2, s3⟩ := atPure_strays hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
    Except.ok.inj ((atPure_ok hA).2.2.1.symm.trans h.laid.value)
  have key : ∀ F : FileDescription ProofFile.Inst, F = P5J.F0T OnBytes.secondHashFunction Zp Np cF →
      (∀ b ∈ F.shared.blocksInOrder, b.place.kind ≠ .K8) ∧ ∀ b ∈ F.second.blocksInOrder, b.place.kind ≠ .K8 := by
    intro F e
    subst e
    exact k8_places_elsewhere h
  obtain ⟨p2, p3⟩ := key A.F eF
  refine ⟨fun g hg e => ?_, fun g hg e => ?_⟩
  · obtain ⟨b, hb, hpl⟩ := side_on_chain s2 hg
    exact p2 b hb (by rw [hpl]; exact e)
  · obtain ⟨b, hb, hpl⟩ := side_on_chain s3 hg
    exact p3 b hb (by rw [hpl]; exact e)

end Places

/-! ## At the lists built from the filling's lots -/

section
variable {files : VerifierAndGoals.PublicFiles} {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok returned) (h : HeadAtReturn files returned)
    (mine : List (SLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst))
    (named : ∀ s ∈ mine, (baseFilling files).lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ (baseFilling files).lots, ∀ s,
      (mine.find? fun s => s.name == L.name) = some s →
      (s.rows returned.Z returned.G).map (·.half) = L.halves returned.Z returned.G)
    (shared : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins OnBytes.TableKey) Unit OnBytes.TableKey))
    (hs : shared.map (·.half) = (baseFilling files).shared returned.Z returned.G)
    (second : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst))
    (h₃ : second.map (·.half) = (baseFilling files).second returned.Z returned.G)
    (Ls : Letters h.description returned.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (f₁ : List (Fall h.description.S₁)) (f₂ : List (Fall h.description.S₂))
    (f₃ : List (Fall h.description.S₃))
    (laid : k8LotAtBase ∈ mine)
include made laid

omit made in
/-- A row of the kind among the rows that the overlay lays is a row of the kind's lot. -/
theorem k8_row_of_overlay :
    ∀ u ∈ (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs
        second h₃).rows.first, u.place.kind = .K8 →
      u ∈ k8LotAtBase.rows returned.Z returned.G := by
  intro u hu hk
  obtain ⟨l, hl, hul⟩ := rows_of_overlay (ls := [k8LotAtBase]) apart
    (fun l hl => by rw [List.mem_singleton.1 hl]; exact laid) hm
    (fun M hM => by
      rcases otherLotsLayNoSideOfK8 matrixInput _ _ _ returned.Z returned.G M hM with name | none
      · exact Or.inl ⟨_, List.mem_singleton.2 rfl, name.symm⟩
      · exact Or.inr none) u hu hk
  obtain rfl := List.mem_singleton.1 hl
  exact hul

/-- **KindPays at the lists built from the lots**, at letters that narrow On and bud at the kind's row. -/
theorem k8KindPays_at_the_sides
    (narrows : ∀ u ∈ k8LotAtBase.rows returned.Z returned.G, Narrows (Ls.first u) u) :
    KindPays (theSides h.description Ls
      (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs second
        h₃).rows f₁ f₂ f₃) .K8 := by
  have hsay := small_rows_at_base made h.head
  have hel := k8_places_elsewhere h.head
  refine kindPays_of_rows Ls _ f₁ f₂ f₃ .K8 (fun u hu hk σ hσ => ?_) (fun u _ hk σ hσ => ?_)
    (fun u _ hk σ hσ => ?_)
  · have hul := k8_row_of_overlay mine named apart hm shared hs second h₃ laid u hu hk
    obtain ⟨σ', hσ', good⟩ := hsay.2.2.2.2 u hul _ .own _ 0 0 f₁
    obtain rfl : σ' = σ := Option.some.inj (hσ'.symm.trans hσ)
    exact ⟨narrows u hul, _, _, good⟩
  · obtain ⟨b, hb, e⟩ := block_of_seated hσ
    exact absurd (by rw [e]; exact hk) (hel.1 b hb)
  · obtain ⟨b, hb, e⟩ := block_of_seated hσ
    exact absurd (by rw [e]; exact hk) (hel.2 b hb)

/-- **The lists of the kind at that G are rows of the lot, in the first chain alone.** -/
theorem k8ListsBear_at_the_sides
    (whole : ∀ u ∈ k8LotAtBase.rows returned.Z returned.G, (Ls.first u).bare = u) :
    ListsOfTheKindBear (theSides h.description Ls
      (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs second
        h₃).rows f₁ f₂ f₃) .K8 (k8LotAtBase.rows returned.Z returned.G) := by
  obtain ⟨-, -, -, -, -, -, -, -, e₂, e₃, -⟩ := atPure_ok made
  obtain ⟨n₂, n₃⟩ := k8_none_elsewhere made h.head
  refine ⟨?_, ?_, ?_⟩
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₁ u).1] at hk
    have hul := k8_row_of_overlay mine named apart hm shared hs second h₃ laid u hu hk
    rw [whole u hul]
    exact hul
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₂ u).1] at hk
    have side : u.half ∈ returned.H.shared := by
      rw [e₂, ← hs]
      exact List.mem_map_of_mem hu
    exact n₂ _ side hk
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₃ u).1] at hk
    have side : u.half ∈ returned.H.second := by
      rw [e₃, ← h₃]
      exact List.mem_map_of_mem hu
    exact n₃ _ side hk

end

/-! ## What K's maker owes at this lot -/

/-- **A lot of the base filling that bears the kind's lot's name is the kind's lot.** -/
theorem k8_slot_by_name :
    ∀ L ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
      openHonest).lots,
      L.name = (smallLot (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := Inst) (X := Unit) id matsO).name →
      L = smallLot (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := Inst) (X := Unit) id matsO := by
  intro L hL hn
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots] at hL
  simp only [widerPairs, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hL
  rcases hL with (((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl) | rfl
  all_goals first | exact absurd hn (by decide) | rfl

/-- **The field named of KindRows at this lot.** -/
theorem k8_named (files : VerifierAndGoals.PublicFiles) :
    (baseFilling files).lots.any (fun L => L.name == k8LotAtBase.name) = true :=
  List.any_eq_true.2 ⟨_, P1K8.term_small_mem matrixInput OnBytes.secondHashFunction Sz.ref openHonest, by rfl⟩

/-- **The field lots_fit of KindRows at this lot.** -/
theorem k8_lots_fit (files : VerifierAndGoals.PublicFiles) (Zq : Pub) (G : Ground) :
    ∀ L ∈ (baseFilling files).lots, L.name = k8LotAtBase.name →
      (k8LotAtBase.rows Zq G).map (·.half) = L.halves Zq G := by
  intro L hL hn
  rw [k8_slot_by_name L hL hn]
  exact congrArg (fun H => HLot.halves H Zq G) (smallSLot_toHLot id matsO)

/-! ## The row stands -/

/-- **At each of the 25 segments a list that bears a row of the lot stands in the first chain's lists,
with a side over the description, at the kind's member.** A definition, meant as a theorem's end. -/
def K8Stands {W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Inst} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (rows : List (Unlettered (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)) : Prop :=
  ∀ l, l < 25 → ∃ L ∈ G.first, L.bare ∈ rows ∧ ∃ σ, L.side F.first.blocksInOrder G.falls₁ = some σ ∧
    F.first.blocksInOrder[14 * l + (if l = 24 then 5 else 4) + 2]? = some σ.block

section
variable {files : VerifierAndGoals.PublicFiles} {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok returned) (h : HeadAtReturn files returned)
    (mine : List (SLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst))
    (named : ∀ s ∈ mine, (baseFilling files).lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ (baseFilling files).lots, ∀ s,
      (mine.find? fun s => s.name == L.name) = some s →
      (s.rows returned.Z returned.G).map (·.half) = L.halves returned.Z returned.G)
    (shared : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins OnBytes.TableKey) Unit OnBytes.TableKey))
    (hs : shared.map (·.half) = (baseFilling files).shared returned.Z returned.G)
    (second : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst))
    (h₃ : second.map (·.half) = (baseFilling files).second returned.Z returned.G)
    (Ls : Letters h.description returned.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (f₁ : List (Fall h.description.S₁)) (f₂ : List (Fall h.description.S₂))
    (f₃ : List (Fall h.description.S₃))
    (laid : k8LotAtBase ∈ mine)
include made laid

/-- **The kind's row stands at each segment, with a side at the kind's member.** -/
theorem k8Stands_at_the_sides
    (whole : ∀ u ∈ k8LotAtBase.rows returned.Z returned.G, (Ls.first u).bare = u) :
    K8Stands (theSides h.description Ls
      (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs second
        h₃).rows f₁ f₂ f₃) (k8LotAtBase.rows returned.Z returned.G) := by
  intro l hl
  obtain ⟨-, hGr, -⟩ := atPure_ok made
  obtain ⟨G₀, Xl, blk, hb₀, hX, hf, hp, -, -⟩ := small_block_at h.head hl
  obtain rfl : G₀ = returned.G := Option.some.inj (hb₀.symm.trans hGr)
  have hr := smallSLot_rows_of_built (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := Inst) (X := Unit) (Pb := Inst)
    (Z := returned.Z) id matsO hX
  have found : overlayLot mine (smallLot (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := Inst) (X := Unit) id matsO) =
      k8LotAtBase := by
    unfold overlayLot
    have f' : (mine.find? fun t => t.name ==
        (smallLot (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := Inst) (X := Unit) id matsO).name) =
        some k8LotAtBase := find_name apart laid
    rw [f']
  have inRows : smallBare (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := Inst) (X := Unit) (Pb := Inst) id
      (ProofFile.k8Par returned.Z returned.G Xl l, matsO returned.Z returned.G Xl l) ∈
      rowsOfLots returned.Z returned.G ((baseFilling files).lots.map (overlayLot mine)) :=
    List.mem_flatMap.2 ⟨_, List.mem_map.2
      ⟨_, P1K8.term_small_mem matrixInput OnBytes.secondHashFunction Sz.ref openHonest, found⟩, hr⟩
  obtain ⟨σ, hσ, -⟩ := (small_rows_at_base made h.head).2.2.2.2 _ hr [] .own [] 0 0 f₁
  refine ⟨Ls.first _, List.mem_map_of_mem inRows, ?_, σ, ?_, ?_⟩
  · rw [whole _ hr]
    exact hr
  · show Side.seated _ (Ls.first _).place (Ls.first _).row f₁ = some σ
    rw [(Ls.keeps₁ _).1, (Ls.keeps₁ _).2]
    exact hσ
  · obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 hσ
    have hfind := find_at _ _ blk (first_nodup h.head) hf
    have hpe : (smallBare (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := Inst) (X := Unit) (Pb := Inst) id
        (ProofFile.k8Par returned.Z returned.G Xl l, matsO returned.Z returned.G Xl l)).place = blk.place :=
      hp.symm
    rw [hpe, hfind] at hb
    obtain rfl := Option.some.inj hb
    rw [← e]
    exact hf

end

/-! ## The two conditions of use -/

section
variable {Ky X₀ : Type} {F : FileDescription Inst} {Bk : ProverCoinCounts}
  {G : Sides F Bk FullSizeMatrix IndexCommitterCoins Ky Cells X₀ Unit} {Zq : Pub} {Gr : Ground}

theorem k8KindBud_of_bear (bear : ListsOfTheKindBear G .K8 (k8LotAtBase.rows Zq Gr)) :
    Johnson.M1.KindBud G .K8 :=
  ⟨fun L hL hk =>
      Johnson.M1.budOwed_true F L (small_on_at Zq Gr L.bare (bear.first L hL hk)).2,
    fun L hL e => absurd e (bear.noneShared L hL), fun L hL e => absurd e (bear.noneSecond L hL)⟩

theorem k8OnAtEveryRun_of_bear (bear : ListsOfTheKindBear G .K8 (k8LotAtBase.rows Zq Gr))
    {H : Prover FullSizeMatrix IndexCommitterCoins Inst Ky Cells X₀ Unit} (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R) :
    KindOnAtEveryRun (G := G) (H := H) Rel T .K8 :=
  fun w₀ rc x hrel k R hR ρ r _ _ _ =>
    kindOnAtRun_of_rows bear (fun L hL => (small_on_at Zq Gr L.bare hL).1)
      (T w₀ rc x hrel k R hR) ρ r

end

/-! ## At G by its name -/

section
variable {Wt : Type} {files : VerifierAndGoals.PublicFiles} {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok returned) (h : HeadAtReturn files returned)
    (T : ThreadParts returned Wt) (K : KindRows (baseFilling files) returned.Z returned.G)
    (laid : k8LotAtBase ∈ K.lots)
include made laid

/-- **KindPays (theGAtBase h T K) .K8.** -/
theorem k8KindPays_at_theGAtBase : KindPays (theGAtBase h T K) .K8 :=
  k8KindPays_at_the_sides made h K.lots K.named K.apart K.lots_fit _ _ _ _ (theLetters h T) _ _ _
    laid fun _ _ => narrows_of_bare rfl

/-- **KindPays (theGOfReturn made h T K) .K8.** -/
theorem k8KindPays_at_theGOfReturn : KindPays (theGOfReturn made h T K) .K8 :=
  castSides_of (Q := fun _ G => KindPays G .K8) (atPure_at_laid h.head.laid made).2
    (k8KindPays_at_theGAtBase made h T K laid)

/-- **The lists of the kind at that G are rows of the lot.** -/
theorem k8ListsBear_at_theGOfReturn :
    ListsOfTheKindBear (theGOfReturn made h T K) .K8 (k8LotAtBase.rows returned.Z returned.G) :=
  castSides_of (Q := fun _ G => ListsOfTheKindBear G .K8 (k8LotAtBase.rows returned.Z returned.G))
    (atPure_at_laid h.head.laid made).2
    (k8ListsBear_at_the_sides made h K.lots K.named K.apart K.lots_fit _ _ _ _ (theLetters h T) _ _
      _ laid fun _ _ => rfl)

theorem k8KindBud_at_theGOfReturn : Johnson.M1.KindBud (theGOfReturn made h T K) .K8 :=
  k8KindBud_of_bear (k8ListsBear_at_theGOfReturn made h T K laid)

theorem k8OnAtEveryRun_at_theGOfReturn
    {H : Prover FullSizeMatrix IndexCommitterCoins Inst OnBytes.TableKey Cells Unit Unit} (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k R) :
    KindOnAtEveryRun (G := theGOfReturn made h T K) (H := H) Rel Th .K8 :=
  k8OnAtEveryRun_of_bear (k8ListsBear_at_theGOfReturn made h T K laid) Rel Th

/-- **The kind's row stands at that G.** -/
theorem k8Stands_at_theGOfReturn :
    K8Stands (theGOfReturn made h T K) (k8LotAtBase.rows returned.Z returned.G) :=
  castSides_of (Q := fun _ G => K8Stands G (k8LotAtBase.rows returned.Z returned.G))
    (atPure_at_laid h.head.laid made).2
    (k8Stands_at_the_sides made h K.lots K.named K.apart K.lots_fit _ _ _ _ (theLetters h T) _ _ _
      laid fun _ _ => rfl)

/-- **The three shares in one record.** -/
theorem k8Share_at_theGOfReturn (H : Prover FullSizeMatrix IndexCommitterCoins Inst OnBytes.TableKey Cells Unit Unit)
    (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k R) :
    KindShare returned (theGOfReturn made h T K) H Rel Th .K8 :=
  ⟨k8KindPays_at_theGOfReturn made h T K laid, k8KindBud_at_theGOfReturn made h T K laid,
    k8OnAtEveryRun_at_theGOfReturn made h T K laid Rel Th⟩

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8_places_elsewhere
#print axioms ProofFile.Honest.K8.k8KindPays_at_theGOfReturn
#print axioms ProofFile.Honest.K8.k8Share_at_theGOfReturn
#print axioms ProofFile.Honest.K8.k8Stands_at_theGOfReturn
