-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ReplyShareAtTheG.lean: the share of the next token's part (kind K7: the label of that sub-protocol in
the description) in the premises of T3's theorem, at the sides that E2E/TheSides.lean builds.

  reply_fits_the_base_slot, reply_fit_at_name   the base filling's lot of that name is this lot
  reply_named_base                               the base filling has a lot of that name
  reply_good_at_head       Good at the side, at the row's own On and bound, under the library's head
  ReplyListsAt             five statements on the lists of this kind
  reply_pays_at_rows, reply_lists_at_rows   at the rows that KindRows lays
  reply_share_at_the_G     CONDITIONAL: made; h; hk: KindShare at theGOfReturn
  reply_row_in_the_G       CONDITIONAL: made; h; hk: the one row stands in G's first chain and is seated

The row's On and bound hold everywhere, so no family of invariants is read.
No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import E2E.TheG
import E2E.KindPaysOfALot
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsByKind
import Johnson.Desc.ProofFile.Honest.Law.KindPaysOnlineForms
import Johnson.Desc.ProofFile.Honest.K7.Rows
import Johnson.Desc.ProofFile.Honest.K7.RowsAtScope
import Johnson.Desc.ProofFile.Honest.K7.AtBook
import Johnson.Desc.ProofFile.Honest.K7.AtFill
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.K1.Pay.Pays
import E2E.TheKOfRecord

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.TheSides
open AtPublicFiles.AtFiles
open ProofFile.Honest
open ProofFile.Honest.Term (baseMaker baseFilling matrixInput onlineBase online_shared_kinds
  online_second_kinds)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.TheG (ThreadParts theGOfReturn)
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open VerifiableInference.Compilation (KindPays)
open P5J (AtMgA TS)

/-- The row's lot at the base filling's letters. -/
abbrev replyBaseLot : SLot (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst :=
  replySLot (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit)

/-- **A lot of the base filling that bears the name is this lot, its simulators forgotten.** -/
theorem reply_fits_the_base_slot (files : VerifierAndGoals.PublicFiles) :
    ∀ L ∈ (baseFilling files).lots, L.name = replyBaseLot.name → replyBaseLot.toHLot = L := by
  intro L hL hn
  have hL' : L ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
      openHonest).lots := hL
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots] at hL'
  simp only [widerPairs, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hL'
  rcases hL' with (((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl) | rfl
  case inl.inl.inl.inr.inr.inl => rfl
  all_goals exact absurd hn (by decide)

/-- The lot's halves are the filling's at that name. -/
theorem reply_fit_at_name (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) :
    ∀ L ∈ (baseFilling files).lots, L.name = replyBaseLot.name →
      (replyBaseLot.rows Z Gr).map (·.half) = L.halves Z Gr := by
  intro L hL hn
  rw [← reply_fits_the_base_slot files L hL hn]
  rfl

/-- The base filling has a lot of that name. -/
theorem reply_named_base (files : VerifierAndGoals.PublicFiles) :
    (baseFilling files).lots.any (fun L => L.name == replyBaseLot.name) = true := by
  refine List.any_eq_true.2 ⟨lotK7, ?_, ?_⟩
  · show _ ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots
    rw [fillPairs_lots]
    exact List.mem_map.2 ⟨(lotK7, KindName.K7), List.mem_append_left _ (by simp [widerPairs]), rfl⟩
  · rfl

/-- **What this kind hands in for its lot.** -/
def k7Entry (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) : LotEntry (baseFilling files) Z Gr :=
  ⟨replyBaseLot, reply_named_base files, reply_fit_at_name files Z Gr⟩

section Good
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc X₀ X : Type} {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}

/-- **Good at the side at the last link, at the row's own On and bound.** CONDITIONAL: h; made. -/
theorem reply_good_at_head (h : AtMgA OnBytes.secondHashFunction Z D r₀ A.Z Np cF x₀)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (ord : List Place) (chain firstTree : Nat)
    (fs : List (Fall TS))
    {σ : Side TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Cells) (Local W₀ Rc ProofFile.Inst Cells) X ProofFile.Inst}
    (hσ : Side.seated cF.blocksInOrder (⟨1, some 24, 1, .K7⟩ : Place) (replyRow 24 1) fs = some σ) :
    Good pre Face.own σ A.B ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) (fun _ _ _ => True) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hr, ho⟩ := reply_seated_at_scope h.scope h.reads O fs σ hσ
  have hW := ProofFile.Honest.K14.atPure_book_at_head h made
  have hp : (P5J.F0T OnBytes.secondHashFunction A.Z Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  exact reply_good_seated pre A.B ord chain firstTree _ fs hσ hr ho
    (fun q => reply_spent_of_open h.scope h.reads O hW hp q)

end Good

/-- **Five statements on the lists of this kind.** -/
structure ReplyListsAt {F : FileDescription ProofFile.Inst} {Bk : ProverCoinCounts}
    (G : Sides F Bk FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (rows : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
      ProofFile.Inst)) : Prop where
  first : ∀ L ∈ G.first, L.place.kind = KindName.K7 → L.bare ∈ rows
  noneShared : ∀ L ∈ G.shared, L.place.kind ≠ KindName.K7
  noneSecond : ∀ L ∈ G.second, L.place.kind ≠ KindName.K7
  on : ∀ L ∈ G.first, L.place.kind = KindName.K7 → ∀ v ca m front, L.On v ca m front
  bud : ∀ L ∈ G.first, L.place.kind = KindName.K7 → ∀ a b c, L.bud a b c

variable {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

theorem reply_alone (Z : ProofFile.Pub) (Gr : ProofFile.Ground) :
    ∀ M ∈ (baseFilling files).lots, (∃ l ∈ [replyBaseLot], l.name = M.name) ∨
      ∀ x ∈ M.halves Z Gr, x.place.kind ≠ KindName.K7 := by
  intro M hM
  rcases lot_alone _ _ _ _ (onlyK7 _ _ _ _) Z Gr M hM with rfl | hno
  · exact Or.inl ⟨_, List.mem_singleton.2 rfl, rfl⟩
  · exact Or.inr hno

theorem shared_not_reply (h : AtMgA OnBytes.secondHashFunction files D r₀ A.Z Np cF x₀) :
    ∀ q ∈ (baseFilling files).shared A.Z A.G, q.place.kind ≠ KindName.K7 := by
  intro q hq hk
  rcases online_shared_kinds h A.G q hq with e | e | e <;> exact absurd (hk.symm.trans e) (by decide)

theorem second_not_reply : ∀ q ∈ (baseFilling files).second A.Z A.G, q.place.kind ≠ KindName.K7 := by
  intro q hq hk
  exact absurd (hk.symm.trans (online_second_kinds _ _ q hq)) (by decide)

/-- The row, under the head. -/
theorem reply_row_at_head (h : AtMgA OnBytes.secondHashFunction files D r₀ A.Z Np cF x₀)
    (made : baseMaker files = .ok A) : replyBaseLot.rows A.Z A.G = [replyUnlettered 24 1] := by
  obtain ⟨-, hG, -⟩ := atPure_ok made
  show [replyUnlettered (A.G.built.size - 1) 1] = _
  rw [ProofFile.Honest.FirstFill.built_25 h hG]

/-- **KindPays at this kind at the rows that the kinds lay.** CONDITIONAL: h; made; e; hk; hb. -/
theorem reply_pays_at_rows (h : AtMgA OnBytes.secondHashFunction files D r₀ A.Z Np cF x₀)
    (made : baseMaker files = .ok A) {F : FileDescription ProofFile.Inst} (e : F = A.F)
    (K : KindRows (baseFilling files) A.Z A.G)
    (Ls : Letters F A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (hk : replyBaseLot ∈ K.lots) (hb : ∀ u, (Ls.first u).bare = u) :
    KindPays (theSides F Ls K.slots.rows f₁ f₂ f₃) KindName.K7 := by
  subst e
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction A.Z Np cF :=
    (ProofFile.Honest.atPure_at_laid h.laid made).2
  refine kindPays_of_kindRows K Ls f₁ f₂ f₃ KindName.K7 [replyBaseLot] (fun l hl => ?_)
    (reply_alone A.Z A.G) (fun q hq hk' => absurd hk' (shared_not_reply h q hq))
    (fun q hq hk' => absurd hk' (second_not_reply q hq)) (fun l hl u hu _ σ hσ => ?_)
    (fun u hu hk' σ hσ => ?_) (fun u hu hk' σ hσ => ?_)
  · rw [List.mem_singleton.1 hl]
    exact hk
  · obtain rfl := List.mem_singleton.1 hl
    rw [reply_row_at_head h made] at hu
    obtain rfl := List.mem_singleton.1 hu
    have hq := hb (replyUnlettered 24 1)
    refine ⟨⟨fun _ _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩, fun _ _ _ _ => False,
      fun _ _ _ _ => False, ?_⟩
    obtain ⟨Z', G', F', B', H', rd', rw'⟩ := A
    dsimp only at eF h made hσ ⊢
    subst eF
    exact reply_good_at_head h made _ _ _ _ f₁ hσ
  · obtain ⟨q, hq, hp⟩ := List.any_eq_true.1 (K.shared_named u hu)
    exact absurd (by rw [beq_iff_eq.1 hp]; exact hk') (shared_not_reply h q hq)
  · obtain ⟨q, hq, hp⟩ := List.any_eq_true.1 (K.second_named u hu)
    exact absurd (by rw [beq_iff_eq.1 hp]; exact hk') (second_not_reply q hq)

/-- **The five statements at the rows that the kinds lay.** CONDITIONAL: h; made; e; hk; hb. -/
theorem reply_lists_at_rows (h : AtMgA OnBytes.secondHashFunction files D r₀ A.Z Np cF x₀)
    (made : baseMaker files = .ok A) {F : FileDescription ProofFile.Inst} (e : F = A.F)
    (K : KindRows (baseFilling files) A.Z A.G)
    (Ls : Letters F A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (hk : replyBaseLot ∈ K.lots) (hb : ∀ u, (Ls.first u).bare = u) :
    ReplyListsAt (theSides F Ls K.slots.rows f₁ f₂ f₃) [replyUnlettered 24 1] := by
  subst e
  have hfirst : ∀ L ∈ (theSides A.F Ls K.slots.rows f₁ f₂ f₃).first, L.place.kind = KindName.K7 →
      L.bare ∈ [replyUnlettered (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit) 24 1] := by
    intro L hL hkind
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [hb u]
    have hk' : u.place.kind = KindName.K7 := (Ls.keeps₁ u).1 ▸ hkind
    obtain ⟨l, hl, hul⟩ := rows_of_overlay (Z := A.Z) (Gr := A.G) (ls := [replyBaseLot]) K.apart
      (fun l hl => by rw [List.mem_singleton.1 hl]; exact hk) K.lots_fit (reply_alone A.Z A.G) u hu hk'
    obtain rfl := List.mem_singleton.1 hl
    rw [reply_row_at_head h made] at hul
    exact hul
  refine ⟨hfirst, fun L hL hkind => ?_, fun L hL hkind => ?_, fun L hL hkind v ca m front => ?_,
    fun L hL hkind a b c => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hu
    have eq := overlayRow_half (K.shared_fit q hq)
    have ep : (Ls.shared (overlayRow K.shared q)).place = q.place := by
      rw [(Ls.keeps₂ _).1]
      exact congrArg Placed.place eq
    rw [ep] at hkind
    exact shared_not_reply h q hq hkind
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hu
    have eq := overlayRow_half (K.second_fit q hq)
    have ep : (Ls.second (overlayRow K.second q)).place = q.place := by
      rw [(Ls.keeps₃ _).1]
      exact congrArg Placed.place eq
    rw [ep] at hkind
    exact second_not_reply q hq hkind
  · have hr : L.bare = replyUnlettered 24 1 := List.mem_singleton.1 (hfirst L hL hkind)
    have : L.bare.On v ca m front := by
      rw [hr]
      trivial
    exact this
  · have hr : L.bare = replyUnlettered 24 1 := List.mem_singleton.1 (hfirst L hL hkind)
    have : L.bare.bud a b c := by
      rw [hr]
      trivial
    exact this

/-- **KindPays and the five statements give the share**, at every prover, relation and family of
invariants. -/
theorem reply_share_of_lists {G : Sides A.F A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit}
    {rows : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
      ProofFile.Inst)}
    (p : KindPays G KindName.K7) (l : ReplyListsAt G rows)
    (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready A.F A.B (G.prover H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B (G.prover H) w₀ rc x k R) :
    KindShare A G H Rel Th KindName.K7 :=
  ⟨p,
    ⟨fun L hL hk => Johnson.M1.budOwed_true _ L (l.bud L hL hk),
      fun L hL hk => absurd hk (l.noneShared L hL), fun L hL hk => absurd hk (l.noneSecond L hL)⟩,
    fun _ _ _ _ _ _ _ ρ r _ _ _ =>
      ⟨fun L hL hk => onAtRun₁_of_always _ ρ r (l.on L hL hk),
        fun L hL hk => absurd hk (l.noneShared L hL), fun L hL hk => absurd hk (l.noneSecond L hL)⟩⟩

variable {Wt : Type}

/-- **The share at G at the return's own description.** CONDITIONAL: made; h; hk. -/
theorem reply_share_at_the_G (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G) (hk : replyBaseLot ∈ K.lots)
    (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T K).prover H) w₀ rc x k R) :
    KindShare A (theGOfReturn made h T K) H Rel Th KindName.K7 :=
  have e := (ProofFile.Honest.atPure_at_laid h.head.laid made).2.symm
  reply_share_of_lists
    (castSides_of (Q := fun _ G => KindPays G KindName.K7) _
      (reply_pays_at_rows h.head made e K _ _ _ _ hk fun _ => rfl))
    (castSides_of (Q := fun _ G => ReplyListsAt G [replyUnlettered 24 1]) _
      (reply_lists_at_rows h.head made e K _ _ _ _ hk fun _ => rfl)) H Rel Th

/-- The one row stands in the first chain of the sides, and is seated where the description has its
block. CONDITIONAL: h; made; e; hk; hb; hs. -/
theorem reply_row_in_sides (h : AtMgA OnBytes.secondHashFunction files D r₀ A.Z Np cF x₀)
    (made : baseMaker files = .ok A) {F : FileDescription ProofFile.Inst} (e : F = A.F)
    (K : KindRows (baseFilling files) A.Z A.G)
    (Ls : Letters F A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (hk : replyBaseLot ∈ K.lots) (hb : ∀ u, (Ls.first u).bare = u)
    (hs : ∃ σ, Side.seated A.F.first.blocksInOrder (⟨1, some 24, 1, .K7⟩ : Place)
      (replyRow (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit) 24 1) [] = some σ) :
    ∃ L ∈ (theSides F Ls K.slots.rows f₁ f₂ f₃).first, L.bare = replyUnlettered 24 1 ∧
      ∃ σ, L.side F.first.blocksInOrder = some σ := by
  subst e
  obtain ⟨M, hM, hn⟩ := List.any_eq_true.1 (K.named _ hk)
  have hf := find_name K.apart hk
  rw [← beq_iff_eq.1 hn] at hf
  have he : overlayLot K.lots M = replyBaseLot := by
    unfold overlayLot
    rw [hf]
  have hr : replyUnlettered 24 1 ∈ replyBaseLot.rows A.Z A.G := by
    rw [reply_row_at_head h made]
    exact List.mem_singleton.2 rfl
  have hin : replyUnlettered 24 1 ∈ rowsOfLots A.Z A.G
      ((baseFilling files).lots.map (overlayLot K.lots)) :=
    List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨M, hM, rfl⟩, he ▸ hr⟩
  obtain ⟨ep, er⟩ := Ls.keeps₁ (replyUnlettered 24 1)
  obtain ⟨σ, hσ⟩ := hs
  refine ⟨Ls.first (replyUnlettered 24 1), List.mem_map_of_mem hin, hb _, σ, ?_⟩
  show Side.seated A.F.first.blocksInOrder (Ls.first (replyUnlettered 24 1)).place
    (Ls.first (replyUnlettered 24 1)).row [] = some σ
  rw [ep, er]
  exact hσ

/-- **The one row stands in G's first chain, and is seated.** CONDITIONAL: made; h; hk. -/
theorem reply_row_in_the_G (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G) (hk : replyBaseLot ∈ K.lots) :
    ∃ L ∈ (theGOfReturn made h T K).first, L.bare = replyUnlettered 24 1 ∧
      ∃ σ, L.side A.F.first.blocksInOrder = some σ := by
  have e := (ProofFile.Honest.atPure_at_laid h.head.laid made).2
  obtain ⟨-, -, e3, -, -, -, -, eH, -⟩ := atPure_ok made
  obtain ⟨-, t1, -⟩ := atPure_tests made
  have hl : (lotK7 : HLot (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit) ∈
      (baseFilling files).lots := by
    show _ ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots
    rw [fillPairs_lots]
    exact List.mem_map.2 ⟨(lotK7, KindName.K7), List.mem_append_left _ (by simp [widerPairs]), rfl⟩
  have hf := reply_fit_at_name files A.Z A.G _ hl rfl
  have hin : (replyUnlettered (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit) 24 1).half ∈ A.H.first := by
    rw [eH]
    refine List.mem_flatMap.2 ⟨_, hl, ?_⟩
    rw [← hf, reply_row_at_head h.head made]
    exact List.mem_singleton.2 rfl
  obtain ⟨b, hb, eb⟩ := ProofFile.Honest.K1.Pay.of_strays t1 hin
  have hsome : ∃ σ, Side.seated A.F.first.blocksInOrder (⟨1, some 24, 1, .K7⟩ : Place)
      (replyRow (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit) 24 1) [] = some σ := by
    unfold Side.seated
    cases hq : A.F.first.blocksInOrder.find? fun b => b.place == (⟨1, some 24, 1, .K7⟩ : Place) with
    | none =>
      exact absurd (by rw [eb]; rfl) (List.find?_eq_none.1 hq b hb)
    | some c => exact ⟨_, rfl⟩
  exact castSides_of (Q := fun F₀ G => ∃ L ∈ G.first, L.bare = replyUnlettered 24 1 ∧
      ∃ σ, L.side F₀.first.blocksInOrder = some σ) _
    (reply_row_in_sides h.head made e.symm K _ _ _ _ hk (fun _ => rfl) hsome)

end AtPublicFiles.TheSides

#print axioms AtPublicFiles.TheSides.reply_fits_the_base_slot
#print axioms AtPublicFiles.TheSides.reply_fit_at_name
#print axioms AtPublicFiles.TheSides.reply_named_base
#print axioms AtPublicFiles.TheSides.reply_good_at_head
#print axioms AtPublicFiles.TheSides.reply_pays_at_rows
#print axioms AtPublicFiles.TheSides.k7Entry
#print axioms AtPublicFiles.TheSides.reply_lists_at_rows
#print axioms AtPublicFiles.TheSides.reply_share_at_the_G
#print axioms AtPublicFiles.TheSides.reply_row_in_the_G
