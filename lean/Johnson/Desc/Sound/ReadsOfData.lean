-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsOfData.lean: AT EVERY DESCRIPTION, EVERY PIECE's VIEW SHOWS JUST THE KEYS
AND POSITIONS THAT `Block.step` LOOKS FOR. Statements (`def … : Prop`) and their proofs.

Johnson/Desc/Sound/ReadsAre.lean has the law at one piece, under `KeysMatch`. Here:
  `Piece.ReadsFit p`: at all oracles and transcripts, the opened columns of the view that p's stage
    makes have, in order, the keys and positions that p's block reads by its declared rounds.
  `CutReads`: under `ChainFit` and `KeysMatch` every piece that the maker cuts has it.
  `KeysOfOk`: where the makers' tests say yes, the data's three keys match the declared labels: at
    ft = 0 on the first and the shared chain, and on the second chain at the first chain's number of
    roots + 1.
  `ReadsOfData`: FOR EVERY DESCRIPTION F, every D with `F.data file = .ok D`, `F.sealLast = true`:
    at every `Three` whose pieces are the maker's and whose three numbers ft are 0, 0 and
    `F.lastChainFirstTreeNumber` (those with which `FileDescription.runEnd` runs its folds), every piece of the three
    rows has `ReadsFit`.
NO CLAUSE OF `planOk` IS LEANT ON (not `labelsOk`): the data's key of a tree is made of the label
under which the tree is opened, and the makers' test asks that a tree has one shape at all its
openings.
Limits: the widths are not said (ReadsAre.lean). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ReadsAre
import Johnson.Desc.Sound.TilesDataProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker Johnson.G.OfPlan
open _root_.Run.PQ (CK SgX)
open OnBytes.Params (Rounds)
open OnBytes.Three (rootsIn)

variable {C : CK} {F : Frame} {S Cl W : Type}

/-- The view that the piece's stage makes shows just the keys and positions that its block reads. -/
def Piece.ReadsFit (p : Piece C F S Cl W) : Prop :=
  ∀ (y : F.E.Str) (τ : Iop.Tr (uLT C p.ds)),
    (sView C p.stage y τ).opened.map (fun c => (c.1, c.2.1)) =
      ((p.b.reads F.ft (((sView C p.stage y τ).rounds ++ p.back).map (·.drawn))).flatMap id).map
        fun w => (w.1, w.2.1)

/-! ## 1 Along the maker's cuts -/

theorem keys_nil (key : ℕ → ℕ) (ft : ℕ) (rs : List Fmt.DeclaredRound) : KeysMatch key ft rs [] := by
  cases rs <;> trivial

theorem keys_split (key : ℕ → ℕ) (ft : ℕ) :
    ∀ (rs₁ rs₂ : List Fmt.DeclaredRound) (ds : List RDT), KeysMatch key ft (rs₁ ++ rs₂) ds →
      KeysMatch key ft rs₁ (ds.take rs₁.length) ∧ KeysMatch key ft rs₂ (ds.drop rs₁.length)
  | [], rs₂, ds, h => by
    simp only [List.length_nil, List.take_zero, List.drop_zero]
    exact ⟨trivial, h⟩
  | r :: rs₁, rs₂, [], _ => by
    simp only [List.take_nil, List.drop_nil]
    exact ⟨trivial, keys_nil key ft rs₂⟩
  | r :: rs₁, rs₂, d :: ds, h => by
    have h' : RoundKeys key ft r d ∧ KeysMatch key ft (rs₁ ++ rs₂) ds := h
    obtain ⟨h1, h2⟩ := keys_split key ft rs₁ rs₂ ds h'.2
    simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons]
    exact ⟨⟨h'.1, h1⟩, h2⟩

/-- What `ChainFit` gives at the first stretch, and `ChainFit` at the rest. -/
theorem chainFit_cons (dep : ℕ → Option ℕ) (base : ℕ) (b b' : Block S Cl) (l : List (Block S Cl))
    (ds : List RDT) (pb : List Fmt.RoundView) (h : ChainFit F dep base b (b' :: l) ds pb) :
    (Matches F.a dep b.rounds (ds.take b.rounds.length) ∧ InTime base (ds.take b.rounds.length) ∧
      ∀ n sh, treeShT (ds.take b.rounds.length) n = some sh → dep (base + n) = some sh.a) ∧
    ChainFit F dep (base + nTrees (ds.take b.rounds.length)) b' l (ds.drop b.rounds.length) pb := by
  have hM := matches_split F.a dep b.rounds ((b' :: l).flatMap (·.rounds)) ds
    (by have t := h.rounds; rwa [List.flatMap_cons] at t)
  have hc := h.count
  rw [List.flatMap_cons, List.length_append] at hc
  have hs : pb.length ≤ lastRounds b' l := h.sealLast
  have hr := lastRounds_le l b'
  have hds : ds.take b.rounds.length ++ ds.drop b.rounds.length = ds := List.take_append_drop _ _
  have hT := inTime_append (ds.take b.rounds.length) (ds.drop b.rounds.length) base
    (by rw [hds]; exact h.inTime)
  refine ⟨⟨hM.1, hT.1, fun n sh hn => ?_⟩, ⟨hM.2, ?_, hs, hT.2, fun n sh hn => ?_, h.listed⟩⟩
  · have t : treeShT (ds.take b.rounds.length ++ ds.drop b.rounds.length) n = some sh := by
      rw [treeShT_append, if_pos (treeShT_lt _ _ _ hn)]
      exact hn
    rw [hds] at t
    exact h.own n sh t
  · rw [List.length_drop]
    omega
  · have t : treeShT (ds.take b.rounds.length ++ ds.drop b.rounds.length)
        (nTrees (ds.take b.rounds.length) + n) = some sh := by
      rw [treeShT_append, if_neg (by omega), Nat.add_sub_cancel_left]
      exact hn
    rw [hds] at t
    have u := h.own _ sh t
    rwa [← Nat.add_assoc] at u

/-- **Every piece that the maker cuts shows its block just what it looks for.** -/
def CutReads : Prop :=
  ∀ (C : CK) (F : Frame) (S Cl W : Type) (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds)
    (putBack : List Fmt.RoundView) (dep : ℕ → Option ℕ) (l : List (Block S Cl)) (b : Block S Cl)
    (i base : ℕ) (ds : List RDT),
    ChainFit F dep base b l ds putBack → KeysMatch F.key F.ft ((b :: l).flatMap (·.rounds)) ds →
    ∀ p ∈ (cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2, p.ReadsFit

theorem cutReads : CutReads := by
  intro C F S Cl W rest putBack dep l
  induction l with
  | nil =>
    intro b i base ds h k p hp
    rw [cutRow_nil] at hp
    have e : p = pieceOf b base ds putBack (rest i ds) := by simpa using hp
    subst e
    exact pieceReads C F S Cl W dep b base ds putBack (rest i ds) (by simpa using h.rounds)
      (by simpa using k) h.inTime h.own h.listed
  | cons b' l ih =>
    intro b i base ds h k p hp
    rw [cutRow_cons] at hp
    obtain ⟨⟨m1, t1, o1⟩, h2⟩ := chainFit_cons dep base b b' l ds putBack h
    have k' := keys_split F.key F.ft b.rounds ((b' :: l).flatMap (·.rounds)) ds
      (by rwa [List.flatMap_cons] at k)
    rcases List.mem_cons.1 hp with e | hp
    · subst e
      exact pieceReads C F S Cl W dep b base _ [] (rest i _) m1 k'.1 t1 o1 h.listed
    · exact ih b' (i + 1) _ _ h2 k'.2 p hp

/-! ## 2 The data's keys -/

theorem key_of_treeIs (Wh : Three.Whole) (c : ℕ) (s : Fmt.Shape) (j : ℕ) (h : TreeIs Wh s j) :
    Wh.key c j = s.tree - (if c = 2 then Three.first₃ Wh.t₁ else 0) := by
  obtain ⟨t, ht, rfl⟩ := h
  unfold Three.Whole.key
  rw [ht]
  rfl

/-- One chain: the key of each opened tree is its declared label's number less the chain's first. -/
theorem keys_chain (Wh : Three.Whole) (c : ℕ) (e : List (List ByteArray × ByteArray))
    (dl : List Fmt.DeclaredRound) (R : Rounds) (ds : List Three.RDL) (w : WrittenAs e dl R)
    (f : DataFits Wh R ds) :
    List.Forall₂ (RoundKeys (Wh.key c) (if c = 2 then Three.first₃ Wh.t₁ else 0)) dl
      (ds.map rdtOf) := by
  rw [List.forall₂_map_right_iff]
  have f' : List.Forall₂ (fun x d => RoundData Wh (keyOf x) d) R ds := List.forall₂_map_left_iff.1 f
  refine (forall₂_comp w f').imp ?_
  rintro r d ⟨x, ⟨hx, -⟩, -, g2⟩
  have g2' : List.Forall₂ (TreeIs Wh) (x.1.opens.map (·.1)) d.opens := g2
  show List.Forall₂ _ r.opens d.opens
  rw [round_shapes e r x.1 hx, List.forall₂_map_left_iff] at g2'
  exact g2'.imp fun o j ho => key_of_treeIs Wh c o.1 j ho

theorem keys_of_prefix (key : ℕ → ℕ) (ft : ℕ) : ∀ (rs : List Fmt.DeclaredRound) (ds ds' : List RDT),
    List.Forall₂ (RoundKeys key ft) rs ds → ds' <+: ds → KeysMatch key ft rs ds'
  | [], _, _, _, _ => trivial
  | _ :: _, _, [], _, _ => trivial
  | _ :: _, [], _ :: _, h, _ => by cases h
  | r :: rs, d :: ds, d' :: ds', h, p => by
    obtain ⟨h1, t⟩ := List.forall₂_cons.1 h
    obtain ⟨e, p'⟩ := List.cons_prefix_cons.1 p
    subst e
    exact ⟨h1, keys_of_prefix key ft rs ds ds' t p'⟩

theorem foldl_roots : ∀ (l : List Fmt.DeclaredRound) (n : ℕ),
    l.foldl (fun n r => n + r.entry.roots) n = n + (l.map (·.entry.roots)).sum
  | [], n => by simp
  | r :: l, n => by
    rw [List.foldl_cons, foldl_roots l, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem round_entry (e : List (List ByteArray × ByteArray)) (r : Fmt.DeclaredRound) (x : Fmt.Round)
    (h : r.round e = some x) : x.entry = r.entry := by
  unfold Fmt.DeclaredRound.round at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨os, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

theorem fits_roots {R₁ R₂ R₃ : Rounds} {m : ℕ} (h : Three.Whole.fits R₁ R₂ R₃ m = true) :
    ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots := by
  unfold Three.Whole.fits at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨c1, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  intro r hr
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 c1 (0, R₁) (by simp)) r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact h1.2

theorem rootsIn_written (e : List (List ByteArray × ByteArray)) : ∀ (dl : List Fmt.DeclaredRound)
    (R : Rounds), WrittenAs e dl R → (∀ r ∈ R, r.1.items.countP (· == .root) = r.1.entry.roots) →
    rootsIn R = (dl.map (·.entry.roots)).sum
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | r :: dl, x :: R, h, q => by
    obtain ⟨⟨h1, -⟩, t⟩ := List.forall₂_cons.1 h
    have ih := rootsIn_written e dl R t fun z hz => q z (List.mem_cons_of_mem _ hz)
    unfold rootsIn at ih ⊢
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, q x List.mem_cons_self,
      round_entry e r x.1 h1]

/-- **Where the makers' tests say yes, the data's keys match the declared labels.** -/
def KeysOfOk : Prop :=
  ∀ (a : ℕ) (R₁ R₂ R₃ : Rounds) (e₁ e₂ e₃ : List (List ByteArray × ByteArray))
    (d₁ d₂ d₃ : List Fmt.DeclaredRound),
    WrittenAs e₁ d₁ R₁ → WrittenAs e₂ d₂ R₂ → WrittenAs e₃ d₃ R₃ →
    okAt a (some (R₁, R₂, R₃)) = true →
    KeysMatch (dataOf a R₁ R₂ R₃).key₁ 0 d₁ (dataOf a R₁ R₂ R₃).ds₁ ∧
      KeysMatch (dataOf a R₁ R₂ R₃).key₂ 0 d₂ (dataOf a R₁ R₂ R₃).ds₂ ∧
      KeysMatch (dataOf a R₁ R₂ R₃).key₃ (d₁.foldl (fun n r => n + r.entry.roots) 0 + 1) d₃
        (dataOf a R₁ R₂ R₃).ds₃

theorem keysOfOk : KeysOfOk := by
  intro a R₁ R₂ R₃ e₁ e₂ e₃ d₁ d₂ d₃ w₁ w₂ w₃ hok
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := (okAt_parts (R := (R₁, R₂, R₃)) hok).fits
  have k₁ := keys_chain (Three.Whole.of R₁ R₂ R₃) 0 e₁ d₁ R₁ _ w₁ (dataFits₁ hf)
  have k₂ := keys_chain (Three.Whole.of R₁ R₂ R₃) 1 e₂ d₂ R₂ _ w₂ (dataFits₂ hf)
  have k₃ := keys_chain (Three.Whole.of R₁ R₂ R₃) 2 e₃ d₃ R₃ _ w₃ (dataFits₃ hf)
  have r₁ : rootsIn R₁ = (d₁.map (·.entry.roots)).sum := rootsIn_written e₁ d₁ R₁ w₁ (fits_roots hf)
  have e₃' : d₁.foldl (fun n r => n + r.entry.roots) 0 + 1 =
      (if (2 : ℕ) = 2 then Three.first₃ (Three.Whole.of R₁ R₂ R₃).t₁ else 0) := by
    rw [foldl_roots, Nat.zero_add, ← r₁]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · refine keys_of_prefix _ _ d₁ _ _ k₁ ?_
    show (Three.Whole.of R₁ R₂ R₃).ds₁.dropLast.map rdtOf <+: _
    rw [List.map_dropLast]
    exact List.dropLast_prefix _
  · exact keys_of_prefix _ _ d₂ _ _ k₂ (List.prefix_refl _)
  · rw [e₃']
    exact keys_of_prefix _ _ d₃ _ _ k₃ (List.prefix_refl _)

/-! ## 3 At every description -/

/-- **At every description every piece's view shows just the keys and positions that the step looks
for.** -/
def ReadsOfData : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    F.sealLast = true →
    ∀ (C : CK) (Y S₁ S₂ S₃ X₁ X₂ Cl W : Type) (T : Three C D (allOf D) Y S₁ S₂ S₃ X₁ X₂ Cl W)
      (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
      (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl)) rest₁ rest₂ rest₃ (r : Fmt.RoundView),
      (b₁ :: l₁).map (·.rounds) = F.first.blocksInOrder.map (·.rounds) →
      (b₂ :: l₂).map (·.rounds) = F.shared.blocksInOrder.map (·.rounds) →
      (b₃ :: l₃).map (·.rounds) = F.second.blocksInOrder.map (·.rounds) →
      T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r →
      T.ft₁ = 0 → T.ft₂ = 0 → T.ft₃ = F.lastChainFirstTreeNumber →
      (∀ p ∈ T.p₁ :: T.l₁, p.ReadsFit) ∧ (∀ p ∈ T.p₂ :: T.l₂, p.ReadsFit) ∧
        ∀ p ∈ T.p₃ :: T.l₃, p.ReadsFit

theorem readsOfData : ReadsOfData := by
  intro Xi F file D h hs C Y S₁ S₂ S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r g₁ g₂ g₃ hc
    f₁ f₂ f₃
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hok, rfl⟩ := data_ok F file D h
  obtain ⟨w₁, w₂, w₃⟩ := written_as file F.roundsDeclaredByBlocks _ hR
  have hl : 1 ≤ lastRounds b₁ l₁ := by
    rw [lastRounds_eq, g₁, List.getLast?_map]
    have hq := sealLast_any F hs
    cases hg : F.first.blocksInOrder.getLast? with
    | none => rw [hg] at hq; cases hq
    | some b =>
      rw [hg] at hq
      have hne : b.rounds ≠ [] := by
        intro e
        simp [e] at hq
      show 1 ≤ b.rounds.length
      exact List.length_pos_iff.2 hne
  obtain ⟨c₁, c₂, c₃⟩ := fitOfOk _ R₁ R₂ R₃ _ _ _ _ _ _ w₁ w₂ w₃ hok S₁ S₂ S₃ Cl b₁ l₁ b₂ l₂ b₃ l₃ r
    (dataOf F.tableDepth R₁ R₂ R₃).key₁ (dataOf F.tableDepth R₁ R₂ R₃).key₂
    (dataOf F.tableDepth R₁ R₂ R₃).key₃ T.ft₁ T.ft₂ T.ft₃
    (flat_of_map _ _ g₁) (flat_of_map _ _ g₂) (flat_of_map _ _ g₃) hl
  obtain ⟨k₁, k₂, k₃⟩ := keysOfOk _ R₁ R₂ R₃ _ _ _ _ _ _ w₁ w₂ w₃ hok
  have p₁ := congrArg Prod.fst hc.c₁
  have q₁ := congrArg Prod.snd hc.c₁
  have p₂ := congrArg Prod.fst hc.c₂
  have q₂ := congrArg Prod.snd hc.c₂
  have p₃ := congrArg Prod.fst hc.c₃
  have q₃ := congrArg Prod.snd hc.c₃
  simp only at p₁ q₁ p₂ q₂ p₃ q₃
  refine ⟨?_, ?_, ?_⟩
  · rw [p₁, q₁]
    refine cutReads _ _ _ _ _ _ _ _ _ _ _ _ _ c₁ ?_
    show KeysMatch _ T.ft₁ _ _
    rw [f₁, flat_of_map _ _ g₁]
    exact k₁
  · rw [p₂, q₂]
    refine cutReads _ _ _ _ _ _ _ _ _ _ _ _ _ c₂ ?_
    show KeysMatch _ T.ft₂ _ _
    rw [f₂, flat_of_map _ _ g₂]
    exact k₂
  · rw [p₃, q₃]
    refine cutReads _ _ _ _ _ _ _ _ _ _ _ _ _ c₃ ?_
    show KeysMatch _ T.ft₃ _ _
    rw [f₃, flat_of_map _ _ g₃]
    exact k₃

end VerifiableInference.Desc.Sound
