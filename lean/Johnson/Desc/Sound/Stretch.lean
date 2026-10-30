-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/Stretch.lean: A PIECE's STRETCH IS THE DATA OF ITS OWN BLOCK's DECLARED ROUNDS.
Statements (`def … : Prop`) and their proofs.

Why. A block's law of soundness is owed at the piece that the maker cuts (`cutRow`, Tiles.lean): at
ITS stretch of the rounds' data. The tiling says of a stretch only counts, stored parts and depths.
Whoever proves its law has to know the stretch: round by round, field by field.
  `RoundIs num r d`: the round's data d are those of the declared round r: the entry; the kind,
    which is that of the entry's name; the items; the stored parts; THE TREES THAT IT OPENS, BY
    THEIR NUMBERS THROUGH THE FILE (`num`: for chain c `numAt D.t₁ D.t₂ c`,
    Johnson/Desc/BlockSlot.lean); and it sends as many trees as the entry says roots.
  `Along P rs ds`: round by round, as far as the data go.
  `CutAlong`: what holds along a chain holds along every piece that the maker cuts.
  `StretchOfOk`: where the makers' tests say yes, `RoundIs` holds along the three chains.
  `StretchOfData`: FOR EVERY DESCRIPTION F and every D with `F.data file = .ok D`: at every `Three`
    whose pieces are the maker's: along every piece of the three rows.
HOW FAR THE DATA GO: by the tiling (`fitsOfData`: `Owed`'s first count, Tiles.lean) a piece's
stretch has as many rounds as its block declares, less the rounds put back (the sealing round, at
the first chain's last block alone): so `Along` reaches every declared round but that one.
So of the six fields of a round's data five are said in closed form.
Limits. THE SIXTH, THE SHAPES OF THE TREES THAT A ROUND SENDS, IS NOT SAID HERE: by the data's make
a tree's shape is the shape under which it is first opened, anywhere in the file; that this is what
the sending block tells of it (`Block.oracles`) hangs on a clause of `planOk`:
Johnson/Desc/Sound/OraclesAre.lean. No clause of `planOk` is leant on here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ReadsOfData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker Johnson.G.OfPlan
open _root_.Run.PQ (CK SgX)
open OnBytes.Params (Rounds)
open OnBytes.Three (rootsIn rdsFromL rdOf wholeNo tagRoot tagRun)

variable {C : CK} {F : Frame} {S Cl W : Type}

/-- The round's data d are those of the declared round r, but for the shapes of the trees that it
sends. -/
def RoundIs (num : Fmt.TreeSource → ℕ) (r : Fmt.DeclaredRound) (d : RDT) : Prop :=
  d.entry = r.entry ∧ Fmt.kindOf r.entry.name = some d.kind ∧ d.items = r.items ∧
    d.stored = r.stored ∧ d.opens = r.opens.map (fun o => num o.2) ∧
    d.trees.length = r.entry.roots

/-- Round by round, as far as the data go. -/
def Along (P : Fmt.DeclaredRound → RDT → Prop) : List Fmt.DeclaredRound → List RDT → Prop
  | r :: rs, d :: ds => P r d ∧ Along P rs ds
  | _, _ => True

/-! ## 1 Along the maker's cuts -/

theorem along_nil (P : Fmt.DeclaredRound → RDT → Prop) (rs : List Fmt.DeclaredRound) : Along P rs [] := by
  cases rs <;> trivial

theorem along_split (P : Fmt.DeclaredRound → RDT → Prop) :
    ∀ (rs₁ rs₂ : List Fmt.DeclaredRound) (ds : List RDT), Along P (rs₁ ++ rs₂) ds →
      Along P rs₁ (ds.take rs₁.length) ∧ Along P rs₂ (ds.drop rs₁.length)
  | [], rs₂, ds, h => by
    simp only [List.length_nil, List.take_zero, List.drop_zero]
    exact ⟨trivial, h⟩
  | r :: rs₁, rs₂, [], _ => by
    simp only [List.take_nil, List.drop_nil]
    exact ⟨trivial, along_nil P rs₂⟩
  | r :: rs₁, rs₂, d :: ds, h => by
    have h' : P r d ∧ Along P (rs₁ ++ rs₂) ds := h
    obtain ⟨h1, h2⟩ := along_split P rs₁ rs₂ ds h'.2
    simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons]
    exact ⟨⟨h'.1, h1⟩, h2⟩

/-- **What holds along a chain holds along every piece that the maker cuts.** -/
def CutAlong : Prop :=
  ∀ (C : CK) (F : Frame) (S Cl W : Type) (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds)
    (putBack : List Fmt.RoundView) (P : Fmt.DeclaredRound → RDT → Prop) (l : List (Block S Cl))
    (b : Block S Cl) (i base : ℕ) (ds : List RDT), Along P ((b :: l).flatMap (·.rounds)) ds →
    ∀ p ∈ (cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2,
      Along P p.b.rounds p.ds

theorem cutAlong : CutAlong := by
  intro C F S Cl W rest putBack P l
  induction l with
  | nil =>
    intro b i base ds k p hp
    rw [cutRow_nil] at hp
    have e : p = pieceOf b base ds putBack (rest i ds) := by simpa using hp
    subst e
    have k' : Along P b.rounds ds := by simpa using k
    exact k'
  | cons b' l ih =>
    intro b i base ds k p hp
    rw [cutRow_cons] at hp
    have k' := along_split P b.rounds ((b' :: l).flatMap (·.rounds)) ds
      (by rwa [List.flatMap_cons] at k)
    rcases List.mem_cons.1 hp with e | hp
    · subst e
      exact k'.1
    · exact ih b' (i + 1) _ _ k'.2 p hp

theorem along_of_prefix (P : Fmt.DeclaredRound → RDT → Prop) :
    ∀ (rs : List Fmt.DeclaredRound) (ds ds' : List RDT), List.Forall₂ P rs ds → ds' <+: ds →
      Along P rs ds'
  | [], _, _, _, _ => trivial
  | _ :: _, _, [], _, _ => trivial
  | _ :: _, [], _ :: _, h, _ => by cases h
  | r :: rs, d :: ds, d' :: ds', h, p => by
    obtain ⟨h1, t⟩ := List.forall₂_cons.1 h
    obtain ⟨e, p'⟩ := List.cons_prefix_cons.1 p
    subst e
    exact ⟨h1, along_of_prefix P rs ds ds' t p'⟩

/-! ## 2 The numbers of the opened trees -/

/-- The stand-ins under which `writtenOf` writes the trees that the third chain takes over. -/
def standIns (n₁ n₂ : ℕ) : List (List ByteArray × ByteArray) :=
  [((List.range n₁).map tagRoot, tagRun 1), ((List.range n₂).map tagRoot, tagRun 2)]

theorem tagRoot_size (n : ℕ) : (tagRoot n).size = n + 1 := by
  unfold tagRoot
  show (Array.replicate (n + 1) (0 : UInt8)).size = n + 1
  exact Array.size_replicate

theorem whole_own (t₁ t₂ here n : ℕ) :
    wholeNo t₁ t₂ (here, n) = numAt t₁ t₂ here (.own n) := by
  unfold wholeNo numAt
  match here with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem named_one (here q : ℕ) :
    OnBytes.Three.named here (.given (tagRoot q) (tagRun 1)) = some (0, q) := by
  show (if (tagRoot q).size = 0 then none
    else if (tagRun 1 == tagRun 1) = true then some (0, (tagRoot q).size - 1)
    else if (tagRun 1 == tagRun 2) = true then some (1, (tagRoot q).size - 1) else none) = _
  rw [if_neg (by rw [tagRoot_size]; omega), if_pos (by decide), tagRoot_size, Nat.add_sub_cancel]

theorem named_two (here q : ℕ) :
    OnBytes.Three.named here (.given (tagRoot q) (tagRun 2)) = some (1, q) := by
  show (if (tagRoot q).size = 0 then none
    else if (tagRun 2 == tagRun 1) = true then some (0, (tagRoot q).size - 1)
    else if (tagRun 2 == tagRun 2) = true then some (1, (tagRoot q).size - 1) else none) = _
  rw [if_neg (by rw [tagRoot_size]; omega), if_neg (by decide), if_pos (by decide), tagRoot_size,
    Nat.add_sub_cancel]

theorem range_tag (n p : ℕ) (r : ByteArray) (h : ((List.range n).map tagRoot)[p]? = some r) :
    r = tagRoot p := by
  rw [List.getElem?_map] at h
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 h
  have e : p = q := by
    have := (List.getElem?_eq_some_iff.1 hq).2
    simpa using this
  rw [e]

/-- A declared source, written, names the tree whose number `numAt` gives: with no stand-ins, or
with `writtenOf`'s. -/
theorem num_of_src (t₁ t₂ here : ℕ) (e : List (List ByteArray × ByteArray))
    (he : e = [] ∨ ∃ n₁ n₂, e = standIns n₁ n₂) (o : Fmt.TreeSource) (s : Fmt.Src)
    (h : o.src e = some s) :
    (OnBytes.Three.named here s).map (wholeNo t₁ t₂) = some (numAt t₁ t₂ here o) := by
  cases o with
  | own n =>
    have e1 : s = .own n := (Option.some.inj h).symm
    subst e1
    show some (wholeNo t₁ t₂ (here, n)) = _
    rw [whole_own]
  | taken c p =>
    have h' : ((e[c]?).bind fun x => (x.1[p]?).map fun r => Fmt.Src.given r x.2) = some s := h
    rcases he with rfl | ⟨n₁, n₂, rfl⟩
    · simp at h'
    · obtain ⟨x, hx, h'⟩ := Option.bind_eq_some_iff.1 h'
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h'
      match c, hx with
      | 0, hx =>
        have ex : x = ((List.range n₁).map tagRoot, tagRun 1) := (Option.some.inj hx).symm
        subst ex
        have er := range_tag n₁ p r hr
        subst er
        show (OnBytes.Three.named here (.given (tagRoot p) (tagRun 1))).map _ = _
        rw [named_one]
        show some (wholeNo t₁ t₂ (0, p)) = some (numAt t₁ t₂ here (.taken 0 p))
        simp [wholeNo, numAt]
      | 1, hx =>
        have ex : x = ((List.range n₂).map tagRoot, tagRun 2) := (Option.some.inj hx).symm
        subst ex
        have er := range_tag n₂ p r hr
        subst er
        show (OnBytes.Three.named here (.given (tagRoot p) (tagRun 2))).map _ = _
        rw [named_two]
        show some (wholeNo t₁ t₂ (1, p)) = some (numAt t₁ t₂ here (.taken 1 p))
        simp [wholeNo, numAt]
      | _ + 2, hx => simp [standIns] at hx

theorem opens_num (t₁ t₂ here : ℕ) (e : List (List ByteArray × ByteArray))
    (he : e = [] ∨ ∃ n₁ n₂, e = standIns n₁ n₂) :
    ∀ {l : List (Fmt.Shape × Fmt.TreeSource)} {os : List (Fmt.Shape × Fmt.Src)},
      List.Forall₂ (fun o b => (o.2.src e).map (fun s => (o.1, s)) = some b) l os →
      (os.filterMap fun b => (OnBytes.Three.named here b.2).map (wholeNo t₁ t₂)) =
        l.map fun o => numAt t₁ t₂ here o.2
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    have hn := num_of_src t₁ t₂ here e he _ s hs
    simp only [List.filterMap_cons, List.map_cons, hn, opens_num t₁ t₂ here e he t]

/-! ## 3 One chain -/

theorem zipWith_forall₂ {α β γ : Type} (f : α → β → γ) : ∀ (l : List α) (l' : List β),
    l'.length = l.length → List.Forall₂ (fun x z => ∃ y, z = f x y) l (List.zipWith f l l')
  | [], _, _ => by simp
  | _ :: _, [], h => by cases h
  | x :: l, y :: l', h => by
    rw [List.zipWith_cons_cons]
    exact .cons ⟨y, rfl⟩ (zipWith_forall₂ f l l' (Nat.succ.inj h))

theorem roundIs_chain (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ)
    (e : List (List ByteArray × ByteArray)) (he : e = [] ∨ ∃ n₁ n₂, e = standIns n₁ n₂)
    (dl : List Fmt.DeclaredRound) (R : Rounds) (w : WrittenAs e dl R)
    (hr : ∀ r ∈ R, r.1.items.countP (· == .root) = r.1.entry.roots) :
    List.Forall₂ (RoundIs (numAt t₁ t₂ here)) dl
      ((rdsFromL all t₁ t₂ here base first R).map rdtOf) := by
  rw [List.forall₂_map_right_iff]
  have z := zipWith_forall₂ (rdOf all t₁ t₂ here base first) R (Three.sentBefore R)
    (sentBefore_length R)
  have w' := forall₂_and_right w hr
  refine (forall₂_comp w' z).imp ?_
  rintro r d ⟨x, ⟨⟨hx, hs⟩, hc⟩, n, rfl⟩
  unfold Fmt.DeclaredRound.round at hx
  obtain ⟨k, hk, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨os, hos, hx⟩ := Option.map_eq_some_iff.1 hx
  have f := mapM_forall₂ _ _ _ hos
  obtain ⟨x1, x2⟩ := x
  have hx' : x1 = ⟨r.entry, k, r.items, os⟩ := hx.symm
  subst hx'
  have hs' : x2 = r.stored := hs
  subst hs'
  refine ⟨rfl, hk, rfl, rfl, opens_num t₁ t₂ here e he f, ?_⟩
  show ((List.range (r.items.countP (· == .root))).map _).length = r.entry.roots
  rw [List.length_map, List.length_range]
  exact hc

theorem fits_roots_all {R₁ R₂ R₃ : Rounds} {m : ℕ} (h : Three.Whole.fits R₁ R₂ R₃ m = true) :
    (∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots) ∧
      (∀ r ∈ R₂, r.1.items.countP (· == .root) = r.1.entry.roots) ∧
      ∀ r ∈ R₃, r.1.items.countP (· == .root) = r.1.entry.roots := by
  unfold Three.Whole.fits at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨c1, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  have key : ∀ (c : ℕ) (R : Rounds), (c, R) ∈ [(0, R₁), (1, R₂), (2, R₃)] →
      ∀ r ∈ R, r.1.items.countP (· == .root) = r.1.entry.roots := by
    intro c R hm r hr
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 c1 (c, R) hm) r hr
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact h1.2
  exact ⟨key 0 R₁ (by simp), key 1 R₂ (by simp), key 2 R₃ (by simp)⟩

/-! ## 4 The statements -/

/-- **Where the makers' tests say yes, the data are the declared rounds' data**, along the three
chains. e₃: no stand-ins, or `writtenOf`'s. -/
def StretchOfOk : Prop :=
  ∀ (a : ℕ) (R₁ R₂ R₃ : Rounds) (e₃ : List (List ByteArray × ByteArray))
    (d₁ d₂ d₃ : List Fmt.DeclaredRound), (e₃ = [] ∨ ∃ n₁ n₂, e₃ = standIns n₁ n₂) →
    WrittenAs [] d₁ R₁ → WrittenAs [] d₂ R₂ → WrittenAs e₃ d₃ R₃ →
    okAt a (some (R₁, R₂, R₃)) = true →
    Along (RoundIs (numAt (dataOf a R₁ R₂ R₃).t₁ (dataOf a R₁ R₂ R₃).t₂ 0)) d₁
        (dataOf a R₁ R₂ R₃).ds₁ ∧
      Along (RoundIs (numAt (dataOf a R₁ R₂ R₃).t₁ (dataOf a R₁ R₂ R₃).t₂ 1)) d₂
        (dataOf a R₁ R₂ R₃).ds₂ ∧
      Along (RoundIs (numAt (dataOf a R₁ R₂ R₃).t₁ (dataOf a R₁ R₂ R₃).t₂ 2)) d₃
        (dataOf a R₁ R₂ R₃).ds₃

theorem stretchOfOk : StretchOfOk := by
  intro a R₁ R₂ R₃ e₃ d₁ d₂ d₃ he w₁ w₂ w₃ hok
  have P := okAt_parts (R := (R₁, R₂, R₃)) hok
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := P.fits
  have hcn : countsFit a (Three.Whole.of R₁ R₂ R₃) = true := P.counts
  unfold countsFit at hcn
  simp only [Bool.and_eq_true, beq_iff_eq] at hcn
  have t₁ : (dataOf a R₁ R₂ R₃).t₁ = rootsIn R₁ := hcn.1
  have t₂ : (dataOf a R₁ R₂ R₃).t₂ = rootsIn R₂ := hcn.2
  obtain ⟨r₁, r₂, r₃⟩ := fits_roots_all hf
  rw [t₁, t₂]
  refine ⟨?_, ?_, ?_⟩
  · refine along_of_prefix _ d₁ _ _
      (roundIs_chain (Three.Whole.of R₁ R₂ R₃).opens _ _ 0 0 0 [] (Or.inl rfl) d₁ R₁ w₁ r₁) ?_
    show (Three.Whole.of R₁ R₂ R₃).ds₁.dropLast.map rdtOf <+: _
    rw [List.map_dropLast]
    exact List.dropLast_prefix _
  · exact along_of_prefix _ d₂ _ _
      (roundIs_chain (Three.Whole.of R₁ R₂ R₃).opens _ _ 1 (rootsIn R₁) 0 [] (Or.inl rfl) d₂ R₂ w₂
        r₂) (List.prefix_refl _)
  · exact along_of_prefix _ d₃ _ _
      (roundIs_chain (Three.Whole.of R₁ R₂ R₃).opens _ _ 2 (rootsIn R₁ + rootsIn R₂)
        (Three.first₃ (rootsIn R₁)) e₃ he d₃ R₃ w₃ r₃) (List.prefix_refl _)

/-- **At every description a piece's stretch is the data of its own block's declared rounds.** -/
def StretchOfData : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    ∀ (C : CK) (Y S₁ S₂ S₃ X₁ X₂ Cl W : Type) (T : Three C D (allOf D) Y S₁ S₂ S₃ X₁ X₂ Cl W)
      (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
      (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl)) rest₁ rest₂ rest₃ (r : Fmt.RoundView),
      (b₁ :: l₁).map (·.rounds) = F.first.blocksInOrder.map (·.rounds) →
      (b₂ :: l₂).map (·.rounds) = F.shared.blocksInOrder.map (·.rounds) →
      (b₃ :: l₃).map (·.rounds) = F.second.blocksInOrder.map (·.rounds) →
      T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r →
      (∀ p ∈ T.p₁ :: T.l₁, Along (RoundIs (numAt D.t₁ D.t₂ 0)) p.b.rounds p.ds) ∧
        (∀ p ∈ T.p₂ :: T.l₂, Along (RoundIs (numAt D.t₁ D.t₂ 1)) p.b.rounds p.ds) ∧
        ∀ p ∈ T.p₃ :: T.l₃, Along (RoundIs (numAt D.t₁ D.t₂ 2)) p.b.rounds p.ds

theorem stretchOfData : StretchOfData := by
  intro Xi F file D h C Y S₁ S₂ S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r g₁ g₂ g₃ hc
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hok, rfl⟩ := data_ok F file D h
  obtain ⟨w₁, w₂, w₃⟩ := written_as file F.roundsDeclaredByBlocks _ hR
  obtain ⟨k₁, k₂, k₃⟩ := stretchOfOk _ R₁ R₂ R₃ _ _ _ _ (Or.inr ⟨_, _, rfl⟩) w₁ w₂ w₃ hok
  have p₁ := congrArg Prod.fst hc.c₁
  have q₁ := congrArg Prod.snd hc.c₁
  have p₂ := congrArg Prod.fst hc.c₂
  have q₂ := congrArg Prod.snd hc.c₂
  have p₃ := congrArg Prod.fst hc.c₃
  have q₃ := congrArg Prod.snd hc.c₃
  simp only at p₁ q₁ p₂ q₂ p₃ q₃
  refine ⟨?_, ?_, ?_⟩
  · rw [p₁, q₁]
    refine cutAlong _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
    rw [flat_of_map _ _ g₁]
    exact k₁
  · rw [p₂, q₂]
    refine cutAlong _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
    rw [flat_of_map _ _ g₂]
    exact k₂
  · rw [p₃, q₃]
    refine cutAlong _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
    rw [flat_of_map _ _ g₃]
    exact k₃

end VerifiableInference.Desc.Sound
