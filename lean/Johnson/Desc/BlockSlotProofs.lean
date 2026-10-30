-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/BlockSlotProofs.lean: the statements of Johnson/Desc/BlockSlot.lean, proved.

Main statements.
  `okViewIs : OkViewIs`: the fold's test on a view's words is `okView` (OnBytes/Maker/OkView.lean),
    and the drawn elements' words.
  `ofData : OfData`: at data D with `F.data file = .ok D`: what the slot reads at D is what the
    description's declared rounds read by their own shapes (`WantsAre`); the slot's keys are those
    by which `Block.step` looks (`KeysAre`); and so are the reads as a view's columns show them
    (`ReadsAre`).

The road to `ofData`. `data_ok`, `writtenOf_ok`, `round_ok`: what a yes of `F.data` says: each
declared round was written, the makers' tests said yes, D is made of the written rounds.
`namesGo₀`, `namesGo₁`, `namesGo₂`: the name under which a declared source is written (a stand-in
for a tree that is taken over) stands for the tree with the source's number over the file.
`chain_is`: chain by chain, a round's data hold the declared round's stored tables and its openings
by number, and each opened tree stands in the makers' table with the shape that the opening states
(from the makers' test `Whole.fits`). `wantsOf_eq_decl`, `wantsDecl_reads`: the two general steps.

Limits. No description of the protocol is here: nothing is said at a real plan. Whether `F.data`
says yes at a given description is a run's matter. Nothing on soundness.

-/
import Johnson.Desc.BlockSlot
import OnBytes.Maker.DataFitsOf
import OnBytes.Maker.SrcFitsOf
import OnBytes.Maker.OkOfShapes
import OnBytes.Maker.TypingViews

set_option autoImplicit false

namespace VerifiableInference.Desc
open OnBytes OnBytes.Maker
open OnBytes.Three (wholeNo opensOf rdOf rdsFromL tagRoot tagRun rootsIn)
open Johnson.G.OfPlan (rootsOf)

/-- The test `okGot` on an item as read, written out on words. -/
theorem okGot_eq (g : Fmt.ItemValue) :
    okGot g = (match g with
      | .f x => decide (x < fieldPrimeWord)
      | .e x => decide (x.1 < fieldPrimeWord) && decide (x.2.1 < fieldPrimeWord) && decide (x.2.2 < fieldPrimeWord)
      | .answer x => decide (x.1 < fieldPrimeWord) && decide (x.2.1 < fieldPrimeWord) && decide (x.2.2 < fieldPrimeWord)
      | .word _ => true
      | .root _ => true) := by
  cases g <;> rfl

/-- **`OkViewIs` holds.** -/
theorem okViewIs : OkViewIs := by
  intro v
  unfold viewWordsBelowPrime okView
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hr, ho⟩
    refine ⟨⟨fun r hr' g hg => ?_, ho⟩, fun r hr' => (hr r hr').1⟩
    rw [okGot_eq]
    exact (hr r hr').2 g hg
  · rintro ⟨⟨hv, ho⟩, hd⟩
    refine ⟨fun r hr' => ⟨hd r hr', fun g hg => ?_⟩, ho⟩
    have := hv r hr' g hg
    rw [okGot_eq] at this
    exact this

/-! ## What is read: two general steps -/

/-- The slot's wants at rounds' data are the declared rounds' wants, where round by round the data
hold the declared round's stored tables and its openings by number, every stored table has the
depth a, and every opened tree has the depth that its opening states. -/
theorem wantsOf_eq_decl (a : ℕ) (dep : ℕ → Option ℕ) (num : Fmt.TreeSource → ℕ) {ds : List RDT}
    {l : List Fmt.DeclaredRound}
    (h : List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
      d.stored = r.stored ∧ d.opens = r.opens.map (fun o => num o.2) ∧
        (∀ s ∈ r.stored, s.sh.a = a) ∧ ∀ o ∈ r.opens, dep (num o.2) = some o.1.a) ds l) :
    ∀ Rs, wantsOf a dep ds Rs = wantsDecl num l Rs := by
  induction h with
  | nil => intro Rs; simp [wantsOf, wantsDecl]
  | cons hd _ ih =>
    intro Rs
    cases Rs with
    | nil => simp [wantsOf, wantsDecl]
    | cons R Rs =>
      obtain ⟨h1, h2, h3, h4⟩ := hd
      simp only [wantsOf, wantsDecl]
      rw [ih Rs, h1, h2, List.flatMap_map]
      congr 1
      congr 1
      · exact List.flatMap_congr fun s hs => by rw [h3 s hs]
      · exact List.flatMap_congr fun o ho => by simp only [h4 o ho]

/-- The declared rounds' wants, as a view's columns show them, are what the blocks' rounds read,
where at every opening the key is the one by which `Block.step` looks. -/
theorem wantsDecl_reads (key : ℕ → ℕ) (num : Fmt.TreeSource → ℕ) (firstTree : ℕ) :
    ∀ (l : List Fmt.DeclaredRound), (∀ r ∈ l, ∀ o ∈ r.opens, key (num o.2) = o.1.tree - firstTree) →
      ∀ Rs, (wantsDecl num l Rs).map (wantAt key) = readsAt firstTree l Rs
  | [], _, Rs => by simp [wantsDecl, readsAt, groupsOf]
  | _ :: _, _, [] => by simp [wantsDecl, readsAt, groupsOf]
  | r :: l, h, R :: Rs => by
    have ih := wantsDecl_reads key num firstTree l
      (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) Rs
    unfold readsAt at ih ⊢
    simp only [wantsDecl, groupsOf, List.map_append, List.flatMap_append, ih]
    congr 1
    congr 1
    · simp only [List.map_flatMap, List.flatMap_map, List.map_map, id]
      exact List.flatMap_congr fun s _ => List.map_congr_left fun x _ => rfl
    · simp only [List.map_flatMap, List.flatMap_map, List.map_map, id]
      exact List.flatMap_congr fun o ho => List.map_congr_left fun x _ => by
        simp only [Function.comp, wantAt, h r (List.mem_cons_self ..) o ho]

/-! ## What `F.data file = .ok D` says -/

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem mapM_ok {α β ε : Type} (f : α → Except ε β) :
    ∀ (l : List α) (R : List β), l.mapM f = .ok R → List.Forall₂ (fun a b => f a = .ok b) l R
  | [], R, h => by
    rw [List.mapM_nil] at h
    cases h
    exact .nil
  | a :: l, R, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨S, hS, h⟩ := bind_ok h
    cases h
    exact .cons hb (mapM_ok f l S hS)

/-- A declared round and the written round that is made of it. e: the earlier chains' stand-ins. -/
def Written (e : List (List ByteArray × ByteArray)) (r : Fmt.DeclaredRound)
    (x : Fmt.Round × List Fmt.Stored) : Prop :=
  ∃ y, r.round e = some y ∧ x = (y, r.stored)

/-- The stand-ins for the two earlier chains, as `writtenOf` lays them. -/
def standIns (D : Johnson.G.OfPlan.Decl3) : List (List ByteArray × ByteArray) :=
  [((List.range (Johnson.G.OfPlan.rootsOf D.1)).map Three.tagRoot, Three.tagRun 1),
   ((List.range (Johnson.G.OfPlan.rootsOf D.2.1)).map Three.tagRoot, Three.tagRun 2)]

/-- What a yes of `writtenOf` says, chain by chain. -/
theorem writtenOf_ok {file : String} {D : Johnson.G.OfPlan.Decl3}
    {R : Params.Rounds × Params.Rounds × Params.Rounds}
    (h : Johnson.G.OfPlan.writtenOf file D = .ok R) :
    List.Forall₂ (Written []) D.1 R.1 ∧ List.Forall₂ (Written []) D.2.1 R.2.1 ∧
      List.Forall₂ (Written (standIns D)) D.2.2 R.2.2 := by
  unfold Johnson.G.OfPlan.writtenOf at h
  dsimp only at h
  obtain ⟨R₁, h₁, h⟩ := bind_ok h
  obtain ⟨R₂, h₂, h⟩ := bind_ok h
  obtain ⟨R₃, h₃, h⟩ := bind_ok h
  cases h
  have step : ∀ (e : List (List ByteArray × ByteArray)) (c : String) (l : List Fmt.DeclaredRound)
      (S : Params.Rounds), List.Forall₂ (fun (r : Fmt.DeclaredRound) x =>
        (match r.round e with
          | some x => (pure (x, r.stored) : Except String (Fmt.Round × List Fmt.Stored))
          | none => throw <| Johnson.G.OfPlan.refusal s!"{file}, {c} chain" <|
              s!"the round \"{r.entry.name}\" " ++
              (if (Fmt.kindOf r.entry.name).isNone then "has a name that the format does not know"
               else "takes over a tree that the earlier chain does not send")) = .ok x) l S →
      List.Forall₂ (Written e) l S := by
    intro e c l S hS
    refine hS.imp fun r x hx => ?_
    cases hr : r.round e with
    | none => rw [hr] at hx; cases hx
    | some y => rw [hr] at hx; cases hx; exact ⟨y, hr, rfl⟩
  exact ⟨step _ _ _ _ (mapM_ok _ _ _ h₁), step _ _ _ _ (mapM_ok _ _ _ h₂),
    step _ _ _ _ (mapM_ok _ _ _ h₃)⟩

/-- What `F.data file = .ok D` says. -/
theorem data_ok {Xi : Type} {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) :
    ∃ R, Johnson.G.OfPlan.writtenOf file F.roundsDeclaredByBlocks = .ok R ∧ okAt F.tableDepth (some R) = true ∧
      D = WholeD.of F.tableDepth (wholeAt (some R)) := by
  unfold FileDescription.data at h
  obtain ⟨R, hR, h⟩ := bind_ok h
  refine ⟨R, hR, ?_⟩
  dsimp only at h
  by_cases hk : okAt F.tableDepth (some R) = true
  · rw [if_pos hk] at h
    exact ⟨hk, (Except.ok.inj h).symm⟩
  · rw [if_neg hk] at h
    cases h

/-! ## A declared round and its written round -/

theorem obind_ok {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : x >>= f = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem optMapM_ok {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (R : List β), l.mapM f = some R → List.Forall₂ (fun a b => f a = some b) l R
  | [], R, h => by
    rw [List.mapM_nil] at h
    cases h
    exact .nil
  | a :: l, R, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := obind_ok h
    obtain ⟨S, hS, h⟩ := obind_ok h
    cases h
    exact .cons hb (optMapM_ok f l S hS)

/-- An opening as declared and as written. -/
def OpenIs (e : List (List ByteArray × ByteArray)) (o : Fmt.Shape × Fmt.TreeSource)
    (p : Fmt.Shape × Fmt.Src) : Prop :=
  o.2.src e = some p.2 ∧ p.1 = o.1

theorem round_ok {e : List (List ByteArray × ByteArray)} {r : Fmt.DeclaredRound} {y : Fmt.Round}
    (h : r.round e = some y) :
    y.entry = r.entry ∧ y.items = r.items ∧ List.Forall₂ (OpenIs e) r.opens y.opens := by
  unfold Fmt.DeclaredRound.round at h
  cases hk : Fmt.kindOf r.entry.name with
  | none => rw [hk] at h; cases h
  | some k =>
    rw [hk] at h
    have h' : Option.map (fun os => (⟨r.entry, k, r.items, os⟩ : Fmt.Round))
        (r.opens.mapM fun (o : Fmt.Shape × Fmt.TreeSource) => (o.2.src e).map fun s => (o.1, s)) =
        some y := h
    obtain ⟨os, hm, rfl⟩ := Option.map_eq_some_iff.1 h'
    refine ⟨rfl, rfl, (optMapM_ok _ _ _ hm).imp fun o p hp => ?_⟩
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 hp
    exact ⟨hs, rfl⟩

/-- The name under which a declared source is written stands for the tree with the source's number
over the file. -/
def NamesGo (t₁ t₂ here : ℕ) (e : List (List ByteArray × ByteArray)) : Prop :=
  ∀ (o : Fmt.TreeSource) (s : Fmt.Src), o.src e = some s →
    (Three.named here s).map (wholeNo t₁ t₂) = some (numAt t₁ t₂ here o)

theorem namesGo₀ (t₁ t₂ : ℕ) : NamesGo t₁ t₂ 0 [] := by
  intro o s h
  cases o with
  | own n => cases h; simp [Three.named, wholeNo, numAt]
  | taken c p => simp [Fmt.TreeSource.src] at h

theorem namesGo₁ (t₁ t₂ : ℕ) : NamesGo t₁ t₂ 1 [] := by
  intro o s h
  cases o with
  | own n => cases h; simp [Three.named, wholeNo, numAt]
  | taken c p => simp [Fmt.TreeSource.src] at h

theorem namesGo₂ (t₁ t₂ : ℕ) : NamesGo t₁ t₂ 2
    [((List.range t₁).map tagRoot, tagRun 1), ((List.range t₂).map tagRoot, tagRun 2)] := by
  intro o s h
  cases o with
  | own n => cases h; simp [Three.named, wholeNo, numAt]
  | taken c p =>
    match c, h with
    | 0, h =>
      simp [Fmt.TreeSource.src] at h
      obtain ⟨w, hw, rfl⟩ := h
      obtain ⟨_, hw'⟩ := List.getElem?_eq_some_iff.1 hw
      rw [List.getElem_range] at hw'
      subst hw'
      have h11 : (tagRun 1 == tagRun 1) = true := by decide
      simp [Three.named, tagRoot_size, wholeNo, numAt, h11]
    | 1, h =>
      simp [Fmt.TreeSource.src] at h
      obtain ⟨w, hw, rfl⟩ := h
      obtain ⟨_, hw'⟩ := List.getElem?_eq_some_iff.1 hw
      rw [List.getElem_range] at hw'
      subst hw'
      have h21 : (tagRun 2 == tagRun 1) = false := by decide
      have h22 : (tagRun 2 == tagRun 2) = true := by decide
      simp [Three.named, tagRoot_size, wholeNo, numAt, h21, h22]
    | c + 2, h => simp [Fmt.TreeSource.src] at h

/-! ## One chain: the makers' data against the declared rounds -/

/-- The written openings' numbers over the file are the declared sources' numbers. -/
theorem opens_eq {t₁ t₂ here : ℕ} {e : List (List ByteArray × ByteArray)}
    (hn : NamesGo t₁ t₂ here e) {A : List (Fmt.Shape × Fmt.TreeSource)}
    {B : List (Fmt.Shape × Fmt.Src)} (h : List.Forall₂ (OpenIs e) A B) :
    (B.filterMap fun p => (Three.named here p.2).map (wholeNo t₁ t₂)) =
      A.map fun o => numAt t₁ t₂ here o.2 := by
  induction h with
  | nil => rfl
  | cons hd _ ih => rw [List.filterMap_cons, hn _ _ hd.1, List.map_cons, ih]

/-- Each declared opening's tree stands in the table with the shape that the opening states. -/
theorem opens_tree (W : Three.Whole) {t₁ t₂ here : ℕ} {e : List (List ByteArray × ByteArray)}
    (hn : NamesGo t₁ t₂ here e) {A : List (Fmt.Shape × Fmt.TreeSource)}
    {B : List (Fmt.Shape × Fmt.Src)} (h : List.Forall₂ (OpenIs e) A B)
    (hB : ∀ p ∈ B, ∀ y, Three.named here p.2 = some y → TreeIs W p.1 (wholeNo t₁ t₂ y)) :
    ∀ o ∈ A, TreeIs W o.1 (numAt t₁ t₂ here o.2) := by
  induction h with
  | nil => intro o ho; cases ho
  | @cons o p A B hd _ ih =>
    intro o' ho'
    rcases List.mem_cons.1 ho' with rfl | ho'
    · obtain ⟨y, hy, hy'⟩ := Option.map_eq_some_iff.1 (hn _ _ hd.1)
      rw [← hy', ← hd.2]
      exact hB p List.mem_cons_self y hy
    · exact ih (fun p' hp' => hB p' (List.mem_cons_of_mem _ hp')) o' ho'

/-- What ties a round's data to the declared round. -/
def RoundIs (W : Three.Whole) (num : Fmt.TreeSource → ℕ) (d : Three.RDL) (r : Fmt.DeclaredRound) : Prop :=
  d.stored = r.stored ∧ d.opens = r.opens.map (fun o => num o.2) ∧
    ∀ o ∈ r.opens, TreeIs W o.1 (num o.2)

theorem zip_is (W : Three.Whole) (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) {t₁ t₂ here : ℕ}
    (base first : ℕ) {e : List (List ByteArray × ByteArray)} (hn : NamesGo t₁ t₂ here e)
    {l : List Fmt.DeclaredRound} {R : Params.Rounds} (hw : List.Forall₂ (Written e) l R) :
    (∀ x ∈ R, ∀ p ∈ x.1.opens, ∀ y, Three.named here p.2 = some y →
      TreeIs W p.1 (wholeNo t₁ t₂ y)) →
    ∀ L : List ℕ, L.length = R.length →
      List.Forall₂ (RoundIs W (numAt t₁ t₂ here))
        (List.zipWith (rdOf all t₁ t₂ here base first) R L) l := by
  induction hw with
  | nil => intro _ L _; rw [List.zipWith_nil_left]; exact .nil
  | @cons r x l R hd _ ih =>
    intro hT L hL
    cases L with
    | nil => cases hL
    | cons n L =>
      rw [List.zipWith_cons_cons]
      obtain ⟨y, hy, rfl⟩ := hd
      obtain ⟨-, -, ho⟩ := round_ok hy
      exact .cons ⟨rfl, opens_eq hn ho, opens_tree W hn ho (hT _ List.mem_cons_self)⟩
        (ih (fun x' hx' => hT x' (List.mem_cons_of_mem _ hx')) L (Nat.succ.inj hL))

/-- **One chain.** -/
theorem chain_is (W : Three.Whole) (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) {t₁ t₂ here : ℕ}
    (base first : ℕ) {e : List (List ByteArray × ByteArray)} (hn : NamesGo t₁ t₂ here e)
    {l : List Fmt.DeclaredRound} {R : Params.Rounds} (hw : List.Forall₂ (Written e) l R)
    (h3 : ∀ z ∈ opensOf t₁ t₂ here R, TreeIs W z.2.1 z.1) :
    List.Forall₂ (RoundIs W (numAt t₁ t₂ here)) (rdsFromL all t₁ t₂ here base first R) l := by
  refine zip_is W all base first hn hw (fun x hx p hp y hy => ?_) _ (sentBefore_length R)
  obtain ⟨i, hi⟩ := mem_zipIdx_of R 0 x hx
  refine h3 (wholeNo t₁ t₂ y, p.1, here, i) ?_
  unfold opensOf
  exact List.mem_flatMap.2 ⟨(x, i), hi, List.mem_filterMap.2 ⟨p, hp, by rw [hy]; rfl⟩⟩

/-- The roots that written rounds send are those that the declared rounds' entries count. -/
theorem rootsIn_eq {e : List (List ByteArray × ByteArray)} {l : List Fmt.DeclaredRound}
    {R : Params.Rounds} (hw : List.Forall₂ (Written e) l R)
    (hf : ∀ x ∈ R, x.1.items.countP (· == .root) = x.1.entry.roots) : rootsIn R = rootsOf l := by
  unfold rootsIn rootsOf
  induction hw with
  | nil => rfl
  | @cons r x l R hd _ ih =>
    obtain ⟨y, hy, rfl⟩ := hd
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
      ih fun x' hx' => hf x' (List.mem_cons_of_mem _ hx'), hf _ List.mem_cons_self,
      (round_ok hy).1]

/-- An entry counts its message's roots. -/
theorem fits_roots {R₁ R₂ R₃ : Params.Rounds} {m : ℕ} (h : Three.Whole.fits R₁ R₂ R₃ m = true) :
    ∀ x ∈ [(0, R₁), (1, R₂), (2, R₃)], ∀ r ∈ x.2,
      r.1.items.countP (· == .root) = r.1.entry.roots := by
  unfold Three.Whole.fits at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨c1, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  intro x hx r hr
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 c1 x hx) r hr
  exact eq_of_beq (Bool.and_eq_true _ _ ▸ h1 : _ ∧ _).2

/-! ## `OfData` -/

theorem forall₂_dropLast {α β : Type} {P : α → β → Prop} :
    ∀ {A : List α} {B : List β}, List.Forall₂ P A B → List.Forall₂ P A.dropLast B.dropLast
  | _, _, .nil => .nil
  | _, _, .cons _ .nil => .nil
  | _, _, .cons h (.cons h' t) => .cons h (forall₂_dropLast (.cons h' t))

theorem forall₂_right {α β : Type} {P : α → β → Prop} {A : List α} {B : List β}
    (h : List.Forall₂ P A B) : ∀ b ∈ B, ∃ a, P a b := by
  induction h with
  | nil => intro b hb; cases hb
  | cons hd _ ih =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, hd⟩
    · exact ih b hb

/-- From the tie round by round to what `wantsOf_eq_decl` asks. -/
theorem to_wants (a : ℕ) (W : Three.Whole) (dep : ℕ → Option ℕ) (num : Fmt.TreeSource → ℕ)
    (hd : ∀ sh j, TreeIs W sh j → dep j = some sh.a) {ds : List Three.RDL}
    {l : List Fmt.DeclaredRound} (h : List.Forall₂ (RoundIs W num) ds l) :
    (∀ d ∈ ds, ∀ s ∈ d.stored, s.sh.a = a) →
    List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
      d.stored = r.stored ∧ d.opens = r.opens.map (fun o => num o.2) ∧
        (∀ s ∈ r.stored, s.sh.a = a) ∧ ∀ o ∈ r.opens, dep (num o.2) = some o.1.a)
      (ds.map rdtOf) l := by
  induction h with
  | nil => intro _; exact .nil
  | cons hr _ ih =>
    intro hs
    obtain ⟨h1, h2, h3⟩ := hr
    exact .cons ⟨h1, h2, fun s hs' => hs _ List.mem_cons_self s (h1 ▸ hs'),
      fun o ho => hd _ _ (h3 o ho)⟩ (ih fun d hd' => hs d (List.mem_cons_of_mem _ hd'))

theorem foldl_roots (l : List Fmt.DeclaredRound) :
    ∀ k, l.foldl (fun n r => n + r.entry.roots) k = k + rootsOf l := by
  unfold rootsOf
  induction l with
  | nil => intro k; rfl
  | cons r l ih => intro k; rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- **`OfData` holds.** -/
theorem ofData : OfData := by
  intro Xi F file D h
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hk, rfl⟩ := data_ok h
  obtain ⟨w₁, w₂, w₃⟩ := writtenOf_ok hR
  have parts := okAt_parts hk
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := parts.fits
  have e₁ : rootsIn R₁ = F.t₁ := rootsIn_eq w₁ (fits_roots hf (0, R₁) (by simp))
  have e₂ : rootsIn R₂ = F.t₂ := rootsIn_eq w₂ (fits_roots hf (1, R₂) (by simp))
  have hst : standIns F.roundsDeclaredByBlocks =
      [((List.range (rootsIn R₁)).map tagRoot, tagRun 1),
       ((List.range (rootsIn R₂)).map tagRoot, tagRun 2)] := by
    rw [e₁, e₂]; rfl
  rw [hst] at w₃
  have c₁ : List.Forall₂ (RoundIs (Three.Whole.of R₁ R₂ R₃) (numAt F.t₁ F.t₂ 0))
      (Three.Whole.of R₁ R₂ R₃).ds₁ F.roundsDeclaredByBlocks.1 := by
    rw [← e₁, ← e₂]
    exact chain_is _ _ 0 0 (namesGo₀ _ _) w₁
      fun z hz => fits_trees hf z (List.mem_append_left _ hz)
  have c₂ : List.Forall₂ (RoundIs (Three.Whole.of R₁ R₂ R₃) (numAt F.t₁ F.t₂ 1))
      (Three.Whole.of R₁ R₂ R₃).ds₂ F.roundsDeclaredByBlocks.2.1 := by
    rw [← e₁, ← e₂]
    exact chain_is _ _ _ 0 (namesGo₁ _ _) w₂
      fun z hz => fits_trees hf z (List.mem_append_right _ (List.mem_append_left _ hz))
  have c₃ : List.Forall₂ (RoundIs (Three.Whole.of R₁ R₂ R₃) (numAt F.t₁ F.t₂ 2))
      (Three.Whole.of R₁ R₂ R₃).ds₃ F.roundsDeclaredByBlocks.2.2 := by
    rw [← e₁, ← e₂]
    exact chain_is _ _ _ _ (namesGo₂ _ _) w₃
      fun z hz => fits_trees hf z (List.mem_append_right _ (List.mem_append_right _ hz))
  have hWt : (Three.Whole.of R₁ R₂ R₃).t₁ = F.t₁ := e₁
  have hshape : shapesFit F.tableDepth (Three.Whole.of R₁ R₂ R₃) = true :=
    shapesFit_of_okAt (R := (R₁, R₂, R₃)) hk
  have hstored : storedFit F.tableDepth (Three.Whole.of R₁ R₂ R₃) = true := parts.stored
  change WantsAre F (WholeD.of F.tableDepth (Three.Whole.of R₁ R₂ R₃)) ∧
    KeysAre F (WholeD.of F.tableDepth (Three.Whole.of R₁ R₂ R₃)) ∧
    ReadsAre F (WholeD.of F.tableDepth (Three.Whole.of R₁ R₂ R₃))
  clear parts hk hf w₁ w₂ w₃ hR h hst e₁ e₂
  generalize Three.Whole.of R₁ R₂ R₃ = W at *
  have hdep : ∀ sh j, TreeIs W sh j → (WholeD.of F.tableDepth W).depth j = some sh.a := by
    rintro sh j ⟨t, ht, rfl⟩
    rw [WholeD.depth_shape, shapesFit_at hshape ht]
    rfl
  have hkey : ∀ c sh j, TreeIs W sh j →
      W.key c j = sh.tree - (if c = 2 then Three.first₃ W.t₁ else 0) := by
    rintro c sh j ⟨t, ht, rfl⟩
    unfold Three.Whole.key
    rw [ht]
    rfl
  unfold storedFit at hstored
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hstored
  obtain ⟨hs13, hs2⟩ := hstored
  have none₁ : ∀ d ∈ W.ds₁.dropLast, ∀ s ∈ d.stored, s.sh.a = F.tableDepth := by
    intro d hd s hs
    have := hs13 d (List.mem_append_left _ (List.mem_of_mem_dropLast hd))
    rw [List.isEmpty_iff.1 this] at hs
    cases hs
  have none₃ : ∀ d ∈ W.ds₃, ∀ s ∈ d.stored, s.sh.a = F.tableDepth := by
    intro d hd s hs
    have := hs13 d (List.mem_append_right _ hd)
    rw [List.isEmpty_iff.1 this] at hs
    cases hs
  have some₂ : ∀ d ∈ W.ds₂, ∀ s ∈ d.stored, s.sh.a = F.tableDepth := by
    intro d hd s hs
    have := List.all_eq_true.1 (hs2 d hd) s hs
    rw [Bool.and_eq_true] at this
    exact eq_of_beq this.1
  have wants : WantsAre F (WholeD.of F.tableDepth W) :=
    ⟨wantsOf_eq_decl _ _ _ (to_wants _ W _ _ hdep (forall₂_dropLast c₁) none₁),
      wantsOf_eq_decl _ _ _ (to_wants _ W _ _ hdep c₂ some₂),
      wantsOf_eq_decl _ _ _ (to_wants _ W _ _ hdep c₃ none₃)⟩
  have hft : F.lastChainFirstTreeNumber = Three.first₃ W.t₁ := by
    unfold FileDescription.lastChainFirstTreeNumber Three.first₃
    rw [foldl_roots, Nat.zero_add, hWt]
    rfl
  have keys : KeysAre F (WholeD.of F.tableDepth W) := by
    refine ⟨fun r hr o ho => ?_, fun r hr o ho => ?_, fun r hr o ho => ?_⟩
    · obtain ⟨d, -, -, h3⟩ := forall₂_right c₁ r hr
      exact hkey 0 _ _ (h3 o ho)
    · obtain ⟨d, -, -, h3⟩ := forall₂_right c₂ r hr
      exact hkey 1 _ _ (h3 o ho)
    · obtain ⟨d, -, -, h3⟩ := forall₂_right c₃ r hr
      rw [hft]
      exact hkey 2 _ _ (h3 o ho)
  refine ⟨wants, keys, fun Rs => ?_, fun Rs => ?_, fun Rs => ?_⟩
  · rw [wants.1 Rs]
    exact wantsDecl_reads _ _ 0 _
      (fun r hr o ho => keys.1 r (List.mem_of_mem_dropLast hr) o ho) Rs
  · rw [wants.2.1 Rs]
    exact wantsDecl_reads _ _ 0 _ keys.2.1 Rs
  · rw [wants.2.2 Rs]
    exact wantsDecl_reads _ _ _ _ keys.2.2 Rs

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.okViewIs
#print axioms VerifiableInference.Desc.wantsOf_eq_decl
#print axioms VerifiableInference.Desc.wantsDecl_reads
#print axioms VerifiableInference.Desc.writtenOf_ok
#print axioms VerifiableInference.Desc.data_ok
#print axioms VerifiableInference.Desc.round_ok
#print axioms VerifiableInference.Desc.namesGo₂
#print axioms VerifiableInference.Desc.chain_is
#print axioms VerifiableInference.Desc.rootsIn_eq
#print axioms VerifiableInference.Desc.fits_roots
#print axioms VerifiableInference.Desc.ofData
