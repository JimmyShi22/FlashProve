-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/OraclesAre.lean: WHAT THE BLOCKS TELL OF A TREE IS THE DATA's SHAPE OF IT.
Statements (`def … : Prop`) and their proofs.

Why. One shape by two roads. The rounds' data give a tree the shape under which it is first opened,
anywhere in the file; the stage types the tree's columns by that shape. `Oracle.cut`
(Johnson/Desc/Msg.lean) cuts a column by what the SENDING block tells of the tree (`Block.oracles`:
log-length, words, tenants). Where the two part, no leaf is shown, every pin is false, and all that
is said of committed words is empty.
  `FileDescription.sentFit F` (Johnson/Desc/Block.lean): the last clause of `FileDescription.planOkCore` (which
    `FileDescription.planOk` asks): in each chain every opening of an own tree has the log-length and the
    words that are told of the tree, and every tree of which something is told is opened somewhere.
    `sentFit_of_planOk` (proved): a yes of `planOk` gives it.
  `baseOf t₁ t₂ c`: the number through the file of chain c's first tree.
  `TreeIsDecl`: where the makers' tests say yes: every opening of every declared round opens, under
    its own declared shape, the tree whose number `numAt` gives.
  `OpenedShape`: so each member (n, a, W) of `openedOwn` at chain c: the data's shape of the tree
    number baseOf c + n has the depth a and W words.
  `ToldShape`: FOR EVERY DESCRIPTION F and D with `F.data file = .ok D` and `F.sentFit = true`: of
    whichever tree n of chain c something is told: the data's shape of the tree number baseOf c + n
    has that log-length and these words.
  `OraclesAre`: the same at `FileDescription.oracleAt`, by the number through the file, where the first two
    chains tell of as many trees as they send.
Limits. That a chain tells of as many trees as it sends is a premise (`Block.shaped`, a clause of
`planOk`, gives it: not shown here). The label and the flag of a shape are not compared. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.Stretch
import Johnson.Desc.Msg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker Johnson.G.OfPlan
open OnBytes.Params (Rounds)
open OnBytes.Three (rootsIn rdsFromL)

/-- It is the last clause of `planOkCore`, which `planOk` asks. -/
theorem sentFit_of_planOk {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) :
    F.sentFit = true := by
  unfold FileDescription.planOk at h
  rw [Bool.and_eq_true] at h
  have h' := h.1
  unfold FileDescription.planOkCore at h'
  rw [Bool.and_eq_true] at h'
  exact h'.2

/-- The number through the file of chain c's first tree. -/
def baseOf (t₁ t₂ c : ℕ) : ℕ := if c = 0 then 0 else if c = 1 then t₁ else t₁ + t₂

/-! ## 1 Every declared opening opens the tree that its number names, under its own shape -/

theorem forall₂_both {α β : Type} {P Q : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ P l l' → List.Forall₂ Q l l' → List.Forall₂ (fun x y => P x y ∧ Q x y) l l'
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, g => by
    obtain ⟨g1, g2⟩ := List.forall₂_cons.1 g
    exact .cons ⟨h, g1⟩ (forall₂_both t g2)

theorem forall₂_left {α β : Type} {P : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ P l l' → ∀ x ∈ l, ∃ y, P x y
  | _, _, .nil, _, h => by cases h
  | _, _, .cons h t, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, h⟩
    · exact forall₂_left t x hx

theorem forall₂_self {α β γ : Type} {P : β → γ → Prop} (f : α → β) (g : α → γ) : ∀ l : List α,
    List.Forall₂ P (l.map f) (l.map g) → ∀ x ∈ l, P (f x) (g x)
  | [], _, _, h => by cases h
  | a :: l, h, x, hx => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.forall₂_cons.1 h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact forall₂_self f g l h2 x hx

theorem treeIs_chain (Wh : Three.Whole) (t₁ t₂ here base first : ℕ)
    (e : List (List ByteArray × ByteArray)) (he : e = [] ∨ ∃ n₁ n₂, e = standIns n₁ n₂)
    (dl : List Fmt.DeclaredRound) (R : Rounds) (w : WrittenAs e dl R)
    (hr : ∀ r ∈ R, r.1.items.countP (· == .root) = r.1.entry.roots)
    (f : DataFits Wh R (rdsFromL Wh.opens t₁ t₂ here base first R)) :
    ∀ r ∈ dl, ∀ o ∈ r.opens, TreeIs Wh o.1 (numAt t₁ t₂ here o.2) := by
  have F2 := roundIs_chain Wh.opens t₁ t₂ here base first e he dl R w hr
  rw [List.forall₂_map_right_iff] at F2
  have f' : List.Forall₂ (fun x d => RoundData Wh (keyOf x) d) R
      (rdsFromL Wh.opens t₁ t₂ here base first R) := List.forall₂_map_left_iff.1 f
  have F1 : List.Forall₂ (fun (r : Fmt.DeclaredRound) (d : Three.RDL) =>
      List.Forall₂ (TreeIs Wh) (r.opens.map (·.1)) d.opens) dl
      (rdsFromL Wh.opens t₁ t₂ here base first R) := by
    refine (forall₂_comp w f').imp ?_
    rintro r d ⟨x, ⟨hx, -⟩, -, g2⟩
    have g2' : List.Forall₂ (TreeIs Wh) (x.1.opens.map (·.1)) d.opens := g2
    rwa [round_shapes e r x.1 hx] at g2'
  intro r hr' o ho
  obtain ⟨d, h1, h2⟩ := forall₂_left (forall₂_both F1 F2) r hr'
  have e5 : d.opens = r.opens.map fun o => numAt t₁ t₂ here o.2 := h2.2.2.2.2.1
  rw [e5] at h1
  exact forall₂_self (fun o : Fmt.Shape × Fmt.TreeSource => o.1) (fun o => numAt t₁ t₂ here o.2)
    r.opens h1 o ho

/-- **Every declared opening opens, under its own shape, the tree whose number `numAt` gives.** -/
def TreeIsDecl : Prop :=
  ∀ (a : ℕ) (R₁ R₂ R₃ : Rounds) (e₃ : List (List ByteArray × ByteArray))
    (d₁ d₂ d₃ : List Fmt.DeclaredRound), (e₃ = [] ∨ ∃ n₁ n₂, e₃ = standIns n₁ n₂) →
    WrittenAs [] d₁ R₁ → WrittenAs [] d₂ R₂ → WrittenAs e₃ d₃ R₃ →
    okAt a (some (R₁, R₂, R₃)) = true →
    ∀ (c : ℕ) (dl : List Fmt.DeclaredRound), (dl, c) ∈ [(d₁, 0), (d₂, 1), (d₃, 2)] →
      ∀ r ∈ dl, ∀ o ∈ r.opens,
        (dataOf a R₁ R₂ R₃).shape (numAt (rootsIn R₁) (rootsIn R₂) c o.2) = some o.1

theorem treeIsDecl : TreeIsDecl := by
  intro a R₁ R₂ R₃ e₃ d₁ d₂ d₃ he w₁ w₂ w₃ hok c dl hm r hr o ho
  have P := okAt_parts (R := (R₁, R₂, R₃)) hok
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := P.fits
  have hsf : shapesFit a (Three.Whole.of R₁ R₂ R₃) = true :=
    shapesFit_of_okAt (R := (R₁, R₂, R₃)) hok
  obtain ⟨r₁, r₂, r₃⟩ := fits_roots_all hf
  have key : TreeIs (Three.Whole.of R₁ R₂ R₃) o.1 (numAt (rootsIn R₁) (rootsIn R₂) c o.2) := by
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact treeIs_chain (Three.Whole.of R₁ R₂ R₃) _ _ 0 0 0 [] (Or.inl rfl) _ R₁ w₁ r₁
        (dataFits₁ hf) r hr o ho
    · exact treeIs_chain (Three.Whole.of R₁ R₂ R₃) _ _ 1 (rootsIn R₁) 0 [] (Or.inl rfl) _ R₂ w₂ r₂
        (dataFits₂ hf) r hr o ho
    · exact treeIs_chain (Three.Whole.of R₁ R₂ R₃) _ _ 2 (rootsIn R₁ + rootsIn R₂)
        (Three.first₃ (rootsIn R₁)) e₃ he _ R₃ w₃ r₃ (dataFits₃ hf) r hr o ho
  obtain ⟨t, ht, e⟩ := key
  show (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).shape _ = _
  rw [shapesFit_at hsf ht, e]

/-! ## 2 The openings of a chain's own trees -/

/-- **Each opening of an own tree**: the data's shape of that tree has its depth and its words. -/
def OpenedShape : Prop :=
  ∀ (a : ℕ) (R₁ R₂ R₃ : Rounds) (e₃ : List (List ByteArray × ByteArray))
    (d₁ d₂ d₃ : List Fmt.DeclaredRound), (e₃ = [] ∨ ∃ n₁ n₂, e₃ = standIns n₁ n₂) →
    WrittenAs [] d₁ R₁ → WrittenAs [] d₂ R₂ → WrittenAs e₃ d₃ R₃ →
    okAt a (some (R₁, R₂, R₃)) = true →
    ∀ (c : ℕ) (z : ℕ × ℕ × ℕ), z ∈ openedOwn (d₁, d₂, d₃) c →
      ∃ sh, (dataOf a R₁ R₂ R₃).shape (baseOf (rootsIn R₁) (rootsIn R₂) c + z.1) = some sh ∧
        sh.a = z.2.1 ∧ sh.W = z.2.2

theorem openedShape : OpenedShape := by
  intro a R₁ R₂ R₃ e₃ d₁ d₂ d₃ he w₁ w₂ w₃ hok c z hz
  unfold openedOwn at hz
  obtain ⟨x, hx, hz⟩ := List.mem_flatMap.1 hz
  obtain ⟨o, ho, hz⟩ := List.mem_filterMap.1 hz
  obtain ⟨r, hr, ho⟩ := List.mem_flatMap.1 ho
  have hx' : (x.1, x.2) ∈ [(d₁, 0), (d₂, 1), (d₃, 2)] := hx
  have key := treeIsDecl a R₁ R₂ R₃ e₃ d₁ d₂ d₃ he w₁ w₂ w₃ hok x.2 x.1 hx' r hr o ho
  cases hs : o.2 with
  | own n =>
    rw [hs] at hz key
    have hz' : (if x.2 == c then some (n, o.1.a, o.1.W) else none) = some z := hz
    by_cases hc : (x.2 == c) = true
    · rw [if_pos hc] at hz'
      have ez := Option.some.inj hz'
      subst ez
      have ec : x.2 = c := beq_iff_eq.1 hc
      subst ec
      exact ⟨o.1, key, rfl, rfl⟩
    · rw [if_neg hc] at hz'
      cases hz'
  | taken ch sent =>
    rw [hs] at hz key
    have hz' : (if ch == c then some (sent, o.1.a, o.1.W) else none) = some z := hz
    by_cases hc : (ch == c) = true
    · rw [if_pos hc] at hz'
      have ez := Option.some.inj hz'
      subst ez
      have ec : ch = c := beq_iff_eq.1 hc
      subst ec
      exact ⟨o.1, key, rfl, rfl⟩
    · rw [if_neg hc] at hz'
      cases hz'

/-! ## 3 At every description -/

/-- What the blocks of chain c tell of their trees: log-length and words. -/
def sentAt {Xi : Type} (F : FileDescription Xi) (c : ℕ) : List (ℕ × ℕ) :=
  ([sentOf F.first.blocksInOrder, sentOf F.shared.blocksInOrder, sentOf F.second.blocksInOrder][c]?).getD []

/-- **Of whichever tree something is told: the data's shape of it has that log-length and these
words.** -/
def ToldShape : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    F.sentFit = true → ∀ (c n : ℕ) (p : ℕ × ℕ), (sentAt F c)[n]? = some p →
      ∃ sh, D.shape (baseOf D.t₁ D.t₂ c + n) = some sh ∧ sh.a = p.1 ∧ sh.W = p.2

theorem toldShape : ToldShape := by
  intro Xi F file D h hs c n p hp
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hok, rfl⟩ := data_ok F file D h
  obtain ⟨w₁, w₂, w₃⟩ := written_as file F.roundsDeclaredByBlocks _ hR
  have hcn : countsFit F.tableDepth (Three.Whole.of R₁ R₂ R₃) = true :=
    (okAt_parts (R := (R₁, R₂, R₃)) hok).counts
  unfold countsFit at hcn
  simp only [Bool.and_eq_true, beq_iff_eq] at hcn
  have t₁ : (dataOf F.tableDepth R₁ R₂ R₃).t₁ = rootsIn R₁ := hcn.1
  have t₂ : (dataOf F.tableDepth R₁ R₂ R₃).t₂ = rootsIn R₂ := hcn.2
  rw [t₁, t₂]
  have hc : ∃ l, [sentOf F.first.blocksInOrder, sentOf F.shared.blocksInOrder, sentOf F.second.blocksInOrder][c]? = some l ∧
      l[n]? = some p := by
    unfold sentAt at hp
    cases hl : [sentOf F.first.blocksInOrder, sentOf F.shared.blocksInOrder, sentOf F.second.blocksInOrder][c]? with
    | none => rw [hl] at hp; simp at hp
    | some l => rw [hl] at hp; exact ⟨l, rfl, hp⟩
  obtain ⟨l, hl, hn⟩ := hc
  unfold FileDescription.sentFit at hs
  have hm : (l, c) ∈
      [sentOf F.first.blocksInOrder, sentOf F.shared.blocksInOrder, sentOf F.second.blocksInOrder].zipIdx := by
    have t := mem_zipIdx_get _ 0 c l hl
    rwa [Nat.zero_add] at t
  have h1 := List.all_eq_true.1 hs (l, c) hm
  simp only [Bool.and_eq_true] at h1
  obtain ⟨a1, a2⟩ := h1
  have hlt : n < l.length := (List.getElem?_eq_some_iff.1 hn).1
  obtain ⟨z, hz, ez⟩ := List.any_eq_true.1 (List.all_eq_true.1 a2 n (List.mem_range.2 hlt))
  have en : z.1 = n := beq_iff_eq.1 ez
  have e2 := beq_iff_eq.1 (List.all_eq_true.1 a1 z hz)
  rw [en, hn] at e2
  have ep : p = (z.2.1, z.2.2) := Option.some.inj e2
  obtain ⟨sh, g1, g2, g3⟩ := openedShape _ R₁ R₂ R₃ _ _ _ _ (Or.inr ⟨_, _, rfl⟩) w₁ w₂ w₃ hok c z hz
  rw [en] at g1
  exact ⟨sh, g1, by rw [g2, ep], by rw [g3, ep]⟩

theorem sentOf_eq {S Cl : Type} (bs : List (Block S Cl)) :
    sentOf bs = (oraclesOf bs).map fun o => (o.logLength, o.words) := by
  unfold sentOf oraclesOf
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih]
    congr 1
    induction b.oracles with
    | nil => rfl
    | cons l ls ih' =>
      rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih']
      rfl

/-- **The same by the number through the file.** -/
def OraclesAre : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    F.sentFit = true → (oraclesOf F.first.blocksInOrder).length = D.t₁ →
    (oraclesOf F.shared.blocksInOrder).length = D.t₂ →
    ∀ (j : ℕ) (o : Oracle), F.oracleAt j = some o →
      ∃ sh, D.shape j = some sh ∧ o.logLength = sh.a ∧ o.words = sh.W

theorem oraclesAre : OraclesAre := by
  intro Xi F file D h hs c₁ c₂ j o ho
  unfold FileDescription.oracleAt at ho
  have told := toldShape Xi F file D h hs
  have pick : ∀ (c n : ℕ) (bs : List Oracle),
      (sentAt F c) = bs.map (fun o => (o.logLength, o.words)) → bs[n]? = some o →
      baseOf D.t₁ D.t₂ c + n = j → ∃ sh, D.shape j = some sh ∧ o.logLength = sh.a ∧
        o.words = sh.W := by
    intro c n bs e1 e2 e3
    obtain ⟨sh, g1, g2, g3⟩ := told c n (o.logLength, o.words) (by
      rw [e1, List.getElem?_map, e2]
      rfl)
    rw [e3] at g1
    exact ⟨sh, g1, g2.symm, g3.symm⟩
  by_cases h1 : j < D.t₁
  · rw [List.append_assoc, List.getElem?_append_left (by rw [c₁]; exact h1)] at ho
    exact pick 0 j _ (sentOf_eq _) ho (by simp [baseOf])
  · rw [List.append_assoc, List.getElem?_append_right (by rw [c₁]; omega), c₁] at ho
    by_cases h2 : j - D.t₁ < D.t₂
    · rw [List.getElem?_append_left (by rw [c₂]; exact h2)] at ho
      exact pick 1 (j - D.t₁) _ (sentOf_eq _) ho (by simp [baseOf]; omega)
    · rw [List.getElem?_append_right (by rw [c₂]; omega), c₂] at ho
      exact pick 2 (j - D.t₁ - D.t₂) _ (sentOf_eq _) ho (by simp [baseOf]; omega)

end VerifiableInference.Desc.Sound
