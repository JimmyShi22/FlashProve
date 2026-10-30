-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsAre.lean: WHAT A BLOCK IS SHOWN OF ITS STRETCH: (a) THE COLUMNS ARE THE
COMMITTED STRINGS' VALUES AT THE OPENED POSITIONS; (b) THEIR KEYS AND POSITIONS ARE THOSE THAT
`Block.step` LOOKS FOR. Statements (`def … : Prop`) and their proofs.

The setting. In the rule of composition a block runs on the view that the library's stage makes of
the oracles in front of the block and of the stretch's transcript (`sView`,
OnBytes/Maker/Stage.lean).
  `shownAs`: a want as the view shows it, its column read off the STRINGS
    (Johnson/Desc/Sound/MsgAt.lean): the stored table's in front of the block; a tree's BEHIND the
    block (so also of a tree that the block itself sends).
  `ReadsAreStrings`: where the stretch's trees are listed, the view's opened columns are, one for
    one and in order, the wants shown so. IT IS EXACT: in the oracle model nothing stands between a
    string and a read. (The event that an opening shows another value than was committed belongs to
    the compiler's theorem, not here.)
  `RoundKeys`, `KeysMatch`: tree by tree, the key under which the frame shows a tree is the number
    in its declared label less ft, as `Block.step` looks for it.
  `ReadsMatch`: where declared rounds match the data (`Matches`) and the keys match, what the
    declared rounds read, as key and position, is what the data's draws ask for, as the frame shows
    it: at all draws.
  `PieceReads`: so at every piece, at all oracles and transcripts, the view's columns have just the
    keys and positions that `Block.step` looks for, in order.
What it is for. The tiling (Tiles.lean) counts. Without (b) the frame's keys could part from the
declared labels: every block that reads a tree would then refuse every transcript of its stage, its
law would be free, and the rule of composition would say nothing.
Limits. THE WIDTHS ARE NOT SAID: `Block.step` also compares each column's number of words with the
declared width; a tree that the stretch itself sends has its width by type, but the strings in front
of a block are any lists: that they have their widths is a condition at the boundary. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TilesCutProofs
import Johnson.Desc.Sound.MsgAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj Fo.Peel
open _root_.Run.PQ (CK SgX)

variable {C : CK} {F : Frame} {S Cl W : Type}

/-! ## 1 The columns are the strings' values -/

/-- A want as a view shows it, its column read off the strings: y: in front of the block; y':
behind. -/
def shownAs (F : Frame) (y y' : F.E.Str) : Want → ℕ × ℕ × List UInt64
  | .table item x => (Fmt.storedKey item, x, ((cellAt F y x).map (·.2)).getD [])
  | .tree j x => (F.key j, x, colAt F y' j x)

/-- **A block's reads are the committed strings' values at the opened positions.** -/
def ReadsAreStrings : Prop :=
  ∀ (C : CK) (F : Frame) (b : ℕ) (ds : List RDT), ListedAt F b ds →
    ∀ (y : F.E.Str) (τ : Iop.Tr (uLT C ds)),
      (sView C (stg F b ds) y τ).opened =
        (sWants C (stg F b ds) (rhoT C ds τ)).map
          (shownAs F y (y.1, sLeft C (stg F b ds) y τ))

theorem filterMap_eq_map {α β : Type} (f : α → Option β) (g : α → β) : ∀ l : List α,
    (∀ x ∈ l, f x = some (g x)) → l.filterMap f = l.map g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons_some (h x List.mem_cons_self), List.map_cons,
      filterMap_eq_map f g l fun z hz => h z (List.mem_cons_of_mem _ hz)]

theorem readsAreStrings : ReadsAreStrings := by
  intro C F b ds hL y τ
  refine filterMap_eq_map _ _ _ fun w hw => ?_
  cases w with
  | table item x =>
    have hx : x < 2 ^ F.a := mem_wantsOf_table _ _ item x _ _ hw
    have e1 : sCol C (stg F b ds) y τ (.table item x) = some (y.1 ⟨x, hx⟩).2 := dif_pos hx
    have e2 : cellAt F y x = some (y.1 ⟨x, hx⟩) := dif_pos hx
    rw [e1]
    show some (Fmt.storedKey item, x, (y.1 ⟨x, hx⟩).2) = some (Fmt.storedKey item, x, _)
    rw [e2]
    rfl
  | tree j x =>
    obtain ⟨-, a', ha, hx⟩ := mem_wantsOf_tree _ _ j x _ _ hw
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (sCol_isSome C (stg F b ds) y τ _ _ hw)
    have hp : ∃ p, posL F.all j x = some p := by
      rw [depth_eq] at ha
      by_cases hj : j < b
      · rw [if_pos hj] at ha
        exact posL_of_find _ j x a' ha hx
      · rw [if_neg hj] at ha
        obtain ⟨sh, hsh, rfl⟩ := Option.map_eq_some_iff.1 ha
        have t := hL _ sh hsh
        rw [show b + (j - b) = j by omega] at t
        exact posL_of_find _ j x sh.a t hx
    obtain ⟨p, hp⟩ := hp
    have e : colAt F (y.1, sLeft C (stg F b ds) y τ) j x = c := by
      unfold colAt
      rw [hp]
      show sLeft C (stg F b ds) y τ p = c
      rw [sLeft_at C F ds b y τ j x p hp, hc]
      rfl
    rw [hc]
    show some (F.key j, x, c) = some (F.key j, x, _)
    rw [e]

/-! ## 2 The keys and the positions are those that the step looks for -/

/-- One round: tree by tree the frame's key is the number in the declared label less ft. -/
def RoundKeys (key : ℕ → ℕ) (ft : ℕ) (r : Fmt.DeclaredRound) (d : RDT) : Prop :=
  List.Forall₂ (fun (o : Fmt.Shape × Fmt.TreeSource) (j : ℕ) => key j = o.1.tree - ft) r.opens d.opens

/-- Round by round, as far as the data go. -/
def KeysMatch (key : ℕ → ℕ) (ft : ℕ) : List Fmt.DeclaredRound → List RDT → Prop
  | r :: rs, d :: ds => RoundKeys key ft r d ∧ KeysMatch key ft rs ds
  | _, _ => True

/-- A want as a view's column shows it: key and position. -/
def wantKP (key : ℕ → ℕ) : Want → ℕ × ℕ
  | .table item x => (Fmt.storedKey item, x)
  | .tree j x => (key j, x)

/-- **What the declared rounds read, as key and position, is what the data's draws ask for, as the
frame shows it**: at all draws. -/
def ReadsMatch : Prop :=
  ∀ (ft a : ℕ) (dep : ℕ → Option ℕ) (key : ℕ → ℕ) (rs : List Fmt.DeclaredRound) (ds : List RDT)
    (Rs : List Fmt.Drawn), Matches a dep rs ds → KeysMatch key ft rs ds →
    ((groupsOf ft rs Rs).flatMap id).map (fun w => (w.1, w.2.1)) =
      (wantsOf a dep ds Rs).map (wantKP key)

theorem kp_stored (a : ℕ) (key : ℕ → ℕ) (poss : List ℕ) : ∀ st : List Fmt.Stored,
    (∀ s ∈ st, s.sh.a = a) →
    ((st.map fun s => (Fmt.listOf ((Fmt.partOf s poss).map (· % 2 ^ s.sh.a))).map fun x =>
        (Fmt.storedKey s.item, x, s.sh.W)).flatMap id).map (fun w => (w.1, w.2.1)) =
      (st.flatMap fun s => (Fmt.listOf ((Fmt.partOf s poss).map (· % 2 ^ a))).map fun x =>
        Want.table s.item x).map (wantKP key)
  | [], _ => rfl
  | s :: st, h => by
    have ih := kp_stored a key poss st fun t ht => h t (List.mem_cons_of_mem _ ht)
    have hs := h s List.mem_cons_self
    simp only [List.map_cons, List.flatMap_cons, List.map_append, List.map_map, id_eq, ih, hs]
    rfl

theorem kp_opens (ft : ℕ) (dep : ℕ → Option ℕ) (key : ℕ → ℕ) (poss : List ℕ) :
    ∀ (os : List (Fmt.Shape × Fmt.TreeSource)) (js : List ℕ),
    List.Forall₂ (fun (o : Fmt.Shape × Fmt.TreeSource) (j : ℕ) => dep j = some o.1.a) os js →
    List.Forall₂ (fun (o : Fmt.Shape × Fmt.TreeSource) (j : ℕ) => key j = o.1.tree - ft) os js →
    ((os.map fun o => (Fmt.listOf (poss.map (· % 2 ^ o.1.a))).map fun x =>
        (o.1.tree - ft, x, o.1.W)).flatMap id).map (fun w => (w.1, w.2.1)) =
      (js.flatMap (treeWants dep poss)).map (wantKP key)
  | _, _, .nil, _ => rfl
  | o :: os, j :: js, .cons h t, k => by
    obtain ⟨k1, k2⟩ := List.forall₂_cons.1 k
    have ih := kp_opens ft dep key poss os js t k2
    have e : treeWants dep poss j =
        (Fmt.listOf (poss.map (· % 2 ^ o.1.a))).map fun x => Want.tree j x := by
      unfold treeWants
      rw [h]
    simp only [List.map_cons, List.flatMap_cons, List.map_append, List.map_map, id_eq, ih, e]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    show (o.1.tree - ft, x) = (key j, x)
    rw [k1]

theorem readsMatch : ReadsMatch := by
  intro ft a dep key rs
  induction rs with
  | nil =>
    intro ds Rs h _
    cases ds with
    | nil => cases Rs <;> rfl
    | cons d ds => exact (h : False).elim
  | cons r rs ih =>
    intro ds Rs h k
    cases ds with
    | nil =>
      have h' : (r.stored = [] ∧ r.opens = []) ∧ Matches a dep rs [] := h
      cases Rs with
      | nil => rfl
      | cons R Rs =>
        have t := ih [] Rs h'.2 (by cases rs <;> trivial)
        rw [wantsOf_nil] at t ⊢
        have e : groupsOf ft (r :: rs) (R :: Rs) = groupsOf ft rs Rs := by
          simp only [groupsOf, h'.1.1, h'.1.2, List.map_nil, List.nil_append]
        rw [e, t]
    | cons d ds =>
      have h' : RoundMatch a dep r d ∧ Matches a dep rs ds := h
      have k' : RoundKeys key ft r d ∧ KeysMatch key ft rs ds := k
      cases Rs with
      | nil => rfl
      | cons R Rs =>
        have t := ih ds Rs h'.2 k'.2
        obtain ⟨h1, h2, h3⟩ := h'.1
        rw [wantsOf_cons, h1]
        simp only [groupsOf, List.flatMap_append, List.map_append, t,
          kp_stored a key R.poss r.stored h2, kp_opens ft dep key R.poss r.opens d.opens h3 k'.1]

/-- **At a piece the view's columns have just the keys and positions that `Block.step` looks for**,
in order, at all oracles and transcripts. -/
def PieceReads : Prop :=
  ∀ (C : CK) (F : Frame) (S Cl W : Type) (dep : ℕ → Option ℕ) (b : Block S Cl) (base : ℕ)
    (ds : List RDT) (back : List Fmt.RoundView) (x : Rest C F S W ds),
    Matches F.a dep b.rounds ds → KeysMatch F.key F.ft b.rounds ds → InTime base ds →
    (∀ n sh, treeShT ds n = some sh → dep (base + n) = some sh.a) →
    (∀ j a', dep j = some a' → (F.all.filter (·.no == j)).map (·.a) = [a']) →
    ∀ (y : F.E.Str) (τ : Iop.Tr (uLT C ds)),
      (sView C (pieceOf b base ds back x).stage y τ).opened.map (fun c => (c.1, c.2.1)) =
        ((b.reads F.ft (((sView C (pieceOf b base ds back x).stage y τ).rounds ++ back).map
          (·.drawn))).flatMap id).map fun w => (w.1, w.2.1)

theorem pieceReads : PieceReads := by
  intro C F S Cl W dep b base ds back x hM hK hT own listed y τ
  have hL : ListedAt F base ds := fun n sh h => find_of_filter _ _ _ (listed _ _ (own n sh h))
  have e1 : ((sView C (stg F base ds) y τ).rounds ++ back).map (·.drawn) =
      drawnT C ds (rhoT C ds τ) ++ back.map (·.drawn) := by
    rw [List.map_append]
    exact congrArg (· ++ _) (rvT_drawn C ds τ)
  have e2 : wantsOf F.a dep ds (drawnT C ds (rhoT C ds τ) ++ back.map (·.drawn)) =
      wantsOf F.a dep ds (drawnT C ds (rhoT C ds τ)) := by
    have t := wantsOf_append F.a dep ds [] (drawnT C ds (rhoT C ds τ)) (back.map (·.drawn))
      (drawnT_length C ds _)
    rw [List.append_nil] at t
    rw [t, wantsOf_nil, List.append_nil]
  show (sView C (stg F base ds) y τ).opened.map (fun c => (c.1, c.2.1)) =
    ((groupsOf F.ft b.rounds (((sView C (stg F base ds) y τ).rounds ++ back).map
      (·.drawn))).flatMap id).map fun w => (w.1, w.2.1)
  rw [e1, readsMatch F.ft F.a dep F.key b.rounds ds _ hM hK, e2,
    ← wantsOf_congr F.a (stg F base ds).depth dep ds _
      (depth_agrees F dep base ds (inTime_below ds base hT) own listed (matches_dep _ _ _ _ hM)),
    readsAreStrings C F base ds hL y τ, List.map_map]
  refine List.map_congr_left fun w _ => ?_
  cases w <;> rfl

end VerifiableInference.Desc.Sound
