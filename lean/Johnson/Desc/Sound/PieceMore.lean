-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PieceMore.lean: WHAT A BLOCK's LAW ASKS OF THE PIECE AT ITS PLACE BESIDE THE BLOCK: WHAT IS NOBODY ELSE's. The kinds' laws on a seated block take the piece q at a place k of a chain's row and ask: q.back = [] · q.ds, round by round, IS the block's declared rounds · q.err = the cap · every tree that the law's pins read lies
below q.base. One structure, one definition, nine theorems.
THE FIRST THREE HAVE THEIR RULES IN OTHER FILES (Johnson/Road/K4/PieceAtFits.lean | PieceAtDesc.lean | PieceAtCut.lean: tiled_owed · tiled_back · tiled_base · fits_piece · cutRow_back · cutRow_err): THEY ARE CALLED HERE, all but fits_piece and cutRow_back, which no proof in this file calls.

WHAT IS ADDED HERE:
  forall₂_of_along: "along, as far as the data go" with equal lengths IS round by round: the form in which the laws take q.ds.
  rootsOf b · nTrees_of_rounds · trees_is_roots: a piece whose stretch is its block's declared rounds sends just the trees that these rounds' entries say as roots.
  PieceMore num base₀ bs k q: block · back = [] · rounds (List.Forall₂ (fun d r => RoundIs num r d) q.ds q.b.rounds) · **base: q.base = base₀ + THE ROOTS THAT THE BLOCKS IN FRONT DECLARE: a number that is read off the description's blocks alone, no piece named.**
    PieceMore.same: each round's entry, kind, items alone ("SameAs", Johnson/Desc/First/Look/K3DigRounds.lean, written out) · **PieceMore.below: THE LAWS' FORM "every tenant's tree lies below q.base": a tree's number below base₀ + the roots declared in front lies below q.base.**
  row_more: PieceMore at a place of a tiled row along which RoundIs holds, if the place is not the last or nothing is put back anywhere.
  more_of_data: **AT EVERY DESCRIPTION, AT THE MAKER's PIECES: the first chain but its last place (base₀ = 0) · THE SHARED CHAIN AND THE LAST CHAIN AT EVERY PLACE, THE LAST TOO (base₀ = D.t₁ | D.t₁ + D.t₂)**: fits_piece speaks of the first chain.
  cap_of_cut: the cap, chain by chain, at a Three whose pieces are the maker's: three calls of cutRow_err.

Limits. The shapes of the trees that a round SENDS are not said (Johnson/Desc/Sound/OraclesAre.lean). The first chain's LAST piece is left out (the sealing round is put back there). That the roots declared in front are the oracles that the blocks in front TELL, and which tenant's tree lies below: tests on the plan: not here. No law of a block. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Road.K4.PieceAtFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Err)
open OnBytes.Road.K4 (tiled_owed tiled_back tiled_base cutRow_back cutRow_err)

variable {C : CK} {F : Frame} {S Cl W : Type}

/-! ## 2 Along, with equal lengths, is round by round -/

theorem forall₂_of_along (P : Fmt.DeclaredRound → RDT → Prop) :
    ∀ (rs : List Fmt.DeclaredRound) (ds : List RDT), Along P rs ds → ds.length = rs.length →
      List.Forall₂ (fun d r => P r d) ds rs
  | [], [], _, _ => List.Forall₂.nil
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | r :: rs, d :: ds, h, hl => by
    have h' : P r d ∧ Along P rs ds := h
    exact List.Forall₂.cons h'.1 (forall₂_of_along P rs ds h'.2 (by simpa using hl))

/-! ## 3 The trees that a stretch sends are the roots that its block declares -/

/-- The roots that a block's declared rounds say. -/
def rootsOf (b : Block S Cl) : ℕ := (b.rounds.map (·.entry.roots)).sum

theorem nTrees_of_rounds (num : Fmt.TreeSource → ℕ) :
    ∀ (ds : List RDT) (rs : List Fmt.DeclaredRound), List.Forall₂ (fun d r => RoundIs num r d) ds rs →
      nTrees ds = (rs.map (·.entry.roots)).sum
  | _, _, .nil => rfl
  | _, _, .cons (a := d) (b := r) (l₁ := ds) (l₂ := rs) h t => by
    rw [nTrees_cons, List.map_cons, List.sum_cons, nTrees_of_rounds num ds rs t, h.2.2.2.2.2]

/-- A piece whose stretch is its block's declared rounds sends just the trees that these say. -/
theorem trees_is_roots (num : Fmt.TreeSource → ℕ) (q : Piece C F S Cl W)
    (h : List.Forall₂ (fun d r => RoundIs num r d) q.ds q.b.rounds) : q.trees = rootsOf q.b :=
  nTrees_of_rounds num q.ds q.b.rounds h

/-! ## 4 The four, but the cap -/

/-- **What a block's law asks of the piece at its place beside the block** (the cap apart). -/
structure PieceMore (num : Fmt.TreeSource → ℕ) (base₀ : ℕ) (bs : List (Block S Cl)) (k : ℕ)
    (q : Piece C F S Cl W) : Prop where
  /-- the piece holds the k-th block -/
  block : bs[k]? = some q.b
  /-- nothing is put behind its rounds -/
  back : q.back = []
  /-- its stretch is, round by round, the data of its block's declared rounds -/
  rounds : List.Forall₂ (fun d r => RoundIs num r d) q.ds q.b.rounds
  /-- its first tree's number: the chain's first, and the roots that the blocks in front declare -/
  base : q.base = base₀ + ((bs.take k).map rootsOf).sum

/-- The first three clauses of each round alone: the entry, the kind, the items. -/
theorem PieceMore.same {num : Fmt.TreeSource → ℕ} {base₀ : ℕ} {bs : List (Block S Cl)} {k : ℕ}
    {q : Piece C F S Cl W} (h : PieceMore num base₀ bs k q) :
    List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
      d.entry = r.entry ∧ Fmt.kindOf r.entry.name = some d.kind ∧ d.items = r.items) q.ds q.b.rounds :=
  h.rounds.imp fun _ _ x => ⟨x.1, x.2.1, x.2.2.1⟩

/-- A tree whose number lies below the chain's first and the roots declared in front lies below the piece's base. -/
theorem PieceMore.below {num : Fmt.TreeSource → ℕ} {base₀ : ℕ} {bs : List (Block S Cl)} {k : ℕ}
    {q : Piece C F S Cl W} (h : PieceMore num base₀ bs k q) {n : ℕ}
    (hn : n < base₀ + ((bs.take k).map rootsOf).sum) : n < q.base := by
  rw [h.base]
  exact hn

/-- **At a place of a tiled row along which the rounds are the declared ones.** ok: the place is not the last, or nothing is put back at any piece. -/
theorem row_more (num : Fmt.TreeSource → ℕ) (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (ht : Tiled p l) (ha : ∀ x ∈ p :: l, Along (RoundIs num) x.b.rounds x.ds)
    (k : ℕ) (q : Piece C F S Cl W) (hq : (p :: l)[k]? = some q)
    (ok : k < l.length ∨ ∀ x ∈ p :: l, x.back = []) :
    PieceMore num p.base ((p :: l).map (·.b)) k q := by
  -- every piece at a place j ≤ k has nothing put back, so its stretch is as long as its declared rounds
  have full : ∀ (j : ℕ) (x : Piece C F S Cl W), (p :: l)[j]? = some x → j ≤ k →
      x.back = [] ∧ List.Forall₂ (fun d r => RoundIs num r d) x.ds x.b.rounds := by
    intro j x hx hj
    have hmem : x ∈ p :: l := List.mem_of_getElem? hx
    have ho := tiled_owed l p ht x hmem
    have hb' : x.back = [] := by
      rcases ok with h | h
      · exact tiled_back l p ht j x (Nat.lt_of_le_of_lt hj h) hx
      · exact h x hmem
    refine ⟨hb', forall₂_of_along _ _ _ (ha x hmem) ?_⟩
    have := ho.1
    rw [hb', List.length_nil, Nat.add_zero] at this
    exact this
  have hbase := tiled_base l p ht k q hq
  refine ⟨by rw [List.getElem?_map, hq]; rfl, (full k q hq (Nat.le_refl k)).1,
    (full k q hq (Nat.le_refl k)).2, ?_⟩
  rw [hbase, ← List.map_take, List.map_map]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.1 hx
  have hjk : j < k := by
    have := hj
    rw [List.length_take] at this
    exact Nat.lt_of_lt_of_le this (Nat.min_le_left _ _)
  have hx' : (p :: l)[j]? = some x := by
    rw [← hxj, List.getElem_take]
    exact List.getElem?_eq_getElem _
  exact trees_is_roots num x (full j x hx' (Nat.le_of_lt hjk)).2

/-- Where the row's end has nothing put back, no piece of a tiled row has. -/
theorem back_all (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)) (ht : Tiled p l)
    (hb : rowBack p l = []) : ∀ x ∈ p :: l, x.back = [] := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  rcases Nat.lt_or_ge j l.length with h | h
  · exact tiled_back l p ht j _ h (List.getElem?_eq_getElem hj)
  · have hj' : j = (p :: l).length - 1 := by
      have : j < l.length + 1 := by simpa using hj
      simp only [List.length_cons, Nat.add_sub_cancel]
      omega
    have e : (p :: l)[j] = (p :: l).getLast (List.cons_ne_nil p l) := by
      rw [List.getLast_eq_getElem]
      congr 1
    rw [e]
    exact hb

/-! ## 5 At every description -/

variable {D : WholeD} {Y S₁ S₂ S₃ X₁ X₂ : Type}

/-- **PieceMore at the three rows of every description's pieces.** -/
theorem more_of_data (Xi : Type) (Fd : FileDescription Xi) (file : String) (D : WholeD)
    (h : Fd.data file = .ok D) (hs : Fd.sealLast = true) (C : CK) (Y S₁ S₂ S₃ X₁ X₂ Cl W : Type)
    (T : Three C D (allOf D) Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
    (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl)) rest₁ rest₂ rest₃ (r : Fmt.RoundView)
    (g₁ : (b₁ :: l₁).map (·.rounds) = Fd.first.blocksInOrder.map (·.rounds))
    (g₂ : (b₂ :: l₂).map (·.rounds) = Fd.shared.blocksInOrder.map (·.rounds))
    (g₃ : (b₃ :: l₃).map (·.rounds) = Fd.second.blocksInOrder.map (·.rounds))
    (hc : T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r) :
    (∀ k q, (T.p₁ :: T.l₁)[k]? = some q → k < l₁.length →
        PieceMore (numAt D.t₁ D.t₂ 0) 0 (b₁ :: l₁) k q) ∧
      (∀ k q, (T.p₂ :: T.l₂)[k]? = some q → PieceMore (numAt D.t₁ D.t₂ 1) D.t₁ (b₂ :: l₂) k q) ∧
      ∀ k q, (T.p₃ :: T.l₃)[k]? = some q →
        PieceMore (numAt D.t₁ D.t₂ 2) (D.t₁ + D.t₂) (b₃ :: l₃) k q := by
  have hF := fitsOfData Xi Fd file D h hs C Y S₁ S₂ S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r
    g₁ g₂ g₃ hc
  obtain ⟨a₁, a₂, a₃⟩ := stretchOfData Xi Fd file D h C Y S₁ S₂ S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂ b₃ l₃ rest₁
    rest₂ rest₃ r g₁ g₂ g₃ hc
  have e₁ : (T.p₁ :: T.l₁).map (·.b) = b₁ :: l₁ := by
    have := cutBlocks C _ S₁ Cl W rest₁ [r] l₁ b₁ 0 0 D.ds₁
    rw [← hc.c₁] at this
    exact this
  have e₂ : (T.p₂ :: T.l₂).map (·.b) = b₂ :: l₂ := by
    have := cutBlocks C _ S₂ Cl W rest₂ [] l₂ b₂ 0 D.t₁ D.ds₂
    rw [← hc.c₂] at this
    exact this
  have e₃ : (T.p₃ :: T.l₃).map (·.b) = b₃ :: l₃ := by
    have := cutBlocks C _ S₃ Cl W rest₃ [] l₃ b₃ 0 (D.t₁ + D.t₂) D.ds₃
    rw [← hc.c₃] at this
    exact this
  have n₂ : ∀ x ∈ T.p₂ :: T.l₂, x.back = [] := by
    have hb := cutBack C _ S₂ Cl W rest₂ [] l₂ b₂ 0 D.t₁ D.ds₂
    rw [← hc.c₂] at hb
    exact back_all T.p₂ T.l₂ hF.tiled₂ hb
  have n₃ : ∀ x ∈ T.p₃ :: T.l₃, x.back = [] := by
    have hb := cutBack C _ S₃ Cl W rest₃ [] l₃ b₃ 0 (D.t₁ + D.t₂) D.ds₃
    rw [← hc.c₃] at hb
    exact back_all T.p₃ T.l₃ hF.tiled₃ hb
  refine ⟨fun k q hq hk => ?_, fun k q hq => ?_, fun k q hq => ?_⟩
  · have hl : T.l₁.length = l₁.length := by
      have := congrArg List.length e₁
      simpa using this
    have := row_more _ T.p₁ T.l₁ hF.tiled₁ a₁ k q hq (Or.inl (hl ▸ hk))
    rwa [e₁, hF.base₁] at this
  · have := row_more _ T.p₂ T.l₂ hF.tiled₂ a₂ k q hq (Or.inr n₂)
    rwa [e₂, hF.base₂] at this
  · have := row_more _ T.p₃ T.l₃ hF.tiled₃ a₃ k q hq (Or.inr n₃)
    rwa [e₃, hF.base₃] at this

/-- **And the cap**, chain by chain, where that chain's rest is at the cap. -/
theorem cap_of_cut (C : CK) (D : WholeD) (all : List LeftT) (Y S₁ S₂ S₃ X₁ X₂ Cl W : Type)
    (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
    (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl)) rest₁ rest₂ rest₃ (r : Fmt.RoundView)
    (hc : T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r) :
    (AtCap rest₁ → ∀ q ∈ T.p₁ :: T.l₁, q.err = Err.cap 128 (uLT C q.ds)) ∧
      (AtCap rest₂ → ∀ q ∈ T.p₂ :: T.l₂, q.err = Err.cap 128 (uLT C q.ds)) ∧
      (AtCap rest₃ → ∀ q ∈ T.p₃ :: T.l₃, q.err = Err.cap 128 (uLT C q.ds)) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := fun q => cutRow_err rest₁ h [r] l₁ b₁ 0 0 D.ds₁ q
    rw [← hc.c₁] at this
    exact this
  · have := fun q => cutRow_err rest₂ h [] l₂ b₂ 0 D.t₁ D.ds₂ q
    rw [← hc.c₂] at this
    exact this
  · have := fun q => cutRow_err rest₃ h [] l₃ b₃ 0 (D.t₁ + D.t₂) D.ds₃ q
    rw [← hc.c₃] at this
    exact this

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.forall₂_of_along
#print axioms VerifiableInference.Desc.Sound.trees_is_roots
#print axioms VerifiableInference.Desc.Sound.PieceMore.same
#print axioms VerifiableInference.Desc.Sound.PieceMore.below
#print axioms VerifiableInference.Desc.Sound.back_all
#print axioms VerifiableInference.Desc.Sound.row_more
#print axioms VerifiableInference.Desc.Sound.more_of_data
#print axioms VerifiableInference.Desc.Sound.cap_of_cut
