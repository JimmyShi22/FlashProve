-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ShownOfData.lean: AT EVERY DESCRIPTION, BEHIND THE PIECE THAT SENDS A MEMBER's
TREE THE MEMBER IS SHOWN. Statements (`def … : Prop`) and their proofs: the join of ShownBehind.lean
(a typed column has its shape's words) with OraclesAre.lean (what the blocks tell of a tree is the
data's shape of it) along the maker's cuts.
  `shape_own₁`, `shape_own₂`, `shape_own₃`: a chain's tree number n has, through the file, the
    chain's base + n, and the data's shape there is its shape.
  `CutOwn`: what is so of a chain's trees is so of the trees of every piece that the maker cuts, at
    the piece's own base.
  `CutShown`: so behind every piece of a row, a member that sits at a tree which the piece's stretch
    sends, at a seat that fits, is shown.
  `ShownOfData`: FOR EVERY DESCRIPTION F and every D with `F.data file = .ok D`, `F.sentFit = true`
    (a clause of `planOk`), the first two chains telling of as many trees as they send: at every
    `Three` whose pieces are the maker's: at every piece of the three rows.
So the promise's clause "every leaf is shown" (`CfAt`, MsgSig.lean) is GAINED FOR CERTAIN, AT NO
PRICE, behind the sending, and rides from there (`pinStays`).
Limits. `SeatFits` is a premise: a test on the plan. Across a seam between two chains (another
frame) nothing is said here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ShownBehind
import Johnson.Desc.Sound.OraclesAre

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker Fo.Peel Johnson.Pack
open _root_.Run.PQ (CK SgX)

/-! ## 1 A chain's trees through the file -/

theorem shape_own₁ (D : WholeD) (n : ℕ) (sh : Fmt.Shape) (h : treeShT D.ds₁ n = some sh) :
    D.shape (0 + n) = some sh := by
  have hl : n < D.t₁ := treeShT_lt _ _ _ h
  unfold WholeD.shape
  rw [Nat.zero_add, if_pos hl]
  exact h

theorem shape_own₂ (D : WholeD) (n : ℕ) (sh : Fmt.Shape) (h : treeShT D.ds₂ n = some sh) :
    D.shape (D.t₁ + n) = some sh := by
  have hl : n < D.t₂ := treeShT_lt _ _ _ h
  unfold WholeD.shape
  rw [if_neg (by omega), Nat.add_sub_cancel_left, if_pos hl]
  exact h

theorem shape_own₃ (D : WholeD) (n : ℕ) (sh : Fmt.Shape) (h : treeShT D.ds₃ n = some sh) :
    D.shape (D.t₁ + D.t₂ + n) = some sh := by
  unfold WholeD.shape
  rw [if_neg (by omega), if_neg (by omega), show D.t₁ + D.t₂ + n - D.t₁ - D.t₂ = n by omega]
  exact h

/-! ## 2 Along the maker's cuts -/

/-- **What is so of a chain's trees is so of every piece's trees, at the piece's own base.** -/
def CutOwn : Prop :=
  ∀ (C : CK) (F : Frame) (S Cl W : Type) (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds)
    (putBack : List Fmt.RoundView) (f : ℕ → Option Fmt.Shape) (l : List (Block S Cl)) (b : Block S Cl)
    (i base : ℕ) (ds : List RDT),
    (∀ n sh, treeShT ds n = some sh → f (base + n) = some sh) →
    ∀ p ∈ (cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2,
      ∀ n sh, treeShT p.ds n = some sh → f (p.base + n) = some sh

theorem cutOwn : CutOwn := by
  intro C F S Cl W rest putBack f l
  induction l with
  | nil =>
    intro b i base ds h p hp
    rw [cutRow_nil] at hp
    have e : p = pieceOf b base ds putBack (rest i ds) := by simpa using hp
    subst e
    exact h
  | cons b' l ih =>
    intro b i base ds h p hp
    rw [cutRow_cons] at hp
    have hds : ds.take b.rounds.length ++ ds.drop b.rounds.length = ds := List.take_append_drop _ _
    rcases List.mem_cons.1 hp with e | hp
    · subst e
      intro n sh hn
      have hn' : treeShT (ds.take b.rounds.length) n = some sh := hn
      have t : treeShT (ds.take b.rounds.length ++ ds.drop b.rounds.length) n = some sh := by
        rw [treeShT_append, if_pos (treeShT_lt _ _ _ hn')]
        exact hn'
      rw [hds] at t
      exact h n sh t
    · refine ih b' (i + 1) _ _ (fun n sh hn => ?_) p hp
      have t : treeShT (ds.take b.rounds.length ++ ds.drop b.rounds.length)
          (nTrees (ds.take b.rounds.length) + n) = some sh := by
        rw [treeShT_append, if_neg (by omega), Nat.add_sub_cancel_left]
        exact hn
      rw [hds] at t
      have u := h _ sh t
      rwa [← Nat.add_assoc] at u

/-- Behind the piece every member whose tree the piece's stretch sends is shown. -/
def Piece.ShownAll {C : CK} {Fr : Frame} {S Cl W Xi : Type} (p : Piece C Fr S Cl W)
    (G : FileDescription Xi) (cs : OnBytes.Codes) (m : List (OnBytes.OracleShape × ℕ))
    (seat : Fin m.length → ℕ × ℕ) : Prop :=
  ∀ (y : Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (k : Fin m.length) (n : ℕ) (sh : Fmt.Shape),
    (seat k).1 = p.base + n → treeShT p.ds n = some sh →
    ShownAt G cs m seat (strsOf Fr (behind C Fr p.base p.ds y τ)) k

/-- **Behind every piece of a row a member whose tree the piece's stretch sends is shown.** -/
def CutShown : Prop :=
  ∀ (C : CK) (F : Frame) (S Cl W : Type) (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds)
    (putBack : List Fmt.RoundView) (D : WholeD) (l : List (Block S Cl)) (b : Block S Cl) (i base : ℕ)
    (ds : List RDT), F.all = allOf D →
    (∀ n sh, treeShT ds n = some sh → D.shape (base + n) = some sh) →
    ∀ (Xi : Type) (G : FileDescription Xi) (cs : OnBytes.Codes) (m : List (OnBytes.OracleShape × ℕ))
      (seat : Fin m.length → ℕ × ℕ), SeatFits G cs m seat →
      (∀ j o, G.oracleAt j = some o →
        ∃ sh, D.shape j = some sh ∧ o.logLength = sh.a ∧ o.words = sh.W) →
      ∀ p ∈ (cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2,
        p.ShownAll G cs m seat

theorem cutShown : CutShown := by
  intro C F S Cl W rest putBack D l b i base ds hall hown Xi G cs m seat hS hO p hp y τ k n sh hj hs
  have own := cutOwn C F S Cl W rest putBack D.shape l b i base ds hown p hp
  have hL : ListedAt F p.base p.ds := by
    intro n' sh' h'
    have hd : D.depth (p.base + n') = some sh'.a := by
      rw [WholeD.depth_shape, own n' sh' h']
      rfl
    rw [hall]
    exact find_of_filter _ _ _ (allOf_listed D _ _ hd)
  refine shownBehind Xi G cs m seat hS C F p.base p.ds hL y τ k n sh hj hs fun o ho => ?_
  obtain ⟨sh', g1, g2, g3⟩ := hO _ o ho
  have e : sh' = sh := Option.some.inj (g1.symm.trans (own n sh hs))
  subst e
  exact ⟨g2, g3⟩

/-! ## 3 At every description -/

/-- **At every description, behind the piece that sends a member's tree the member is shown.** -/
def ShownOfData : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    F.sentFit = true → (oraclesOf F.first.blocksInOrder).length = D.t₁ →
    (oraclesOf F.shared.blocksInOrder).length = D.t₂ →
    ∀ (cs : OnBytes.Codes) (m : List (OnBytes.OracleShape × ℕ)) (seat : Fin m.length → ℕ × ℕ),
      SeatFits F cs m seat →
    ∀ (C : CK) (Y S₁ S₂ S₃ X₁ X₂ Cl W : Type) (T : Three C D (allOf D) Y S₁ S₂ S₃ X₁ X₂ Cl W)
      (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
      (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl)) rest₁ rest₂ rest₃ (r : Fmt.RoundView),
      T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r →
      (∀ p ∈ T.p₁ :: T.l₁, p.ShownAll F cs m seat) ∧ (∀ p ∈ T.p₂ :: T.l₂, p.ShownAll F cs m seat) ∧
        ∀ p ∈ T.p₃ :: T.l₃, p.ShownAll F cs m seat

theorem shownOfData : ShownOfData := by
  intro Xi F file D h hs c₁ c₂ cs m seat hS C Y S₁ S₂ S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
    rest₃ r hc
  have hO := oraclesAre Xi F file D h hs c₁ c₂
  have p₁ := congrArg Prod.fst hc.c₁
  have q₁ := congrArg Prod.snd hc.c₁
  have p₂ := congrArg Prod.fst hc.c₂
  have q₂ := congrArg Prod.snd hc.c₂
  have p₃ := congrArg Prod.fst hc.c₃
  have q₃ := congrArg Prod.snd hc.c₃
  simp only at p₁ q₁ p₂ q₂ p₃ q₃
  refine ⟨?_, ?_, ?_⟩
  · rw [p₁, q₁]
    exact cutShown _ _ _ _ _ _ _ D _ _ _ _ _ rfl (shape_own₁ D) Xi F cs m seat hS hO
  · rw [p₂, q₂]
    exact cutShown _ _ _ _ _ _ _ D _ _ _ _ _ rfl (shape_own₂ D) Xi F cs m seat hS hO
  · rw [p₃, q₃]
    exact cutShown _ _ _ _ _ _ _ D _ _ _ _ _ rfl (shape_own₃ D) Xi F cs m seat hS hO

end VerifiableInference.Desc.Sound
