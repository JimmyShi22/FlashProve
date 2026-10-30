-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/RowCut.lean: WHERE THE MAKER's ROWS ARE CUT, IN CLOSED FORM: what the n-th piece's base, stretch and «put behind» ARE. Book-keeping, general in the description.
Why. `rowGetⱼ` (RowPieces.lean) has the three under «there are»: the files of a kind whose law asks something OF the stretch (it has two rounds; they send and draw as declared; the trees below the base are just so many) want a closed form.
Main names.
  `cutBase` | `cutDs` | `cutPut`: the three, by the maker's own recursion. `cutRow_at`: THE n-TH PIECE OF THE MAKER's CUT IS `pieceOf b' (cutBase …) (cutDs …) (cutPut …) (rest (i + n) (cutDs …))` at the n-th block b'.
  `before b l n`: the number of rounds that the first n blocks declare.
  `cutDs_inner`: a block that is not the last takes `(ds.drop (before b l n)).take ‹its own declared rounds›` · `cutDs_last`: the last takes what is left: `ds.drop (before b l l.length)`.
  `cutBase_eq`: the base is `base + nTrees (ds.take (before b l n))`: the chain's first tree and the trees that the rounds in front send.
  `cutPut_inner` | `cutPut_last`: nothing is put behind but at the last.
  `rowAt₁` | `₂` | `₃`: so at `atDesc F (piecesAt C F D …)`: chain 1: first tree 0, data `D.ds₁`, the sealing round put behind the last · chain 2: first tree `D.t₁`, data `D.ds₂` · chain 3: first tree `D.t₁ + D.t₂`, data `D.ds₃`; the blocks `held c :: k.map held` (`(held b).rounds = b.rounds`).
Nothing on soundness.

-/
import Johnson.Top.Fire.Code.RowPieces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

section
variable {S Cl : Type}

/-- The n-th piece's base, by the maker's own recursion. -/
def cutBase : ℕ → List RDT → Block S Cl → List (Block S Cl) → ℕ → ℕ
  | base, _, _, [], _ => base
  | base, _, _, _ :: _, 0 => base
  | base, ds, b, b' :: l, n + 1 => cutBase (base + nTrees (ds.take b.rounds.length)) (ds.drop b.rounds.length) b' l n

/-- Its stretch. -/
def cutDs : List RDT → Block S Cl → List (Block S Cl) → ℕ → List RDT
  | ds, _, [], _ => ds
  | ds, b, _ :: _, 0 => ds.take b.rounds.length
  | ds, b, b' :: l, n + 1 => cutDs (ds.drop b.rounds.length) b' l n

/-- What is put behind its rounds. -/
def cutPut (putBack : List _root_.Fmt.RoundView) : List (Block S Cl) → ℕ → List _root_.Fmt.RoundView
  | [], _ => putBack
  | _ :: _, 0 => []
  | _ :: l, n + 1 => cutPut putBack l n

/-- The rounds that the first n blocks declare. -/
def before : Block S Cl → List (Block S Cl) → ℕ → ℕ
  | _, _, 0 => 0
  | b, [], _ + 1 => b.rounds.length
  | b, b' :: l, n + 1 => b.rounds.length + before b' l n

variable {C : CK} {Fr : Frame} {W : Type}

/-- **The n-th piece of the maker's cut, in the maker's own terms.** -/
theorem cutRow_at (rest : (i : ℕ) → (ds : List RDT) → Rest C Fr S W ds) (putBack : List _root_.Fmt.RoundView) :
    ∀ (l : List (Block S Cl)) (n i base : ℕ) (ds : List RDT) (b : Block S Cl) (p : Piece C Fr S Cl W),
      ((cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2)[n]? = some p →
      ∃ b' : Block S Cl, (b :: l)[n]? = some b' ∧
        p = pieceOf b' (cutBase base ds b l n) (cutDs ds b l n) (cutPut putBack l n) (rest (i + n) (cutDs ds b l n))
  | [], 0, _, _, _, b, _, h =>
    ⟨b, List.getElem?_cons_zero, (Option.some.inj (List.getElem?_cons_zero.symm.trans h)).symm⟩
  | [], n + 1, _, _, _, _, _, h => by
    have h' := List.getElem?_cons_succ.symm.trans h
    exact absurd h' (by simp [cutRow])
  | _ :: _, 0, _, _, _, b, _, h =>
    ⟨b, List.getElem?_cons_zero, (Option.some.inj (List.getElem?_cons_zero.symm.trans h)).symm⟩
  | b' :: l, n + 1, i, base, ds, b, p, h => by
    obtain ⟨b'', hb, hp⟩ := cutRow_at rest putBack l n (i + 1) _ _ b' p (List.getElem?_cons_succ.symm.trans h)
    have e : i + 1 + n = i + (n + 1) := by omega
    rw [e] at hp
    exact ⟨b'', List.getElem?_cons_succ.trans hb, hp⟩

theorem nTrees_append (x y : List RDT) : nTrees (x ++ y) = nTrees x + nTrees y := by
  unfold nTrees
  rw [List.map_append, List.sum_append]

/-- **A block that is not the last takes its own declared rounds off the front of what is left.** -/
theorem cutDs_inner : ∀ (l : List (Block S Cl)) (n : ℕ) (ds : List RDT) (b b' : Block S Cl), n < l.length → (b :: l)[n]? = some b' →
    cutDs ds b l n = (ds.drop (before b l n)).take b'.rounds.length
  | [], _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, ds, b, b', _, hb => by
    have e : b = b' := Option.some.inj (List.getElem?_cons_zero.symm.trans hb)
    subst e
    rfl
  | c :: l, n + 1, ds, b, b', h, hb => by
    have ih := cutDs_inner l n (ds.drop b.rounds.length) c b' (Nat.lt_of_succ_lt_succ h) (List.getElem?_cons_succ.symm.trans hb)
    have e : cutDs ds b (c :: l) (n + 1) = cutDs (ds.drop b.rounds.length) c l n := rfl
    have e' : before b (c :: l) (n + 1) = b.rounds.length + before c l n := rfl
    rw [e, ih, e', List.drop_drop]

/-- **The last takes what is left.** -/
theorem cutDs_last : ∀ (l : List (Block S Cl)) (ds : List RDT) (b : Block S Cl), cutDs ds b l l.length = ds.drop (before b l l.length)
  | [], _, _ => rfl
  | c :: l, ds, b => by
    have e : cutDs ds b (c :: l) (c :: l).length = cutDs (ds.drop b.rounds.length) c l l.length := rfl
    have e' : before b (c :: l) (c :: l).length = b.rounds.length + before c l l.length := rfl
    rw [e, cutDs_last l _ c, e', List.drop_drop]

/-- **The base: the chain's first tree and the trees that the rounds in front send.** -/
theorem cutBase_eq : ∀ (l : List (Block S Cl)) (n base : ℕ) (ds : List RDT) (b : Block S Cl), n ≤ l.length →
    cutBase base ds b l n = base + nTrees (ds.take (before b l n))
  | [], 0, base, ds, b, _ => by
    have e : cutBase base ds b [] 0 = base := rfl
    have e' : before b [] 0 = 0 := rfl
    rw [e, e', List.take_zero]
    rfl
  | [], _ + 1, _, _, _, h => absurd h (Nat.not_succ_le_zero _)
  | c :: l, 0, base, ds, b, _ => by
    have e : cutBase base ds b (c :: l) 0 = base := rfl
    have e' : before b (c :: l) 0 = 0 := rfl
    rw [e, e', List.take_zero]
    rfl
  | c :: l, n + 1, base, ds, b, h => by
    have ih := cutBase_eq l n (base + nTrees (ds.take b.rounds.length)) (ds.drop b.rounds.length) c (Nat.le_of_succ_le_succ h)
    have e : cutBase base ds b (c :: l) (n + 1) = cutBase (base + nTrees (ds.take b.rounds.length)) (ds.drop b.rounds.length) c l n := rfl
    have e' : before b (c :: l) (n + 1) = b.rounds.length + before c l n := rfl
    rw [e, ih, e', List.take_add, nTrees_append, Nat.add_assoc]

theorem cutPut_inner (putBack : List _root_.Fmt.RoundView) : ∀ (l : List (Block S Cl)) (n : ℕ), n < l.length → cutPut putBack l n = []
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: l, n + 1, h => cutPut_inner putBack l n (Nat.lt_of_succ_lt_succ h)

theorem cutPut_last (putBack : List _root_.Fmt.RoundView) : ∀ l : List (Block S Cl), cutPut putBack l l.length = putBack
  | [] => rfl
  | _ :: l => cutPut_last putBack l

end

section
variable {Xi W : Type} (C : CK) (F : FileDescription Xi) (D : WholeD)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)

/-- **Chain 1's n-th piece at a description's own rows**: the chain's first tree is number 0; its data are `D.ds₁`; the sealing round is put behind the last. -/
theorem rowAt₁ (n : ℕ) (p) (h : ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = some p) :
    ∃ b : Block F.S₁ F.Cl, (c₁ :: k₁)[n]? = some b ∧
      p = pieceOf (held b) (cutBase 0 D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n) (cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n)
        (cutPut [sealRound] (k₁.map (held (P := F.XiPub))) n) (rest₁ n (cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n)) := by
  obtain ⟨b', hb, hp⟩ := cutRow_at rest₁ [sealRound] (k₁.map held) n 0 0 D.ds₁ (held c₁) p h
  obtain ⟨b, hb', rfl⟩ := held_get c₁ k₁ n b' hb
  rw [Nat.zero_add] at hp
  exact ⟨b, hb', hp⟩

/-- **Chain 2's n-th piece at a description's own rows**: the chain's first tree is number D.t₁; its data are `D.ds₂`. -/
theorem rowAt₂ (n : ℕ) (p) (h : ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = some p) :
    ∃ b : Block F.S₂ F.Cl, (c₂ :: k₂)[n]? = some b ∧
      p = pieceOf (held b) (cutBase D.t₁ D.ds₂ (held c₂ : Block ((F.XiPub × F.S₁) × F.S₂) F.Cl) (k₂.map held) n) (cutDs D.ds₂ (held c₂ : Block ((F.XiPub × F.S₁) × F.S₂) F.Cl) (k₂.map held) n)
        (cutPut [] (k₂.map (held (P := (F.XiPub × F.S₁)))) n) (rest₂ n (cutDs D.ds₂ (held c₂ : Block ((F.XiPub × F.S₁) × F.S₂) F.Cl) (k₂.map held) n)) := by
  obtain ⟨b', hb, hp⟩ := cutRow_at rest₂ [] (k₂.map held) n 0 D.t₁ D.ds₂ (held c₂) p h
  obtain ⟨b, hb', rfl⟩ := held_get c₂ k₂ n b' hb
  rw [Nat.zero_add] at hp
  exact ⟨b, hb', hp⟩

/-- **Chain 3's n-th piece at a description's own rows**: the chain's first tree is number D.t₁ + D.t₂; its data are `D.ds₃`. -/
theorem rowAt₃ (n : ℕ) (p) (h : ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[n]? = some p) :
    ∃ b : Block F.S₃ F.Cl, (c₃ :: k₃)[n]? = some b ∧
      p = pieceOf (held b) (cutBase (D.t₁ + D.t₂) D.ds₃ (held c₃ : Block ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl) (k₃.map held) n) (cutDs D.ds₃ (held c₃ : Block ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl) (k₃.map held) n)
        (cutPut [] (k₃.map (held (P := (F.XiPub × F.S₁ × F.S₂)))) n) (rest₃ n (cutDs D.ds₃ (held c₃ : Block ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl) (k₃.map held) n)) := by
  obtain ⟨b', hb, hp⟩ := cutRow_at rest₃ [] (k₃.map held) n 0 (D.t₁ + D.t₂) D.ds₃ (held c₃) p h
  obtain ⟨b, hb', rfl⟩ := held_get c₃ k₃ n b' hb
  rw [Nat.zero_add] at hp
  exact ⟨b, hb', hp⟩

end

end LPFD

#print axioms LPFD.cutRow_at
#print axioms LPFD.cutDs_inner
#print axioms LPFD.cutDs_last
#print axioms LPFD.cutBase_eq
#print axioms LPFD.cutPut_inner
#print axioms LPFD.cutPut_last
#print axioms LPFD.rowAt₁
#print axioms LPFD.rowAt₂
#print axioms LPFD.rowAt₃
