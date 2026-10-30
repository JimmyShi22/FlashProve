-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/RowPieces.lean: THE MAKER's ROWS OF PIECES, PIECE BY PIECE. Book-keeping, general in the description: so that a law can be owed and paid AT ONE NUMBERED BLOCK.
Main names.
  `cutRow_get`: the n-th piece of the maker's cut is `pieceOf b' base' ds' back' (rest (i + n) ds')` at the n-th block b'.
  `rowGet₁` | `rowGet₂` | `rowGet₃`: so at `atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ …)`: the n-th piece of chain j is `pieceOf (held b) base ds back (restⱼ n ds)` at the n-th block b of `cⱼ :: kⱼ`.
  `rowNone₁` | `rowNone₂` | `rowNone₃`: behind its last piece a row holds nothing.
  `KeepsAt on L ps n`: the law «promise kept, and true behind gives true in front» OWED AT THE n-TH PIECE ALONE, between the borders n and n + 1.
  `eachKeeps_of_at`: the law at every number gives the rule's premise `EachKeeps on L 0 ps`.
Nothing on soundness.

-/
import Johnson.Desc.Sound.PaidAtDesc
import Johnson.Desc.Plain.FoldChain
import Johnson.Top.Fire.Code.RowLengths

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

section
variable {C : CK} {Fr : Frame} {S Cl W : Type}

/-- The n-th piece of the maker's cut, of its parts. -/
theorem cutRow_get (rest : (i : ℕ) → (ds : List RDT) → Rest C Fr S W ds) (putBack : List _root_.Fmt.RoundView) :
    ∀ (l : List (Block S Cl)) (n i base : ℕ) (ds : List RDT) (b : Block S Cl) (p : Piece C Fr S Cl W),
      ((cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2)[n]? = some p →
      ∃ (b' : Block S Cl) (base' : ℕ) (ds' : List RDT) (back' : List _root_.Fmt.RoundView),
        (b :: l)[n]? = some b' ∧ p = pieceOf b' base' ds' back' (rest (i + n) ds')
  | [], 0, _, base, ds, b, _, h =>
    ⟨b, base, ds, putBack, List.getElem?_cons_zero, (Option.some.inj (List.getElem?_cons_zero.symm.trans h)).symm⟩
  | [], n + 1, _, _, _, _, _, h => by
    have h' := List.getElem?_cons_succ.symm.trans h
    exact absurd h' (by simp [cutRow])
  | _ :: _, 0, _, base, ds, b, _, h =>
    ⟨b, base, ds.take b.rounds.length, [], List.getElem?_cons_zero, (Option.some.inj (List.getElem?_cons_zero.symm.trans h)).symm⟩
  | b' :: l, n + 1, i, base, ds, b, p, h => by
    obtain ⟨b'', base', ds', back', hb, hp⟩ :=
      cutRow_get rest putBack l n (i + 1) _ _ b' p (List.getElem?_cons_succ.symm.trans h)
    have e : i + 1 + n = i + (n + 1) := by omega
    rw [e] at hp
    exact ⟨b'', base', ds', back', List.getElem?_cons_succ.trans hb, hp⟩

/-- **The law owed at the n-th piece alone.** -/
def KeepsAt (on L : ℕ → S × Fr.E.Str → Prop) (ps : List (Piece C Fr S Cl W)) (n : ℕ) : Prop :=
  ∀ p, ps[n]? = some p → p.ior.red.Keeps (on n) (on (n + 1)) (L n) (L (n + 1)) p.err

theorem eachKeeps_from (on L : ℕ → S × Fr.E.Str → Prop) :
    ∀ (ps : List (Piece C Fr S Cl W)) (j : ℕ),
      (∀ (n : ℕ) (p : Piece C Fr S Cl W), ps[n]? = some p → p.ior.red.Keeps (on (j + n)) (on (j + n + 1)) (L (j + n)) (L (j + n + 1)) p.err) →
      Plain.EachKeeps on L j ps
  | [], _, _ => trivial
  | p :: l, j, h =>
    ⟨h 0 p List.getElem?_cons_zero, eachKeeps_from on L l (j + 1) fun n q hq => by
      have e := h (n + 1) q (List.getElem?_cons_succ.trans hq)
      have e1 : j + (n + 1) = j + 1 + n := by omega
      rw [e1] at e
      exact e⟩

/-- **The law at every number gives the rule's premise.** -/
theorem eachKeeps_of_at {on L : ℕ → S × Fr.E.Str → Prop} {ps : List (Piece C Fr S Cl W)} (h : ∀ n, KeepsAt on L ps n) :
    Plain.EachKeeps on L 0 ps :=
  eachKeeps_from on L ps 0 fun n p hp => by
    rw [Nat.zero_add]
    exact h n p hp

end

section
variable {Xi W : Type} (C : CK) (F : FileDescription Xi) (D : WholeD)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)

/-- A block of `held c :: k.map held` is a block of `c :: k`, held. -/
theorem held_get {P S Cl : Type} (c : Block S Cl) (k : List (Block S Cl)) (n : ℕ) (b' : Block (P × S) Cl)
    (h : (held c :: k.map held)[n]? = some b') : ∃ b, (c :: k)[n]? = some b ∧ b' = held b := by
  have h' : ((c :: k).map (held (P := P)))[n]? = some b' := h
  rw [List.getElem?_map] at h'
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 h'
  exact ⟨b, hb, e.symm⟩

theorem rowGet₁ (n : ℕ) (p) (h : ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = some p) :
    ∃ (b : Block F.S₁ F.Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView), (c₁ :: k₁)[n]? = some b ∧ p = pieceOf (held b) base ds back (rest₁ n ds) := by
  obtain ⟨b', base, ds, back, hb, hp⟩ := cutRow_get rest₁ _ (k₁.map held) n 0 _ _ (held c₁) p h
  obtain ⟨b, hb', rfl⟩ := held_get c₁ k₁ n b' hb
  rw [Nat.zero_add] at hp
  exact ⟨b, base, ds, back, hb', hp⟩

theorem rowGet₂ (n : ℕ) (p) (h : ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = some p) :
    ∃ (b : Block F.S₂ F.Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView), (c₂ :: k₂)[n]? = some b ∧ p = pieceOf (held b) base ds back (rest₂ n ds) := by
  obtain ⟨b', base, ds, back, hb, hp⟩ := cutRow_get rest₂ _ (k₂.map held) n 0 _ _ (held c₂) p h
  obtain ⟨b, hb', rfl⟩ := held_get c₂ k₂ n b' hb
  rw [Nat.zero_add] at hp
  exact ⟨b, base, ds, back, hb', hp⟩

theorem rowGet₃ (n : ℕ) (p) (h : ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[n]? = some p) :
    ∃ (b : Block F.S₃ F.Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView), (c₃ :: k₃)[n]? = some b ∧ p = pieceOf (held b) base ds back (rest₃ n ds) := by
  obtain ⟨b', base, ds, back, hb, hp⟩ := cutRow_get rest₃ _ (k₃.map held) n 0 _ _ (held c₃) p h
  obtain ⟨b, hb', rfl⟩ := held_get c₃ k₃ n b' hb
  rw [Nat.zero_add] at hp
  exact ⟨b, base, ds, back, hb', hp⟩

/-- Behind its last piece chain 1's row holds nothing. -/
theorem rowNone₁ (n : ℕ) (h : k₁.length + 1 ≤ n) :
    ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = none :=
  List.getElem?_eq_none (by rw [List.length_cons, rowLen₁]; exact h)

/-- Behind its last piece chain 2's row holds nothing. -/
theorem rowNone₂ (n : ℕ) (h : k₂.length + 1 ≤ n) :
    ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = none :=
  List.getElem?_eq_none (by rw [List.length_cons, rowLen₂]; exact h)

/-- Behind its last piece chain 3's row holds nothing. -/
theorem rowNone₃ (n : ℕ) (h : k₃.length + 1 ≤ n) :
    ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[n]? = none :=
  List.getElem?_eq_none (by rw [List.length_cons, rowLen₃]; exact h)

end

end LPFD

#print axioms LPFD.cutRow_get
#print axioms LPFD.eachKeeps_of_at
#print axioms LPFD.rowGet₁
#print axioms LPFD.rowGet₂
#print axioms LPFD.rowGet₃
#print axioms LPFD.rowNone₁
