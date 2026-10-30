-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/PieceYes.lean: from a piece's yes to its block's yes, in the words in which a
kind's law wants it. A piece (Johnson/Desc/Sound/ChainRule.lean) is a block of the description
with its stretch of rounds, read as an interactive oracle reduction. Theorems with their proofs,
general in the block.

THE GROUND IS NOT HERE: `Piece.out_iff` (Johnson/Desc/Sound/RunIsDecide.lean) says just where a
piece says yes, as an equivalence, with `Shown` (as many rounds as the block declares; they fit;
the opened leaves are those that the block reads, all of them) and `groupsAt` (the leaves in the
groups in which decide is handed them). What stands here are corollaries.

Main names:

  `Piece.shownR p τ`: the rounds that the block is shown: the transcript's rounds as a view has
    them, then the rounds that the piece puts behind.
  `piece_iff`, `piece_yes`: `Piece.out_iff`, and its forward half, at `p.shownR τ`, with the
    oracles behind written out: the stored table as it was and what the stage leaves. Decide says
    yes AT THE ROUNDS SHOWN WITHOUT THE SEALED DIGEST.
  `below_yes`, `piece_below_yes`: at a piece that holds `below b` the yes gives the whole of that
    block's test on the words (of the rounds and of the leaves handed), and b's own yes.
    `okWords_of_view`, `piece_below_words`: the rounds' half of that test in the library's
    spelling (okGot, okE).
  `piece_below_plain`: where the piece puts no round behind its own: at the transcript's own
    rounds, with the test of work.
  `lift_yes`, `piece_lift_yes`: the same at a block that is lifted to a wider record
    (`Block.lift`): at a piece that holds `(below b).lift get set`.
  `noDigest_vals`, `noDigest_elems`: striking the digest turns neither the items nor the elements
    drawn.
  `left_below`: what the stage leaves at an entry that `posL` finds for a tree sent in front of
    the stretch is what stood there. `left_all`: the oracles behind are the oracles in front,
    under three premises.

Limits. THE FOLD AT ONE BLOCK DOES NOT ASK THAT THE WORDS ARE BELOW THE PRIME: at a piece that
holds b itself nothing on the words follows; it follows at `below b` alone. But for `piece_iff`
all go one way: nothing is said where the piece refuses. `left_all`'s premises: no round of the
stretch sends a tree (public data); every entry of the frame's list is the one that `posL` finds
for its number and leaf, which holds where the numbers are distinct (the frame's maker pays); the
oracles in front are empty at every tree whose number is not below the stretch's base (it belongs
in the condition on the statement in front). These are equations on what texts return: they have
no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.RunIsDecide
import OnBytes.Maker.OkView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK SgX)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-! ## The piece's yes -/

/-- The rounds that the piece's block is shown: the transcript's rounds as a view has them, then the
rounds that the piece puts behind. -/
def Piece.shownR (p : Piece C F S Cl W) (τ : Iop.Tr (uLT C p.ds)) : List Fmt.RoundView :=
  rvT C p.ds τ ++ p.back

/-- **Just where the piece says yes**: `Piece.out_iff`, at the rounds shown, with the oracles behind
written out. -/
theorem piece_iff (p : Piece C F S Cl W) (a a' : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) :
    p.ior.red.out a τ = some a' ↔
      sTests C p.stage a.2 τ = true ∧
      Shown F.ft p.b (p.shownR τ) (sView C p.stage a.2 τ).opened ∧
      p.b.decide a.1 ((p.shownR τ).map noDigest)
        (groupsAt F.ft p.b (p.shownR τ) (sView C p.stage a.2 τ).opened) = .ok a'.1 ∧
      a'.2 = (a.2.1, sLeft C p.stage a.2 τ) :=
  Piece.out_iff p a a' τ

/-- **Where the piece says yes.** -/
theorem piece_yes (p : Piece C F S Cl W) (a a' : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (h : p.ior.red.out a τ = some a') :
    sTests C p.stage a.2 τ = true ∧
      Shown F.ft p.b (p.shownR τ) (sView C p.stage a.2 τ).opened ∧
      p.b.decide a.1 ((p.shownR τ).map noDigest)
        (groupsAt F.ft p.b (p.shownR τ) (sView C p.stage a.2 τ).opened) = .ok a'.1 ∧
      a'.2 = (a.2.1, sLeft C p.stage a.2 τ) :=
  (piece_iff p a a' τ).1 h

/-! ## The test on the words -/

/-- `below b`'s yes: the words are below the prime, and b says yes. -/
theorem below_yes (b : Block S Cl) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : (below b).decide s rs gs = .ok s') :
    viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ = true ∧
      b.decide s rs gs = .ok s' := by
  have h' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ = true then
      b.decide s rs gs else .error "a word is not below the prime") = .ok s' := h
  by_cases hk : viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ = true
  · rw [if_pos hk] at h'
    exact ⟨hk, h'⟩
  · rw [if_neg hk] at h'
    cases h'

/-- The fold's test on the words gives the library's, round by round: every item that holds an
element, and every element drawn. -/
theorem okWords_of_view (v : Fmt.View) (h : viewWordsBelowPrime v = true) :
    (v.rounds.all fun r =>
      r.vals.all OnBytes.Maker.okGot && r.drawn.elems.all fun x => okE (E.ofTriple x)) = true := by
  unfold viewWordsBelowPrime at h
  rw [Bool.and_eq_true] at h
  have h1 := h.1
  rw [List.all_eq_true] at h1 ⊢
  intro r hr
  have k := h1 r hr
  rw [Bool.and_eq_true] at k ⊢
  refine ⟨?_, k.1⟩
  have k2 := k.2
  rw [List.all_eq_true] at k2 ⊢
  intro g hg
  have k3 := k2 g hg
  cases g <;> exact k3

theorem noDigest_vals (r : Fmt.RoundView) : (noDigest r).vals = r.vals := rfl

theorem noDigest_elems (r : Fmt.RoundView) : (noDigest r).drawn.elems = r.drawn.elems := rfl

/-- **Where a piece that holds `below b` says yes**: what `piece_yes` says, of b's own decide, and
the whole of the test on the words: of the rounds that decide is shown and of the leaves that it is
handed. -/
theorem piece_below_yes (p : Piece C F S Cl W) (b : Block S Cl) (hb : p.b = below b)
    (a a' : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (h : p.ior.red.out a τ = some a') :
    Shown F.ft b (p.shownR τ) (sView C p.stage a.2 τ).opened ∧
      viewWordsBelowPrime ⟨(p.shownR τ).map noDigest,
                    ((groupsAt F.ft b (p.shownR τ) (sView C p.stage a.2 τ).opened).flatMap id).map
                      fun c => (0, c.1, c.2)⟩ = true ∧
      b.decide a.1 ((p.shownR τ).map noDigest)
        (groupsAt F.ft b (p.shownR τ) (sView C p.stage a.2 τ).opened) = .ok a'.1 ∧
      a'.2 = (a.2.1, sLeft C p.stage a.2 τ) := by
  obtain ⟨_, f1, f3, f4⟩ := piece_yes p a a' τ h
  rw [hb] at f1 f3
  obtain ⟨g1, g2⟩ := below_yes b _ _ _ _ f3
  exact ⟨f1, g1, g2, f4⟩

/-- The rounds' half of that test, in the library's spelling. -/
theorem piece_below_words (p : Piece C F S Cl W) (b : Block S Cl) (hb : p.b = below b)
    (a a' : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (h : p.ior.red.out a τ = some a') :
    (((p.shownR τ).map noDigest).all fun r =>
      r.vals.all OnBytes.Maker.okGot && r.drawn.elems.all fun x => okE (E.ofTriple x)) = true :=
  okWords_of_view _ (piece_below_yes p b hb a a' τ h).2.1

/-- **The same where the piece puts no round behind its own**: at the transcript's own rounds, and
with the test of work, which stands among the tests in front of the run. -/
theorem piece_below_plain (p : Piece C F S Cl W) (b : Block S Cl) (hb : p.b = below b)
    (hback : p.back = []) (a a' : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (h : p.ior.red.out a τ = some a') :
    passT C p.ds (rhoT C p.ds τ) = true ∧ a'.2 = (a.2.1, sLeft C p.stage a.2 τ) ∧
      (((rvT C p.ds τ).map noDigest).all fun r =>
        r.vals.all OnBytes.Maker.okGot && r.drawn.elems.all fun x => okE (E.ofTriple x)) = true ∧
      ∃ cols, b.decide a.1 ((rvT C p.ds τ).map noDigest) cols = .ok a'.1 := by
  have ht := (piece_yes p a a' τ h).1
  obtain ⟨_, _, f3, f5⟩ := piece_below_yes p b hb a a' τ h
  have f4 := piece_below_words p b hb a a' τ h
  have e : p.shownR τ = rvT C p.ds τ := by
    unfold Piece.shownR
    rw [hback, List.append_nil]
  rw [e] at f3 f4
  unfold sTests at ht
  rw [Bool.and_eq_true, Bool.and_eq_true] at ht
  exact ⟨ht.1.1, f5, f4, _, f3⟩

/-! ## A block that is lifted to a wider record -/

/-- The yes of a lifted block's decide is the block's own yes at the part, laid back. -/
theorem lift_yes {T : Type} (get : T → S) (set : T → S → T) (b : Block S Cl) (t t' : T)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (h : (b.lift get set).decide t rs gs = .ok t') :
    ∃ s', b.decide (get t) rs gs = .ok s' ∧ t' = set t s' := by
  have h' : (b.decide (get t) rs gs).map (set t) = .ok t' := h
  cases hd : b.decide (get t) rs gs with
  | error e =>
    rw [hd] at h'
    have h2 : (Except.error e : Except String T) = .ok t' := h'
    cases h2
  | ok s' =>
    rw [hd] at h'
    have h2 : (Except.ok (set t s') : Except String T) = .ok t' := h'
    exact ⟨s', rfl, (Except.ok.inj h2).symm⟩

/-- **Where a piece that holds `(below b).lift get set` says yes**: b's own decide says yes at the
part of the record in front; the record behind is that record with b's laid back; and the rest as in
`piece_below_yes`. -/
theorem piece_lift_yes {T : Type} (p : Piece C F T Cl W) (get : T → S) (set : T → S → T)
    (b : Block S Cl) (hb : p.b = (below b).lift get set) (a a' : T × F.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) (h : p.ior.red.out a τ = some a') :
    ∃ s', b.decide (get a.1) ((p.shownR τ).map noDigest)
        (groupsAt F.ft b (p.shownR τ) (sView C p.stage a.2 τ).opened) = .ok s' ∧
      a'.1 = set a.1 s' ∧
      Shown F.ft b (p.shownR τ) (sView C p.stage a.2 τ).opened ∧
      viewWordsBelowPrime ⟨(p.shownR τ).map noDigest,
                    ((groupsAt F.ft b (p.shownR τ) (sView C p.stage a.2 τ).opened).flatMap id).map
                      fun c => (0, c.1, c.2)⟩ = true ∧
      a'.2 = (a.2.1, sLeft C p.stage a.2 τ) := by
  obtain ⟨_, f1, f3, f4⟩ := piece_yes p a a' τ h
  rw [hb] at f1 f3
  obtain ⟨s', k1, k2⟩ := lift_yes get set (below b) _ _ _ _ f3
  obtain ⟨g1, g2⟩ := below_yes b _ _ _ _ k1
  exact ⟨s', g2, k2, f1, g1, f4⟩

/-! ## The oracles behind -/

/-- What the stage leaves at an entry that `posL` finds for a tree sent in front of the stretch is
what stood there. -/
theorem left_below (p : Piece C F S Cl W) (y : F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (j x : ℕ)
    (q : PosL F.all) (hq : posL F.all j x = some q) (hj : j < p.base) :
    sLeft C p.stage y τ q = y.2 q := by
  have e := sLeft_at C F p.ds p.base y τ j x q hq
  rw [sCol_eq, if_pos hj, hq] at e
  exact e

/-- A stretch that sends no tree has no column of a tree of its own. -/
theorem colAtST_noTree (C : CK) : ∀ (ds : List RDT) (τ : Iop.Tr (uLT C ds)) (n x : ℕ),
    (∀ d ∈ ds, d.trees = []) → colAtST C ds τ n x = none
  | [], _, _, _, _ => rfl
  | d :: ds, (_, _, τ), n, x, h => by
    have hd : d.trees = [] := h d (by simp)
    rw [colAtST_cons, if_neg (by rw [hd]; exact Nat.not_lt_zero n)]
    exact colAtST_noTree C ds τ _ x fun e he => h e (List.mem_cons_of_mem _ he)

/-- **The oracles behind are the oracles in front**, where no tree is sent in the stretch, every
entry of the frame's list is the one that `posL` finds for its number and leaf, and the oracles in
front are empty at the trees that are not yet sent. -/
theorem left_all (p : Piece C F S Cl W) (y : F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hT : ∀ d ∈ p.ds, d.trees = [])
    (hD : ∀ q : PosL F.all, posL F.all (F.all.get q.1).no q.2.val = some q)
    (hE : ∀ q : PosL F.all, p.base ≤ (F.all.get q.1).no → y.2 q = []) :
    ((y.1, sLeft C p.stage y τ) : F.E.Str) = y := by
  have e : sLeft C p.stage y τ = y.2 := by
    funext q
    by_cases hj : (F.all.get q.1).no < p.base
    · exact left_below p y τ _ _ q (hD q) hj
    · have k := sLeft_at C F p.ds p.base y τ _ _ q (hD q)
      rw [sCol_eq, if_neg hj, colAtST_noTree C p.ds τ _ _ hT] at k
      rw [hE q (Nat.le_of_not_lt hj)]
      exact k
  rw [e]

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.piece_iff
#print axioms VerifiableInference.Desc.Sound.piece_yes
#print axioms VerifiableInference.Desc.Sound.piece_below_yes
#print axioms VerifiableInference.Desc.Sound.piece_below_words
#print axioms VerifiableInference.Desc.Sound.piece_below_plain
#print axioms VerifiableInference.Desc.Sound.lift_yes
#print axioms VerifiableInference.Desc.Sound.piece_lift_yes
#print axioms VerifiableInference.Desc.Sound.left_below
#print axioms VerifiableInference.Desc.Sound.left_all
