-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ShownBehind.lean: BEHIND THE BLOCK THAT SENDS A TREE EVERY LEAF OF IT IS SHOWN.
Statements (`def … : Prop`) and their proofs.

Why. The promise beside a pin holds "every leaf is shown" (`ShownAt`, MsgSig.lean): at a boundary
the strings are any lists, and a tree that is not sent reads as the zero word, which is a code word.
Past a block that sends other trees the promise rides unturned (`pinStays`). HERE IT IS GAINED, for
certain, at no price: a column of a tree that the stretch itself sends has its words by type.
  `colT_length`, `colAtST_length`: a typed column of a tree has as many words as the tree's shape
    says.
  `ColBehind`: behind a block, at a tree that its stretch sends (number base + n, shape sh), where
    the tree is listed: at every leaf below 2 ^ sh.a the string holds a column of sh.W words.
  `WordBehind`: so, where what the blocks tell of that tree (`FileDescription.oracleAt`) has the shape's
    words, each of its tenants shows a symbol at every such leaf.
  `ShownBehind`: so a member that sits there, at a seat that fits (`SeatFits`), is shown
    (`ShownAt`), if what is told of the tree has the shape's depth and words.
Limits. THAT WHAT IS TOLD OF A TREE HAS THE DATA's SHAPE (depth and words) IS A PREMISE HERE: it
hangs on a clause of `planOk`: Johnson/Desc/Sound/OraclesAre.lean. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MsgSig
import Johnson.Desc.Sound.TilesCutProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)

theorem colT_length : ∀ (ts : List Fmt.Shape) (n x : ℕ) (p : PosT ts), posAtT ts n x = some p →
    ∀ (c : SymT ts p) (sh : Fmt.Shape), ts[n]? = some sh → (colT ts p c).length = sh.W
  | [], _, _, _, h, _, _, _ => by cases h
  | s :: ts, 0, x, p, h, c, sh, hs => by
    have e : sh = s := (Option.some.inj hs).symm
    subst e
    have h' : (if g : x < 2 ^ sh.a then some (Sum.inl ⟨x, g⟩ : Fin (2 ^ sh.a) ⊕ PosT ts)
        else none) = some p := h
    by_cases hx : x < 2 ^ sh.a
    · rw [dif_pos hx] at h'
      have ep := Option.some.inj h'
      subst ep
      exact List.length_ofFn
    · rw [dif_neg hx] at h'
      cases h'
  | s :: ts, k + 1, x, p, h, c, sh, hs => by
    have h' : (posAtT ts k x).map Sum.inr = some p := h
    obtain ⟨p', hp', ep⟩ := Option.map_eq_some_iff.1 h'
    subst ep
    exact colT_length ts k x p' hp' c sh hs

theorem colAtST_length (C : CK) : ∀ (ds : List RDT) (τ : Iop.Tr (uLT C ds)) (n x : ℕ)
    (c : List UInt64) (sh : Fmt.Shape), colAtST C ds τ n x = some c → treeShT ds n = some sh →
    c.length = sh.W
  | [], _, _, _, _, _, h, _ => by cases h
  | d :: ds, τ, n, x, c, sh, h, hs => by
    rw [colAtST_cons] at h
    rw [treeShT_cons] at hs
    by_cases hn : n < d.trees.length
    · rw [if_pos hn] at h hs
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
      exact colT_length d.trees n x p hp _ sh hs
    · rw [if_neg hn] at h hs
      exact colAtST_length C ds τ.2.2 _ x c sh h hs

/-- **Behind a block every leaf of a tree that its stretch sends holds a column of the shape's
words.** -/
def ColBehind : Prop :=
  ∀ (C : CK) (F : Frame) (b : ℕ) (ds : List RDT), ListedAt F b ds →
    ∀ (y : F.E.Str) (τ : Iop.Tr (uLT C ds)) (n : ℕ) (sh : Fmt.Shape), treeShT ds n = some sh →
      ∀ x, x < 2 ^ sh.a → (colAt F (behind C F b ds y τ) (b + n) x).length = sh.W

theorem colBehind : ColBehind := by
  intro C F b ds hL y τ n sh hs x hx
  obtain ⟨p, hp⟩ := posL_of_find F.all (b + n) x sh.a (hL n sh hs) hx
  obtain ⟨c, hc⟩ := colAtST_isSome C ds τ n x sh.a (by rw [hs]; rfl) hx
  have e : colAt F (behind C F b ds y τ) (b + n) x = c := by
    unfold colAt
    rw [hp]
    show sLeft C (stg F b ds) y τ p = c
    rw [sLeft_at C F ds b y τ (b + n) x p hp, sCol_eq, if_neg (by omega), Nat.add_sub_cancel_left,
      hc]
    rfl
  rw [e]
  exact colAtST_length C ds τ n x c sh hc hs

/-- So each tenant of it shows a symbol there, where what is told of the tree has the shape's words.
-/
def WordBehind : Prop :=
  ∀ (Xi : Type) (G : FileDescription Xi) (C : CK) (F : Frame) (b : ℕ) (ds : List RDT), ListedAt F b ds →
    ∀ (y : F.E.Str) (τ : Iop.Tr (uLT C ds)) (n : ℕ) (sh : Fmt.Shape) (o : Oracle) (t : ℕ),
      treeShT ds n = some sh → G.oracleAt (b + n) = some o → o.words = sh.W →
      t < o.tenants.length → ∀ x, x < 2 ^ sh.a →
        (wordOf G (strsOf F (behind C F b ds y τ)) (b + n) t x).isSome = true

theorem wordBehind : WordBehind := by
  intro Xi G C F b ds hL y τ n sh o t hs ho hw ht x hx
  have hl := colBehind C F b ds hL y τ n sh hs x hx
  show ((G.oracleAt (b + n)).bind fun o' =>
    o'.cut t (colAt F (behind C F b ds y τ) (b + n) x)).isSome = true
  rw [ho]
  show (o.cut t (colAt F (behind C F b ds y τ) (b + n) x)).isSome = true
  unfold Oracle.cut
  rw [List.getElem?_eq_getElem ht]
  show (if _ = o.words then some _ else none : Option Sym).isSome = true
  rw [if_pos (by rw [hl, hw])]
  rfl

/-- **So a member that sits there, at a seat that fits, is shown.** -/
def ShownBehind : Prop :=
  ∀ (Xi : Type) (G : FileDescription Xi) (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ), SeatFits G cs l seat →
    ∀ (C : CK) (F : Frame) (b : ℕ) (ds : List RDT), ListedAt F b ds →
    ∀ (y : F.E.Str) (τ : Iop.Tr (uLT C ds)) (i : Fin l.length) (n : ℕ) (sh : Fmt.Shape),
      (seat i).1 = b + n → treeShT ds n = some sh →
      (∀ o, G.oracleAt (b + n) = some o → o.logLength = sh.a ∧ o.words = sh.W) →
      ShownAt G cs l seat (strsOf F (behind C F b ds y τ)) i

theorem shownBehind : ShownBehind := by
  intro Xi G cs l seat hS C F b ds hL y τ i n sh hj hs ho x hx
  obtain ⟨o, nt, h1, h2, h3, -⟩ := hS i
  rw [hj] at h1
  obtain ⟨ha, hw⟩ := ho o h1
  rw [hj]
  refine wordBehind Xi G C F b ds hL y τ n sh o (seat i).2 hs h1 hw ?_ x
    (by rw [← ha, h3]; exact hx)
  exact (List.getElem?_eq_some_iff.1 h2).1

end VerifiableInference.Desc.Sound
