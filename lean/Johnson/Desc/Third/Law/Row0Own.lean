-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Row0Own.lean: THE LAST CHAIN's FIRST BLOCK ("K14, second part") HAS WHAT A
KIND's FILES OWE AT A TABLE OF JOINTS (Piece.Own, Johnson/Desc/Sound/Spine.lean): from "the items
that the block closes hold" to "the items that it opens hold": GIVEN FIVE LINKS between the table's
letters (its promises on | on', its items' meaning) and the terms of
Johnson/Desc/Third/Law/Row0Wide.lean. General in the table: its items, their meaning, the record.
THE FENCE, THE WORDS AND THE TWO READERS OF THE WITNESS ARE FAMILIES IN WHAT WAS HANDED TO THE CHAIN
(hand : the record → what was handed; a yes leaves it as it is): a table's promise holds of
statements with many handed parts, and a fence that names one of them would hold of no other.
Theorems, and four tries.

  row0_own             **the clause.** The links: (0) the promise in front, the piece's yes, the
                       block's own yes and what it lays give the fence of the two records,
                       inside which words is asked to read aright · (1) the promise in front and
                       the block's own yes give AtDot and Names at the chain's own record · (2) the
                       promise in front, the piece's yes, the block's own yes and what it lays give
                       the promise behind · (3) inside the promise behind, "the opened items hold"
                       gives RowsHold at the words read through the record behind · (4) inside the
                       promise in front, RowsHold at the words read through the record in front and
                       the semantic (Dot) give "the closed items hold".
  fixedFence_one       A TRY: under a fence that names one statement, link (0) makes all records
                       inside the promise at which the piece says yes bear that one statement: why
                       the fence is a family.
  deafWrap_not_yesOf   A TRY: a wrap that says yes to all is no YesOf of a block that refuses all.
  shiftWords_not_reads   A TRY: words that read an older message otherwise through the record behind
                       do not meet Reads, wherever the block can say yes, inside the fence, at a
                       statement with a message.
  bookWords_reads      A TRY THE OTHER WAY: a words that names the record's book meets Reads at a
                       fence on the two books: THE FORM ADMITS IT, no more: inside that fence these
                       words are the constant 0: it sends no message to a component by the book.
OBJECT   (batchLinearConstraintsSecondPart p).decide, through YesOf.
USER     rowZero (Johnson/Desc/Third/Law/Row0AtTable.lean): CALLED BY NAME.
LETTERS  get · hand · the family Ok | words | omW | wv · the table's on | on' | means | In | Out.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.
What is not claimed. THE FIVE LINKS ARE PREMISES: they are the filling's matter. NO MEMBER OF THE
FAMILY (a fence, words and readers with Reads at every handed part) IS SHOWN HERE. What is owed for
the items that ride past the block (Piece.Frames) is not here. All that
Johnson/Desc/Third/Law/Row0Wide.lean does not claim.

-/
import Johnson.Desc.Sound.Spine
import Johnson.Desc.Third.Law.Row0Wide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Third.Law
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open VerifiableInference.Desc.Sound (Frame Piece goodIn_of_sure relAt)
open _root_.Run.PQ (CK)

variable {T U Cl Cl₀ W ι : Type} {C : CK} {F : Frame} {K : Type} [Field K] (ρ : Model.Reading K)

/-- **The clause of the table at the block.** -/
theorem row0_own (p : P₁₄) (get : T → S₃) (hand : T → U) (pc : Piece C F T Cl W)
    (hb : YesOf get (batchLinearConstraintsSecondPart p : Block S₃ Cl₀) pc.b) (hext : ∀ a τ w, pc.ext a τ w = w)
    (Ok : U → S₃ → S₃ → Prop) (words : U → S₃ → W → Words K) (omW wv : U → W → Nat → K)
    (hR : ∀ u, Reads p (Ok u) (words u) (omW u) (wv u)) (on on' : T × F.E.Str → Prop)
    (hh : ∀ a τ b, on a → pc.ior.red.out a τ = some b → hand b.1 = hand a.1)
    (means : ι → T × F.E.Str → W → Prop) (In Out : ι → Prop)
    (h0 : ∀ a τ b, on a → pc.ior.red.out a τ = some b →
      (∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl₀).decide (get a.1) rs gs = .ok (get b.1)) →
      Says p (get a.1) (get b.1) → Ok (hand a.1) (get a.1) (get b.1))
    (h1 : ∀ a s', on a → (∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl₀).decide (get a.1) rs gs = .ok s') →
      AtDot p (get a.1) ∧ Names (get a.1))
    (h2 : ∀ a τ b, on a → pc.ior.red.out a τ = some b →
      (∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl₀).decide (get a.1) rs gs = .ok (get b.1)) →
      Says p (get a.1) (get b.1) → on' b)
    (h3 : ∀ b w, on' b → relAt means Out b w →
      RowsHold ρ (get b.1) (words (hand b.1) (get b.1) w))
    (h4 : ∀ a w, on a → RowsHold ρ (get a.1) (words (hand a.1) (get a.1) w) →
      DotSem ρ p (omW (hand a.1)) (wv (hand a.1)) (get a.1) w → relAt means In a w) :
    pc.Own on on' means In Out := by
  refine goodIn_of_sure pc _ _ _ _ fun a τ b ha hout => ?_
  obtain ⟨_, rs, gs, hd⟩ := pc.out_of_decide a τ b hout
  obtain ⟨rs', gs', hd'⟩ := hb _ _ _ _ hd
  have hk := (law_k14Second (Cl := Cl₀) p).1 _ _ _ _ hd'
  have hs := (law_k14Second (Cl := Cl₀) p).2 _ _ _ _ hd'
  have hon := h2 a τ b ha hout ⟨rs', gs', hd'⟩ hs
  refine ⟨hon, fun w hw => ?_⟩
  rw [hext]
  have h3' := h3 b w hon hw
  rw [hh a τ b ha hout] at h3'
  obtain ⟨r1, r2⟩ := row0_backW ρ p (Ok (hand a.1)) (words (hand a.1)) (omW (hand a.1))
    (wv (hand a.1)) (hR (hand a.1)) (get a.1) (get b.1) (h0 a τ b ha hout ⟨rs', gs', hd'⟩ hs) hs hk
    (h1 a _ ha ⟨rs', gs', hd'⟩).1 (h1 a _ ha ⟨rs', gs', hd'⟩).2 w h3'
  exact h4 a w ha r1 r2

/-- **A try**: under a fence that names one statement, link (0) makes every record inside the
promise at which the piece says yes, and lays what the block lays, bear that statement. -/
theorem fixedFence_one (p : P₁₄) (get : T → S₃) (pc : Piece C F T Cl W) (st₁ : Statement)
    (Ok : S₃ → S₃ → Prop) (hOk : ∀ s s', Ok s s' → s.st = st₁) (on : T × F.E.Str → Prop)
    (h0 : ∀ a τ b, on a → pc.ior.red.out a τ = some b → Says p (get a.1) (get b.1) →
      Ok (get a.1) (get b.1))
    (a a' b b' : T × F.E.Str) (τ τ' : Iop.Tr (OnBytes.Maker.uLT C pc.ds)) (ha : on a) (ha' : on a')
    (hout : pc.ior.red.out a τ = some b) (hout' : pc.ior.red.out a' τ' = some b')
    (hs : Says p (get a.1) (get b.1)) (hs' : Says p (get a'.1) (get b'.1)) :
    (get a.1).st = (get a'.1).st :=
  (hOk _ _ (h0 a τ b ha hout hs)).trans (hOk _ _ (h0 a' τ' b' ha' hout' hs')).symm

/-- **A try**: a wrap that says yes to all is no YesOf of a block that refuses all. -/
theorem deafWrap_not_yesOf (s : S₃) :
    ¬ YesOf id (roundlessBlock (Cl := Unit) "no" 3 none 0 fun _ : S₃ => .error "no")
      (roundlessBlock (Cl := Unit) "yes" 3 none 0 fun t : S₃ => .ok t) := by
  intro h
  obtain ⟨_, _, hd⟩ := h s [] [] s rfl
  cases hd

/-- **A try**: words that read an older message otherwise through the record behind do not meet
Reads, wherever the block can say yes at a statement with a message. -/
theorem shiftWords_not_reads [Nontrivial K] (p : P₁₄) (Ok : S₃ → S₃ → Prop) (omW wv : W → Nat → K)
    (s s' : S₃) (w : W) (ok : Ok s s') (h : Says p s s') (h0 : 0 < s.st.oracles.size) :
    ¬ Reads p Ok
      (fun t (_ : W) _ _ _ => if t.st.oracles.size = s.st.oracles.size then (0 : K) else 1)
      omW wv := by
  intro hR
  have e := hR.older s s' w ok h 0 h0 .main 0
  obtain ⟨_, _, _, _, _, _, _, _, hsz, _⟩ := h
  simp only [hsz, if_true] at e
  rw [if_neg (by omega)] at e
  exact one_ne_zero e

/-- **A try the other way**: words that hang on the record's book (here: on how many trees it
holds) meet Reads at the fence "both books hold no tree". -/
theorem bookWords_reads (p : P₁₄) :
    Reads (W := W) p (fun s s' => s.book.trees.size = 0 ∧ s'.book.trees.size = 0)
      (fun t _ _ _ _ => ((t.book.trees.size : Nat) : K)) (fun _ _ => 0) (fun _ _ => 0) where
  older := fun s s' _ ok _ _ _ _ _ => by rw [ok.1, ok.2]
  omega := fun s s' _ ok _ _ _ => by rw [ok.2]; exact Nat.cast_zero
  w := fun s s' _ ok _ _ _ => by rw [ok.2]; exact Nat.cast_zero

end VerifiableInference.Desc.Third.Law
