-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Row0Wide.lean: the last chain's first block ("K14, second part") in the form
of the rule of composition, with the words read through the record
(Johnson/Desc/Third/Law/Row0Words.lean), AT A PIECE OF A WIDER RECORD T WHOSE BLOCK IS NOT THE
BLOCK ITSELF BUT A WRAP OF IT: all that is asked of the piece's block is that a yes of its decision
is a yes of the block's decision at the part get t of the record, to the part get t' (YesOf). The
wrap in which a description's pieces hold the last chain's blocks is such a one: the
test that every word shown is below the prime, inside the lift to a pair of what was handed to the
chain and the chain's own record. Theorems.

  YesOf get b B        a yes of B at t is a yes of b at get t, to get t'.
  yesOf_self · yesOf_below · yesOf_lift   the block itself; the test on the words in front; the lift
                       to a pair. yesOf_wrap: the two together. yesOf_retype · yesOf_wrap_retype:
                       the block carried to another type of claims, bare and in the wrap. THE BLOCK
                       AND THE PIECE's BLOCK MAY STAND AT TWO TYPES OF CLAIMS.
  lift_fst             the lift leaves the pair's first part.
  row0_goodInT         **the row at the wider record.** The premises on Prm and Rc are asked under
                       the promise in front alone; so is the fence of the two records (hOk): the
                       promise in front, the piece's yes and what it lays give it.
OBJECT   (batchLinearConstraintsSecondPart p).decide; Block.lift · below · Block.retype (the wraps' texts).
USER     YesOf and its lemmas: row0_own · make_wrap | make_retype
         (Johnson/Desc/Third/Law/Row0AtTable.lean). row0_goodInT IS A FORERUNNER: nobody calls it.
LETTERS  get · the two types of claims.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.
What is not claimed. All that Johnson/Desc/Third/Law/Row0Words.lean does not claim. RowsHold holds
for nothing at a record whose own group is not there: in front of the block that is the promise's
matter. The promise behind is what a yes gives: it is not a table's promise.

-/
import Johnson.Desc.Third.Law.Row0Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Third.Law
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open VerifiableInference.Desc.Sound (Frame Piece goodIn_of_sure below)
open _root_.Run.PQ (CK)

variable {T U Cl Cl₀ : Type}

/-- A yes of B at t is a yes of b at the part get t of the record, to get t'. -/
def YesOf (get : T → S₃) (b : Block S₃ Cl₀) (B : Block T Cl) : Prop :=
  ∀ t rs gs t', B.decide t rs gs = .ok t' → ∃ rs' gs', b.decide (get t) rs' gs' = .ok (get t')

/-- The block itself. -/
theorem yesOf_self (b : Block S₃ Cl) : YesOf id b b := fun _ rs gs _ h => ⟨rs, gs, h⟩

/-- The test that every word shown is below the prime, in front. -/
theorem yesOf_below (get : T → S₃) (b : Block S₃ Cl₀) (B : Block T Cl) (h : YesOf get b B) :
    YesOf get b (below B) := by
  intro t rs gs t' hd
  have hd' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then B.decide t rs gs
      else .error "a word is not below the prime") = .ok t' := hd
  split at hd'
  · exact h t rs gs t' hd'
  · cases hd'

/-- The lift to a pair. -/
theorem yesOf_lift (get : T → S₃) (b : Block S₃ Cl₀) (B : Block T Cl) (h : YesOf get b B) :
    YesOf (fun x : U × T => get x.2) b (Block.lift Prod.snd (fun x s => (x.1, s)) B) := by
  intro x rs gs x' hd
  have hd' : (B.decide x.2 rs gs).map (fun s => (x.1, s)) = .ok x' := hd
  cases hB : B.decide x.2 rs gs with
  | error e => rw [hB] at hd'; cases hd'
  | ok s =>
    rw [hB] at hd'
    cases hd'
    exact h x.2 rs gs s hB

/-- The wrap in which a description's pieces hold the last chain's blocks. -/
theorem yesOf_wrap (b : Block S₃ Cl) :
    YesOf (fun x : U × S₃ => x.2) b (Block.lift Prod.snd (fun x s => (x.1, s)) (below b)) :=
  yesOf_lift id b (below b) (yesOf_below id b b (yesOf_self b))

/-- The block carried to another type of claims (Block.retype, Johnson/Desc/Block.lean): it decides
as the block itself. -/
theorem yesOf_retype (get : T → S₃) (b : Block S₃ Cl₀) {Cl₁ : Type} (B : Block T Cl₁)
    (h : YesOf get b B) : YesOf get b (B.retype (Cl' := Cl)) :=
  fun t rs gs t' hd => h t rs gs t' hd

/-- The wrap around the block carried to the description's type of claims: the form in which a
description that lays a later chain by Chain.retype holds its blocks. -/
theorem yesOf_wrap_retype (b : Block S₃ Cl₀) :
    YesOf (fun x : U × S₃ => x.2) b
      (Block.lift Prod.snd (fun x s => (x.1, s)) (below (b.retype (Cl' := Cl)))) :=
  yesOf_lift id b _ (yesOf_below id b _ (yesOf_retype id b b (yesOf_self b)))

/-- The lift leaves the pair's first part. -/
theorem lift_fst (B : Block T Cl) (x x' : U × T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (Block.lift Prod.snd (fun x s => (x.1, s)) B).decide x rs gs = .ok x') : x'.1 = x.1 := by
  have hd' : (B.decide x.2 rs gs).map (fun s => (x.1, s)) = .ok x' := h
  cases hB : B.decide x.2 rs gs with
  | error e => rw [hB] at hd'; cases hd'
  | ok s =>
    rw [hB] at hd'
    cases hd'
    rfl

variable {K : Type} [Field K] (ρ : Model.Reading K) {W : Type} {C : CK} {F : Frame}

/-- **The row at the wider record.** -/
theorem row0_goodInT (p : P₁₄) (get : T → S₃) (pc : Piece C F T Cl W)
    (hb : YesOf get (batchLinearConstraintsSecondPart p : Block S₃ Cl₀) pc.b) (hext : ∀ a τ w, pc.ext a τ w = w)
    (Ok : S₃ → S₃ → Prop) (words : S₃ → W → Words K) (omW wv : W → Nat → K)
    (hR : Reads p Ok words omW wv) (Prm : T × F.E.Str → Prop)
    (hOk : ∀ a τ b, AtDot p (get a.1) → Names (get a.1) → Prm a → pc.ior.red.out a τ = some b →
      Says p (get a.1) (get b.1) → Ok (get a.1) (get b.1))
    (hkeep : ∀ a τ b, AtDot p (get a.1) → Names (get a.1) → pc.ior.red.out a τ = some b →
      Says p (get a.1) (get b.1) → Prm a → Prm b)
    (Rc : T × F.E.Str → W → Prop)
    (hback : ∀ a τ b w, AtDot p (get a.1) → Names (get a.1) → Prm a →
      pc.ior.red.out a τ = some b → Says p (get a.1) (get b.1) → Rc b w → Rc a w) :
    pc.GoodIn (fun a => AtDot p (get a.1) ∧ Names (get a.1) ∧ Prm a)
      (fun b => (∃ s, AtDot p s ∧ Says p s (get b.1)) ∧ Prm b)
      (fun a w => RowsHold ρ (get a.1) (words (get a.1) w) ∧ DotSem ρ p omW wv (get a.1) w ∧
        Rc a w)
      (fun b w => RowsThere ρ (get b.1) (words (get b.1) w) ∧ Rc b w) := by
  refine goodIn_of_sure pc _ _ _ _ fun a τ b ha hout => ?_
  obtain ⟨_, rs, gs, hd⟩ := pc.out_of_decide a τ b hout
  obtain ⟨rs', gs', hd'⟩ := hb _ _ _ _ hd
  have hk := (law_k14Second (Cl := Cl₀) p).1 _ _ _ _ hd'
  have hs := (law_k14Second (Cl := Cl₀) p).2 _ _ _ _ hd'
  refine ⟨⟨⟨get a.1, ha.1, hs⟩, hkeep a τ b ha.1 ha.2.1 hout hs ha.2.2⟩, fun w hw => ?_⟩
  rw [hext]
  obtain ⟨r1, r2⟩ := row0_backW ρ p Ok words omW wv hR (get a.1) (get b.1)
    (hOk a τ b ha.1 ha.2.1 ha.2.2 hout hs) hs hk ha.1 ha.2.1 w (rowsHold_of_there ρ _ _ hw.1)
  exact ⟨r1, r2, hback a τ b w ha.1 ha.2.1 ha.2.2 hout hs hw.2⟩

end VerifiableInference.Desc.Third.Law
