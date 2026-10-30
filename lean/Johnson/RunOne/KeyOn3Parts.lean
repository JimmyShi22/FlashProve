-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyOn3Parts.lean: THE KEY FILE's LAST CHAIN: THE WHOLE INVARIANT on₃ … k
(Johnson/RunOne/KeyRows23At.lean) AT A STATEMENT (z, y), SORTED INTO THREE HEAPS, AT THE TABLES'
LETTERS. The sibling of Johnson/RunOne/KeyOn2Parts.lean (the shared chain: Tests₂ · Strings₂ ·
on₂_of_parts), in its form.
 (α) Tests₃ k z: THE FACTS ON THE VERIFIER's STATE ALONE: ten: shape (the tables' own test with code
   shapeB₃) · placed · omega₀ · omega · order · order₀ · maskW · lin₀ · seatW · seatOmega₀.
   [Free₃'s in₀ · inOwn · inOmega are NOT asked: they follow from order₀ | order by the tables' own
   sampleIn_of_order | openIn_of_order.]
 (β) THE LETTERS: arr · reads.
 (γ) Strings₃ k z y: THE ORACLE STRINGS' SIDE: record (FreeAt) · at every open pin: shown · smp ·
   noColl.
THIS FILE SHOWS NO MEMBER: AN IMPLICATION AND ITS CONVERSE. It is the invariant's definition,
sorted: so that the state's side can be had off the history alone (KeyASide3AtFk.lean).
OBJECT: on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ k (z, y) · USER: KeyASide3AtFk.lean; a
member of the guards of rows 3.0 … 3.3 · LETTERS: the tables'.
  Tests₃ · Strings₃ · on₃_of_parts · parts_of_on₃ (the way back: the three heaps ask no more than
  the invariant)
Nothing on soundness.
-/
import Johnson.RunOne.KeyRows23At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (Fr₃ : Frame)
  (G₃ : Reading (P₃ × St₃) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)

/-- **(α) The facts on the verifier's state alone**, at border k of the last chain. -/
structure Tests₃ (k : Nat) (z : P₃ × St₃) : Prop where
  shape : shapeB₃ S K₁ a idx src t₁ k z.2 = true
  placed : k ≤ 2 → Placed K₁.orc (fun o => z.2.book.place[o]?) off₃ at_ [0, 2]
  omega₀ : k = 0 → ∃ b, z.2.loc.border = some b ∧
    Placed (fun _ => some b.shared.omega) (fun o => b.shared.book.place[o]?) off₂ at_ [4]
  omega : 1 ≤ k → k ≤ 2 →
    Placed (fun _ => some z.2.loc.omega) (fun o => z.2.book.place[o]?) off₃ at_ [4]
  order : Means.InOrder z.2.st
  order₀ : k = 0 → ∃ b, z.2.loc.border = some b ∧ Means.InOrder b.shared.st
  maskW : MaskWith (fun i => z.2.book.place[i]?) z.2.loc.w (z.2.loc.w + 1)
  lin₀ : k = 0 → OnBytes.linOk z.2.st.codes S = true
  seatW : k = 0 → (z.2.st.oracles[z.2.loc.w]?).any (·.shape == S.w) = true
  seatOmega₀ : k = 0 → ∀ b, z.2.loc.border = some b →
    (b.shared.st.oracles[b.shared.omega]?).any (·.shape == S.omega) = true

/-- **(γ) The oracle strings' side**, at border k. -/
structure Strings₃ (k : Nat) (z : P₃ × St₃) (y : Strs) : Prop where
  record : FreeAt G₃ coll z y
  shown : ∀ j ∈ pinned (open₃ k), ShownAt F at_ j y
  smp : ∀ j ∈ pinned (open₃ k), hasSmp G₃ (at_ j).1 (at_ j).2 z = true
  noColl : ∀ j ∈ pinned (open₃ k), NoColl F G₃ (at_ j).1 (at_ j).2 z y

/-- **THE LAST CHAIN's WHOLE INVARIANT, FROM THE THREE HEAPS.** -/
theorem on₃_of_parts (k : Nat) (z : P₃ × St₃) (y : Fr₃.E.Str)
    (T : Tests₃ at_ S K₁ a idx src off₂ off₃ t₁ k z)
    (harr : ArrOk G₃ at_ [0, 2, 4]) (hreads : ReadsPinned G₃ at_ R [0, 2, 4])
    (Y : Strings₃ F G₃ at_ coll k z (strsOf Fr₃ y)) :
    on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ k (z, y) :=
  Or.inr ⟨T.shape, List.all_eq_true.2 fun j hj => Y.smp j hj,
    { record := Y.record, arr := harr, reads := hreads, placed := T.placed, omega₀ := T.omega₀
      omega := T.omega
      in₀ := fun h0 => by
        obtain ⟨b, hb, hO⟩ := T.order₀ h0
        exact ⟨b, hb, sampleIn_of_order hO _⟩
      inOwn := fun _ => ⟨fun _ _ o _ => sampleIn_of_order T.order o, openIn_of_order T.order _⟩
      inOmega := fun _ _ => sampleIn_of_order T.order _
      order := T.order, order₀ := T.order₀, shown := Y.shown, maskW := T.maskW, lin₀ := T.lin₀
      seatW := T.seatW, seatOmega₀ := T.seatOmega₀ },
    Y.noColl⟩

/-- **The way back**: the invariant gives the three heaps: they ask no more than it. -/
theorem parts_of_on₃ (k : Nat) (z : P₃ × St₃) (y : Fr₃.E.Str)
    (h : on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ k (z, y)) :
    Tests₃ at_ S K₁ a idx src off₂ off₃ t₁ k z ∧ ArrOk G₃ at_ [0, 2, 4] ∧
      ReadsPinned G₃ at_ R [0, 2, 4] ∧ Strings₃ F G₃ at_ coll k z (strsOf Fr₃ y) := by
  rcases h with hn | ⟨h1, h2, f, h4⟩
  · exact absurd trivial hn
  · exact ⟨⟨h1, f.placed, f.omega₀, f.omega, f.order, f.order₀, f.maskW, f.lin₀, f.seatW,
      f.seatOmega₀⟩, f.arr, f.reads,
      ⟨f.record, f.shown, fun j hj => List.all_eq_true.1 h2 j hj, h4⟩⟩

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.on₃_of_parts
#print axioms Johnson.RunOne.KeyRows23.parts_of_on₃
