-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyOn2Parts.lean: THE SKELETON OF «on₂_of_tests» (in the
first chain's shape: on₁_of_tests, Johnson/RunOne/KeyFillOn.lean),
ITS PARAMETRIC CORE: THE SHARED CHAIN's WHOLE PROMISE on₂ … k
(Johnson/RunOne/KeyRows23At.lean) AT A STATEMENT (z, y), FROM THREE HEAPS, AT THE TABLES' LETTERS:
 (α) Tests₂ k z: THE FACTS ON THE STATE ALONE: sixteen: each has, or is to have, a Bool form that is
   ridden at the honest walk (by runs): shape · last · eval · placed₁ ·
   order₁ · key · codes · lay · placed · order · linOk · seatU · seatOmega · fits · mask₁ · maskU.
   [Free₂'s in₁ · samples · rowsIn are NOT asked: they follow from order₁ | order by the tables' own
   handedIn_of_order | sampleIn_of_order | openIn_of_order.]
 (β) THE LETTERS: arr · reads: at the filling of KeyFillBaseAt.lean: arrOk_six₂ · readsPinned_fam.
 (γ) Strings₂ k z y: THE STRINGS' SIDE: record (FreeAt) · at every open pin: shown · hasSmp ·
   NoColl: at the filling: member_of_record₂ (Johnson/RunOne/KeyFillChains.lean) and not_coll_words.
THIS FILE SHOWS NO MEMBER: AN IMPLICATION. It is the promise's definition, sorted: its worth is
that whoever is to show a heap sees its list, to the letter, and that what follows from «in
order» is struck from the list.
OBJECT: on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k (z, y) · USER: on₂_of_tests at that
filling; a member of the guards of rows 2.0 … 2.8 · LETTERS: the tables'.
  Tests₂ · Strings₂ · on₂_of_parts · parts_of_on₂ (the way back, where the statement is unmarked: so
    the three heaps are no more than the promise)
Nothing on soundness.
-/
import Johnson.RunOne.KeyRows23At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- **(α) The facts on the state alone**, at border k. -/
structure Tests₂ (k : Nat) (z : P₂ × St₂) : Prop where
  shape : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a k z.2) = true
  last : last₁ z.1.2 = true
  eval : EvalIs S z.1.2
  placed₁ : Placed K₁.orc (fun o => z.1.2.d.book.place[o]?) id at_ [0, 2]
  order₁ : Means.InOrder z.1.2.d.st
  key : z.2.loc.key = z.1.1.key
  codes : z.2.st.codes = z.1.2.d.st.codes
  lay : 3 ≤ k → z.2.loc.oU.lay = vectorLay z.2.st.codes S.fold.u S.fold.rowsHigh
  placed : Placed (plan₂ S).orc (fun o => z.2.book.place[o]?) off₂ at_ ((pinned (open₂ k)).filter (3
      ≤ ·))
  order : Means.InOrder z.2.st
  linOk : 2 ≤ k → OnBytes.linOk z.2.st.codes S = true
  seatU : 3 ≤ k → (z.2.st.oracles[0]?).any (·.shape == S.fold.u) = true
  seatOmega : 6 ≤ k → (z.2.st.oracles[2]?).any (·.shape == S.omega) = true
  fits : z.1.1.key.fits S.fold.index = true
  mask₁ : ∀ o, K₁.orc 2 = some o → MaskWith (fun i => z.1.2.d.book.place[i]?) o (o + 1)
  maskU : 3 ≤ k → MaskWith (fun i => z.2.book.place[i]?) 0 1

/-- **(γ) The strings' side**, at border k. -/
structure Strings₂ (k : Nat) (z : P₂ × St₂) (y : Strs) : Prop where
  record : FreeAt G₂ coll z y
  shown : ∀ j ∈ pinned (open₂ k), ShownAt F at_ j y
  smp : ∀ j ∈ pinned (open₂ k), hasSmp G₂ (at_ j).1 (at_ j).2 z = true
  noColl : ∀ j ∈ pinned (open₂ k), NoColl F G₂ (at_ j).1 (at_ j).2 z y

/-- **THE SHARED CHAIN's WHOLE PROMISE, FROM THE THREE HEAPS.** -/
theorem on₂_of_parts (k : Nat) (z : P₂ × St₂) (y : Fr₂.E.Str)
    (T : Tests₂ at_ S K₁ a last₁ off₂ k z)
    (harr : ArrOk G₂ at_ [0, 2, 3, 4, 5]) (hreads : ReadsPinned G₂ at_ R [0, 2, 3, 4, 5])
    (Y : Strings₂ F G₂ at_ coll k z (strsOf Fr₂ y)) :
    on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k (z, y) :=
  Or.inr ⟨T.shape, List.all_eq_true.2 fun j hj => Y.smp j hj,
    { record := Y.record, last := T.last, eval := T.eval, placed₁ := T.placed₁
      in₁ := handedIn_of_order K₁.orc z.1.2 T.order₁, order₁ := T.order₁, key := T.key, codes :=
          T.codes, lay := T.lay
      arr := harr, reads := hreads, placed := T.placed
      samples := fun _ _ o _ => sampleIn_of_order T.order o
      rowsIn := fun _ => ⟨openIn_of_order T.order _, openIn_of_order T.order _⟩
      order := T.order, linOk := T.linOk, seatU := T.seatU, seatOmega := T.seatOmega, shown :=
          Y.shown, fits := T.fits
      mask₁ := T.mask₁, maskU := T.maskU },
    Y.noColl⟩

/-- **The way back**: where the statement is unmarked the promise gives the three heaps: they ask no
more than it. -/
theorem parts_of_on₂ (k : Nat) (z : P₂ × St₂) (y : Fr₂.E.Str) (hm : (meaning₂ S K₁ R enc
    rad).unmarked z)
    (h : on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k (z, y)) :
    Tests₂ at_ S K₁ a last₁ off₂ k z ∧ ArrOk G₂ at_ [0, 2, 3, 4, 5] ∧ ReadsPinned G₂ at_ R [0, 2, 3,
        4, 5] ∧
      Strings₂ F G₂ at_ coll k z (strsOf Fr₂ y) := by
  rcases h with hn | ⟨h1, h2, f, h4⟩
  · exact absurd hm hn
  · exact ⟨⟨h1, f.last, f.eval, f.placed₁, f.order₁, f.key, f.codes, f.lay, f.placed, f.order,
      f.linOk, f.seatU, f.seatOmega, f.fits, f.mask₁, f.maskU⟩,
      f.arr, f.reads, ⟨f.record, f.shown, fun j hj => List.all_eq_true.1 h2 j hj, h4⟩⟩

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.on₂_of_parts
#print axioms Johnson.RunOne.KeyRows23.parts_of_on₂
