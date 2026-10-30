-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastRowTwo.lean: ROW 2 OF THE LAST CHAIN's TABLE: THE TWO FIELDS
`prom` AND `pins` OF `RowTwoAtTable` (Johnson/Flat/Last/LastOnePage.lean) AT THE TABLES'
FILLINGS BY SIGNATURE: the table's promise at border 2 gives the promise in front of the proximity
test (`Promised`: each of mine has its sample, is shown, has no collision); and "each of mine is
pinned" (`Pinned`) is what the table's three items pinV, pinI, pinO say there. General in the
records' types.

The letters. Mg := `tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT M₁) (meaningSigS cs G arr
smp₂ ms₂ decT₂ MS)`, Pm := `promSigS cs G smp₂ ms₂ stOf bookOf P₀`, Oc := `ocEnd get N₁ (meaningSig
…) links ps`, N := `tiedNumbers N₁ Ns` (Johnson/Desc/Sound/TieEnd.lean, BordersFill.lean,
BordersSharedFill.lean). ms₁, ms₂: THE FIRST AND THE SHARED TABLE's OWN LISTS OF MEMBERS: two
letters, as the tables' joint filling has them (Johnson/Desc/Sound/JointFilling.lean).
smp: the sample as the last chain's law reads it off
the WHOLE record; smp₁, smp₂: as the first and the shared chain's tables read it off theirs.
  `cfAt_of_smp`, `pinAt_of_smp`: a member's "no collision" and its pin read the record through its
    sample alone.
  `MineSits`: WHAT IS ASKED OF mine: each of mine sits at W's or the index masks' seat and is of
    ms₁, or at Omega's and is of ms₂, and its sample off the whole record is the one that the table
    of that seat reads; whoever of a table's list sits at one of its seats is of mine; at each of
    the three somebody sits; Omega's seat is neither of the other two.
  `prom_sig`: **the field prom**: from MineSits and a test on the first table: W's and the index
    masks' seats are among the sampled ones at its last border.
  `pins_sig`: **the field pins**: from MineSits.
Every "there is": in MineSits: the member that sits at a seat: the plan's.
Limits. MineSits is shown at no plan: its clauses on seats are tests on the plan; its three
equations of samples are the make of smp. Nothing on soundness.
-/
import Johnson.Flat.Last.LastOnePage
import Johnson.Desc.Sound.TieEnd
import Johnson.Desc.Sound.BordersSharedFill
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LLT25
open OnBytes OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers openSets sampledIn start)

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {A A' Cells Tok : Type}
  (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (smp' : A' → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- "No collision" reads the record through the member's sample alone. -/
theorem cfAt_of_smp (x : Mem) (a : A) (a' : A') (y : Strs) (e : smp a x.1 x.2 = smp' a' x.1 x.2)
    (h : CfAt G cs x.1.l x.1.seat (fun z => smp' z x.1) x.2 a' y) :
    CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 a y := by
  obtain ⟨z, hz, h'⟩ := h
  exact ⟨z, e.trans hz, h'⟩

/-- The pin reads the record through the member's sample alone. -/
theorem pinAt_of_smp (x : Mem) (a : A) (a' : A') (y : Strs) (w : Wit Cells Tok MsgT)
    (e : smp a x.1 x.2 = smp' a' x.1 x.2)
    (h : PinAt G cs x.1.l x.1.seat (fun z => smp' z x.1) arr x.2 a' y w) :
    PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w := by
  obtain ⟨z, hz, h'⟩ := h
  exact ⟨z, e.trans hz, h'⟩

end

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {P S₁ S₂ S₃ P₀ Cells Tok : Type}
  (arr : ℕ → ℕ → ℕ) {Fr : Frame}
  (smp : ((P × S₁ × S₂) × S₃) → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (smp₂ : S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms₁ ms₂ mine : List Mem) (get : P × S₁ → P₀ × First.S) (N₁ : Numbers) (Ns : NumbersS)

/-- **What is asked of mine.** -/
structure MineSits : Prop where
  /-- each of mine is a member of the list of the table at whose seat it sits (W's and the index
  masks': the first table's ms₁; Omega's: the shared table's ms₂), and its sample off the whole
  record is the one that that table reads -/
  each : ∀ x ∈ mine,
    (x ∈ ms₁ ∧ SitsAt x N₁.w.1 N₁.w.2 ∧
        ∀ a, smp a x.1 x.2 = smp₁ (get (a.1.1, a.1.2.1)) x.1 x.2) ∨
      (x ∈ ms₁ ∧ SitsAt x N₁.index.1 N₁.index.2 ∧
        ∀ a, smp a x.1 x.2 = smp₁ (get (a.1.1, a.1.2.1)) x.1 x.2) ∨
      (x ∈ ms₂ ∧ SitsAt x (Ns.tenant .oOmega).1 (Ns.tenant .oOmega).2 ∧
        ∀ a, smp a x.1 x.2 = smp₂ a.1.2.2 x.1 x.2)
  /-- whoever of a table's list sits at one of its seats is of mine -/
  allW : ∀ x ∈ ms₁, SitsAt x N₁.w.1 N₁.w.2 → x ∈ mine
  allI : ∀ x ∈ ms₁, SitsAt x N₁.index.1 N₁.index.2 → x ∈ mine
  allO : ∀ x ∈ ms₂, SitsAt x (Ns.tenant .oOmega).1 (Ns.tenant .oOmega).2 → x ∈ mine
  /-- at each of the three somebody sits -/
  someW : ∃ x ∈ ms₁, SitsAt x N₁.w.1 N₁.w.2
  someI : ∃ x ∈ ms₁, SitsAt x N₁.index.1 N₁.index.2
  someO : ∃ x ∈ ms₂, SitsAt x (Ns.tenant .oOmega).1 (Ns.tenant .oOmega).2
  /-- Omega's seat is neither W's nor the index masks' -/
  apartWO : N₁.w ≠ Ns.tenant .oOmega
  apartIO : N₁.index ≠ Ns.tenant .oOmega

variable {cs smp smp₁ smp₂ ms₁ ms₂ mine get N₁ Ns}

theorem seat_eq {x : Mem} {u v : ℕ × ℕ} (h : SitsAt x u.1 u.2) (h' : SitsAt x v.1 v.2) : u = v :=
  (show u = (u.1, u.2) from rfl).trans ((h.symm.trans h').trans rfl)

/-- One of mine at W's or the index masks' seat has the first table's sample. -/
theorem MineSits.first (H : MineSits cs smp smp₁ smp₂ ms₁ ms₂ mine get N₁ Ns) {x : Mem}
    (hx : x ∈ mine)
    (hs : SitsAt x N₁.w.1 N₁.w.2 ∨ SitsAt x N₁.index.1 N₁.index.2) :
    ∀ a, smp a x.1 x.2 = smp₁ (get (a.1.1, a.1.2.1)) x.1 x.2 := by
  rcases H.each x hx with ⟨-, -, e⟩ | ⟨-, -, e⟩ | ⟨-, hO, -⟩
  · exact e
  · exact e
  · rcases hs with hs | hs
    · exact absurd (seat_eq hs hO) H.apartWO
    · exact absurd (seat_eq hs hO) H.apartIO

/-- One of mine at Omega's seat has the shared table's sample. -/
theorem MineSits.shared (H : MineSits cs smp smp₁ smp₂ ms₁ ms₂ mine get N₁ Ns) {x : Mem}
    (hx : x ∈ mine)
    (hs : SitsAt x (Ns.tenant .oOmega).1 (Ns.tenant .oOmega).2) :
    ∀ a, smp a x.1 x.2 = smp₂ a.1.2.2 x.1 x.2 := by
  rcases H.each x hx with ⟨-, hW, -⟩ | ⟨-, hI, -⟩ | ⟨-, -, e⟩
  · exact absurd (seat_eq hW hs) H.apartWO
  · exact absurd (seat_eq hI hs) H.apartIO
  · exact e

variable (decT : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → S₂ → Option Cells)
  (M₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS S₂ (P × S₁) (Wit Cells Tok MsgT))
  (ML : MeaningL S₃ (Wit Cells Tok MsgT)) (stOf : S₂ → OnBytes.Statement)
  (bookOf : S₂ → OnBytes.TreeBook) (Pm₀ : PromMeaning S₂) (PLm : PromMeaningL S₂ S₃ (P × S₁))
  (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)

/-- **The field prom of row 2, at the fillings by signature.** -/
theorem prom_sig (H : MineSits cs smp smp₁ smp₂ ms₁ ms₂ mine get N₁ Ns)
    (hW : N₁.w ∈ sampledIn N₁ ((openSets links ps (start links))[ps.length]?.getD []))
    (hI : N₁.index ∈ sampledIn N₁ ((openSets links ps (start links))[ps.length]?.getD []))
    (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str)
    (h : onQ₃ (tiedNumbers N₁ Ns)
      (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT M₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
      (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) PLm
      (ocEnd get N₁ (meaningSig cs G arr smp₁ ms₁ decT M₁) links ps) 2 a) :
    Promised cs G smp mine a.1 (strsOf Fr a.2) := by
  intro x hx
  obtain ⟨hOc, hun, hO, -, -⟩ := h
  have hs : ∀ u ∈ sampledIn N₁ ((openSets links ps (start links))[ps.length]?.getD []),
      shownJT cs G ms₁ u.1 u.2 (strsOf Fr a.2) ∧
        noCollJT cs G smp₁ ms₁ u.1 u.2 (get (a.1.1.1, a.1.1.2.1)) (strsOf Fr a.2) := by
    rcases hOc.2 with h' | h'
    · exact absurd hun h'
    · exact h'.2.2.1
  rcases H.each x hx with ⟨hm, h1, e⟩ | ⟨hm, h1, e⟩ | ⟨hm, h1, e⟩
  · exact cfAt_of_smp cs G smp smp₁ x a.1 _ _ (e a.1) ((hs _ hW).2 x hm h1)
  · exact cfAt_of_smp cs G smp smp₁ x a.1 _ _ (e a.1) ((hs _ hI).2 x hm h1)
  · exact cfAt_of_smp cs G smp smp₂ x a.1 _ _ (e a.1) ((hO (by decide)).2 x hm h1)

/-- **The field pins of row 2, at the fillings by signature.** -/
theorem pins_sig (H : MineSits cs smp smp₁ smp₂ ms₁ ms₂ mine get N₁ Ns)
    (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (hP : Pinned cs G arr smp mine a.1 (strsOf Fr a.2) w) :
    meansQ₃ (tiedNumbers N₁ Ns)
        (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT M₁)
          (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML .pinV a w ∧
      meansQ₃ (tiedNumbers N₁ Ns)
        (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT M₁)
          (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML .pinI a w ∧
      meansQ₃ (tiedNumbers N₁ Ns)
        (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT M₁)
          (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML .pinO a w :=
  ⟨⟨H.someW, fun x hm hs => pinAt_of_smp cs G arr smp₁ smp x _ a.1 _ w
      (H.first (H.allW x hm hs) (Or.inl hs) a.1).symm (hP x (H.allW x hm hs))⟩,
    ⟨H.someI, fun x hm hs => pinAt_of_smp cs G arr smp₁ smp x _ a.1 _ w
      (H.first (H.allI x hm hs) (Or.inr hs) a.1).symm (hP x (H.allI x hm hs))⟩,
    ⟨H.someO, fun x hm hs => pinAt_of_smp cs G arr smp₂ smp x _ a.1 _ w
      (H.shared (H.allO x hm hs) hs a.1).symm (hP x (H.allO x hm hs))⟩⟩

end

end LLT25

#print axioms LLT25.cfAt_of_smp
#print axioms LLT25.pinAt_of_smp
#print axioms LLT25.prom_sig
#print axioms LLT25.pins_sig
