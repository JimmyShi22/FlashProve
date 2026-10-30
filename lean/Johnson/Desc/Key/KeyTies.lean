-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- DEFINITIONS AND THREE SMALL LAWS.
/-
One file of the set of files on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyTies.lean: the table of joints of the key file: two ties on the letters that are no Bool on a state, general in the chain: they stand in a promise's last letter («free»), beside the clause on the stored table.
  ArrOk G at_ l            for every k of l: the seat at_ k is message k's: G.arr (at_ k).1 (at_ k).2 = k: so that PIN k pins the table msgOf G w (at_ k) = G.lay … (w.msg k) (w.pad …) of message k (it is not w.msg k bare). Without it: at arr := 0 all pins pin message 0's table.
  ReadsPinned G at_ R l    for every k of l: the table that the rows and named claims read (KRead.of) is the table that PIN k pins: R.of w k = msgOf G w (at_ k).1 (at_ k).2. Without it: what is pinned and what is read are two.
  Placed orc place off at_ l   for every k of l: the statement's message number orc k lies, by the chain's own book (place o: its tree, in the sending chain's own numbers, and its place among that tree's tenants), where at_ k says: at_ k = (off tree, tenant). off: from a tree's number in the
                           book to its number through the file (the first chain: the same number). Without it: a proximity test opens the trees that the book names, while PIN reads the committed word at at_ k: nothing ties the two.
  ArrOk.mono | Placed.mono | Placed.congr   fewer numbers; a book that places alike
No Mathlib. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyBorders
import Johnson.Desc.Key.KeyWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

/-- **The seat at_ k is message k's.** -/
def ArrOk {A Cells M Smp Rec : Type} (G : Reading A Cells M Smp Rec) (at_ : Where) (l : List Nat) : Prop := ∀ k ∈ l, G.arr (at_ k).1 (at_ k).2 = k

/-- **What the rows read is what PIN pins.** -/
def ReadsPinned {A Cells M Smp Rec : Type} (G : Reading A Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (l : List Nat) : Prop :=
  ∀ (w : Wit Cells Unit M), ∀ k ∈ l, R.of w k = msgOf G w (at_ k).1 (at_ k).2

/-- **Every leaf of message k's seat shows its symbol.** (MsgSig.ShownAt, Johnson/Desc/Sound/MsgSig.lean, with the tree's told log-length.) WHY IT STANDS IN THE PROMISE AT EVERY OPEN PIN (by a reading of that file and Johnson/Desc/Msg.lean): Msg.far counts a leaf that shows nothing as parting, the library's word reads it as 0, and the zero word is a code word:
without «shown» the arrow from the library's candidate to Member fails at K12's rows. EARNED at the sending of the tree (shownOfData, Johnson/Desc/Sound/ShownOfData.lean: a fact of the piece); it rides wherever the word at the seat stays. -/
def ShownAt {XI : Type} (F : FileDescription XI) (at_ : Where) (k : Nat) (y : Strs) : Prop :=
  ∀ o, F.oracleAt (at_ k).1 = some o → ∀ x, x < 2 ^ o.logLength → (wordOf F y (at_ k).1 (at_ k).2 x).isSome = true

theorem shownAt_ride {XI : Type} (F : FileDescription XI) (at_ : Where) (k : Nat) (y y' : Strs) (hw : wordOf F y' (at_ k).1 (at_ k).2 = wordOf F y (at_ k).1 (at_ k).2) (h : ShownAt F at_ k y) : ShownAt F at_ k y' :=
  fun o ho x hx => by rw [hw]; exact h o ho x hx

/-- **Message r lies in message o's tree, the next part.** BY THE BOOK's OWN INDEX, not through at_ (K12's promise FirstOpens reads the mask's place in the book, which Placed, on the pinned members alone, does not fence. EARNED at the sending: recvP lays message n0 + i at (the book's next tree + lay.tree i, lay.part i).) -/
def MaskWith (place : Nat → Option (Nat × Nat)) (o r : Nat) : Prop := ∃ q p, place o = some (q, p) ∧ place r = some (q, p + 1)

/-- **The book places message k where at_ k says.** -/
def Placed (orc : Nat → Option Nat) (place : Nat → Option (Nat × Nat)) (off : Nat → Nat) (at_ : Where) (l : List Nat) : Prop :=
  ∀ k ∈ l, ∃ o t, orc k = some o ∧ place o = some t ∧ at_ k = (off t.1, t.2)

theorem ArrOk.mono {A Cells M Smp Rec : Type} {G : Reading A Cells M Smp Rec} {at_ : Where} {l l' : List Nat} (h : ArrOk G at_ l) (hs : ∀ k ∈ l', k ∈ l) : ArrOk G at_ l' :=
  fun k hk => h k (hs k hk)

theorem Placed.mono {orc : Nat → Option Nat} {place : Nat → Option (Nat × Nat)} {off : Nat → Nat} {at_ : Where} {l l' : List Nat} (h : Placed orc place off at_ l) (hs : ∀ k ∈ l', k ∈ l) :
    Placed orc place off at_ l' := fun k hk => h k (hs k hk)

theorem Placed.congr {orc : Nat → Option Nat} {place place' : Nat → Option (Nat × Nat)} {off : Nat → Nat} {at_ : Where} {l : List Nat} (h : Placed orc place off at_ l) (he : ∀ o, place' o = place o) :
    Placed orc place' off at_ l := fun k hk => by
  obtain ⟨o, t, h1, h2, h3⟩ := h k hk
  exact ⟨o, t, h1, (he o).trans h2, h3⟩

end VerifiableInference.Desc.Key
