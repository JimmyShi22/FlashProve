-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyOneReading.lean: ONE READING OF THE KEY FILE's ORACLES, SEEN FROM THE THREE CHAINS' RECORDS: so that the premises Agree₁ | Agree of the two seams' lemmas (KeySeam1.lean · KeySeams23.lean) have a member, whatever the base. Msg.lean's letters enc (a relation) · rad · meets take the seat (j, t), and the three fields' types of Base and of BaseSt follow. Both bases have the letter lay, one for the three chains. The first chain's state is FirstState. Agree's clause recOf is met: the record is read off the INSTANCE; agree₁_of_base is in KeySeam1.lean. A SECOND MEMBER, BaseSt: A MESSAGE's SAMPLE IS READ OFF THE STATEMENT THAT THE CHAIN's OWN RECORD HOLDS (the last chain: its own, which begins as the first chain's last; Omega's, until it is taken over, off the border's copy of the shared chain's): so a test that runs on the own statement and a pin that reads the reading speak of one sample; h₂ h₃ meet Agree where the description's start is the last chain's own: agree_of_baseSt. THE READING GOES BY THE MESSAGE's NUMBER OUTRIGHT: Reading.arr says which of the table's messages sits at tenant t of tree j (ArrOk ties it to at_), the chain's plan says its number in the chain's statement: NO BOOK, NO OFFSET, NO t₁ IN A READING (a reading that sought the message at a seat in the book could, at a made-up book with a twin place, read another message's sample). A SAMPLE IS READ OFF THE MESSAGE's OWN RECORD IN THE STATEMENT, BY ITS NUMBER (sm; smAt): a sample row names its message by number, so whoever fills sm from the row's coefficients needs it.
  Base           what a code, a sample and the stored table's record give, ONCE: arr · enc · rad · meets · decT · the record off the INSTANCE · a message's sample off THE STATE OF THE CHAIN THAT SENT ITS TREE (smp₁ | smp₂ | smp₃) · t₁ t₂: how many trees the
                 first | the shared chain sends
  g₁ | g₂ | g₃   the reading at the first | shared | last chain's record: a tree below t₁ is read in the first chain's last state, one below t₁ + t₂ in the shared chain's, a later one in the last chain's own
  agree_of_base   PROVED: g₂ g₃ meet Agree, at every start, WHERE THE MESSAGES WHOSE PIN IS OPEN AT THE SEAM LIE IN TREES OF THE CHAINS IN FRONT ((at_ k).1 < t₁ + t₂) (agree₁_of_base: g₁ g₂ meet Agree₁: in KeySeam1.lean)
What is not claimed. THAT THE READINGS WHICH THE BLOCKS' LAWS AND THE RULE's PREMISES WILL USE ARE g₁ | g₂ | g₃ OF ONE Base: that is to be so made where they are filled. That any Base is the library's (code, radius, sample, decoding): all its fields are letters still. (Where
this and lean/THEOREM.md differ, the page holds.) That at the key file's description I and V lie in trees below t₁ and Omega in one below t₁ + t₂: by the plan's book (by a look at it: chain 1 sends 6 trees; Omega's is
the shared chain's second): not held here. Nothing on soundness.

-/
import Johnson.RunOne.KeySeam2On

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)

structure Base (Cells M Smp Rec : Type) where
  arr : Nat → Nat → Nat
  lay : Nat → Nat → M → M → M
  enc : VerifiableInference.Desc.Oracle → Nat → Nat → M → (Nat → Option Sym) → Prop
  rad : VerifiableInference.Desc.Oracle → Nat → Nat → Nat
  meets : VerifiableInference.Desc.Oracle → Nat → Nat → M → Smp → Prop
  decT : (Nat → Option (Nat × List UInt64)) → Rec → Option Cells
  recOf : Xi → Option Rec
  smp₁ : FirstState → Nat → Nat → Option Smp
  smp₂ : St₂ → Nat → Nat → Option Smp
  smp₃ : St₃ → Nat → Nat → Option Smp
  t₁ : Nat
  t₂ : Nat

variable {Cells M Smp Rec : Type} (B : Base Cells M Smp Rec)

def Base.g₁ : Reading (Xi × FirstState) Cells M Smp Rec :=
  { arr := B.arr, lay := B.lay, enc := B.enc, rad := B.rad, meets := B.meets, decT := B.decT, recOf := fun a => B.recOf a.1, smp := fun a j t => B.smp₁ a.2 j t }

def Base.g₂ : Reading (P₂ × St₂) Cells M Smp Rec :=
  { arr := B.arr, lay := B.lay, enc := B.enc, rad := B.rad, meets := B.meets, decT := B.decT, recOf := fun a => B.recOf a.1.1
    smp := fun a j t => if j < B.t₁ then B.smp₁ a.1.2 j t else B.smp₂ a.2 j t }

def Base.g₃ : Reading (P₃ × St₃) Cells M Smp Rec :=
  { arr := B.arr, lay := B.lay, enc := B.enc, rad := B.rad, meets := B.meets, decT := B.decT, recOf := fun a => B.recOf a.1.1
    smp := fun a j t => if j < B.t₁ then B.smp₁ a.1.2.1 j t else if j < B.t₁ + B.t₂ then B.smp₂ a.1.2.2 j t else B.smp₃ a.2 j t }

theorem agree_of_base (at_ : Where) (start : Xi → FirstState → St₂ → Except String St₃) (h : ∀ k ∈ pinned end₂, (at_ k).1 < B.t₁ + B.t₂) : Agree B.g₂ B.g₃ at_ start :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun x s₁ s₂ s₃ _ k hk => by
    simp only [Base.g₂, Base.g₃, if_pos (h k hk)], fun _ _ _ _ _ => rfl⟩

/-! ## A second member: each chain's own record is read -/

/-- The shared chain's plan's numbers (they hang on no shape). -/
def orc₂ (k : Nat) : Option Nat := if k == 3 then some 0 else if k == 4 then some 2 else if k == 5 then some 3 else none

theorem orc₂_eq (S : LinShape) : (plan₂ S).orc = orc₂ := rfl

structure BaseSt (Cells M Smp Rec : Type) where
  arr : Nat → Nat → Nat
  lay : Nat → Nat → M → M → M
  enc : VerifiableInference.Desc.Oracle → Nat → Nat → M → (Nat → Option Sym) → Prop
  rad : VerifiableInference.Desc.Oracle → Nat → Nat → Nat
  meets : VerifiableInference.Desc.Oracle → Nat → Nat → M → Smp → Prop
  decT : (Nat → Option (Nat × List UInt64)) → Rec → Option Cells
  recOf : Xi → Option Rec
  /-- the sample that a message's own record in a statement holds, at the statement's codes and the message's number there -/
  sm : Codes → Nat → OnBytes.Oracle → Option Smp
  /-- the first chain's plan's numbers: under which number its statement holds the table's message k -/
  orc₁ : Nat → Option Nat

variable (T : BaseSt Cells M Smp Rec)

/-- The sample of a statement's message number o. -/
def BaseSt.smAt (St : Statement) (o : Nat) : Option Smp := (St.oracles[o]?).bind (T.sm St.codes o)

/-- The letter sm does not read a message's ledger of mask entries (which blocks without a draw turn). FOR THE PREMISE ON THE READING IN THE FIRST CHAIN's FILES (ReadsL, Johnson/RunOne/KeyCaller.lean). SPENT BY NO THEOREM HERE. -/
def BaseSt.SmReads : Prop := ∀ (c : Codes) (o : Nat) (x : OnBytes.Oracle) L, T.sm c o { x with ledger := L } = T.sm c o x

def BaseSt.h₁ : Reading (Xi × FirstState) Cells M Smp Rec :=
  { arr := T.arr, lay := T.lay, enc := T.enc, rad := T.rad, meets := T.meets, decT := T.decT, recOf := fun a => T.recOf a.1
    smp := fun a j t => (T.orc₁ (T.arr j t)).bind (T.smAt a.2.d.st) }

/-- The shared chain's own statement holds nothing of the first chain's: the table's messages 0 · 1 · 2 are read in what was handed; its own (3 · 4 · 5) at its plan's numerals. -/
def BaseSt.h₂ : Reading (P₂ × St₂) Cells M Smp Rec :=
  { arr := T.arr, lay := T.lay, enc := T.enc, rad := T.rad, meets := T.meets, decT := T.decT, recOf := fun a => T.recOf a.1.1
    smp := fun a j t => if T.arr j t < 3 then (T.orc₁ (T.arr j t)).bind (T.smAt a.1.2.d.st) else (orc₂ (T.arr j t)).bind (T.smAt a.2.st) }

/-- THE LAST CHAIN READS ITS OWN RECORD ALONE: its statement at the first chain's plan's numbers; Omega (the table's message 4): while the border lies in the border's copy of the shared statement, at the shared plan's numeral; behind it in the own statement at the
own count (as «srow 4» does: KeyRows23At.lean). -/
def BaseSt.h₃ : Reading (P₃ × St₃) Cells M Smp Rec :=
  { arr := T.arr, lay := T.lay, enc := T.enc, rad := T.rad, meets := T.meets, decT := T.decT, recOf := fun a => T.recOf a.1.1
    smp := fun a j t => if T.arr j t < 3 then (T.orc₁ (T.arr j t)).bind (T.smAt a.2.st) else
      match a.2.loc.border with
      | some b => (orc₂ (T.arr j t)).bind (T.smAt b.shared.st)
      | none => if T.arr j t == 4 then T.smAt a.2.st (nOwn a.2) else none }

theorem agree_of_baseSt (at_ : Where) (codes : Codes) (S : LinShape) (hm : S.masksAhead = true) (start : Xi → FirstState → St₂ → Except String St₃) (hst : Starts S codes start) :
    Agree T.h₂ T.h₃ at_ start :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun x s₁ s₂ s₃ hs k _ => by
    obtain ⟨o, l, -, ⟨h1, -, -, -⟩, he⟩ := hst x s₁ s₂ s₃ hs
    obtain ⟨e1, -, -, -, -, f, -, eb⟩ := start₃_plain codes S _ _ _ _ _ _ _ o s₃ he
    simp only [BaseSt.h₂, BaseSt.h₃, eb]
    by_cases hj : T.arr (at_ k).1 (at_ k).2 < 3
    · simp only [if_pos hj, e1]
      rfl
    · simp only [if_neg hj, h1], fun _ _ _ _ _ => rfl⟩

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.agree_of_baseSt
#print axioms Johnson.RunOne.KeyRows23.agree_of_base
