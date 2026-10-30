-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ReadRide.lean: THE FORM's HALF AT A SWITCH: WHAT RIDES FOR THE READING
(ReadSeat, Johnson/Prover/Link/ReadSeat.lean) RIDES THROUGH A STAGE. Every turn of a stage touches a
message on one field (its ledger; the mark "spent as a mask"; its sample's rows and pad; at one
number its groups), and the one clause of ReadSeat that reads the statement's messages, the guard
G9, reads of a message how many answers its shape counts and its list of groups alone (shareKey). So
one lemma serves every ride.

Main names (namespace Johnson.Prover.Link).
  shareKey, bind_of_key, sharesOk_of_key   what the guard G9 reads of a message; it reads no more.
  ReadSeat.ride   THE LEMMA: the key kept at the members and the fresh message · no message lost ·
    the tree kept · the places kept.
  key_modify, key_closeLedgers   turns that keep the key.
  ReadSeat.withRows, .begun, .ledgerShut, .bookRead, .fold   THE RIDES: over open rows that are
    added · the beginning of a test · the closing of a ledger · the reading of ANOTHER tree · a fold
    (a message marked as spent, a group added).

By: withRows_oracles (OnBytes/Slice/BlkCalls.lean) · closeLedgers_get, closeLedgers_size
(OnBytes/Slice/BlkProxEarlierMessagesAndGroups.lean).

Limits. ReadSeat is a premise: where it begins is other files'. The ride over a sending is
ReadSeat.sent (Johnson/Prover/Link/ReadPay.lean). The ride over a fold is stated at the statement's
term, written out; the file that names that term is not imported. "mask" is the library's name:
nothing is said of what a mask does.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ReadPay
import OnBytes.Slice.BlkProxEarlierMessagesAndGroups
import Johnson.Desc.First.Base.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc

/-! ## One lemma for every ride -/

/-- What the guard G9 (of Tw.L9.openOne, which readOld runs; Johnson/Top/H0/Tw/L9/Switch.lean) reads
of a message: how many answers its shape counts, and its groups. -/
def shareKey (x : OnBytes.Oracle) : Nat × List Nat := (x.shape.answers, x.groups)

/-- What the guard makes of a message hangs on the key alone. -/
theorem bind_of_key : ∀ (a b : Option OnBytes.Oracle), a.map shareKey = b.map shareKey →
    (a.bind fun x => if x.shape.answers == 0 then none else some x.groups) =
      b.bind fun x => if x.shape.answers == 0 then none else some x.groups
  | none, none, _ => rfl
  | none, some _, e => nomatch e
  | some _, none, e => nomatch e
  | some x, some y, e => by
    have e' := Option.some.inj e
    have ea : x.shape.answers = y.shape.answers := congrArg Prod.fst e'
    have eg : x.groups = y.groups := congrArg Prod.snd e'
    show (if x.shape.answers == 0 then none else some x.groups) =
      if y.shape.answers == 0 then none else some y.groups
    rw [ea, eg]

/-- **The guard G9 reads of a statement the key at the tree's parts alone.** -/
theorem sharesOk_of_key (S S' : Statement) (tr : Tree)
    (h : ∀ o ∈ tr.parts.toList, (S'.oracles[o]?).map shareKey = (S.oracles[o]?).map shareKey) :
    sharesOk S' tr = sharesOk S tr := by
  unfold sharesOk
  rw [List.filterMap_congr fun o ho => bind_of_key _ _ (h o ho)]

/-- **What rides, rides**: where the key is kept at the members and the fresh message, no
message is lost, the tree is kept and the places are kept. -/
theorem ReadSeat.ride {S S' : Statement} {Bk Bk' : TreeBook} {ms : List Nat} {id t : Nat}
    {tr : Tree} (H : ReadSeat S Bk ms id t tr)
    (hk : ∀ o ∈ ms ++ [id], (S'.oracles[o]?).map shareKey = (S.oracles[o]?).map shareKey)
    (hn : S.oracles.size ≤ S'.oracles.size) (ht : Bk'.trees[t]? = Bk.trees[t]?)
    (hp : ∀ (o : Nat) (p : Nat × Nat), Bk.place[o]? = some p → Bk'.place[o]? = some p) :
    ReadSeat S' Bk' ms id t tr where
  inBook := ht.trans H.inBook
  place := fun p h => hp _ _ (H.place p h)
  parts := H.parts
  once := H.once
  shares := by
    rw [sharesOk_of_key S S' tr fun o ho => hk o (by
      rw [H.parts] at ho
      simpa using ho)]
    exact H.shares
  there := fun o ho => Nat.lt_of_lt_of_le (H.there o ho) hn

/-! ## The rides -/

/-- A turn of one message that keeps the key keeps it at every number. -/
theorem key_modify (os : Array OnBytes.Oracle) (a : Nat) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, shareKey (f x) = shareKey x) (o : Nat) :
    ((os.modify a f)[o]?).map shareKey = (os[o]?).map shareKey := by
  rw [Array.getElem?_modify]
  split
  · cases os[o]? with
    | none => rfl
    | some x => exact congrArg some (hf x)
  · rfl

theorem key_closeLedgers (l : List Nat) (S : Statement) (o : Nat) :
    ((closeLedgers S l).oracles[o]?).map shareKey = (S.oracles[o]?).map shareKey := by
  rw [closeLedgers_get]
  cases S.oracles[o]? with
  | none => rfl
  | some x =>
    show some (shareKey (if o ∈ l then shut x else x)) = some (shareKey x)
    split <;> rfl

variable {S : Statement} {Bk : TreeBook} {ms : List Nat} {id t : Nat} {tr : Tree}

/-- Over open rows that are added. -/
theorem ReadSeat.withRows (H : ReadSeat S Bk ms id t tr) (g : Nat) (l : List Row) :
    ReadSeat (OnBytes.Slice.withRows S g l) Bk ms id t tr :=
  H.ride (fun o _ => by rw [(withRows_oracles g l S).1])
    (Nat.le_of_eq (congrArg Array.size (withRows_oracles g l S).1).symm) rfl fun _ _ h => h

/-- Over the beginning of a test. -/
theorem ReadSeat.begun (H : ReadSeat S Bk ms id t tr) (g : Nat) (G : Group) :
    ReadSeat (OnBytes.Slice.begun S g G) Bk ms id t tr :=
  H.ride (fun o _ => key_closeLedgers G.members.toList S o)
    (Nat.le_of_eq (closeLedgers_size G.members.toList S).symm) rfl fun _ _ h => h

/-- over the closing of one ledger -/
theorem ReadSeat.ledgerShut (H : ReadSeat S Bk ms id t tr) (T : SwitchTarget) (g : Nat) :
    ReadSeat (OnBytes.Slice.ledgerShut S T g) Bk ms id t tr := by
  unfold OnBytes.Slice.ledgerShut
  split
  · exact H.ride (fun o _ => key_closeLedgers [g] S o)
      (Nat.le_of_eq (closeLedgers_size [g] S).symm) rfl fun _ _ h => h
  · exact H

/-- Over the reading of another tree. -/
theorem ReadSeat.bookRead (H : ReadSeat S Bk ms id t tr) (t' : Nat) (h : t' ≠ t) :
    ReadSeat S (Johnson.Prover.Link.bookRead Bk t') ms id t tr :=
  H.ride (fun _ _ => rfl) (Nat.le_refl _)
    (by
      show (Bk.trees.modify t' _)[t]? = _
      rw [Array.getElem?_modify, if_neg h])
    fun _ _ h => h

/-- OVER THE FOLD: a message is marked as spent, and a group is added. The statement is written out:
at a name for the marking a caller closes by unfolding. -/
theorem ReadSeat.fold (H : ReadSeat S Bk ms id t tr) (id' c z : Nat) :
    ReadSeat (Ground.withGroup
      { S with oracles := S.oracles.modify id' fun x => { x with spentAsMask := true } } c z)
      Bk ms id t tr :=
  H.ride (fun o _ => key_modify S.oracles id' (fun x => { x with spentAsMask := true })
      (fun _ => rfl) o)
    (Nat.le_of_eq Array.size_modify.symm) rfl fun _ _ h => h

end Johnson.Prover.Link
