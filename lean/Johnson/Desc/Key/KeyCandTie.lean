-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyCandTie.lean: the key file's table of joints: from a
candidate of the library's list to a pin of the table: the lower half of what a reading must be.
One structure and small theorems.

`Reading.enc` (Johnson/Desc/Msg.lean) is a relation. Members of `LaysReads` are built under stated
premises in KeyFillFamLays.lean (`fam_lays`) and KeyFillSrc.lean (`src_lays`); at other readings
none is shown. Nothing on soundness. (Where this and lean/THEOREM.md differ, the page holds.)





The upper half is KeySealTie.lean's SealReads: the table's list lies inside the library's. The empty
reading passes it. What bars the empty reading lies at the row of a kind that closes a pin: it must
make a member. At SealReads' letters, with one more: shown ("every leaf of the seat's word shows its
symbol").

  LaysReads        what a closing seat asks of the reading G: ofU (a message of the library's as a table
                   of the witness) · sec (a section of the upper half's toU, on the lists) · told · mem
                   (the library's candidate is a member that meets the record's sample).
  cand_gives_pin   a candidate gives the pin at a witness whose table at the seat is ofU of it.
  cand_gives_item  the same as the table's item, at a witness that lays one table as message k and as
                   the pad at k's seat (KeyLetters.LaysSeat).
  cands_give_pins  a tuple of candidates, one for each message of ks, gives KeyPins.PinsAt ks false.
  member_iff_cand  the two halves together pin the reading: a table is a member just if its image is a
                   candidate and it is that candidate written back.
  words_of_laid    what the rows then read at the statement's number of message k: entOf of ofU u.

At silly members, on both sides. Narrow: a reading at which nothing is a member: SealReads passes;
mem fails as soon as the library has a candidate at a shown word. Wide: the radius all leaves, meets
always true: mem passes at any ofU; SealReads.mem fails. So only the pair pins the reading. shown :=
True: at oracles whose tree is not sent the library reads 0, and the zero word is a code word, while
far counts every leaf as parting: mem is false at every reading but the wide one. ofU := one constant
table: sec fails at a list with two members. told dropped: a pin asks that the tree be told.

What is not claimed: who gives the candidates (the closing kind's files); that the laid witness keeps
the items that ride; that there is no collision. Nothing on soundness.

-/
import Johnson.Desc.Key.KeySealTie
import Johnson.Desc.Key.KeyPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes VerifiableInference.Desc

section
variable {Xi A Cells M Smp Rec : Type} (F : FileDescription Xi) (G : Reading A Cells M Smp Rec)

/-- **What a closing seat asks of the reading.** The letters are SealReads'; shown: every leaf of the
seat's word shows its symbol; toU: the upper half's map. -/
structure LaysReads {U D Y Y' : Type} (str : Y' → Strs) (Lst : Y' → U → Prop) (ev : D → U → Y)
    (seedIs : A → D → Y → Prop) (shown : Y' → Prop) (j t : Nat) (toU : M → U) where
  /-- a message of the library's, as a table of the witness (with its pad's places) -/
  ofU : U → M
  /-- a section of toU, on the lists -/
  sec : ∀ y' u, Lst y' u → toU (ofU u) = u
  /-- the tree is told -/
  told : (F.oracleAt j).isSome = true
  /-- the library's candidate is a member of the table's list that meets the record's sample -/
  mem : ∀ (a : A) (y' : Y') o z u ρ y, F.oracleAt j = some o → G.smp a j t = some z →
    seedIs a ρ y → shown y' → Cb.Ood.Cand (Lst y') ev ρ y u → Member F G o j t (str y') z (ofU u)

variable {U D Y Y' : Type} {str : Y' → Strs} {Lst : Y' → U → Prop} {ev : D → U → Y}
  {seedIs : A → D → Y → Prop} {shown : Y' → Prop} {j t : Nat} {toU : M → U}

/-! ### AT THE DOOR: the one place of this file that builds a notion of Johnson/Desc/Msg.lean: a pin, out
of its three parts. -/

/-- **A candidate gives the pin**, at a witness whose table at the seat is the candidate's. -/
theorem cand_gives_pin (H : LaysReads F G str Lst ev seedIs shown j t toU) {a : A} {y' : Y'} {ρ : D}
    {y : Y} {u : U} {w : Wit Cells Unit M} (hs : hasSmp G j t a = true) (hse : seedIs a ρ y)
    (hsh : shown y') (hc : Cb.Ood.Cand (Lst y') ev ρ y u) (hw : msgOf G w j t = H.ofU u) :
    PIN F G j t a (str y') w := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 H.told
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hs
  exact ⟨o, z, ho, hz, hw ▸ H.mem a y' o z u ρ y ho hz hse hsh hc⟩

/-- **The two halves together pin the reading.** -/
theorem member_iff_cand (S : SealReads F G str Lst ev seedIs j t)
    (H : LaysReads F G str Lst ev seedIs shown j t S.toU) {a : A} {y' : Y'} {o : Oracle} {z : Smp}
    {ρ : D} {y : Y} (ho : F.oracleAt j = some o) (hz : G.smp a j t = some z) (hse : seedIs a ρ y)
    (hsh : shown y') (m : M) :
    Member F G o j t (str y') z m ↔
      Cb.Ood.Cand (Lst y') ev ρ y (S.toU m) ∧ H.ofU (S.toU m) = m := by
  constructor
  · intro hm
    have hc : Cb.Ood.Cand (Lst y') ev ρ y (S.toU m) := S.mem a y' o z m ρ y ho hz hse hm
    have hm' := H.mem a y' o z (S.toU m) ρ y ho hz hse hsh hc
    exact ⟨hc, S.inj a y' o z _ _ ho hz hm' hm (H.sec y' _ hc.1)⟩
  · rintro ⟨hc, e⟩
    rw [← e]
    exact H.mem a y' o z (S.toU m) ρ y ho hz hse hsh hc

end

section
variable {Xi P S Cells M Smp Rec : Type} (F : FileDescription Xi) (G : Reading (P × S) Cells M Smp Rec)
  (at_ : Where) (Mg : KMeaning P S (Wit Cells Unit M))

/-- **The same as the table's item**, at a witness that lays one table as message k and as its pad. -/
theorem cand_gives_item {U D Y Y' : Type} {str : Y' → Strs} {Lst : Y' → U → Prop} {ev : D → U → Y}
    {seedIs : P × S → D → Y → Prop} {shown : Y' → Prop} {toU : M → U} {k : Nat} {l : List Nat}
    (H : LaysReads F G str Lst ev seedIs shown (at_ k).1 (at_ k).2 toU) {a : P × S} {y' : Y'} {ρ : D}
    {y : Y} {u : U} {w : Wit Cells Unit M} (hs : hasSmp G (at_ k).1 (at_ k).2 a = true)
    (hse : seedIs a ρ y) (hsh : shown y') (hc : Cb.Ood.Cand (Lst y') ev ρ y u)
    (ha : ArrOk G at_ l) (hi : LayIdem G) (hl : LaysSeat at_ l w) (hk : k ∈ l)
    (hm : w.msg k = H.ofU u) : (KItem.pin k).holds F G at_ Mg a (str y') w :=
  cand_gives_pin F G H hs hse hsh hc ((msgOf_of_laysSeat G at_ l w ha hi hl k hk).trans hm)

/-- **A tuple of candidates gives the pins.** What is asked of each message of ks is gathered in one
proposition Got k: whoever closes the pins shows it message by message, by cand_gives_item. -/
theorem cands_give_pins {ks : List Nat} {a : P × S} {y : Strs} {w : Wit Cells Unit M}
    (h : ∀ k ∈ ks, (KItem.pin k).holds F G at_ Mg a y w) : PinsAt F G at_ Mg ks false a y w := by
  intro i hi
  rcases of_mem_pinItems hi with ⟨k, hk, rfl⟩ | ⟨hc, _⟩
  · exact h k hk
  · cases hc

end

section
variable {GE : Type} [CommRing GE] (ρg : Model.Reading GE) {A Cells M Smp Rec : Type}
  (G : Reading A Cells M Smp Rec) (at_ : Where) (K : KPlan) (R : KRead Cells M)

/-- **What the rows then read** at the statement's number of message k. -/
theorem words_of_laid {l : List Nat} {w : Wit Cells Unit M} {k o : Nat} {m : M} (ha : ArrOk G at_ l)
    (hr : ReadsPinned G at_ R l) (hi : LayIdem G) (hl : LaysSeat at_ l w) (hk : k ∈ l)
    (hm : w.msg k = m) (hn : K.num o = some k) : wordsOf ρg K R w o = entOf ρg R m := by
  rw [wordsOf_num ρg K R w hn, reads_of_laysSeat G at_ R l w ha hr hi hl k hk, hm]

end

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.cand_gives_pin
#print axioms VerifiableInference.Desc.Key.member_iff_cand
#print axioms VerifiableInference.Desc.Key.cand_gives_item
#print axioms VerifiableInference.Desc.Key.cands_give_pins
#print axioms VerifiableInference.Desc.Key.words_of_laid
