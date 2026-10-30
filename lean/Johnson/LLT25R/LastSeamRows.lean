-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastSeamRows.lean (each premise and conclusion of the form "∀ a
…, the promise at border 2 → …" stands besides under a letter E of the statement [a
lemma that takes the promise as a named premise, like `tidy_two`, does not]: what holds
beside the promise; at the ledger: the layer on the last chain's own state; the
letter Y of LastSeam.lean is handed through;
mem reads the outer state):
THE ROWS' HALF OF THE SEAM AT THE
LAST CHAIN's OWN TEST (the premise `laid` of `seam_of_core`, LastSeam.lean) IS PAID, AT ins :=
"the seat's door returns, and at what it returns every open row of the record's own group holds of
the words that the witness's tables give", FROM ONE BUNDLE OF PLAIN FACTS ON THE GROUP's MEMBERS
(`cover`).
  `wordsOn_entP`: the words that tables give at a statement, at an oracle message that the statement
    holds at the shape sh and whose table is a typed message's (`entP`), are that message's two
    tables (`tabP`): the inner step of `wordsT_on`, at one message.
  `toMsgT_is`: the tables' files' table of a typed message and K12's files' are one (as in
    Johnson/Flat/Last/RowTwoPays.lean [not in this library]).
  `insOpenAt`: ins. `CoverAt`: the facts: every member of the group under test is named by `mem` as
    one of mine, sits where `seatAt` says, and has that member's shape in the record's statement.
  `memBy`, `GroupSits`, `cover_of_sits`: AT A CLOSED mem (the one of mine at whose seat the record's
    own book lays the number) the cover is: by that book every member of the group under test sits
    at the seat of one of mine and has its shape; no two of mine have one seat.
  `laid_of_cover`: **the half.** By `items_iff_begun` (the rows taken in, behind
    the beginning, are the open rows and the members' sample rows in front), `openSays_agree` (an
    open row reads the members' words alone), `tab_laid` (in a witness in which
    the tuple is laid the table at a member's number is the tuple's message); "in order" and "open
    kinds" are in "tidy", a clause of the book-keeping's test at border 2 (`tidy_two`).
  `seam_of_facts`: **the seam from `CoreFacts` and `CoverAt`, both inside the promise.**
Limits. `CoverAt` and `CoreFacts` are shown at no record. The sample rows' half of `items_iff_begun`
is not spent. Nothing on soundness.
-/
import Johnson.LLT25R.LastSeam
import Johnson.Desc.K12.Law.TupleOn
import Johnson.Desc.Means.ItemsBegun
import Johnson.Desc.Means.ItemsRead
import Johnson.Desc.Sound.TabAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LLT25
open Cb Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Johnson.Pack
open OnBytes.Means H2K.ClaimSays H2K.Pin
open VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.K12.Seat (enterOwn)
open _root_.Desc.K14.Law.Fence (CoreFacts)
open _root_.Run

/-- The words that tables give, at a message whose table is a typed message's. -/
theorem wordsOn_entP (cs : OnBytes.Codes) (S : Statement) (T : ℕ → Bool → ℕ → ℕ → GE) (o : ℕ)
    (sh : OnBytes.OracleShape) (hsh : (S.oracles[o]?).map (·.shape) = some sh)
    (m : (portCode cs sh).J → GE) (hT : T o = entP cs sh m) (part : Part) (i : ℕ) :
    wordsOn S T o part i = tabP cs sh m part i := by
  obtain ⟨x, hx, ex⟩ := Option.map_eq_some_iff.1 hsh
  have hrb : S.rowBits o part = ceilLog2 (sh.rows part) := by
    unfold Statement.rowBits
    rw [hx]
    show ceilLog2 (x.shape.rows part) = _
    rw [ex]
  have hrr : realRows S o part = sh.rows part := by
    unfold realRows
    rw [hx]
    show x.shape.rows part = _
    rw [ex]
  unfold wordsOn
  rw [hrb, hrr, hT]
  cases part with
  | main =>
    rw [(tabP_entP _ _ _ i).1]
    show (if i % 2 ^ k1 _ < sh.mainRows then
        entP _ _ _ false (i % 2 ^ k1 _) (i / 2 ^ k1 _) else 0) =
      entP _ _ _ false (i % 2 ^ k1 _) (i / 2 ^ k1 _)
    split
    · rfl
    · rename_i hr
      show (0 : GE) = (if h : _ ∧ _ then _ else 0)
      rw [dif_neg (fun q => hr q.1)]
  | mask =>
    rw [(tabP_entP _ _ _ i).2]
    show (if i % 2 ^ k2 _ < sh.maskRows then
        entP _ _ _ true (i % 2 ^ k2 _) (i / 2 ^ k2 _) else 0) =
      entP _ _ _ true (i % 2 ^ k2 _) (i / 2 ^ k2 _)
    split
    · rfl
    · rename_i hr
      show (0 : GE) = (if h : _ ∧ _ then _ else 0)
      rw [dif_neg (fun q => hr q.1)]

/-- The tables' files' and K12's files' tables of a typed message are one. -/
theorem toMsgT_is (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (i : Fin l.length)
    (m : ((sigOf cs l).om i).Msg) : toMsgT cs l i m = entP cs (l.get i).1 m := by
  funext mask row place
  cases mask <;> rfl

variable {P S₁ S₂ Cells Tok : Type} {Fr : Frame} (Nn : NumbersS)
  (Mg : MeaningS S₂ (P × S₁) (Wit Cells Tok MsgT)) (Pm : PromMeaning S₂)
  (Oc : P × S₁ → Strs → Prop) (p : P₁₄) (R : List Fmt.DeclaredRound)
  (hand : P × S₁ → Option Handed) (ended : S₂ → Option SharedOut)
  (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : ((P × S₁ × S₂) × S₃) → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (mine : List Mem) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
  (mem : ((P × S₁ × S₂) × S₃) → ℕ → Option Mem)
  (rdM : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (seatAt : ((P × S₁ × S₂) × S₃) → ℕ → Option (ℕ × ℕ))
  (Y : ((P × S₁ × S₂) × S₃) × Fr.E.Str → Prop)

/- what holds beside the promise at border 2: a letter -/
variable {E : ((P × S₁ × S₂) × S₃) × Fr.E.Str → Prop}

/-- **What ins is**: the seat's door returns, and at what it returns every open row of the record's
own group holds of the words that the witness's tables give. -/
def insOpenAt : ((P × S₁ × S₂) × S₃) × Fr.E.Str → Wit Cells Tok MsgT → Prop := fun a w =>
  ∃ t, enterOwn a.1.2 = .ok t ∧ ∀ i, OpenSays OnBytes.Model.Reading.gl t.st t.g i
    (wordsOn t.st (tabAt cs arr (seatAt a.1) t.st w))

/-- **The facts on the group's members**, at one outer record a0, what the door returned and the
group under test. -/
def CoverAt (a0 : (P × S₁ × S₂) × S₃) (t : T12) (G0 : Group) : Prop :=
  ∀ o ∈ G0.members.toList, ∃ x ∈ mine, mem a0 o = some x ∧ seatAt a0 o = some (seatOf x) ∧
    (t.st.oracles[o]?).map (·.shape) = some (x.1.l.get x.2).1

/-- **A closed mem**: the one of mine at whose seat the record's own book lays the number. -/
def memBy (a0 : (P × S₁ × S₂) × S₃) (o : ℕ) : Option Mem :=
  mine.find? fun x => seatAt a0 o == some (seatOf x)

/-- **What is left of the cover at that mem**: by the record's own book every member of the group
under test sits at the seat of one of mine, and has its shape in the record's statement. -/
def GroupSits (a0 : (P × S₁ × S₂) × S₃) (t : T12) (G0 : Group) : Prop :=
  ∀ o ∈ G0.members.toList, ∃ x ∈ mine, seatAt a0 o = some (seatOf x) ∧
    (t.st.oracles[o]?).map (·.shape) = some (x.1.l.get x.2).1

/-- The cover at the closed mem: where no two of mine have one seat. -/
theorem cover_of_sits (hnd : ∀ x ∈ mine, ∀ y ∈ mine, seatOf x = seatOf y → x = y)
    (a0 : (P × S₁ × S₂) × S₃) (t : T12) (G0 : Group) (h : GroupSits mine seatAt a0 t G0) :
    CoverAt mine (memBy mine seatAt) seatAt a0 t G0 := by
  intro o ho
  obtain ⟨x, hx, hs, hsh⟩ := h o ho
  refine ⟨x, hx, ?_, hs, hsh⟩
  unfold memBy
  cases hf : mine.find? fun y => seatAt a0 o == some (seatOf y) with
  | none =>
    have := List.find?_eq_none.1 hf x hx
    rw [hs] at this
    simp at this
  | some y =>
    have hy := List.find?_some hf
    have hym := List.mem_of_find?_eq_some hf
    rw [hs] at hy
    have e : seatOf x = seatOf y := by simpa using hy
    rw [hnd x hx y hym e]

/-- **THE ROWS' HALF.** -/
theorem laid_of_cover
    (hrd : ∀ x m part i, rdM x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (cover : ∀ a t G0, onQ₃ (Fr := Fr) Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      Promised cs G smp mine a.1 (strsOf Fr a.2) → enterOwn a.1.2 = .ok t →
      t.st.groups[t.g]? = some G0 → CoverAt mine mem seatAt a.1 t G0) :
    ∀ a t G0 m, onQ₃ (Fr := Fr) Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      Promised cs G smp mine a.1 (strsOf Fr a.2) → enterOwn a.1.2 = .ok t →
      t.st.groups[t.g]? = some G0 →
      AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
        (_root_.Desc.K14.Law.wordsT cs (mem a.1) rdM m) →
      ∀ w w', LaidBy cs arr mine m w w' →
        insOpenAt (Cells := Cells) (Tok := Tok) (Fr := Fr) cs arr seatAt a w' := by
  intro a t G0 m hon hE hP ht hG hall w w' hl
  have hT : Means.Tidy t.st := by
    obtain rfl : _ = t := Except.ok.inj ht
    exact tidy_two Nn Mg Pm Oc p R hand ended a hon
  refine ⟨t, ht, fun i => ?_⟩
  have h1 := ((items_iff_begun OnBytes.Model.Reading.gl hT.inOrder hT.kinds t.g hG _).1 hall).1 i
  refine (openSays_agree OnBytes.Model.Reading.gl hT.inOrder hG i fun o ho part j => ?_).1 h1
  obtain ⟨x, hx, hm, hs, hsh⟩ := cover a t G0 hon hE hP ht hG o ho
  have e1 : _root_.Desc.K14.Law.wordsT cs (mem a.1) rdM m o part j = rdM x (m x) part j := by
    unfold _root_.Desc.K14.Law.wordsT
    rw [hm]
  rw [e1, hrd]
  exact (wordsOn_entP cs t.st _ o _ hsh (m x)
    ((tab_laid cs arr _ t.st mine m w w' hl x hx o hs hsh).trans (toMsgT_is cs x.1.l x.2 (m x)))
    part j).symm

/-- **THE SEAM AT THE LAST CHAIN's OWN TEST, FROM TWO BUNDLES OF PLAIN FACTS.** -/
theorem seam_of_facts
    (hrd : ∀ x m part i, rdM x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (facts : ∀ a t, onQ₃ Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      Promised cs G smp mine a.1 (strsOf Fr a.2) → enterOwn a.1.2 = .ok t → Y a →
      CoreFacts cs G Fr π no rad smp (mem a.1) (· ∈ mine) t a.2 a.1 (strsOf Fr a.2))
    (cover : ∀ a t G0, onQ₃ (Fr := Fr) Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      Promised cs G smp mine a.1 (strsOf Fr a.2) → enterOwn a.1.2 = .ok t →
      t.st.groups[t.g]? = some G0 → CoverAt mine mem seatAt a.1 t G0) :
    ∀ a t st rest G0 Ly D', onQ₃ Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      Promised cs G smp mine a.1 (strsOf Fr a.2) → enterOwn a.1.2 = .ok t →
      Fixes π t st rest G0 Ly D' → NTuple Fr π no rad rd (t, a.2) st rest G0 Ly D' → Y a →
      candN cs G arr smp Fr mine
        (insOpenAt (Cells := Cells) (Tok := Tok) (Fr := Fr) cs arr seatAt) a :=
  seam_of_core Nn Mg Pm Oc p R hand ended cs G arr smp mine π no rad rd _ mem rdM Y hrd facts
    (laid_of_cover Nn Mg Pm Oc p R hand ended cs G arr smp mine mem rdM seatAt hrd cover)

end LLT25

#print axioms LLT25.wordsOn_entP
#print axioms LLT25.cover_of_sits
#print axioms LLT25.laid_of_cover
#print axioms LLT25.seam_of_facts
