-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/EqRestOf.lean: WHAT IS LEFT OF THE TIE t3 OF A LINK's THIRD PIECE BEHIND
THE PIECE (`EqRest`, TieThreeFront.lean: six plain sentences on the verifier's state), IN THE
PREMISE's VERY FORM AT THE TABLE's OWN CONDITION (`onTR`): FIVE OF THE SIX PAID, from another
file's
list of facts on reached states (`FoldFacts`, Johnson/Desc/First/FoldFacts.lean) at the condition's
own second conjunct, and from the promise's own test `bookAt`. ONE STAYS: "member". Theorems.

What is said.
  `bookAt_of_onQ`: the promise's test on where the book stands, at an unmarked state.
  `eqRest_of_facts`: **EqRest at every state that meets the condition at border k**:
    order   := the list's "tidy" (the four tests say yes exactly where the statement is tidy:
               tidy4B_iff; Tidy holds InOrder) · the number of oracle messages is at most the
               listed shapes' number (the second clause of "K12.msgShapes"), which is at most N (hN)
    codes   := the list's "codes", where the list's codes are the composed meaning's (hcs)
    shapes  := the list's "msgShapes" (msgShape_at), at M := d.M
    numbers := the list's "bookInOrder" (numbers_of_book0), where the first tree's number is 0 (hft)
    places  := the promise's bookAt (as many places as oracle messages) and the list's "bookFits"
               (every message stands in a tree that is there: bookFitsB_iff)
    member  := THE ONE PREMISE ON STATES.

Limits. PREMISES: FF itself · closed: hcs · hft · hN · **member: at
the seat of a message on which the group's last row has a weight other than 0 sits a member of ms
with the listed shape: asked only inside the condition: SHOWN AT NO STATE: NOBODY's.** Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.TieThreeRows
import Johnson.Desc.First.FoldFacts
import Johnson.Desc.K12.Door.DoorGives
import Johnson.Desc.Sound.BookTestsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers FoldFacts FoldData bookAt)

/-- **The test on where the book stands, out of the promise.** -/
theorem bookAt_of_onQ {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × S) (k : ℕ) (a : A × Fr.E.Str)
    (h : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) :
    bookAt N ps[k]? (get a.1).2 = true := by
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · have e := h'.1
    simp only [Bool.and_eq_true] at e
    exact e.2

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Frame}
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "onK" => onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz

/-- **EqRest, IN THE PREMISE's VERY FORM: FIVE PAID, "member" LEFT.** -/
theorem eqRest_of_facts {d : FoldData} {reqW : P → Array UInt32}
    (FF : FoldFacts Rz (fun a : S × F.E.Str => (z, a.1)) d reqW links pl) (N : ℕ)
    (hcs : d.sent.codes = 𝔇.cs) (hft : d.ft = 0) (hN : d.M.length ≤ N)
    (member : ∀ b, onK k b → ∀ G row, b.1.st.groups[𝔇.N.groupAt m]? = some G →
      G.rows.back? = some row → ∀ o part J, Reading.gl.val (row.coefficient o part J) ≠ 0 →
      ∀ q, b.1.book.place[o]? = some q →
      ∃ y, (𝔇.ms.find? fun y => decide (seatOf y = q)) = some y ∧
        d.M[o]? = some (y.1.l.get y.2).1) :
    ∀ b, onK k b → EqRest 𝔇.cs 𝔇.ms d.M (𝔇.N.groupAt m) N b.1 := by
  intro b hb
  have hf : b.1.failed = none := Classical.not_not.1 hb.1.2
  have hsh : K12.Door.msgShapesB d.M b.1.st = true := FF.msgShapes k b hb.2 hf
  have hbk : K12.Door.bookInOrderB d.ft b.1.book b.1.roots = true := FF.bookInOrder k b hb.2 hf
  rw [hft] at hbk
  have hfit : Book.BookFits b.1.book := (bookFitsB_iff b.1.book).1 (FF.bookFits k b hb.2 hf)
  have hat := bookAt_of_onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) k b hb.1.1 hf
  unfold bookAt at hat
  simp only [Bool.and_eq_true, beq_iff_eq] at hat
  have hsz : b.1.book.place.size = b.1.st.oracles.size := hat.1.2
  have hle : b.1.st.oracles.size ≤ d.M.length := by
    unfold K12.Door.msgShapesB at hsh
    rw [Bool.and_eq_true] at hsh
    exact of_decide_eq_true hsh.2
  exact
    { order := ⟨(OnBytes.Means.tidy4B_iff.1 (FF.tidy k b hb.2 hf)).inOrder, Nat.le_trans hle hN⟩
      codes := (FF.codes k b hb.2 hf).trans hcs
      shapes := fun o ho => K12.Door.msgShape_at hsh o ho
      numbers := fun t T hT => K12.Door.numbers_of_book0 hbk t T hT
      places := fun o ho => by
        have ho' : o < b.1.book.place.size := by rw [hsz]; exact ho
        have hq : b.1.book.place[o]? = some b.1.book.place[o] := Array.getElem?_eq_getElem ho'
        obtain ⟨t, ht, _⟩ := hfit o _ hq
        exact ⟨_, hq, (Array.getElem?_eq_some_iff.1 ht).1⟩
      member := member b hb }

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.bookAt_of_onQ
#print axioms VerifiableInference.Desc.LinkJoin.eqRest_of_facts
