-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/AgreePartsPads.lean: THE FRAME's PREMISE "THE OTHER LOTS OF THE
SAME PAD AGREE WITH THIS ONE" (PadLotsAgree, Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean)
CUT INTO PARTS ALONG THE LIST OF LOTS. THE SISTER, FOR PADS, OF
Johnson/Desc/ProofFile/Honest/Small/AgreeParts.lean (for messages; by the authors of the attention
sub-protocol's own rounds), STATEMENT FOR STATEMENT, so that whoever joins the houses' lots can
call the two alike. That file's Limits: "On messages alone: the like for pads (`PadLotsAgree`) is
not written."; its authors' word: "WE HAVE NONE, LOOSE OR OTHERWISE,
AND DO NOT MEAN TO WRITE IT: PLEASE WRITE IT". For every kind of sub-protocol: no kind is named. IT
PAYS NOTHING: it says how the premise at a list put together of parts is made of the premises at
the parts. One definition; twelve theorems after that file's twelve; four negative tests. A TRIAL
THAT COUNTS IN NO COLUMN.
NO PROPERTY IS CLAIMED.

What it is for. PadLotsAgree pl L ranges over all lots of all kinds. A kind's authors can hold it
against their own lots. With this file what is then left is the premise against the others' lots.

PadAgree2 L L' the premise's text at ONE other lot: if L' is a lot of L's pad (one j, one t), then
wherever both texts answer at one entry they give one element. A definition: the form of a
hypothesis. padLotsAgree_iff PadLotsAgree pl L is PadAgree2 L L' at every L' of the list: by
unfolding. padAgree2_self, padAgree2_symm, padAgree2_of_ne, padAgree2_of_never a lot agrees with
itself; the relation is symmetric; lots of two pads agree (another j, or another t); so do lots
that never answer at one entry. padLotsAgree_nil, padLotsAgree_cons, padLotsAgree_append,
padLotsAgree_flatten THE CUT. padsAgree_append "all lots agree" (PadsAgree) at two lists put
together: each agrees in itself, and each lot of the first agrees with the second.
padsAgree_of_pairs, padLotsAgree_cut for a property P of lots any two of which agree: a list of
such lots agrees in itself; in front of another list it falls out of the premise at such a lot.
padAgree2_fails, padLotsAgree_fails, padsAgree_fails THE FORMS CAN FAIL: two lots of one pad whose
texts answer y and y' everywhere, y' not y: none of the three forms holds of them (given one book's
coins and one input: else the forms hold for want of anything to range over; and given y' not y:
that the field has two elements is not said here). padAgree2_of_ne_bites padAgree2_of_ne's premise
is spent: the same two texts at two pads do agree.

WHERE IT PARTS FROM ITS SISTER. A pad has two numbers, j and t, where a message has one, n: so "of
two pads" is "another j, or another t". A pad's text takes no list of what was drawn: so no "take …
fx" stands here. The four negative tests have no like there.

THE COINS. A book's coins stand in each statement as a bound letter k, handed on whole to a lot's
text; in the negative tests the texts do not read it. No value is taken out of a run's coins;
nothing is said on how coins are laid out or drawn.

Whose. By the authors of the shared "sending" (the kind K1). The names stand in the frame's
namespace, beside PadLotsAgree, as the sister's do.

Limits. Nothing is said of what a lot holds, nor that any two lots agree. It stands over the
frame's ScriptLots.lean, a row of laws.12's closed list (stage 13; new there), which does not lie
in laws.11's seal. The sister is not imported: nothing of it is called. Nothing is claimed on
soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open OnBytes.Slice (GE)

variable {Bk : ProverCoinCounts} {W : Type}

/-- **The frame's premise at one other lot**: if L' is a lot of L's pad, then wherever both texts
answer at one entry they give one element. It is a definition: the form of a hypothesis. -/
def PadAgree2 (L L' : PadLot Bk W) : Prop :=
  L'.j = L.j → L'.t = L.t → ∀ k w mask row place y y',
    L.txt k w mask row place = some y → L'.txt k w mask row place = some y' → y' = y

/-- The frame's premise is that form at every lot of the list. -/
theorem padLotsAgree_iff {pl : List (PadLot Bk W)} {L : PadLot Bk W} :
    PadLotsAgree pl L ↔ ∀ L' ∈ pl, PadAgree2 L L' := Iff.rfl

/-- A lot agrees with itself. -/
theorem padAgree2_self (L : PadLot Bk W) : PadAgree2 L L :=
  fun _ _ _ _ _ _ _ _ _ q q' => Option.some.inj (q'.symm.trans q)

/-- The relation is symmetric. -/
theorem padAgree2_symm {L L' : PadLot Bk W} (h : PadAgree2 L L') : PadAgree2 L' L :=
  fun ej et k w mask row place y y' q q' =>
    (h ej.symm et.symm k w mask row place y' y q' q).symm

/-- Lots of two pads agree. -/
theorem padAgree2_of_ne {L L' : PadLot Bk W} (h : L'.j ≠ L.j ∨ L'.t ≠ L.t) : PadAgree2 L L' :=
  fun ej et => h.elim (fun n => absurd ej n) fun n => absurd et n

/-- Lots that never answer at one entry agree. -/
theorem padAgree2_of_never {L L' : PadLot Bk W}
    (h : ∀ k w mask row place, L.txt k w mask row place = none ∨
      L'.txt k w mask row place = none) : PadAgree2 L L' := by
  intro _ _ k w mask row place y y' q q'
  rcases h k w mask row place with n | n
  · rw [n] at q
    cases q
  · rw [n] at q'
    cases q'

/-- Against no lot nothing is asked. -/
theorem padLotsAgree_nil (L : PadLot Bk W) : PadLotsAgree [] L :=
  fun _ hm => absurd hm (List.not_mem_nil)

/-- One lot more. -/
theorem padLotsAgree_cons {pl : List (PadLot Bk W)} {L L' : PadLot Bk W} :
    PadLotsAgree (L' :: pl) L ↔ PadAgree2 L L' ∧ PadLotsAgree pl L :=
  ⟨fun h => ⟨h L' (List.mem_cons_self), fun M hM => h M (List.mem_cons_of_mem _ hM)⟩,
    fun h M hM => by
      rcases List.mem_cons.1 hM with rfl | hM
      · exact h.1
      · exact h.2 M hM⟩

/-- **THE CUT**: the premise at two lists put together is the premise at each. -/
theorem padLotsAgree_append {pl₁ pl₂ : List (PadLot Bk W)} {L : PadLot Bk W} :
    PadLotsAgree (pl₁ ++ pl₂) L ↔ PadLotsAgree pl₁ L ∧ PadLotsAgree pl₂ L :=
  ⟨fun h => ⟨fun M hM => h M (List.mem_append.2 (Or.inl hM)),
      fun M hM => h M (List.mem_append.2 (Or.inr hM))⟩,
    fun h M hM => (List.mem_append.1 hM).elim (h.1 M) (h.2 M)⟩

/-- **THE CUT, over a list of lists**: one list for each kind, say. -/
theorem padLotsAgree_flatten {pls : List (List (PadLot Bk W))} {L : PadLot Bk W} :
    PadLotsAgree pls.flatten L ↔ ∀ pl ∈ pls, PadLotsAgree pl L :=
  ⟨fun h pl hpl M hM => h M (List.mem_flatten.2 ⟨pl, hpl, hM⟩),
    fun h M hM => by
      obtain ⟨pl, hpl, hM'⟩ := List.mem_flatten.1 hM
      exact h pl hpl M hM'⟩

/-- **"All lots agree" at two lists put together**: each agrees in itself, and each lot of the first
agrees with the second. The fourth part, the second against the first, follows by symmetry. -/
theorem padsAgree_append {pl₁ pl₂ : List (PadLot Bk W)} :
    PadsAgree (pl₁ ++ pl₂) ↔
      PadsAgree pl₁ ∧ PadsAgree pl₂ ∧ ∀ L ∈ pl₁, PadLotsAgree pl₂ L :=
  ⟨fun h => ⟨fun L hL => (padLotsAgree_append.1 (h L (List.mem_append.2 (Or.inl hL)))).1,
      fun L hL => (padLotsAgree_append.1 (h L (List.mem_append.2 (Or.inr hL)))).2,
      fun L hL => (padLotsAgree_append.1 (h L (List.mem_append.2 (Or.inl hL)))).2⟩,
    fun h L hL => padLotsAgree_append.2 <| (List.mem_append.1 hL).elim
      (fun hL => ⟨h.1 L hL, h.2.2 L hL⟩)
      (fun hL => ⟨fun M hM => padAgree2_symm (h.2.2 M hM L hL), h.2.1 L hL⟩)⟩

/-- A list of lots with a property any two of which agree, agrees in itself. -/
theorem padsAgree_of_pairs {P : PadLot Bk W → Prop}
    (h : ∀ L L', P L → P L' → PadAgree2 L L') {pl : List (PadLot Bk W)} (hm : ∀ L ∈ pl, P L) :
    PadsAgree pl :=
  fun L hL L' hL' => h L L' (hm L hL) (hm L' hL')

/-- **Such a list falls out of the premise at such a lot**: what is left is the premise against the
rest. -/
theorem padLotsAgree_cut {P : PadLot Bk W → Prop} (h : ∀ L L', P L → P L' → PadAgree2 L L')
    {pl₁ rest : List (PadLot Bk W)} (hm : ∀ L ∈ pl₁, P L) {L : PadLot Bk W} (hL : P L) :
    PadLotsAgree (pl₁ ++ rest) L ↔ PadLotsAgree rest L :=
  padLotsAgree_append.trans ⟨fun x => x.2, fun x => ⟨fun L' hL' => h L L' hL (hm L' hL'), x⟩⟩

/-! ## The forms can fail -/

/-- Two lots of one pad whose texts answer y and y' everywhere, y' not y, do not agree. k, w: one
book's coins and one input, which the texts do not read: without them the form ranges over
nothing. -/
theorem padAgree2_fails (k : Coins Bk) (w : W) (j t : Nat) {y y' : GE} (hne : y' ≠ y) :
    ¬ PadAgree2 (⟨j, t, fun _ _ _ _ _ => some y⟩ : PadLot Bk W)
      ⟨j, t, fun _ _ _ _ _ => some y'⟩ :=
  fun h => hne (h rfl rfl k w false 0 0 y y' rfl rfl)

/-- So the frame's premise fails at the first against a list that holds the second. -/
theorem padLotsAgree_fails (k : Coins Bk) (w : W) (j t : Nat) {y y' : GE} (hne : y' ≠ y)
    (pl : List (PadLot Bk W)) :
    ¬ PadLotsAgree ((⟨j, t, fun _ _ _ _ _ => some y'⟩ : PadLot Bk W) :: pl)
      ⟨j, t, fun _ _ _ _ _ => some y⟩ :=
  fun h => padAgree2_fails k w j t hne (padLotsAgree_cons.1 h).1

/-- And "all lots agree" fails at the list of the two. -/
theorem padsAgree_fails (k : Coins Bk) (w : W) (j t : Nat) {y y' : GE} (hne : y' ≠ y) :
    ¬ PadsAgree [(⟨j, t, fun _ _ _ _ _ => some y⟩ : PadLot Bk W),
      ⟨j, t, fun _ _ _ _ _ => some y'⟩] :=
  fun h => padAgree2_fails k w j t hne
    ((padLotsAgree_cons.1 (padLotsAgree_cons.1 (h _ List.mem_cons_self)).2).1)

/-- padAgree2_of_ne's premise is spent: the same two texts at two pads do agree. -/
theorem padAgree2_of_ne_bites (j t : Nat) (y y' : GE) :
    PadAgree2 (⟨j, t, fun _ _ _ _ _ => some y⟩ : PadLot Bk W)
        ⟨j + 1, t, fun _ _ _ _ _ => some y'⟩ ∧
      PadAgree2 (⟨j, t, fun _ _ _ _ _ => some y⟩ : PadLot Bk W)
        ⟨j, t + 1, fun _ _ _ _ _ => some y'⟩ :=
  ⟨padAgree2_of_ne (Or.inl (Nat.succ_ne_self j)), padAgree2_of_ne (Or.inr (Nat.succ_ne_self t))⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.PadAgree2
#print axioms ProofFile.Honest.FirstThread.padLotsAgree_iff
#print axioms ProofFile.Honest.FirstThread.padAgree2_self
#print axioms ProofFile.Honest.FirstThread.padAgree2_symm
#print axioms ProofFile.Honest.FirstThread.padAgree2_of_ne
#print axioms ProofFile.Honest.FirstThread.padAgree2_of_never
#print axioms ProofFile.Honest.FirstThread.padLotsAgree_nil
#print axioms ProofFile.Honest.FirstThread.padLotsAgree_cons
#print axioms ProofFile.Honest.FirstThread.padLotsAgree_append
#print axioms ProofFile.Honest.FirstThread.padLotsAgree_flatten
#print axioms ProofFile.Honest.FirstThread.padsAgree_append
#print axioms ProofFile.Honest.FirstThread.padsAgree_of_pairs
#print axioms ProofFile.Honest.FirstThread.padLotsAgree_cut
#print axioms ProofFile.Honest.FirstThread.padAgree2_fails
#print axioms ProofFile.Honest.FirstThread.padLotsAgree_fails
#print axioms ProofFile.Honest.FirstThread.padsAgree_fails
#print axioms ProofFile.Honest.FirstThread.padAgree2_of_ne_bites
