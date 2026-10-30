-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/AgreeParts.lean: THE FRAME's PREMISE "THE OTHER LOTS OF THE SAME
MESSAGE AGREE WITH THIS ONE" (`LotsAgree`, Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean) CUT
INTO PARTS ALONG THE LIST OF LOTS. For every kind of sub-protocol: no kind is named. IT PAYS
NOTHING: it says how the premise at a list put together of parts is made of the premises at the
parts. One definition; twelve theorems.

What it is for. `LotsAgree ml L` ranges over all lots of all kinds. A kind's authors can show it
against their own lots. With this file what is then left is the premise against the others' lots.

Main names:
  `Agree2 L L'`: the premise's text at ONE other lot: if L' is a lot of L's message, then wherever
    both texts answer at one entry they give one element.
  `lotsAgree_iff`: `LotsAgree ml L` is `Agree2 L L'` at every L' of the list: by unfolding.
  `agree2_self`, `agree2_symm`, `agree2_of_ne`, `agree2_of_never`: a lot agrees with itself; the
    relation is symmetric; lots of two messages agree; so do lots that never answer at one entry.
  `lotsAgree_nil`, `lotsAgree_cons`, `lotsAgree_append`, `lotsAgree_flatten`: THE CUT.
  `msgsAgree_append`: "all lots agree" (`MsgsAgree`) at two lists put together: each agrees in
    itself, and each lot of the first agrees with the second.
  `msgsAgree_of_pairs`, `lotsAgree_cut`: for a property P of lots any two of which agree: a list of
    such lots agrees in itself; in front of another list it falls out of the premise at such a lot.

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. On messages alone: the like for pads (`PadLotsAgree`) is not written. Nothing is said of
what a lot holds, nor that any two lots agree. The names stand in the frame's namespace, beside
`LotsAgree`. It stands over the frame's ScriptLots.lean, which lies in no seal.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread

variable {Bk : ProverCoinCounts} {W : Type}

/-- **The frame's premise at one other lot**: if L' is a lot of L's message, then wherever both
texts answer at one entry they give one element. It is a definition: the form of a hypothesis. -/
def Agree2 (L L' : MsgLot Bk W) : Prop :=
  L'.n = L.n → ∀ k w (hd : List Fmt.Drawn) mask row place y y',
    L.txt k w (hd.take L.fx) mask row place = some y →
    L'.txt k w (hd.take L'.fx) mask row place = some y' → y' = y

/-- The frame's premise is that form at every lot of the list. -/
theorem lotsAgree_iff {ml : List (MsgLot Bk W)} {L : MsgLot Bk W} :
    LotsAgree ml L ↔ ∀ L' ∈ ml, Agree2 L L' := Iff.rfl

/-- A lot agrees with itself. -/
theorem agree2_self (L : MsgLot Bk W) : Agree2 L L :=
  fun _ _ _ _ _ _ _ _ _ q q' => Option.some.inj (q'.symm.trans q)

/-- The relation is symmetric. -/
theorem agree2_symm {L L' : MsgLot Bk W} (h : Agree2 L L') : Agree2 L' L :=
  fun e k w hd mask row place y y' q q' => (h e.symm k w hd mask row place y' y q' q).symm

/-- Lots of two messages agree. -/
theorem agree2_of_ne {L L' : MsgLot Bk W} (h : L'.n ≠ L.n) : Agree2 L L' :=
  fun e => absurd e h

/-- Lots that never answer at one entry agree. -/
theorem agree2_of_never {L L' : MsgLot Bk W}
    (h : ∀ k w hd hd' mask row place, L.txt k w hd mask row place = none ∨
      L'.txt k w hd' mask row place = none) : Agree2 L L' := by
  intro _ k w hd mask row place y y' q q'
  rcases h k w (hd.take L.fx) (hd.take L'.fx) mask row place with n | n
  · rw [n] at q
    cases q
  · rw [n] at q'
    cases q'

/-- Against no lot nothing is asked. -/
theorem lotsAgree_nil (L : MsgLot Bk W) : LotsAgree [] L :=
  fun _ hm => absurd hm (List.not_mem_nil)

/-- One lot more. -/
theorem lotsAgree_cons {ml : List (MsgLot Bk W)} {L L' : MsgLot Bk W} :
    LotsAgree (L' :: ml) L ↔ Agree2 L L' ∧ LotsAgree ml L :=
  ⟨fun h => ⟨h L' (List.mem_cons_self), fun M hM => h M (List.mem_cons_of_mem _ hM)⟩,
    fun h M hM => by
      rcases List.mem_cons.1 hM with rfl | hM
      · exact h.1
      · exact h.2 M hM⟩

/-- **THE CUT**: the premise at two lists put together is the premise at each. -/
theorem lotsAgree_append {ml₁ ml₂ : List (MsgLot Bk W)} {L : MsgLot Bk W} :
    LotsAgree (ml₁ ++ ml₂) L ↔ LotsAgree ml₁ L ∧ LotsAgree ml₂ L :=
  ⟨fun h => ⟨fun M hM => h M (List.mem_append.2 (Or.inl hM)),
      fun M hM => h M (List.mem_append.2 (Or.inr hM))⟩,
    fun h M hM => (List.mem_append.1 hM).elim (h.1 M) (h.2 M)⟩

/-- **THE CUT, over a list of lists**: one list for each kind, say. -/
theorem lotsAgree_flatten {lls : List (List (MsgLot Bk W))} {L : MsgLot Bk W} :
    LotsAgree lls.flatten L ↔ ∀ ml ∈ lls, LotsAgree ml L :=
  ⟨fun h ml hml M hM => h M (List.mem_flatten.2 ⟨ml, hml, hM⟩),
    fun h M hM => by
      obtain ⟨ml, hml, hM'⟩ := List.mem_flatten.1 hM
      exact h ml hml M hM'⟩

/-- **"All lots agree" at two lists put together**: each agrees in itself, and each lot of the first
agrees with the second. The fourth part, the second against the first, follows by symmetry. -/
theorem msgsAgree_append {ml₁ ml₂ : List (MsgLot Bk W)} :
    MsgsAgree (ml₁ ++ ml₂) ↔
      MsgsAgree ml₁ ∧ MsgsAgree ml₂ ∧ ∀ L ∈ ml₁, LotsAgree ml₂ L :=
  ⟨fun h => ⟨fun L hL => (lotsAgree_append.1 (h L (List.mem_append.2 (Or.inl hL)))).1,
      fun L hL => (lotsAgree_append.1 (h L (List.mem_append.2 (Or.inr hL)))).2,
      fun L hL => (lotsAgree_append.1 (h L (List.mem_append.2 (Or.inl hL)))).2⟩,
    fun h L hL => lotsAgree_append.2 <| (List.mem_append.1 hL).elim
      (fun hL => ⟨h.1 L hL, h.2.2 L hL⟩)
      (fun hL => ⟨fun M hM => agree2_symm (h.2.2 M hM L hL), h.2.1 L hL⟩)⟩

/-- A list of lots with a property any two of which agree, agrees in itself. -/
theorem msgsAgree_of_pairs {P : MsgLot Bk W → Prop}
    (h : ∀ L L', P L → P L' → Agree2 L L') {ml : List (MsgLot Bk W)} (hm : ∀ L ∈ ml, P L) :
    MsgsAgree ml :=
  fun L hL L' hL' => h L L' (hm L hL) (hm L' hL')

/-- **Such a list falls out of the premise at such a lot**: what is left is the premise against the
rest. -/
theorem lotsAgree_cut {P : MsgLot Bk W → Prop} (h : ∀ L L', P L → P L' → Agree2 L L')
    {ml₁ rest : List (MsgLot Bk W)} (hm : ∀ L ∈ ml₁, P L) {L : MsgLot Bk W} (hL : P L) :
    LotsAgree (ml₁ ++ rest) L ↔ LotsAgree rest L :=
  lotsAgree_append.trans ⟨fun x => x.2, fun x => ⟨fun L' hL' => h L L' hL (hm L' hL'), x⟩⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.lotsAgree_iff
#print axioms ProofFile.Honest.FirstThread.agree2_self
#print axioms ProofFile.Honest.FirstThread.agree2_symm
#print axioms ProofFile.Honest.FirstThread.agree2_of_ne
#print axioms ProofFile.Honest.FirstThread.agree2_of_never
#print axioms ProofFile.Honest.FirstThread.lotsAgree_nil
#print axioms ProofFile.Honest.FirstThread.lotsAgree_cons
#print axioms ProofFile.Honest.FirstThread.lotsAgree_append
#print axioms ProofFile.Honest.FirstThread.lotsAgree_flatten
#print axioms ProofFile.Honest.FirstThread.msgsAgree_append
#print axioms ProofFile.Honest.FirstThread.msgsAgree_of_pairs
#print axioms ProofFile.Honest.FirstThread.lotsAgree_cut
