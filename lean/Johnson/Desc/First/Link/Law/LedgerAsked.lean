-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LedgerAsked.lean: IN FRONT OF A LINK's BATCHING, AND OF THE FRAME's
SUB-PROTOCOL BEHIND IT, THE TABLE's PROMISE AT THE COMPOSED MEANING GIVES «the segment's ledger is
well laid» (`ledgerOk`, SizedRides.lean). A Bool on the tables and the written list («the public
item `ledger m` is asked there»), its yes by the kernel at the composed filling and the full list, a
negative test, and the theorem that draws the fact from the promise.

What is said.
  `ledAt`, `ledFit M links ps`: the Bool. `led_at`: the fact at a place. `ledFit_full`: the kernel's
    yes at `moreAll` and the full list. `ledFit_bent`: a negative test: the first segment's
    sub-protocol behind the batching and its one equation, whose row drops the item, changed over:
    no. `ledFit_unmade`: a second: the place whose row makes the first segment's item taken out of
    the list: no. `ledger_of_promise`: **`onT … (mgAll 𝔇 mgBase) … k a` gives `ledgerOk a.1 =
    true`** at these places.

Limits. An evaluation on the tables, and an unfolding of the promise. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OwnBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Pub More Numbers flatPlacesOf start openSets pubSets
  pubOfItems pubHeld pubAll_ledger)
open _root_.Run.PQ (CK)

/-- **The test at number k of the list**: in front of a batching and of the sub-protocol behind it
the item is asked. -/
def ledAt (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]? with
  | some p =>
    match p.link with
    | some m =>
      if p.piece == hearN links m + 1 || p.piece == hearN links m + 2 then
        ((pubSets M links ps)[k]?.getD [] ++
          pubOfItems ((openSets links ps (start links))[k]?.getD [])).contains (.ledger m)
      else true
    | none => true
  | none => true

/-- **The test along the list.** -/
def ledFit (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all (ledAt M links ps)

theorem led_at (M : More) (links : List ModelPart) (ps : List Place) (h : ledFit M links ps = true)
    (k m i : ℕ) (p : Place) (hp : ps[k]? = some p) (hl : p.link = some m)
    (hpc : p.piece = hearN links m + i) (hi : i = 1 ∨ i = 2) :
    Pub.ledger m ∈ (pubSets M links ps)[k]?.getD [] ++
      pubOfItems ((openSets links ps (start links))[k]?.getD []) := by
  unfold ledFit at h
  rw [List.all_eq_true] at h
  have h0 := h k (List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1)
  unfold ledAt at h0
  rw [hp] at h0
  rcases hi with rfl | rfl <;> simpa [hl, hpc] using h0

set_option maxRecDepth 1000000 in
/-- **THE YES AT THE COMPOSED FILLING AND THE FULL LIST.** -/
theorem ledFit_full : ledFit moreAll fullList (flatPlacesOf fullList true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A NEGATIVE TEST: THE FIRST SEGMENT's SUB-PROTOCOL BEHIND THE BATCHING AND ITS ONE EQUATION,
WHOSE ROW DROPS THE ITEM, CHANGED OVER** (numbers 10 and 11 of the list). -/
theorem ledFit_bent : ledFit moreAll fullList (swapAt (flatPlacesOf fullList true) 10) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A SECOND: THE PLACE WHOSE ROW MAKES THE FIRST SEGMENT's ITEM TAKEN OUT OF THE LIST** (number
2). -/
theorem ledFit_unmade :
    ledFit moreAll fullList ((flatPlacesOf fullList true).eraseIdx 2) = false := by
  decide +kernel

variable {C : CK} {F : Frame}
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

/-- **THE PROMISE GIVES «THE LEDGER IS WELL LAID».** -/
theorem ledger_of_promise (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k m i : ℕ)
    (p : Place) (hfit : ledFit moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + i) (hi : i = 1 ∨ i = 2)
    (a : S × F.E.Str) (ha : onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) k a) :
    ledgerOk a.1 = true := by
  have hpub := (onT_bools Nm (mgAll 𝔇 mgBase) links pl z k a ha).2.2.2.2.1
  have hmem := led_at moreAll links pl hfit k m i p hp hl hpc hi
  rw [mgAll_more_base 𝔇] at hpub
  unfold pubHeld at hpub
  have h1 := List.all_eq_true.1 hpub (.ledger m) hmem
  rw [mgAll_pub, pubAll_ledger] at h1
  exact h1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.led_at
#print axioms VerifiableInference.Desc.LinkJoin.ledFit_full
#print axioms VerifiableInference.Desc.LinkJoin.ledFit_bent
#print axioms VerifiableInference.Desc.LinkJoin.ledFit_unmade
#print axioms VerifiableInference.Desc.LinkJoin.ledger_of_promise
