-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/TotOfPromise.lean: BENEATH THE LINK's NAMED LIST: ITS FIELD tot («in
front of the one equation the one sum can be taken») IS AMONG THE PROMISE's OWN PUBLIC TESTS THERE:
so it follows from the promise, under a Bool on the written list. After `index_of_promise`
(OwnBridge.lean). Definitions, theorems, evaluations.

What is said.
  `totAtE`, `totFitE M links ps`: the Bool: at every place of the list with the piece «the link's
    hearings + 3» the public item «the one sum can be taken at link m» is among those that the
    promise asks at that border. `totE_at`: what its yes gives. `totFitE_links`: the kernel's yes at
    `P5J.fullLinks` and its list of places. `totFitE_bent`: a negative test: with numbers 10 and 11
    of the list changed over: no. `total_of_promise`: **the promise at the composed meaning over the
    closed base, at such a border, gives `K9.totalIn (𝔇.N.group m) a.1 = true`.** `tot_of`: **the
    field tot, to the letter.**

Limits. It reads the promise; it proves nothing of a state that the promise does not already ask.
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OwnBridge
import Johnson.Desc.First.Link.Law.K09Cond

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Pub More Numbers flatPlacesOf start openSets pubSets
  pubOfItems pubHeld pubAll_totalIn)
open _root_.Run.PQ (CK)

variable {C : CK} {F : Frame}

/-- **The test at number k of the list**: in front of a one equation the item is asked. -/
def totAtE (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]? with
  | some p =>
    match p.link with
    | some m =>
      if p.piece == hearN links m + 3 then
        ((pubSets M links ps)[k]?.getD [] ++
          pubOfItems ((openSets links ps (start links))[k]?.getD [])).contains (.totalIn m)
      else true
    | none => true
  | none => true

/-- **The test along the list.** -/
def totFitE (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all (totAtE M links ps)

theorem totE_at (M : More) (links : List ModelPart) (ps : List Place) (h : totFitE M links ps = true)
    (k m : ℕ) (p : Place) (hp : ps[k]? = some p) (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 3) :
    Pub.totalIn m ∈ (pubSets M links ps)[k]?.getD [] ++
      pubOfItems ((openSets links ps (start links))[k]?.getD []) := by
  unfold totFitE at h
  rw [List.all_eq_true] at h
  have h0 := h k (List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1)
  unfold totAtE at h0
  rw [hp] at h0
  simpa [hl, hpc] using h0

set_option maxRecDepth 1000000 in
/-- **THE KERNEL's YES AT P5J.fullLinks (Johnson/P5J/MeansQ.lean).** -/
theorem totFitE_links :
    totFitE moreAll P5J.fullLinks (flatPlacesOf P5J.fullLinks true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: numbers 10 and 11 of the list changed over. -/
theorem totFitE_bent :
    totFitE moreAll P5J.fullLinks (swapAt (flatPlacesOf P5J.fullLinks true) 10) = false := by
  decide +kernel

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

/-- **THE PROMISE GIVES IT.** -/
theorem total_of_promise (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k m : ℕ)
    (p : Place) (hfit : totFitE moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + 3) (a : S × F.E.Str)
    (ha : onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) k a) :
    K9.totalIn (𝔇.N.group m) a.1 = true := by
  have hpub := (onT_bools Nm (mgAll 𝔇 mgBase) links pl z k a ha).2.2.2.2.1
  have hmem := totE_at moreAll links pl hfit k m p hp hl hpc
  rw [mgAll_more_base 𝔇] at hpub
  unfold pubHeld at hpub
  have h1 := List.all_eq_true.1 hpub (.totalIn m) hmem
  rw [mgAll_pub, pubAll_totalIn] at h1
  exact h1

/-- **THE FIELD tot.** -/
theorem tot_of (links : List ModelPart) (pl : List Place) (z : P) (Rz : ℕ → S × F.E.Str → Prop)
    (k m : ℕ) (p : Place) (hfit : totFitE moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + 3) :
    ∀ a, onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz k a →
      K9.totalIn (𝔇.N.group m) a.1 = true :=
  fun a ha => total_of_promise 𝔇 𝔇.N links pl z k m p hfit hp hl hpc a ha.1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.totE_at
#print axioms VerifiableInference.Desc.LinkJoin.totFitE_links
#print axioms VerifiableInference.Desc.LinkJoin.totFitE_bent
#print axioms VerifiableInference.Desc.LinkJoin.total_of_promise
#print axioms VerifiableInference.Desc.LinkJoin.tot_of
