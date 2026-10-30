-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/OwnBridge.lean: «NO MESSAGE OF THE LINK's OWN IS THE INDEX MASKS'
MESSAGE» (the second premise of `EqAsks`, EqMg.lean), IN FRONT OF THE ONE EQUATION's SUB-PROTOCOL,
FROM THREE THINGS: a fact along the verifier's run (the open link's frame holds the plan's list of
the link's own oracle messages); the public item «the state's number of the index masks' message is
the plan's», which the table's promise holds open there; a test on the plan's numbers (that number
is in no such list). Definitions, theorems, an evaluation.

What is said.
  `OwnFact Rch pl ownF`: the fact along the run, written out: one conjunct of the field frameIs of
    the structure of facts that the laws take from «reached» (Johnson/Desc/First/FoldFacts.lean),
    at ownF m c
    := the plan's list at segment m and the moment of piece c. `messageNow_own`: a message of the
    link's own, as the one equation's sub-protocol looks it up, is a member of the frame's list.
    `idxAtE`, `idxFitE M links ps`: a Bool on the tables: at each place of a one equation the public
    item is asked in front; `idxFitE_full`: the kernel's yes at the composed filling and the full
    list. `index_of_promise`: so the promise at the composed meaning gives the number.
    `own_of_fact`: **the premise, at the conditions of the second form.** `eqAsks_of`: `EqAsks` from
    it and `OracleAsks`.

Limits. `OwnFact` is a premise (booked as owed by other files). The test on the plan's numbers
(«the index masks' number is in no list of a link's own messages») is a premise: it has run at no
plan. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.GroupBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where messageNow)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Pub More Numbers flatPlacesOf start openSets pubSets
  pubOfItems pubHeld pubAll_indexIs)
open _root_.Run.PQ (CK)

variable {C : CK} {F : Frame}

/-- **The fact along the run**, written out. -/
def OwnFact (Rch : ℕ → S × F.E.Str → Prop) (pl : List Place) (ownF : ℕ → ℕ → Array ℕ) : Prop :=
  ∀ k (a : S × F.E.Str) p m L, Rch k a → a.1.failed = none → pl[k]? = some p → p.link = some m →
    a.1.link? = some L → L.check.frame.own = ownF m p.piece

/-- A message of the link's own is a member of the frame's list. -/
theorem messageNow_own (f : ReqFrame) (m o : ℕ) (h : messageNow f f.link m = some o) :
    o ∈ f.own := by
  unfold messageNow at h
  split at h
  · exact nomatch h
  · rw [if_pos (by simp)] at h
    exact Array.mem_of_getElem? h

/-- **The test at number k of the list**: in front of a one equation the item is asked. -/
def idxAtE (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]? with
  | some p =>
    match p.link with
    | some m =>
      if p.piece == hearN links m + 3 then
        ((pubSets M links ps)[k]?.getD [] ++
          pubOfItems ((openSets links ps (start links))[k]?.getD [])).contains .indexIs
      else true
    | none => true
  | none => true

/-- **The test along the list.** -/
def idxFitE (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all (idxAtE M links ps)

theorem idxE_at (M : More) (links : List ModelPart) (ps : List Place) (h : idxFitE M links ps = true)
    (k m : ℕ) (p : Place) (hp : ps[k]? = some p) (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 3) :
    Pub.indexIs ∈ (pubSets M links ps)[k]?.getD [] ++
      pubOfItems ((openSets links ps (start links))[k]?.getD []) := by
  unfold idxFitE at h
  rw [List.all_eq_true] at h
  have h0 := h k (List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1)
  unfold idxAtE at h0
  rw [hp] at h0
  simpa [hl, hpc] using h0

set_option maxRecDepth 1000000 in
/-- **THE YES AT THE COMPOSED FILLING AND THE FULL LIST.** -/
theorem idxFitE_full : idxFitE moreAll fullList (flatPlacesOf fullList true) = true := by
  decide +kernel

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

/-- The promise at the composed meaning gives the number. -/
theorem index_of_promise (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k m : ℕ)
    (p : Place) (hfit : idxFitE moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + 3) (a : S × F.E.Str)
    (ha : onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) k a) :
    a.1.out.indexMasks = 𝔇.pubD.N.indexNo := by
  have hpub := (onT_bools Nm (mgAll 𝔇 mgBase) links pl z k a ha).2.2.2.2.1
  have hmem := idxE_at moreAll links pl hfit k m p hp hl hpc
  rw [mgAll_more_base 𝔇] at hpub
  unfold pubHeld at hpub
  have h1 := List.all_eq_true.1 hpub .indexIs hmem
  rw [mgAll_pub, pubAll_indexIs] at h1
  have h2 : (a.1.out.indexMasks == 𝔇.pubD.N.indexNo) = true := h1
  exact beq_iff_eq.1 h2

/-- **THE PREMISE, AT THE CONDITIONS OF THE SECOND FORM.** -/
theorem own_of_fact (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P)
    (Rch : ℕ → S × F.E.Str → Prop) (ownF : ℕ → ℕ → Array ℕ) (G : OwnFact Rch pl ownF) (k m : ℕ)
    (p : Place) (hfit : idxFitE moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + 3)
    (hfree : 𝔇.pubD.N.indexNo ∉ ownF m p.piece) (a : S × F.E.Str)
    (ha : onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a) :
    ∀ x, atS.get? a.1 = some x → ∀ m' o,
      messageNow x.L.check.frame x.L.check.frame.link m' = some o → o ≠ a.1.out.indexMasks := by
  intro x hx m' o ho e
  have hf : a.1.failed = none := Classical.not_not.1 ha.1.2
  have hmem := messageNow_own _ m' o ho
  rw [G k a p m x.L ha.2 hf hp hl (part_reads a.1 x hx).1, e,
    index_of_promise 𝔇 Nm links pl z k m p hfit hp hl hpc a ha.1] at hmem
  exact hfree hmem

/-- EqAsks from it and OracleAsks. -/
theorem eqAsks_of (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P)
    (Rch : ℕ → S × F.E.Str → Prop) (ownF : ℕ → ℕ → Array ℕ) (G : OwnFact Rch pl ownF) (k m : ℕ)
    (p : Place) (hfit : idxFitE moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + 3)
    (hfree : 𝔇.pubD.N.indexNo ∉ ownF m p.piece) (base : ℕ) (a b : S × F.E.Str)
    (ha : onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a)
    (O : OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp Nm links pl z k base a.1 b.1) :
    EqAsks 𝔇 Nm links pl z k base a.1 b.1 :=
  ⟨O, own_of_fact 𝔇 Nm links pl z Rch ownF G k m p hfit hp hl hpc hfree a ha⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.messageNow_own
#print axioms VerifiableInference.Desc.LinkJoin.idxFitE_full
#print axioms VerifiableInference.Desc.LinkJoin.index_of_promise
#print axioms VerifiableInference.Desc.LinkJoin.own_of_fact
#print axioms VerifiableInference.Desc.LinkJoin.eqAsks_of
