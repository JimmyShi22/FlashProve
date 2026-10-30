-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GroupField.lean: THE FIELD "groupIs" OF THE LIST OF FACTS ALONG THE
FOLD (Johnson/Desc/First/FoldFacts.lean), PROVED WITH THE FIELD's EXACT TYPE, at every border that
it asks.
"The state": the verifier's state, the value that the fold of the IOP as written in Lean carries
from sub-protocol to sub-protocol. "The cut k": the state behind the flat list's first k entries,
which is the border in front of entry number k.
WHAT THE FIELD ASKS: at a reached border k whose entry's place bears a link m, of every L with
s.link? = some L: L.check.group and L.check.frame.group are groupAt m. In the written list of places
(Johnson/IMR/WrittenList.lean's placesW) an entry that bears the link m has m < 25 and stands at a
number
from 14 m + 1 to 14 m + 14, at m = 24 to 14 m + 16: among link m's own, from "laid" to "cleared"
(link_numbers: a closed test, run by the kernel; this direction alone is tested and spent). These
numbers are 1 to 352: SO THE FIELD ASKS NOTHING AT NUMBER 0 (the front) AND FROM 353 ON (the four
behind the links and the seal).
  framesOf_between: every link's "cleared" lays a state between the links (
    clear_carries, last clause: Johnson/Top/H0/Walk/FrameLaw.lean).
  cleared_shut: behind "cleared" of link l < 25 no link is open.
  front_shut: at the cuts 0 and 1 no link is open (the first state stands between the links; the
    front hands it back).
  shut_between: NO LINK IS OPEN BETWEEN THE LINKS: at the cuts 0, 1, 14 l + 1 and 14 l + 2 (l < 25),
    339 and 353.
  group_is1: Johnson/IMR/GroupHead.lean's group_is from the cut 14 l + 1 on: every border of link l.
  linkFit, link_numbers, link_number_at: the closed test. linkBentAt k m: the written list with a
    place of link m at number k. link_bent_fails: five negative tests: each bound at a link in front
    of the head's and at the head's, and the clause m < 25. link_bent_control: the same form with
    the entry's own link passes.
  groupIs_field: THE TOP: at ps := IM.placesW and groupAt := the identity; general in "reached" and
    in at_, with one premise on "reached": it is the return of a fold from ProofFile.startS Z.
NOT HERE: whether a link is open at the cuts 354 to 358 (the field does not ask). That the flat
list's places are placesW (IM.places_scope). That "reached" in other files' sense gives the fold
(Johnson/Top/H0/Walk/Reach.lean's Reach.fold does, at the first tree's number 0 alone). That the
composed meaning's groupAt (P5J.At.N's, Johnson/P5J/LettersAt.lean) is the identity: the field's
type is met up to unfolding where its groupAt is written as fun m => m. It counts no groups.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: whoever makes a value of the list
of facts along the fold.
The premises are laws' premises: no proof file is shown here for which a fold returns. No soundness.
-/
import Johnson.IMR.GroupHead
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- Every link's "cleared" lays a state between the links. -/
theorem framesOf_between {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs, ∀ s t,
    f.clear s = .ok t → t.atBetween = true := by
  have clr : ∀ (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut)
      (row : RowFn) (s t : S), clearWith X counts left row s = .ok t → t.atBetween = true :=
    fun X counts left row s t k => (Law.clear_carries k).2.2.2.2.2.2.2.2.2
  have th : ∀ (X : LinkPub) (lay : WsLay) (lin : Params.LinShape) (s t : S),
      Close.tailHead X lay lin s = .ok t → t.atBetween = true := fun _ _ _ => clr _ _ _ _
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact th _ _ _
  · split at e
    · split at e
      · cases e
      · cases e
        exact clr _ _ _ _
    · split at e
      · cases e
      · cases e
        exact clr _ _ _ _
      · cases e
        exact clr _ _ _ _

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **BEHIND "cleared" OF LINK l < 25 NO LINK IS OPEN**: the cut 14 (l + 1) + 1; behind the head's
link: 353. -/
theorem cleared_shut (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : ProofFile.InstPub} {R R' : List Fmt.RoundView} {C C' : List VerifiableInference.Desc.OpenedColumn} {t : S}
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * l + 15 + (if l = 24 then 2 else 0))) (ProofFile.startS Z p) R C =
      .ok (t, R', C')) : t.link? = none := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, fr, bL, bB, bC, eL, hlen, hf, -, -, -, hClear, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr l hl
  have e : 14 * l + 15 + (if l = 24 then 2 else 0) = 14 * l + Lk.hear.length + 7 + 1 := by
    rw [hlen]
    by_cases h : l = 24
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  rw [e] at f
  obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 14 * l + Lk.hear.length + 7) f
  obtain ⟨rs, gs, d⟩ := fold_next iC fu f
  rw [dC] at d
  exact link_between
    (framesOf_between hfs fr (List.mem_of_getElem? hf) u t ((hClear u t).1 d).1)

/-- **AT THE CUTS 0 AND 1 NO LINK IS OPEN.** -/
theorem front_shut (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} :
    ∀ k ≤ 1, ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C') → t.link? = none
  | 0, _, t, R', C', f => by
    have fz : foldBlocks 0 (c.blocksInOrder.take 0) (ProofFile.startS Z p) R C = .ok (ProofFile.startS Z p, R, C) := rfl
    rw [fz] at f
    cases f
    exact link_between (start_between O.pub p)
  | 1, _, t, R', C', f => by
    have fz : foldBlocks 0 (c.blocksInOrder.take 0) (ProofFile.startS Z p) R C = .ok (ProofFile.startS Z p, R, C) := rfl
    obtain ⟨b, hb, -, -, -, -, hd⟩ := IM.front_of O
    obtain ⟨rs, gs, d⟩ := fold_next hb fz f
    rw [(hd _ rs gs _).1 d]
    exact link_between (start_between O.pub p)
  | n + 2, hn, _, _, _, _ => absurd hn (by omega)

/-- **NO LINK IS OPEN BETWEEN THE LINKS**: at the cuts 0 and 1; in front of "laid" and of the first
hearing sub-protocol of every link; in front of the place "H:2"; behind the last link. -/
theorem shut_between (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R' : List Fmt.RoundView} {C C' : List VerifiableInference.Desc.OpenedColumn} {t : S}
    {k : Nat} (hk : k ≤ 1 ∨ (∃ l < 25, k = 14 * l + 1 ∨ k = 14 * l + 2) ∨ k = 339 ∨ k = 353)
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C')) :
    t.link? = none := by
  rcases hk with h | ⟨l, hl, rfl | rfl⟩ | rfl | rfl
  · exact front_shut O k h t R' C' f
  · rcases Nat.eq_zero_or_pos l with rfl | h0
    · exact front_shut O 1 (by omega) t R' C' f
    · obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
      refine cleared_shut hS hR O (l := j) (by omega) (p := p) (R := R) (C := C) (R' := R')
        (C' := C') ?_
      rw [if_neg (by omega : ¬ j = 24), show 14 * j + 15 + 0 = 14 * (j + 1) + 1 by omega]
      exact f
  · exact laid_shut hS hR O hl f
  · exact head_shut hS hR O 1 (by omega) t R' C' f
  · refine cleared_shut hS hR O (l := 24) (by omega) (p := p) (R := R) (C := C) (R' := R')
      (C' := C') ?_
    rw [if_pos rfl]
    exact f

/-- **AT EVERY BORDER OF LINK l < 25**, from in front of "laid" to in front of "cleared": of every
open link L: L.check.frame.group = l; L.check.group is that number by definition. (Where no link is
open nothing is said.) -/
theorem group_is1 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : ProofFile.InstPub} {R R' : List Fmt.RoundView} {C C' : List VerifiableInference.Desc.OpenedColumn} {t : S}
    {k : Nat} (h1 : 14 * l + 1 ≤ k) (h2 : k ≤ 14 * l + 14 + (if l = 24 then 2 else 0))
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C')) :
    ∀ L, t.link? = some L → L.check.group = l ∧ L.check.frame.group = l := by
  by_cases h0 : k = 14 * l + 1
  · intro L hL
    rw [shut_between hS hR O (Or.inr (Or.inl ⟨l, hl, Or.inl h0⟩)) f] at hL
    cases hL
  · exact group_is hS hR O hl (by omega) h2 f

end

/-- On a list of places: an entry that bears the link m stands at a number from 14 m + 1 to
14 m + 14, at m = 24 to 14 m + 16, and m < 25. A Boolean check, run by the kernel in
link_numbers. -/
def linkFit (ps : List Place) : Bool :=
  (List.range ps.length).all fun k =>
    match ps[k]? with
    | some p =>
      (match p.link with
       | some m => decide (m < 25) && decide (14 * m + 1 ≤ k) &&
          decide (k ≤ 14 * m + 14 + (if m = 24 then 2 else 0))
       | none => true)
    | none => true

set_option maxRecDepth 1000000 in
theorem link_numbers : linkFit IM.placesW = true := by decide +kernel

/-- The written list with a place of link m at number k. -/
def linkBentAt (k m : Nat) : List Place :=
  IM.placesW.take k ++ { chain := 1, link := some m, piece := 0, kind := .frame } ::
    IM.placesW.drop (k + 1)

set_option maxRecDepth 1000000 in
/-- Five negative tests: link 0 one number too early; link 23 one too late; link 24 one too early;
link 24 one too late; a link 25 at a number inside its own range. -/
theorem link_bent_fails : linkFit (linkBentAt 0 0) = false ∧ linkFit (linkBentAt 337 23) = false ∧
    linkFit (linkBentAt 336 24) = false ∧ linkFit (linkBentAt 353 24) = false ∧
    linkFit (linkBentAt 353 25) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the entry's own link the same form passes. -/
theorem link_bent_control : linkFit (linkBentAt 337 24) = true ∧
    linkFit (linkBentAt 336 23) = true := by decide +kernel

theorem link_number_at {k m : Nat} {p : Place} (hp : IM.placesW[k]? = some p)
    (hl : p.link = some m) :
    m < 25 ∧ 14 * m + 1 ≤ k ∧ k ≤ 14 * m + 14 + (if m = 24 then 2 else 0) := by
  have q := link_numbers
  unfold linkFit at q
  rw [List.all_eq_true] at q
  have q' := q k (List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1)
  simp only [hp, hl, Bool.and_eq_true, decide_eq_true_eq] at q'
  exact ⟨q'.1.1, q'.1.2, q'.2⟩

/-- **THE FIELD "groupIs", WHOLE, WITH ITS EXACT TYPE**, at ps := IM.placesW and groupAt := the
identity. General in Rch and at_, with one premise on Rch: what is reached is the return of a fold
over the flat list's first k entries from ProofFile.startS Z. The fence "no mark" is not spent. -/
theorem groupIs_field {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type}
    (Rch : Nat → X → Prop) (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → ∃ rs cols r q,
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (at_ a).1) rs cols = .ok ((at_ a).2, r, q)) :
    ∀ k a p m L, Rch k a → (at_ a).2.failed = none → IM.placesW[k]? = some p → p.link = some m →
      (at_ a).2.link? = some L → L.check.group = m ∧ L.check.frame.group = m :=
  fun k a _ _ L hr _ hp hl hL => by
    obtain ⟨rs, cols, r, q, f⟩ := hRch k a hr
    obtain ⟨h25, h1, h2⟩ := link_number_at hp hl
    exact group_is1 hS hR O h25 h1 h2 f L hL

#print axioms framesOf_between
#print axioms cleared_shut
#print axioms front_shut
#print axioms shut_between
#print axioms group_is1
#print axioms link_numbers
#print axioms link_bent_fails
#print axioms link_bent_control
#print axioms link_number_at
#print axioms groupIs_field

end Meaning.K2
