-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/PubAtLaterCall.lean: THE CALL: THE
FIELD pub OF FillL (KeepAtLater.lean) AT A LATER PLACE OF KIND K1, at a meaning
whose pub is pubAll D base (the composed meaning's is: mgAll_pub): seven public items are paid by
the two files beneath; every other item is one binder. A statement with its proof.

OBJECT. Any block B over the carried record with KeepsKeeper B (PubAtLaterKeeper.lean),
LaterSend P B (PubAtLaterIndex.lean) and two declared rounds; members of the first two:
laterAt (a link's digits) and IM.k1Reads (a link's reads).
USER. hPub_at (Johnson/Desc/K1/Law/CallsG.lean) calls it, at N := D.N, links := linksFull,
ps := flatPlacesOf linksFull true, k := noL l d, P := parL Z G l d, B := blkL Z G l d X arrs,
t := momL d, by cases on d.
LETTERS. D, base, Mg, links, ps, k, P, B, l, t.
Main names:
  sevenItem   ledger · freeAbove · unheard · indexIs · indexThere · formsIn · formsInT
  inAt_pub    the promise in front, unmarked, holds every public item that is open there
  inAt_book   and the clause on the book
  hPub_of     **the call**
PAID: ledger | freeAbove | unheard: pub_keeper_later · indexIs | indexThere: pub_indexIs_later |
pub_indexThere_later · formsIn: pub_formsIn_later_plan, its premises on the book off the promise in
front, its test on the plan's seats off hP (the row's laterSeatsB) · formsInT: pub_formsInT_later.
PREMISES THAT STAY, BY NAME.
  hMg    Mg.pub = pubAll D base.
  hP     the row's own premise on the plan's numbers, at N := D.N.
  hseg   ON THE TABLE: a formsIn that is open in front of the place is the place's own segment's.
  hRd    ON THE LETTER D.Rd: what a reader gave in front it gives behind (ReadersStay), at the runs
         of a formsIn | formsInT that is open in front.
  hrest  EVERY OTHER PUBLIC ITEM that is open in front and behind: the items without a layer
         (lookIn · lookOut · linkFresh · leftOn · hasRow) and the door's named items among them.
IS IT EMPTY HERE? That the block says yes inside the promise is not shown. By a
look at the table formsInT is open on both sides of none of the fifty places, and formsIn at the
digits' alone: these arms are idle there.
What is not claimed. Nothing on pubP. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.PubAtLaterKeeper
import Johnson.Desc.K1.Law.PubAtLaterIndex
import Johnson.Desc.Tidy.Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers PubData pubAll)
open VerifiableInference.Desc.K13.Law (openAt)

variable {Pp W : Type}

/-- The seven public items whose keeping over a later sending is through Lean. -/
def sevenItem : Pub → Bool
  | .ledger _ => true
  | .freeAbove _ => true
  | .unheard => true
  | .indexIs => true
  | .indexThere => true
  | .formsIn _ _ _ => true
  | .formsInT _ _ _ => true
  | _ => false

/-- The promise in front, unmarked, holds every public item that is open there. -/
theorem inAt_pub {N : Numbers} {Mg : Meaning Pp W} {links : List ModelPart} {ps : List Place} {k : ℕ}
    {x : Pp × S} {y : Strs} (h : InAt N Mg links ps k x y) (q : Pub)
    (hq : q ∈ (First.pubSets Mg.more links ps)[k]?.getD [] ++
      First.pubOfItems (openAt links ps k)) : Mg.pub q x = true := by
  obtain ⟨⟨_, hr⟩, hm⟩ := h
  rcases hr with hx | ⟨h1, _, _, _⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨_, c5⟩, _⟩ := h1
    unfold First.pubHeld at c5
    exact List.all_eq_true.1 c5 q hq

/-- It holds the clause on the book: a place for just the statement's messages; the plan's number
of trees. -/
theorem inAt_book {N : Numbers} {Mg : Meaning Pp W} {links : List ModelPart} {ps : List Place} {k : ℕ}
    {x : Pp × S} {y : Strs} (h : InAt N Mg links ps k x y) :
    x.2.book.place.size = x.2.st.oracles.size ∧ x.2.book.trees.size = N.treesAt ps[k]? := by
  obtain ⟨⟨_, hr⟩, hm⟩ := h
  rcases hr with hx | ⟨h1, _, _, _⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at h1
    obtain ⟨_, c6⟩ := h1
    unfold First.bookAt at c6
    simp only [Bool.and_eq_true, beq_iff_eq] at c6
    exact ⟨c6.1.2, c6.1.1⟩

/-- **THE CALL: the field pub of FillL at a later place**, at a meaning whose pub is pubAll D base:
the seven items are paid; hrest: every other item. -/
theorem hPub_of (D : PubData) (base : Pub → Pp × S → Bool) (Mg : Meaning Pp W)
    (hMg : Mg.pub = pubAll D base) (links : List ModelPart) (ps : List Place) (k : ℕ) (P : Par)
    (B : Block S Unit) (hK : KeepsKeeper B) (hS : LaterSend P B) (h2 : B.rounds.length = 2)
    (l t : ℕ) (ht : t < 3) (hP : laterSeatsB D.N P l t (D.N.treesAt ps[k]?) = true)
    (hseg : ∀ m j r, Pub.formsIn m j r ∈ (First.pubSets Mg.more links ps)[k]?.getD [] ++
      First.pubOfItems (openAt links ps k) → m = l)
    (hRd : ∀ x x' y m j r, YesOf B x x' → InAt D.N Mg links ps k x y →
      (Pub.formsIn m j r ∈ (First.pubSets Mg.more links ps)[k]?.getD [] ++
          First.pubOfItems (openAt links ps k) ∨
        Pub.formsInT m j r ∈ (First.pubSets Mg.more links ps)[k]?.getD [] ++
          First.pubOfItems (openAt links ps k)) → ReadersStay D m j r x.2 x'.2)
    (hrest : ∀ x x' y q, YesOf B x x' → InAt D.N Mg links ps k x y →
      q ∈ (First.pubSets Mg.more links ps)[k]?.getD [] ++ First.pubOfItems (openAt links ps k) →
      q ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] ++
        First.pubOfItems (openAt links ps (k + 1)) → sevenItem q = false → Mg.pub q x' = true) :
    ∀ x x' y q, YesOf B x x' → InAt D.N Mg links ps k x y →
      q ∈ (First.pubSets Mg.more links ps)[k]?.getD [] ++ First.pubOfItems (openAt links ps k) →
      q ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] ++
        First.pubOfItems (openAt links ps (k + 1)) → Mg.pub q x' = true := by
  intro x x' y q hy hIn hq hq'
  have h0 := inAt_pub hIn q hq
  obtain ⟨hb, hT⟩ := inAt_book hIn
  have hy' := hy
  obtain ⟨_, rs, gs, hfit, hd⟩ := hy'
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, h2]
  cases q with
  | ledger m =>
    rw [hMg] at h0 ⊢
    exact pub_keeper_later hK D base _ rfl x x' hy h0
  | freeAbove m =>
    rw [hMg] at h0 ⊢
    exact pub_keeper_later hK D base _ rfl x x' hy h0
  | unheard =>
    rw [hMg] at h0 ⊢
    exact pub_keeper_later hK D base _ rfl x x' hy h0
  | indexIs =>
    rw [hMg] at h0 ⊢
    exact pub_indexIs_later hS D base x x' _ gs hlen hd h0
  | indexThere =>
    rw [hMg] at h0 ⊢
    exact pub_indexThere_later hS D base x x' _ gs hlen hd h0
  | formsIn m j r =>
    have e := hseg m j r hq
    rw [hMg] at h0 ⊢
    exact pub_formsIn_later_plan hS D base x x' _ gs hlen hd m j r
      (hRd x x' y m j r hy hIn (Or.inl hq)) t _ ht hb hT (by rw [e]; exact hP) h0
  | formsInT m j r =>
    rw [hMg] at h0 ⊢
    exact pub_formsInT_later hS D base x x' _ gs hlen hd m j r
      (hRd x x' y m j r hy hIn (Or.inr hq)) h0
  | _ => exact hrest x x' y _ hy hIn hq hq' rfl

end VerifiableInference.Desc.K1
