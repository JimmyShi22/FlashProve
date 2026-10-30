-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/PaysByTriples.lean: the closing of a segment (K10): the entries that the book lays for a part to carry, by name and count,
are one naming function mapped over a list of triples (the sender's address, the message's number in its sending, its count
of coins); so is what the closing's part states. So the two lists of names and counts agree wherever the triples agree, and
no name has to be evaluated. General lemmas on lists; nothing is evaluated here.

  `Dg`, `dg`          what `segmentCarriesAt` (Johnson/Desc/ProofFile/Honest/BookCarryKit.lean) reads of a message: the link's
                     number in its label, two flags, its round, and the triple
  `pickAt`           the text of `segmentCarriesAt` on such rows, with the finder of the fold behind a round as a letter
  `nameAt`           the naming function at a part's address
  `carries_named`    the book's side · `closeCarries_named`   the part's side
  `pickAt_congr`     `pickAt` reads the finder at the rounds of the fresh tables under a link's label alone

Limits. Lists alone: names, addresses, counts. Nothing on the value of a coin.
-/
import Johnson.Desc.ProofFile.Honest.BookCarryKit
import Johnson.Desc.ProofFile.Honest.K10.Half

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10
open VerifiableInference.Desc.First.Close (Par)

/-- What is read of a message. -/
structure Dg where
  link : Option Nat
  fresh : Bool
  masks : Bool
  round : Nat
  b : Borne
  deriving DecidableEq

def dg (m : SentMsg) : Dg := ⟨linkOf m.label, m.fresh, m.masks, m.round, ⟨m.sender, m.j, m.count⟩⟩

/-- The text of `segmentCarriesAt` on such rows. bf: the fold behind a round, and the part that
sends what it leaves. -/
def pickAt (bf : Nat → Option (Addr × Addr)) (ds : List Dg) (a : Addr) : List Borne :=
  (ds.filter fun m => m.fresh && m.link.isSome).flatMap fun f =>
    match bf f.round, f.link with
    | some (p, q), some l =>
      (if p == a then (ds.filter fun m => !m.masks && (m.link.any fun j =>
          decide (j < l) || (j == l && !m.fresh))).map (·.b) else []) ++
      (if q == a then (ds.filter fun m => !m.masks && (m.link.any fun j =>
          decide (j ≤ l))).map (·.b) else [])
    | _, _ => []

/-- The name and the count under which the part at `a` carries a message. -/
def nameAt (a : Addr) (t : Borne) : String × Due := (carriedName t.sender t.msg a, t.count)

theorem flatMap_ext {α β : Type} {f g : α → List β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.Mem.head _),
      flatMap_ext l fun x hx => h x (List.Mem.tail _ hx)]

/-- One filter's messages, carried and named. -/
theorem pick_map (ms : List SentMsg) (F : Dg → Bool) (a : Addr) :
    ((ms.filter fun m => F (dg m)).map (·.carry a)).map Ahead.named =
      (((ms.map dg).filter F).map (·.b)).map (nameAt a) := by
  rw [List.filter_map, List.map_map, List.map_map, List.map_map]
  rfl

/-- **The book's side.** -/
theorem carries_named (here : List PlanB) (ms : List SentMsg) (a : Addr) :
    (segmentCarriesAt here ms a).map Ahead.named =
      (pickAt (behindFold here) (ms.map dg) a).map (nameAt a) := by
  unfold segmentCarriesAt pickAt
  rw [List.map_flatMap, List.map_flatMap, List.filter_map, List.flatMap_map]
  refine flatMap_ext _ fun f _ => ?_
  show (match behindFold here f.round, linkOf f.label with
    | some (p, q), some l => _
    | _, _ => []).map Ahead.named = (match behindFold here f.round, linkOf f.label with
    | some (p, q), some l => _
    | _, _ => []).map (nameAt a)
  generalize behindFold here f.round = o₁
  generalize linkOf f.label = o₂
  rcases o₁ with _ | ⟨p, q⟩
  · rfl
  · rcases o₂ with _ | l
    · rfl
    · show ((if p == a then _ else []) ++ (if q == a then _ else [])).map Ahead.named =
        ((if p == a then _ else []) ++ (if q == a then _ else [])).map (nameAt a)
      rw [List.map_append, List.map_append]
      congr 1
      · split
        · exact pick_map ms (fun m => !m.masks && (m.link.any fun j =>
            decide (j < l) || (j == l && !m.fresh))) a
        · rfl
      · split
        · exact pick_map ms (fun m => !m.masks && (m.link.any fun j => decide (j ≤ l))) a
        · rfl

/-- **The part's side.** -/
theorem closeCarries_named (P : Par) (borne : List Borne) :
    closeCarries ⟨P, borne⟩ = borne.map (nameAt (closeAddr P)) := rfl

/-- `pickAt` reads the finder at the rounds of the fresh tables under a link's label alone. -/
theorem pickAt_congr {bf bf' : Nat → Option (Addr × Addr)} {ds : List Dg} (a : Addr)
    (h : ∀ f ∈ ds, f.fresh = true → f.link.isSome = true → bf f.round = bf' f.round) :
    pickAt bf ds a = pickAt bf' ds a := by
  unfold pickAt
  refine flatMap_ext _ fun f hf => ?_
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hf
  obtain ⟨h3, h4⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  rw [h f h1 h3 h4]

end AtFullSide.K10

#print axioms AtFullSide.K10.flatMap_ext
#print axioms AtFullSide.K10.pick_map
#print axioms AtFullSide.K10.carries_named
#print axioms AtFullSide.K10.closeCarries_named
#print axioms AtFullSide.K10.pickAt_congr
