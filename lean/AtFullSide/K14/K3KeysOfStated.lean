-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/K3KeysOfStated.lean: THE FIRST PREMISE OF fits_of_stated
(AtFullSide/K14/K3FitsOfStated.lean), AN EQUATION OF LISTS OF A BOOK's ENTRIES, FROM AN EQUATION OF
LISTS OF KEYS OF THE FRAME's STRETCHES (Want, Honest/BookEntries.lean). General in the stretches, in
the rest of the entries and in the list of places; nothing is evaluated. A structure, four
definitions with code, statements with their proofs.

WHY. An entry's name is runName of the message's name, the spender and the use (Want.entry); the
lookups' sumName and endName (Honest/K3/Row.lean) are runName maskRowRun of the part's address and
"sum" or "ends". So whoever compares keys (spender, use, the message's name, owner and base, number,
count) need build no name: the names agree by keys_block, a lemma. And the frame's Ahead has no
decidable equality, its Want has. (WantKey is a structure, not a product: for a product of seven
Lean's search finds no decidable equality.)

Limits.
  * IT SAYS NOTHING OF ANY BOOK UNTIL hW AND hr ARE SHOWN OF THAT BOOK's STRETCHES AND OTHER
    ENTRIES. No file shows them.
  * keyEntry is Want.entry's text written once more at a key: entry_of_key holds the two together,
    by rfl.
  * Numbers and addresses on public data: nothing on soundness, completeness or hiding.

  WantKey, wantKey   what a stretch's entry is made of
  keyEntry, entry_of_key   the entry of a key; a stretch's entry is its key's
  K3At.keys, k3Keys   the keys of the runs that the parts state: none at a stage without a call;
                  "sum"; and "ends" where the call has end values
  keys_block, keys_stated   **the keys' entries are the stated runs** (K3At.block, k3Stated)
  stated_of_wants   **where the stretches whose spender stands at one of the places have the stated
                  keys, in that order, and no other entry names such a place: the law's hE**

No option is raised. What is assumed. Nothing beside each statement's own premises.
-/
import AtFullSide.K14.K3FitsOfStated
import Johnson.Desc.ProofFile.Honest.BookEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Place)

/-- What a stretch's entry is made of. -/
structure WantKey where
  spender : Addr
  use : String
  /-- the message's name, owner and base -/
  name : String
  owner : Addr
  base : Due
  /-- the number of the first mask entry -/
  number : Nat
  count : Nat
  deriving DecidableEq

/-- A stretch's key. -/
def wantKey (w : Want) : WantKey :=
  ⟨w.spender, w.use, w.msg.name, w.msg.owner, w.msg.base, w.number, w.count⟩

/-- The book's entry, of a key: the text of Want.entry (Honest/BookEntries.lean). -/
def keyEntry (k : WantKey) : Ahead :=
  ⟨runName k.name k.spender k.use, k.owner, k.base.plus ⟨0, k.number⟩, ⟨0, k.count⟩, k.spender,
    true⟩

/-- A stretch's entry is its key's. -/
theorem entry_of_key (w : Want) : w.entry = keyEntry (wantKey w) := rfl

/-- The keys of the runs that the part of one stage states: none where the stage has no call; "sum";
and "ends" where the call has end values. -/
def K3At.keys (s : K3At) (x : Stage × Nat) : List WantKey :=
  match x.1.call s.at_.face with
  | none => []
  | some k =>
    ⟨⟨s.at_.place, x.2⟩, "sum", maskRowRun, s.o, s.base,
        s.first + firstSlot s.at_.face x.1, ownRun k⟩ ::
      match k.ends with
      | none => []
      | some e => [⟨⟨s.at_.place, x.2⟩, "ends", maskRowRun, s.o, s.base,
          s.first + firstSlot s.at_.face x.1 + x.1.own s.at_.face, e.n⟩]

/-- All sites' keys, site by site, stage by stage. -/
def k3Keys (S : List K3At) : List WantKey :=
  S.flatMap fun s => (stages s.at_.face).zipIdx.flatMap s.keys

/-- A stage's keys' entries are its block. -/
theorem keys_block (s : K3At) (x : Stage × Nat) : (s.keys x).map keyEntry = s.block x := by
  unfold K3At.keys K3At.block runsAt
  cases hc : x.1.call s.at_.face with
  | none => rfl
  | some k =>
    cases he : k.ends with
    | none =>
      simp only [runsOf, he, endRuns]
      rfl
    | some e =>
      simp only [runsOf, he, endRuns]
      rfl

/-- **The keys' entries are the stated runs.** -/
theorem keys_stated (S : List K3At) : (k3Keys S).map keyEntry = k3Stated S := by
  unfold k3Keys k3Stated K3At.stated
  rw [List.map_flatMap]
  refine List.flatMap_congr fun s _ => ?_
  rw [List.map_flatMap]
  exact List.flatMap_congr fun x _ => keys_block s x

/-- **From the stretches' keys to the law's first premise**: where the stretches whose spender
stands at a site's place have the stated keys, and no entry of the rest names such a place. -/
theorem stated_of_wants {ws : List Want} {rest : List Ahead} {S : List K3At}
    (hW : (ws.filter fun w => S.any fun s => s.at_.place == w.spender.place).map wantKey =
      k3Keys S)
    (hr : rest.all (fun e => !S.any fun s => s.at_.place == e.spender.place) = true) :
    (ws.map (·.entry) ++ rest).filter (fun e => S.any fun s => s.at_.place == e.spender.place) =
      k3Stated S := by
  have h2 : rest.filter (fun e => S.any fun s => s.at_.place == e.spender.place) = [] :=
    List.filter_eq_nil_iff.2 fun e he hq => by
      have h3 := List.all_eq_true.1 hr e he
      rw [hq] at h3
      cases h3
  rw [List.filter_append, h2, List.append_nil, List.filter_map, ← keys_stated S, ← hW,
    List.map_map]
  rfl

end AtFullSide.K14

#print axioms AtFullSide.K14.entry_of_key
#print axioms AtFullSide.K14.keys_block
#print axioms AtFullSide.K14.keys_stated
#print axioms AtFullSide.K14.stated_of_wants
