-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR: (K-P2), THE THIRD OF THE FIVE: `ExchangeS` (Honest/Thread/PaysS.lean) AT THE TWO BORDERS OF THE KEY FILE's
  FIRST THREAD AT WHICH A LOOKUP STANDS, NUMBERS 4 AND 10, CUT DOWN TO WHAT THE ROW MAKES ANEW. The sister of
  `exchangeS_of_anew₁` (E2E/KeyRowsLater.lean), which does this at numbers 5, 11 and 14.

E2E/Lookup/Key/LookupExchangeOfTheNewItemsAtTheKey.lean. Three definitions and four theorems with their proofs. The row at
a lookup owes six items. Three it reads and leaves, and these are owed again when the table is read forward: `.pinT`,
`.pin 0`, `.pin 1`. Three it makes anew: `.forms l "objects"`, `.worth l "planes"`, `.worth l "keys"`.

  `lookupContextItems`, `lookupNewItems l`: the two halves of what the row owes
  `lookupNumberAtBorder b`: which lookup stands at a border: 0 at 4, else 1
  `lookupOwesSplit`: the rows at 4 and 10 owe just these, and the first half is open in front and plain: by evaluation
  `lookupContextRidesAcrossAtTheKey`: what the first half says in front it says wherever `LookupKeeps s s'`, at any list
      of played rounds added
  **`lookupExchangeOfTheNewItemsAtTheKey`**: `ExchangeS` at 4 and 10 from the second half alone
  `lookupNewItemsUnfoldedAtTheKey`: what the second half says at the thread, written out

By what. The honest sentences of the three pins (`holdsH`, E2E/KeyRest.lean) do not read the oracles' strings at all, so
that `E.add` cannot turn them; `fwd_at` (E2E/KeyRides.lean) carries them under `ridesBehindTheLookupsStep`. `owed_again`
(E2E/KeyOwedAgain.lean) takes them across the step. `holdsH` at `.forms` and `.worth` is the library's sentence unturned.

Limits. The hypothesis of `lookupExchangeOfTheNewItemsAtTheKey` is the whole content of the debt: that the three new items
hold is not shown here. It is true also where the thread stands at nothing.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import E2E.Lookup.Key.LookupBehindAndRidesPastAtTheKey
import E2E.KeyOwedAgain

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.Lookup.Key
open VerifiableInference.Desc.Key (KItem Xi FirstState Source LaterPlaces)
open AtPublicFiles.KeyThread
open ProofFile.Honest

/-! ## 1 The two halves of what the row owes -/

/-- **What the row at a lookup reads and leaves**: owed again. -/
def lookupContextItems : List KItem := [.pinT, .pin 0, .pin 1]

/-- **What the row at lookup l makes anew.** -/
def lookupNewItems (l : Nat) : List KItem :=
  [.forms l "objects", .worth l "planes", .worth l "keys"]

/-- Which lookup stands at a border of the two. -/
def lookupNumberAtBorder (b : Nat) : Nat := if b = 4 then 0 else 1

theorem lookupOwesSplit : ∀ b ∈ [4, 10],
    (∀ i ∈ (rowsFirst b).owes, i ∈ lookupNewItems (lookupNumberAtBorder b) ∨
      i ∈ lookupContextItems) ∧
      ∀ i ∈ lookupContextItems,
        i ∈ fwdOpen (VerifiableInference.Desc.Key.start₁ 2) rowsFirst b ∧
          VerifiableInference.Desc.Key.plain i = true := by
  decide

/-- A member of the list of what the row makes anew is one of its three. -/
theorem memberOfLookupNewItems {l : Nat} {i : KItem} (listed : i ∈ lookupNewItems l) :
    i = KItem.forms l "objects" ∨ i = KItem.worth l "planes" ∨ i = KItem.worth l "keys" := by
  simpa only [lookupNewItems, List.mem_cons, List.not_mem_nil, or_false] using listed

variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (source : Source) (numbers : H2U.PlaceNums)
  (later : LaterPlaces) (filling : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tables : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {files : VerifierAndGoals.PublicFiles}

/-! ## 2 What is owed again -/

/-- **What the row reads and leaves says behind the lookup's step what it said in front.** -/
theorem lookupContextRidesAcrossAtTheKey (reads : Johnson.RunOne.KeyRows1.ReadsL filling.base.h₁) :
    ∀ i ∈ lookupContextItems, ∀ k s (m : Mid (Local W₀ Rc Xi Unit) X') E s' ps v, LookupKeeps s s' →
      (laid₁ source numbers later filling w₀ rc x halves tables).means m.st.input i
        ((laid₁ source numbers later filling w₀ rc x halves tables).seat k m s)
        ((laid₁ source numbers later filling w₀ rc x halves tables).strs E) v →
      (laid₁ source numbers later filling w₀ rc x halves tables).means m.st.input i
        ((laid₁ source numbers later filling w₀ rc x halves tables).seat k m s')
        ((laid₁ source numbers later filling w₀ rc x halves tables).strs (E.add ps)) v := by
  intro i listed k s m E s' ps v keeps holds
  obtain ⟨heard, ledger, rfl⟩ := keeps
  have plainItem : VerifiableInference.Desc.Key.plain i = true := by
    simp only [lookupContextItems, List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl <;> rfl
  exact fwd_at (D source numbers later) filling.base.h₁ Johnson.RunOne.KeyRows23.atSix filling.meetsT
    (one₀ source) filling.R i plainItem _ s _ _ _ v
    (ridesBehindTheLookupsStep _ _ (Johnson.RunOne.KeyRows1.ReadsL.readsD _ reads) [i] _ s heard
      ledger) holds

/-! ## 3 The exchange -/

/-- **`ExchangeS` at the two lookups is owed for what the row makes anew alone.** -/
theorem lookupExchangeOfTheNewItemsAtTheKey
    (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true)
    (reads : Johnson.RunOne.KeyRows1.ReadsL filling.base.h₁)
    (said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop) : ∀ b ∈ [4, 10],
    (∀ blk, (laid₁ source numbers later filling w₀ rc x halves tables).bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (laid₁ source numbers later filling w₀ rc x halves tables) said b k s m E →
      drawsFit blk.rounds ds = true →
      (laid₁ source numbers later filling w₀ rc x halves tables).Stepped blk k s m E ds y cols s' →
      (laid₁ source numbers later filling w₀ rc x halves tables).Items
        (lookupNewItems (lookupNumberAtBorder b)) k s' y.2 (E.add y.1)) →
    ExchangeS (laid₁ source numbers later filling w₀ rc x halves tables) said b := by
  intro b atLookup new blk found k s m E ds y cols s' thread fits stepped more i owed
  rcases (lookupOwesSplit b atLookup).1 i owed with fresh | context
  · exact new blk found k s m E ds y cols s' thread fits stepped more i fresh
  · exact owed_again (laid₁ source numbers later filling w₀ rc x halves tables) thread.1 stepped
      lookupContextItems (fun j listed => ((lookupOwesSplit b atLookup).2 j listed).1)
      (fun j listed v holds =>
        lookupContextRidesAcrossAtTheKey source numbers later filling w₀ rc x reads j listed k s m E
          s' y.1 v
          (lookupStepKeepsAtTheKey source numbers later filling w₀ rc x sourced scope b atLookup blk
            found k s m E ds y cols s' stepped) holds)
      more i context

/-! ## 4 What the three new items say -/

/-- **The three new items at the thread, written out**: at every continuation of the challenges, the
library's own sentences at what the thread is handed, the oracles' strings and the witness. -/
theorem lookupNewItemsUnfoldedAtTheKey (l : Nat) (k : Coins Bk) (s' : FirstState)
    (mid : Mid (Local W₀ Rc Xi Unit) X') (env : Env) :
    (laid₁ source numbers later filling w₀ rc x halves tables).Items (lookupNewItems l) k s' mid env ↔
      ∀ ds,
        (Johnson.RunOne.KeyRows1.meaning₁At (one₀ source) filling.R).forms l "objects"
            (mid.st.input.x, s') (Env.strs filling.item (srcAt 0 6 11) env)
            (filling.wit k mid.st.input.w₀ mid.st.input.rc (mid.st.heard ++ ds) []) ∧
          (Johnson.RunOne.KeyRows1.meaning₁At (one₀ source) filling.R).worth l "planes"
            (mid.st.input.x, s') (Env.strs filling.item (srcAt 0 6 11) env)
            (filling.wit k mid.st.input.w₀ mid.st.input.rc (mid.st.heard ++ ds) []) ∧
          (Johnson.RunOne.KeyRows1.meaning₁At (one₀ source) filling.R).worth l "keys"
            (mid.st.input.x, s') (Env.strs filling.item (srcAt 0 6 11) env)
            (filling.wit k mid.st.input.w₀ mid.st.input.rc (mid.st.heard ++ ds) []) := by
  constructor
  · intro items ds
    exact ⟨items ds (KItem.forms l "objects") (List.mem_cons_self ..),
      items ds (KItem.worth l "planes") (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      items ds (KItem.worth l "keys")
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩
  · intro said ds i listed
    rcases memberOfLookupNewItems listed with rfl | rfl | rfl
    · exact (said ds).1
    · exact (said ds).2.1
    · exact (said ds).2.2

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.lookupOwesSplit
#print axioms AtPublicFiles.Lookup.Key.lookupContextRidesAcrossAtTheKey
#print axioms AtPublicFiles.Lookup.Key.lookupExchangeOfTheNewItemsAtTheKey
#print axioms AtPublicFiles.Lookup.Key.lookupNewItemsUnfoldedAtTheKey
