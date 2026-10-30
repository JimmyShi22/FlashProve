--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeySources.lean: THE SECOND SUB-PROTOCOL OF THE KEY FILE's THIRD CHAIN ("the taken trees'
sources") ACCEPTS, IN SCOPE, WHERE FOUR TREES' NUMBERS IN THE STATE's BOOK ARE 0, 5, 1, 5. It has no
round and no part of a prover. It compares the numbers of the trees that the own proximity test
reads and this chain has not sent (the own group's members', then the mask's) with the sources that
the own test's declared rounds name. Statements and proofs; one closed line is evaluated by the
kernel. One step of the verifier's: NOTHING IS SHOWN OF ANY PROVER: no completeness, nothing on what
a view shows.

The library's `Third.Law.Tied own s` (Johnson/Desc/Third/Law/Sources.lean) is just what that
sub-protocol asks. It has a half on the state (the list of numbers is there) and a half that
compares this list with public values (the declared rounds).

What is shown.
  `tiedB rounds ts`: the second half as one test with code. `tied_of_B`: the two halves give `Tied`.
  `mapM_some_map`, **`takenOf_of_nums`**: THE FIRST HALF, FROM THE BOOK: where the own group is G
    and every member of G, and the mask, has a place in the book and a tree there with the number
    `num i`: the list is there, and is written out.
  **`ownRounds_full`**: IN SCOPE THE OWN TEST's DECLARED ROUNDS ARE THE LIBRARY's CLOSED ONES
    (`dsOf piKWFull`): under `KeySourced` (E2E/KeyPublic.lean) and `VerifierAndGoals.InScope Z`: by the
    library's
    `rounds_at_key_W` (Johnson/Loose/H2K12/RoundsAtKeySeats.lean), with each of its five premises
    paid: the sized key and the setting are the written values (`key_in_scope`, `set_in_scope`);
    what
    `laterPlaces` returns (`KeySourced`); the description's test on its rounds (`KeyNamed`); its
    rounds are the written ones (the test "its rounds are not the written ones" among those that
    `KeyNamed` holds, through `pinned_is_seat` and `seat_in_scope_key`).
  `takenFull`: the list [(0, 0), (0, 5), (1, 1), (0, 5)]: the index-mask message's tree is number 0
    of the first chain; W's, number 5 of it; Omega's, number 1 of the shared chain; the mask lies in
    W's.
  **`tiedB_full`**: the second half accepts at the closed rounds and that list: BY THE KERNEL.
    `tiedB_teeth`: negative tests: it rejects three other lists there. `toySources_member`: a state
    whose list is `takenFull`: a toy.
  **`tied_in_scope`**, **`takenSources_in_scope`**: so, in scope, where the state's list is
    `takenFull`: `Tied` holds, and the sub-protocol accepts and hands the state on as it is.

Limits.
- That a run's state in front has that list is not shown: `takenOf_of_nums` says from what: the own
  group's members, the mask's number, Omega's number, the places and the trees' numbers in the book.
  The library's test on this chain's book-keeping holds the first three and nothing of the book's
  places and numbers.
- In scope alone: at the full size's public files.



-/
import E2E.KeyPublic
import Johnson.Loose.H2K12.RoundsAtKeySeats
import Johnson.RunOne.Law.K12Facts15Z
import Johnson.Desc.Key.PinnedAtO

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open OnBytes
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Third (S₃ takenOf opensTaken takenSources)
open VerifiableInference.Desc.Third.Law (Tied)
open H2K.Member (piKWFull dsOf)
open VerifierAndGoals (PublicFiles)

/-- The half of `Tied` that compares the list with the declared rounds, as one test with code. -/
def tiedB (rounds : List Fmt.DeclaredRound) (ts : List (Nat × Nat)) : Bool :=
  (ts.all fun x => opensTaken rounds x.1 x.2) &&
    (rounds.flatMap (·.opens)).all fun o =>
      match o.2 with
      | .own _ => true
      | .taken c n => ts.contains (c, n)

/-- The two halves give `Tied`. -/
theorem tied_of_B {Cl : Type} (own : Block S₃ Cl) (s : S₃) (ts : List (Nat × Nat))
    (h1 : takenOf s = some ts) (h2 : tiedB own.rounds ts = true) : Tied own s := by
  obtain ⟨a, b⟩ := Bool.and_eq_true_iff.1 h2
  exact ⟨ts, h1, a, b⟩

theorem mapM_some_map {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => by simp
  | a :: l, h => by
    rw [List.mapM_cons, h a (List.mem_cons_self ..),
      mapM_some_map f g l fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- **The list is there, and what it is**, from the book. -/
theorem takenOf_of_nums (s : S₃) (G : OnBytes.Group) (num : Nat → Nat)
    (hG : s.st.groups[s.loc.own]? = some G)
    (h : ∀ i ∈ G.members.toList ++ s.loc.mask.toList, ∃ q t, s.book.place[i]? = some q ∧
      s.book.trees[q.1]? = some t ∧ t.number = num i) :
    takenOf s = some ((G.members.toList ++ s.loc.mask.toList).map fun i =>
      (if i == s.loc.omega then 1 else 0, num i)) := by
  unfold takenOf
  rw [hG]
  refine mapM_some_map _ _ _ fun i hi => ?_
  obtain ⟨q, t, h1, h2, h3⟩ := h i hi
  rw [h1]
  show ((s.book.trees[q.1]?).map fun t => _) = _
  rw [h2, ← h3]
  rfl

/-- **In scope the own test's declared rounds are the library's closed ones.** -/
theorem ownRounds_full {Z : PublicFiles} {X : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
    {P : VerifiableInference.Desc.Key.LaterPlaces} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true) :
    (VerifiableInference.Desc.Key.ownTest P).rounds = dsOf piKWFull := by
  obtain ⟨X₀, m, h0, hm, hX, -, hP⟩ := hs.source
  obtain ⟨X₁, m₁, h0', hm', -, hl⟩ := hs.named.named
  obtain rfl : X₀ = X₁ := Except.ok.inj (h0.symm.trans h0')
  obtain rfl : m = m₁ := Except.ok.inj (hm.symm.trans hm')
  have hR := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0
  have hk := Johnson.RunOne.Law.KeyInScope.key_in_scope scope hR hm
  have hset : m.p.chains.made.sized.set = H2K.Member.setAt :=
    (Johnson.RunOne.Law.K12Facts15.set_in_scope scope hR hm).trans (by decide +kernel)
  have hpinAt : VerifiableInference.PlanWritten.pinnedKeyAt m (keyFileDescription X N P) = true :=
    hl ("its rounds are not the written ones", _)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hpin : VerifiableInference.PlanWritten.seatPinnedKey Z.pol (keyFileDescription X N P) = true :=
    (VerifiableInference.Desc.Key.pinned_is_seat _
      (VerifiableInference.PlanWritten.publicOfO_scan h0) hm).symm.trans hpinAt
  have hW := (VerifiableInference.PlanWritten.seat_in_scope_key _ _ Z scope hpin).1
  have e1 := (H2K.JointK.seat_rounds ⟨3, none, 2, .K12⟩ P.W
    (H2K.JointK.keyPlan_W X N P hs.named.plan)).1
  have e2 := H2K.JointK.rounds_at_key_W hk hset hP X N hs.named.plan hW
  rw [e2, H2K.Member.rounds_KWFull] at e1
  exact (Option.some.inj e1).symm

/-- The four trees: (1 for Omega's, 0 for every other; the tree's number). -/
def takenFull : List (Nat × Nat) := [(0, 0), (0, 5), (1, 1), (0, 5)]

/-- **The second half accepts at the closed rounds and that list**: by the kernel. -/
theorem tiedB_full : tiedB (dsOf piKWFull) takenFull = true := by decide +kernel

/-- **Negative tests**: the second half rejects, at the closed rounds, a list with another number
for W's tree; a list that lacks Omega's tree; a list with Omega's tree marked as the first chain's.
-/
theorem tiedB_teeth : tiedB (dsOf piKWFull) [(0, 0), (0, 4), (1, 1), (0, 4)] = false ∧
    tiedB (dsOf piKWFull) [(0, 0), (0, 5), (0, 5)] = false ∧
    tiedB (dsOf piKWFull) [(0, 0), (0, 5), (0, 1), (0, 5)] = false := by decide +kernel

/-- A state whose list is that one: three members, a mask in the second member's tree. A toy: no
message, no code. -/
def toySources : S₃ :=
  { st := { groups := #[{ code := 0, members := #[0, 1, 2] }] }
    book :=
      { trees := #[{ shape := {}, number := 0 }, { shape := {}, number := 5 },
          { shape := {}, number := 1 }]
        place := #[(0, 0), (1, 0), (2, 0), (1, 1)] }
    roots := 0
    loc := { w := 1, own := 0, mask := some 3, border := none, omega := 2, firstTree := 0 } }

/-- **A member** of the premise on the state. -/
theorem toySources_member : takenOf toySources = some takenFull := by decide +kernel

/-- **In scope, where the state's list is that one, the sources are tied.** -/
theorem tied_in_scope {Z : PublicFiles} {X : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
    {P : VerifiableInference.Desc.Key.LaterPlaces} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true) (s : S₃) (h : takenOf s = some takenFull) :
    Tied (VerifiableInference.Desc.Key.ownTest P) s :=
  tied_of_B _ s takenFull h (by rw [ownRounds_full hs scope]; exact tiedB_full)

/-- **So the sub-protocol accepts and hands the state on as it is.** -/
theorem takenSources_in_scope {Z : PublicFiles} {X : VerifiableInference.Desc.Key.Source}
    {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true) (s : S₃) (h : takenOf s = some takenFull)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (takenSources (VerifiableInference.Desc.Key.ownTest P)).decide s rs gs = .ok s :=
  takenSources_passes _ s rs gs (tied_in_scope hs scope s h)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.tied_of_B
#print axioms AtPublicFiles.AtFiles.mapM_some_map
#print axioms AtPublicFiles.AtFiles.takenOf_of_nums
#print axioms AtPublicFiles.AtFiles.ownRounds_full
#print axioms AtPublicFiles.AtFiles.tiedB_full
#print axioms AtPublicFiles.AtFiles.tiedB_teeth
#print axioms AtPublicFiles.AtFiles.toySources_member
#print axioms AtPublicFiles.AtFiles.tied_in_scope
#print axioms AtPublicFiles.AtFiles.takenSources_in_scope
