-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AlikeHalf.lean: what the author of a kind has to prove of its two
lists of prover's sides, and how little that is where the second list's lists of parts are the
first's with other moves. Definitions, and lemmas with their proofs.

  1  `memberSteps_length`, `member_counted`, `frontLen`, `frontLen_succ`   a sub-protocol has as
     many rounds as it declares; the number of rounds before a sub-protocol
  2  `AtFront`, `StateBy.hears`, `half_of_re`, `idle_front`, `idle_plain`   the family that knows
     how many challenges are heard; a prover's side beside the side with other moves; the
     sub-protocols without a prover's side
  3  `LotAlike`, `firstOf_alike`   two lists of prover's sides; the first chain's sides

Limits.
  * One relation `T` between the two carried states, kept by hearing a challenge.
  * `RowTo` (hT of `half_of_re`; Honest/AlikeRow.lean) is stated through `MovesTo`
    (Honest/AlikeParts.lean): so it is asked at every value of the columns opened. `AtFront` asks
    that both states show the same columns.
  * `AtFront` counts from 0: it is for the first chain. At the second chain's start the challenges
    of the first and the shared chain are heard already: there `member_re` and `idle_plain`.
  * No pair of lists of sides is proved to meet `LotAlike` here.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.AlikeRow
import Johnson.Desc.ProofFile.Honest.AlikeLots
import Johnson.Desc.ProofFile.Honest.AlikeSelf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block)

variable {S Cl V W X X' : Type}

/-! ## 1 How many rounds -/

/-- A sub-protocol has as many rounds as it declares. -/
theorem memberSteps_length {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {b : Block S Cl} {hs : List (Placed V W X)} {l : List (Step W X)}
    (h : memberSteps B rows look v b hs = .ok l) :
    l.length = (b.rounds.zip b.oracles).length := by
  simp only [memberSteps] at h
  split at h
  · cases h
  rename_i hlen
  have hlen' : b.oracles.length = b.rounds.length := by simpa using hlen
  split at h
  · cases h
    rw [List.length_map]
  · rename_i g hg
    split at h
    · cases h
    rename_i hr
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    cases hc : lendRow B rows look b.place g.parts 0 with
    | error e => simp [hc, Except.mapError, Except.map] at h
    | ok c =>
      simp only [hc, Except.mapError, Except.map] at h
      cases h
      have h0 : g.rounds = b.rounds.length := by simpa using hr
      have e := congrArg List.length (Placed.steps_rows g b v c h0 hlen')
      rw [List.length_map, List.length_map] at e
      exact e

/-- A relation on a sub-protocol's rounds can be given the number of challenges heard. -/
theorem member_counted {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {b : Block S Cl} {hs : List (Placed V W X)} {hs' : List (Placed V W X')}
    {P Q : Mid W X → Mid W X' → Prop}
    (h : StrAlike (StepsAlike P Q) (memberSteps B rows look v b hs)
      (memberSteps B rows look v b hs')) (k : Nat) :
    StrAlike (StepsAlike (Cnt P k) (Cnt Q (k + (b.rounds.zip b.oracles).length)))
      (memberSteps B rows look v b hs) (memberSteps B rows look v b hs') := by
  cases hx : memberSteps B rows look v b hs with
  | error e =>
    rw [hx] at h
    cases hy : memberSteps B rows look v b hs' with
    | error e' =>
      rw [hy] at h
      exact h
    | ok l' =>
      rw [hy] at h
      exact False.elim h
  | ok l =>
    rw [hx] at h
    cases hy : memberSteps B rows look v b hs' with
    | error e' =>
      rw [hy] at h
      exact False.elim h
    | ok l' =>
      rw [hy] at h
      have q : StepsAlike P Q l l' := h
      rw [← memberSteps_length hx]
      exact q.counted k

/-- The number of rounds of the first `j` sub-protocols. -/
def frontLen (bs : List (Block S Cl)) (j : Nat) : Nat :=
  ((bs.take j).map fun b => (b.rounds.zip b.oracles).length).sum

theorem frontLen_succ {bs : List (Block S Cl)} {j : Nat} {b : Block S Cl} (h : bs[j]? = some b) :
    frontLen bs (j + 1) = frontLen bs j + (b.rounds.zip b.oracles).length := by
  unfold frontLen
  rw [List.take_add_one, h]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-! ## 2 The family of relations -/

/-- **The relation before sub-protocol number `j`**: the two runs are at the same challenges,
rounds shown and columns opened, their carried states are in `T`, and as many challenges are heard
as the sub-protocols before have rounds. -/
def AtFront (T : State W X → State W X' → Prop) (bs : List (Block S Cl)) (j : Nat) :
    Mid W X → Mid W X' → Prop :=
  Cnt (MidBy T) (frontLen bs j)

/-- Hearing a challenge keeps `StateBy r`: what `idle_front`, `idle_plain` and `quiet_rowTo`
(Honest/AlikeQuiet.lean) ask of `T`. -/
theorem StateBy.hears (r : X → X' → Prop) (t : State W X) (t' : State W X') (d : Fmt.Drawn)
    (q : StateBy r t t') : StateBy r (t.hears d) (t'.hears d) :=
  ⟨q.1, congrArg (· ++ [d]) q.2.1, q.2.2⟩

/-- **A prover's side beside the side with other moves.** -/
theorem half_of_re (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (bs : List (Block S Cl)) (T : State W X → State W X' → Prop)
    (h : Placed V W X) (R : ReRow X' h.parts) (hT : RowTo T h.parts R) :
    HalfAlike B rows look v bs (AtFront T bs) h ⟨h.place, reRow h.parts R⟩ :=
  ⟨rfl, fun j b hj hp => by
    have f1 : ([h].find? fun g => g.place == b.place) = some h := by
      simp only [List.find?_cons, hp]
    have f2 : ([(⟨h.place, reRow h.parts R⟩ : Placed V W X')].find? fun g => g.place == b.place) =
        some ⟨h.place, reRow h.parts R⟩ := by
      simp only [List.find?_cons, hp]
    have q := member_counted (member_re B rows look v b [h] [⟨h.place, reRow h.parts R⟩] T h R f1 f2
      hT) (frontLen bs j)
    unfold AtFront
    rw [frontLen_succ hj]
    exact q⟩

/-- The sub-protocols without a prover's side, under the family. `hT`: hearing a challenge keeps
`T`. -/
theorem idle_front (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (bs : List (Block S Cl)) (T : State W X → State W X' → Prop)
    (hT : ∀ t t' d, T t t' → T (t.hears d) (t'.hears d)) (j : Nat) (b : Block S Cl)
    (hj : bs[j]? = some b) :
    StrAlike (StepsAlike (AtFront T bs j) (AtFront T bs (j + 1)))
      (memberSteps B rows look v b ([] : List (Placed V W X)))
      (memberSteps B rows look v b ([] : List (Placed V W X'))) :=
  member_idle B rows look v b [] [] rfl rfl _ _ (fun k => Cnt (MidBy T) (frontLen bs j + k))
    (fun _ _ q => q)
    (fun k m m' d e cols q =>
      ⟨⟨congrArg (· ++ [d]) q.1.1,
        congrArg (fun s : Seen => (⟨s.rounds ++ [e], s.opened.map (· ++ cols)⟩ : Seen)) q.1.2.1,
        hT _ _ d q.1.2.2⟩, by
        show (m.st.heard ++ [d]).length = frontLen bs j + (k + 1)
        rw [List.length_append, q.2]
        rfl⟩)
    (fun _ _ q => by
      unfold AtFront
      rw [frontLen_succ hj]
      rw [Nat.zero_add] at q
      exact q)

/-- The same under the relation that does not count. -/
theorem idle_plain (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (T : State W X → State W X' → Prop)
    (hT : ∀ t t' d, T t t' → T (t.hears d) (t'.hears d)) (b : Block S Cl) :
    StrAlike (StepsAlike (MidBy T) (MidBy T))
      (memberSteps B rows look v b ([] : List (Placed V W X)))
      (memberSteps B rows look v b ([] : List (Placed V W X'))) :=
  member_idle B rows look v b [] [] rfl rfl _ _ (fun _ => MidBy T) (fun _ _ q => q)
    (fun _ _ _ d e cols q => ⟨congrArg (· ++ [d]) q.1,
      congrArg (fun s : Seen => (⟨s.rounds ++ [e], s.opened.map (· ++ cols)⟩ : Seen)) q.2.1,
      hT _ _ d q.2.2⟩)
    (fun _ _ q => q)

/-! ## 3 Lists of prover's sides -/

/-- **The hypothesis on two lists of prover's sides**, at a public part and a ground: their sides
are related one by one. -/
def LotAlike (R : Placed V W X → Placed V W X' → Prop) (Z : Pub) (G : Ground) (L : HLot V W X)
    (L' : HLot V W X') : Prop :=
  List.Forall₂ R (L.halves Z G) (L'.halves Z G)

theorem firstOf_alike {R : Placed V W X → Placed V W X' → Prop} {Z : Pub} {G : Ground}
    {ls : List (HLot V W X)} {ls' : List (HLot V W X')}
    (h : List.Forall₂ (LotAlike R Z G) ls ls') :
    List.Forall₂ R (firstOf Z G ls) (firstOf Z G ls') := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons L L' l l' hL _ ih =>
    show List.Forall₂ R (L.halves Z G ++ firstOf Z G l) (L'.halves Z G ++ firstOf Z G l')
    exact List.rel_append hL ih

end ProofFile.Honest

#print axioms ProofFile.Honest.memberSteps_length
#print axioms ProofFile.Honest.member_counted
#print axioms ProofFile.Honest.StateBy.hears
#print axioms ProofFile.Honest.half_of_re
#print axioms ProofFile.Honest.idle_front
#print axioms ProofFile.Honest.idle_plain
#print axioms ProofFile.Honest.firstOf_alike
#print axioms ProofFile.Honest.frontLen_succ
#print axioms ProofFile.Honest.frontLen
#print axioms ProofFile.Honest.AtFront
#print axioms ProofFile.Honest.LotAlike
