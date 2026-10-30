-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/MemberYes.lean: the last composition: from what
Honest/K3/Law/Joined.lean says of the sub-protocol that the lookups' lot states to the same of the
description's own member at the lookup's place. Conditional on `JoinedAt` at the lot's sub-protocol
and on no mark in front of the lookup. Theorems.

Terms. Honest/K3/GLOSSARY.md ("description", "lot", "mark", "member", "step", "sub-protocol").
`JoinedAt` is defined in Joined.lean.

What is shown.
  `renamed_step`: a sub-protocol's step reads no name.
  `steps_member`: the frame's steps of a half read of a sub-protocol its name, place, rounds and
    oracle messages alone.
  `step_decide`: an acceptance by a sub-protocol's step is an acceptance by its decision, at some
    rounds and groups. (The library has that statement under the same short name:
    Johnson/Desc/ChainEndFold.lean.)
  `reply_of_step`, `lot_stated`, `lot_reply`: the reply as in front: from the acceptance of the own
    step of the lot's sub-protocol.
  `joinedAt_member`, the general form: `JoinedAt` at a sub-protocol b under the member's name gives
    `JoinedAt` at the member m, where m has b's place, rounds and oracle messages, m's step accepts
    just where b's accepts with no mark behind it and the reply as in front, every acceptance by b's
    step leaves the reply as in front, and the sentence Q behind the step gives "no mark".
  `joinedAt_site`, at a proof file's description: all but "no mark" is shown: by
    Honest/K3/Law/MemberAtSite.lean and `lot_reply`.
  `member_plain` (also for the sentence of `joined_look`), `member_digits`, `member_head`: at the
    four sentences Q of the four cases of Joined.lean: "no mark" from no mark in front (a
    hypothesis: `s.failed = none`).

Hypotheses that remain.
  `JoinedAt` at the lot's sub-protocol, which is itself conditional (the head of Joined.lean).
  No mark in front of the lookup (`hs0`): this is for a caller that walks the chain to show.
  In `joinedAt_member`: `hp`, `hr`, `ho`: m has b's place, rounds and oracle messages; `hstep`,
    `hrep`, `hQ`: the three sentences on the two steps and on Q that its item above tells. In
    `joinedAt_site` and the last three: `O`, `hb`, `hm`, `hp`: the description returns; b is one of
    the lot's sub-protocols; m is a member of the first chain's flat list, at b's place.
  `h`, `hb`, `H`: (in `step_decide`, `reply_of_step`, `lot_stated`, `lot_reply`) the step accepts; b
    is one of the lot's (in `lot_stated` the membership bears the letter `h`); `DecidesFrom`. `H`:
    (in `joinedAt_member`, `joinedAt_site` and the last three) `JoinedAt` at the lot's sub-protocol
    under the member's name.

How the proof goes. Why not through the member's `decide`: what is known of the member's decision is
when it accepts; that it decides without reading a sealed digest would be an equation of rejections
too. The member's step is known as an "if and only if" on acceptance; and the frame's play reads of
a sub-protocol nothing but four public fields.

Users. This file is imported by Honest/K3/Law/MemberOne.lean and Honest/K3/Law/StatedAtLot.lean
[not in this library].

Limits. The four last theorems assume the conclusions of the cases: they are not composed here with
the cases' own hypotheses. They are composed case by case in Honest/K3/Law/MemberYesAt.lean
[not in this library] and, as one, in
`member_one` (Honest/K3/Law/MemberOne.lean). No instance of these hypotheses is exhibited in this
file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Joined
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberAtSite
import Johnson.Desc.ProofFile.Honest.K3.Law.StatedReply

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc (Block Chain FileDescription Place OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV)

local notation "FS" => VerifiableInference.Desc.First.S

variable {V₁ W₁ X₁ W : Type}

/-- A sub-protocol's step reads no name. -/
theorem renamed_step {Cl : Type} (b : Block FS Cl) (n : String) (ft : Nat) (s : FS)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    ({ b with name := n } : Block FS Cl).step ft s rs cols = b.step ft s rs cols := rfl

/-- The frame's steps of a half at two sub-protocols of one name, place, rounds and oracle messages
are the same. -/
theorem steps_member {Cl : Type} (h : Placed V₁ W₁ X₁) (b m : Block FS Cl) (v : Option V₁)
    (c : RowCoins h.parts) (hp : m.place = b.place) (hr : m.rounds = b.rounds)
    (ho : m.oracles = b.oracles) :
    h.steps m v c = h.steps ({ b with name := m.name } : Block FS Cl) v c := by
  show rowSteps m.name m.place v _ 0 (m.rounds.zip m.oracles) c =
    rowSteps m.name b.place v _ 0 (b.rounds.zip b.oracles) c
  rw [hp, hr, ho]

/-- An acceptance by a sub-protocol's step is an acceptance by its decision, at some rounds and
groups. Conditional on that acceptance. rs' and gs are bound by "∃" and held by what functions
return at them alone: some values: not said to be the step's own. -/
theorem step_decide {Cl : Type} (b : Block FS Cl) (ft : Nat) (s s' : FS) (k : Nat)
    (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (h : b.step ft s rs cols = .ok (s', k)) :
    ∃ rs' gs, b.decide s rs' gs = .ok s' := by
  unfold Block.step at h
  simp only [VerifiableInference.Desc.need, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, _⟩ := h
       exact ⟨_, _, by assumption⟩)
    | cases h

/-- **The reply as in front, from the acceptance of the sub-protocol's own step.** Conditional on
that acceptance. -/
theorem reply_of_step {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public} {a : Place}
    {b : Block FS Cl} {q : Bool} (H : DecidesFrom claim X a b q) (ft : Nat) (s s' : FS) (k : Nat)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (h : b.step ft s rs cols = .ok (s', k)) :
    ProofFile.sameReply s s' = true := by
  obtain ⟨rs', gs, hd⟩ := step_decide b ft s s' k rs cols h
  have e := stated_out H s s' rs' gs hd
  unfold ProofFile.sameReply
  rw [e]
  simp

/-- A sub-protocol of the lookups' lot is the stated sub-protocol at some place. (That the place is
an address of the lot's list is not in the statement: `lot_block_at`, Honest/K3/Law/LotMember.lean,
has the membership.) -/
theorem lot_stated (Z : Pub) (G : Ground) (b : Block FS ProofFile.Cl) (h : b ∈ (K3Lot.lot Z).blocks G) :
    ∃ x : Nat × Bool × Place, VerifiableInference.Desc.K3.theStated K3Lot.ofForm
      (K3Lot.readersAt Z.p.X) Z.p.X Z.first.codes Z.first.shape x.2.2 = some b := by
  rw [lot_blocks] at h
  unfold K3Lot.hear at h
  obtain ⟨x, _, hb⟩ := List.mem_filterMap.1 h
  exact ⟨x, hb⟩

/-- **Every acceptance by the step of a sub-protocol of the lookups' lot leaves the reply as in
front.** Conditional on that acceptance. -/
theorem lot_reply (Z : Pub) (G : Ground) (b : Block FS ProofFile.Cl) (hb : b ∈ (K3Lot.lot Z).blocks G)
    (ft : Nat) (s s' : FS) (k : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (h : b.step ft s rs cols = .ok (s', k)) : ProofFile.sameReply s s' = true := by
  obtain ⟨x, hx⟩ := lot_stated Z G b hb
  exact reply_of_step (theStated_decides _ _ _ _ _ _ b hx) ft s s' k rs cols h

/-- **From the lot's sub-protocol to the member, in general.** Conditional on `JoinedAt` at b under
m's name; on m having b's place, rounds and oracle messages; on m's step accepting just where b's
accepts, no mark stands behind it and the reply is as in front; on every acceptance by b's step
leaving the reply as in front; and on Q giving "no mark". No instance of these hypotheses is
exhibited in this file. -/
theorem joinedAt_member (b m : Block FS ProofFile.Cl) (a : At) (J : LookJobs W) (wit : W₁ → W)
    (v : Option V₁) (mid : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts) (first : Nat)
    (s : FS) (F : Fork) (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (Q : FS → HeardV → Fork → Prop)
    (hp : m.place = b.place) (hr : m.rounds = b.rounds) (ho : m.oracles = b.oracles)
    (hstep : ∀ (ft : Nat) (t t' : FS) (k : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn),
      m.step ft t rs cols = .ok (t', k) ↔
        b.step ft t rs cols = .ok (t', k) ∧ t'.failed = none ∧ ProofFile.sameReply t t' = true)
    (hrep : ∀ (ft : Nat) (t t' : FS) (k : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn),
      b.step ft t rs cols = .ok (t', k) → ProofFile.sameReply t t' = true)
    (hQ : ∀ s' g G, Q s' g G → s'.failed = none)
    (H : JoinedAt ({ b with name := m.name } : Block FS ProofFile.Cl) a J wit v mid ds c first s F chain
      ft
      stored tree Q) :
    JoinedAt m a J wit v mid ds c first s F chain ft stored tree Q := by
  obtain ⟨y, s', g, G, h1, h2, h3, h4, h5, h6, h7, h8⟩ := H
  have h5' : b.step ft s (roundsOf y.1) [] = .ok (s', 0) := h5
  refine ⟨y, s', g, G, ?_, h2, h3, ?_,
    (hstep ft s s' 0 _ []).2 ⟨h5', hQ s' g G h7, hrep ft s s' 0 _ [] h5'⟩, h6, h7, h8⟩
  · rw [steps_member _ b m v c hp hr ho]
    exact h1
  · rw [hr]
    exact h4

/-- **At a proof file's description**: b: a sub-protocol of the lookups' lot; m: the member of the
first chain's flat list at b's place. Conditional on the description's return (`IM.Open`), on
`JoinedAt` at b under m's name, and on Q giving "no mark". No instance of these hypotheses is
exhibited in this file. -/
theorem joinedAt_site (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (b m : Block FS ProofFile.Cl)
    (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀) (hm : m ∈ ch.blocksInOrder) (hp : m.place = b.place) (a : At)
    (J : LookJobs W) (wit : W₁ → W) (v : Option V₁) (mid : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts) (first : Nat)
    (s : FS) (F : Fork) (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (Q : FS → HeardV → Fork → Prop)
    (hQ : ∀ s' g G, Q s' g G → s'.failed = none)
    (H : JoinedAt ({ b with name := m.name } : Block FS ProofFile.Cl) a J wit v mid ds c first s F chain
      ft
      stored tree Q) :
    JoinedAt m a J wit v mid ds c first s F chain ft stored tree Q := by
  obtain ⟨_, hr, ho, _, hstep⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O b hb m hm hp
  exact joinedAt_member b m a J wit v mid ds c first s F chain ft stored tree Q hp hr ho hstep
    (lot_reply Z Bs.G₀ b hb) hQ H

/-! ## At the four sentences of the four cases -/

section Fillings
variable (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub) (Bs : PureBase)
  (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat) (B : SecondSeat)
  (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (b m : Block FS ProofFile.Cl)
  (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀) (hm : m ∈ ch.blocksInOrder) (hp : m.place = b.place) (a : At)
  (J : LookJobs W) (wit : W₁ → W) (v : Option V₁) (mid : Mid W₁ X₁) (ds : List Fmt.Drawn)
  (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts) (first : Nat)
  (s : FS) (F : Fork) (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
  (tree : Fmt.TreeSource → Option (Place × Table)) (hs0 : s.failed = none)
include O hb hm hp hs0

/-- **Where nothing stands behind the lookup, and behind a layers' link's calls**: the sentence of
`joined_plain` and of `joined_look`, at any seat. Conditional on the description's return, on that
case's conclusion at the lot's sub-protocol under the member's name, and on no mark in front.
No instance of these hypotheses is exhibited in this file. -/
theorem member_plain (seat : VerifiableInference.Desc.K3.Seat FS ProofFile.Cl)
    (h : OnBytes.Model.Forest.Shape)
    (H : JoinedAt ({ b with name := m.name } : Block FS ProofFile.Cl) a J wit v mid ds c first s F chain
      ft
      stored tree fun s' g G => ∃ g', VerifiableInference.Desc.K3.toHeard h
        (VerifiableInference.Desc.K3.toHeardG g) = some g' ∧ seat.heard s' = some g' ∧
        seat.fork s' = some G ∧ s'.failed = s.failed) :
    JoinedAt m a J wit v mid ds c first s F chain ft stored tree fun s' g G =>
      ∃ g', VerifiableInference.Desc.K3.toHeard h (VerifiableInference.Desc.K3.toHeardG g) =
        some g' ∧
        seat.heard s' = some g' ∧ seat.fork s' = some G ∧ s'.failed = s.failed :=
  joinedAt_site o pol lay KL Fd Z Bs base ch A B O b m hb hm hp a J wit v mid ds c first s F chain
    ft
    stored tree _ (fun _ _ _ ⟨_, _, _, _, hf⟩ => hf.trans hs0) H

/-- **Behind the digits of a layers' or an attention link**: the sentence of `joined_digits`.
Conditional on the same three. No instance of these hypotheses is exhibited in this file. s' is
bound by "∃": some state of the verifier's between two steps, held by what readers return of it;
there is no equation on it. -/
theorem member_digits (claim : Aff → ProofFile.Cl) (h : OnBytes.Model.Forest.Shape) (claims : Nat)
    (H : JoinedAt ({ b with name := m.name } : Block FS ProofFile.Cl) a J wit v mid ds c first s F chain
      ft
      stored tree fun t g G => ∃ g' s', VerifiableInference.Desc.K3.toHeard h
        (VerifiableInference.Desc.K3.toHeardG g) = some g' ∧
        t = s'.putFork { G with planClaimsF := claims } ∧
        (VerifiableInference.Desc.K3.seatDigits claim).heard s' = some g' ∧ s'.failed = s.failed) :
    JoinedAt m a J wit v mid ds c first s F chain ft stored tree fun t g G =>
      ∃ g' s', VerifiableInference.Desc.K3.toHeard h (VerifiableInference.Desc.K3.toHeardG g) =
        some g' ∧
        t = s'.putFork { G with planClaimsF := claims } ∧
        (VerifiableInference.Desc.K3.seatDigits claim).heard s' = some g' ∧ s'.failed = s.failed :=
  joinedAt_site o pol lay KL Fd Z Bs base ch A B O b m hb hm hp a J wit v mid ds c first s F chain
    ft
    stored tree _
    (fun _ _ _ ⟨_, s', _, ht, _, hf⟩ => by rw [ht, putFork_failed, hf, hs0]) H

/-- **Behind the digits of the head's link**: the sentence of `joined_head`. Conditional on the same
three (that case is itself conditional on `HeadBehind`). No instance of these hypotheses is
exhibited in this file. s' is bound by "∃": some state of the verifier's between two steps, held by
what readers return of it; there is no equation on it. -/
theorem member_head (claim : Aff → ProofFile.Cl) (X : OnBytes.Model.Verify.Public)
    (h : OnBytes.Model.Forest.Shape)
    (H : JoinedAt ({ b with name := m.name } : Block FS ProofFile.Cl) a J wit v mid ds c first s F chain
      ft
      stored tree fun t g G => ∃ g' s', VerifiableInference.Desc.K3.toHeard h
        (VerifiableInference.Desc.K3.toHeardG g) = some g' ∧
        (VerifiableInference.Desc.K3.seatDigits claim).heard s' = some g' ∧
        (VerifiableInference.Desc.K3.seatDigits claim).fork s' = some G ∧ s'.failed = s.failed ∧
        HeadBehind X s' t) :
    JoinedAt m a J wit v mid ds c first s F chain ft stored tree fun t g G =>
      ∃ g' s', VerifiableInference.Desc.K3.toHeard h (VerifiableInference.Desc.K3.toHeardG g) =
        some g' ∧
        (VerifiableInference.Desc.K3.seatDigits claim).heard s' = some g' ∧
        (VerifiableInference.Desc.K3.seatDigits claim).fork s' = some G ∧ s'.failed = s.failed ∧
        HeadBehind X s' t :=
  joinedAt_site o pol lay KL Fd Z Bs base ch A B O b m hb hm hp a J wit v mid ds c first s F chain
    ft
    stored tree _
    (fun t _ _ ⟨_, s', _, _, _, hf, hh⟩ => by rw [(head_keeps X s' t hh).2, hf, hs0]) H

end Fillings

#print axioms ProofFile.Honest.K3.Law.renamed_step
#print axioms ProofFile.Honest.K3.Law.steps_member
#print axioms ProofFile.Honest.K3.Law.step_decide
#print axioms ProofFile.Honest.K3.Law.reply_of_step
#print axioms ProofFile.Honest.K3.Law.lot_stated
#print axioms ProofFile.Honest.K3.Law.lot_reply
#print axioms ProofFile.Honest.K3.Law.joinedAt_member
#print axioms ProofFile.Honest.K3.Law.joinedAt_site
#print axioms ProofFile.Honest.K3.Law.member_plain
#print axioms ProofFile.Honest.K3.Law.member_digits
#print axioms ProofFile.Honest.K3.Law.member_head

end ProofFile.Honest.K3.Law
