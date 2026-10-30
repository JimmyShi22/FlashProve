--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Member/Uses.lean: four uses of the statements on the member at a lot's
place (Johnson/Desc/ProofFile/Honest/Member/AtLot.lean): the three places behind the last segment at
which kind K13's three lots supply the sub-protocol (they are of the kinds K13, K1 and `frame`),
where nothing is laid behind it, and kind K7's place, a segment's first. One definition, and
statements with their proofs.
Main names:
  `k13Own`: kind K13's sub-protocol at "M:3" as its lot supplies it (a definition; that it is the
    lot's own is shown by `rfl` where it is used).
  `k13_m3_alone`, `k13_m4_alone`: at `onlineDescription` a member at "M:3", and one at "M:4", is the lot's
    sub-protocol wrapped alone: so `alone_gives` hands out its fields, its decision and its step.
  `k13_m3_decides`, `k13_m4_decides`: their decisions, as equivalences, with the wrapping's two
    tests.
  `k13_at_m3`, `k13_at_m4`, `k13_at_end`: the statements `K13AtM3`, `K13AtM4`, `K13AtEnd` of
    Statement.lean: the two tests hold there of themselves: where the lot's sub-protocol accepts
    from a state without a mark of failure, the member accepts, with the same state. By `atM3_rec`,
    `atM3_failed`, `atM4_rec` (Johnson/Desc/K13/Law/AtRecord.lean); that the lot of "M:4" has W's
    commitment: `IM.back_of` (Johnson/IMR/BackSeat.lean).
  `k7_steps`: the statement `K7Steps`: the step of the member at kind K7's place accepts just where
    the lot's sub-protocol's step accepts with a state without a mark, if the segment's row of
    `framesOf` hands the state on as it is.

What is not claimed. That `onlineDescription` returns at any three files. That a member stands at any of the
places. In `k13_m4_alone` and `k13_m4_decides`, that the lot has W's commitment w is a premise
(`k13_at_m4` has it from the library). The premise of `k7_steps` on the segment's row: the library
concludes it only for the release's parameters, only at the hash `OnBytes.secondHashFunction`, and for segment
24 alone (`IM.k7_sits`, Johnson/IMR/FirstSeats.lean). Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.Honest.Member.AtLot
import Johnson.IMR.FrontSeat
import Johnson.IMR.FirstSeats
import Johnson.Desc.K13.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.AtPlace
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (atM3 atM4 whereOf wBlock)

variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub} {Bs : PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}

/-- Kind K13's sub-protocol at "M:3" as its lot supplies it. -/
def k13Own (Z : Pub) : Block S Unit :=
  { atM3 (whereOf Z) with
    planOk := (atM3 (Cl := Unit) (whereOf Z)).planOk &&
      (VerifiableInference.Desc.K13.fromOf? Z).isSome }

/-- A member at "M:3" is the lot's sub-protocol wrapped alone. -/
theorem k13_m3_alone (O : IM.Open o pol lay KL F Z Bs base c A B) {m : Block S Cl}
    (hm : m ∈ c.blocksInOrder) (hp : m.place = ⟨1, none, 3, .K13⟩) :
    ∃ x, AsFlat x m ∧ IM.LaidAlone sameReply x (k13Own Z).retype m.name ⟨1, none, 3, .K13⟩ :=
  member_alone o pol lay KL F Z Bs base c A B O _ (IM.k13_in_seat Z) (k13Own Z).retype
    (List.mem_append_left _ (List.mem_map.2 ⟨k13Own Z, List.mem_singleton.2 rfl, rfl⟩))
    (by show KindName.K13 ≠ KindName.frame; decide) (Or.inl rfl) m hm hp

/-- **The decision of a member at "M:3".** -/
theorem k13_m3_decides (O : IM.Open o pol lay KL F Z Bs base c A B) {m : Block S Cl}
    (hm : m ∈ c.blocksInOrder) (hp : m.place = ⟨1, none, 3, .K13⟩) (t t' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    m.decide t rs gs = .ok t' ↔
      (atM3 (Cl := Unit) (whereOf Z)).decide t rs gs = .ok t' ∧ t'.failed = none ∧
        sameReply t t' = true := by
  obtain ⟨x, hF, hA⟩ := k13_m3_alone O hm hp
  rw [(alone_gives sameReply x m _ _ _ hF hA).2.2.2.2.2.1 t t' rs gs]
  have h7 : ¬ KindName.K13 = KindName.K7 := by decide
  exact ⟨fun u => ⟨u.1, u.2.1, u.2.2.resolve_left h7⟩, fun u => ⟨u.1, u.2.1, Or.inr u.2.2⟩⟩

/-- **`K13AtM3`**: the wrapping's two tests hold at "M:3" of themselves. -/
theorem k13_at_m3 : K13AtM3 := by
  intro o pol lay KL F Z Bs base c A B O m hm hp t t' rs gs h0 hd
  refine (k13_m3_decides O hm hp t t' rs gs).2 ⟨hd, ?_, ?_⟩
  · rw [VerifiableInference.Desc.K13.Law.atM3_failed hd]
    exact h0
  · obtain ⟨_, _, _, _, rfl⟩ := VerifiableInference.Desc.K13.Law.atM3_rec hd
    exact IM.sameReply_self _

/-- A member at "M:4" is the lot's sub-protocol wrapped alone. w: W's commitment, as the lot takes
it. -/
theorem k13_m4_alone (O : IM.Open o pol lay KL F Z Bs base c A B) {w : Block S Unit}
    (hw : wBlock Z = some w) {m : Block S Cl} (hm : m ∈ c.blocksInOrder)
    (hp : m.place = ⟨1, none, 4, .K1⟩) :
    ∃ x, AsFlat x m ∧
      IM.LaidAlone sameReply x (atM4 (whereOf Z) w).retype m.name ⟨1, none, 4, .K1⟩ := by
  have hL : VerifiableInference.Desc.K13.lot4 Z ∈ onlineFirstChainBlockTables Z := by
    unfold onlineFirstChainBlockTables
    simp
  have hown : atM4 (whereOf Z) w ∈ (VerifiableInference.Desc.K13.lot4 Z).own Bs.G₀ := by
    show _ ∈ (wBlock Z).toList.map (atM4 (whereOf Z))
    rw [hw]
    exact List.mem_singleton.2 rfl
  have hb : ((atM4 (whereOf Z) w).retype : Block S Cl) ∈
      (VerifiableInference.Desc.K13.lot4 Z).blocks Bs.G₀ :=
    List.mem_append_left _ (List.mem_map.2 ⟨_, hown, rfl⟩)
  have hp' : ((atM4 (whereOf Z) w).retype : Block S Cl).place = ⟨1, none, 4, .K1⟩ := by
    unfold wBlock VerifiableInference.Desc.K1.wAt at hw
    obtain ⟨msg, _, rfl⟩ := Option.map_eq_some_iff.1 hw
    rfl
  have h := member_alone o pol lay KL F Z Bs base c A B O _ hL _ hb
    (by rw [hp']; decide) (Or.inl (by rw [hp'])) m hm (by rw [hp']; exact hp)
  rw [hp'] at h
  exact h

/-- **The decision of a member at "M:4".** -/
theorem k13_m4_decides (O : IM.Open o pol lay KL F Z Bs base c A B) {w : Block S Unit}
    (hw : wBlock Z = some w) {m : Block S Cl} (hm : m ∈ c.blocksInOrder)
    (hp : m.place = ⟨1, none, 4, .K1⟩) (t t' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    m.decide t rs gs = .ok t' ↔
      (atM4 (whereOf Z) w).decide t rs gs = .ok t' ∧ t'.failed = none ∧
        sameReply t t' = true := by
  obtain ⟨x, hF, hA⟩ := k13_m4_alone O hw hm hp
  rw [(alone_gives sameReply x m _ _ _ hF hA).2.2.2.2.2.1 t t' rs gs]
  have h7 : ¬ KindName.K1 = KindName.K7 := by decide
  exact ⟨fun u => ⟨u.1, u.2.1, u.2.2.resolve_left h7⟩, fun u => ⟨u.1, u.2.1, Or.inr u.2.2⟩⟩

/-- **`K13AtM4`**: the lot has W's commitment (`IM.back_of`), and the wrapping's two tests hold at
"M:4" of themselves. -/
theorem k13_at_m4 : K13AtM4 := by
  intro o pol lay KL F Z Bs base c A B O
  obtain ⟨_, _, _, _, _, w, _, _, hw, _⟩ := IM.back_of O
  obtain ⟨P', rfl⟩ : ∃ P', w = VerifiableInference.Desc.K1.sendAtS P' := by
    have h := hw
    unfold wBlock VerifiableInference.Desc.K1.wAt at h
    obtain ⟨msg, _, e⟩ := Option.map_eq_some_iff.1 h
    exact ⟨_, e.symm⟩
  refine ⟨P', hw, fun m hm hp t t' r₁ r₂ gs h0 hd => ?_⟩
  obtain ⟨_, _, hf, ho, _⟩ := VerifiableInference.Desc.K13.Law.atM4_rec hd
  refine (k13_m4_decides O hw hm hp t t' [r₁, r₂] gs).2 ⟨hd, by rw [hf]; exact h0, ?_⟩
  show (t.out.reply == t'.out.reply) = true
  rw [ho]
  exact beq_self_eq_true _

/-- **`K13AtEnd`**: the last sub-protocol hands the state on as it is, so the wrapping's two tests
hold there of themselves. -/
theorem k13_at_end : K13AtEnd := by
  intro o pol lay KL F Z Bs base c A B O m hm hp t t' rs gs h0 hd
  obtain ⟨hF, hA⟩ := member_last o pol lay KL F Z Bs base c A B O m hm hp
  have e : t' = t := by
    have hd' : ((VerifiableInference.Desc.ChainEnd.refuse
        (VerifiableInference.Desc.First.endAsks t)).map fun _ => t) = .ok t' := hd
    cases hr : VerifiableInference.Desc.ChainEnd.refuse
        (VerifiableInference.Desc.First.endAsks t) with
    | error x =>
      rw [hr] at hd'
      cases hd'
    | ok u =>
      rw [hr] at hd'
      exact (Except.ok.inj hd').symm
  subst e
  exact ((alone_gives sameReply c.last m _ _ _ hF hA).2.2.2.2.2.1 t' t' rs gs).2
    ⟨hd, h0, Or.inr (IM.sameReply_self _)⟩

/-- **`K7Steps`**: the step of a member at kind K7's place. -/
theorem k7_steps : K7Steps := by
  intro o pol lay KL F Z Bs base c A B O l hopen L hL b hbL hb m hm hp ft t t' k rs cols
  have hJ := member_first o pol lay KL F Z Bs base c A B O l .K7 L hL b hbL hb (by decide) m hm hp
  obtain ⟨fs, f, hfs, hf, _, _, _, _, hs⟩ := joined_gives Z l m m b b.place (Or.inl rfl) hJ
  rw [hs ft t t' k rs cols, hopen fs f hfs hf]
  constructor
  · rintro ⟨u, a1, _, a3, a4, _, _⟩
    obtain rfl : u = t' := Except.ok.inj a3
    exact ⟨a1, a4⟩
  · rintro ⟨a1, a2⟩
    exact ⟨t', a1, a2, rfl, a2, IM.sameReply_self _, Or.inl (by rw [hb])⟩

end ProofFile.Honest.AtPlace

#print axioms ProofFile.Honest.AtPlace.k13_m3_alone
#print axioms ProofFile.Honest.AtPlace.k13_m3_decides
#print axioms ProofFile.Honest.AtPlace.k13_at_m3
#print axioms ProofFile.Honest.AtPlace.k13_m4_alone
#print axioms ProofFile.Honest.AtPlace.k13_m4_decides
#print axioms ProofFile.Honest.AtPlace.k13_at_m4
#print axioms ProofFile.Honest.AtPlace.k13_at_end
#print axioms ProofFile.Honest.AtPlace.k7_steps
