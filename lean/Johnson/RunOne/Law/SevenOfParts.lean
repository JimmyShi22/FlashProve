-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/SevenOfParts.lean: THE
SEVENTH CLAUSE OF WHAT IS ASKED OF ONE MEMBER OF A PROXIMITY TEST'S GROUP (MemberFacts,
Johnson/Desc/Sound/SeamMembers.lean), FROM ITS PARTS: "the word as sent" off the written oracle at
the member's tree IS the member's word off the plain strings of the frame's oracles. General: no key
file in it.

How: a member's word does not see the rest of the list of members (two calls of wordsOf_eq_symsW,
Johnson/Top/Fire/Code/CandBridge.lean); at the list of that one member the two frames meet
(wordsOf_is_strOf, Johnson/Desc/Sound/FramesMeet.lean), where "the seats fit" is asked at ONE seat;
the member's shape and number are those of the list's entry (hx): the types hang on both, so the
clause is an HEq.

Main names:
  seven_of_parts.

Object: MemberFacts' seventh clause, at m := D.mems.get j, book := D.book, Y := strsOf Fr y.
User: none yet (meant: the members' facts at the field r1_15).
Letters: cs, G, Fr, no, book, y · m, a seat of the test · x, a member of a sending · e0.
Premises: hx: the list's entry at the member is (m.sh, e0) · hF: the seats fit, at the list of that
one member · hS: every leaf of the member's word is shown · hI: SeatIs · hd: no listed depth of the
tree is beyond the told length.

Limits. One clause of seven. Called at no value. Nothing on soundness.

-/
import Johnson.Desc.Sound.FramesMeet
import Johnson.Top.Fire.Code.CandBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.SevenOfParts
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open H2K.First (Seat1)
open H2K.Pin (layOf)

/-- **The seventh clause, from its parts.** -/
theorem seven_of_parts (cs : Codes) {Xi : Type} (G : FileDescription Xi) (Fr : Frame) (no : ℕ → ℕ)
    (book : TreeBook) (y : Fr.E.Str) (m : Seat1) (x : Mem) (e0 : ℕ)
    (hx : x.1.l.get x.2 = (m.sh, e0))
    (hF : SeatFits G cs [x.1.l.get x.2] (fun _ => x.1.seat x.2))
    (hS : ShownAt G cs x.1.l x.1.seat (strsOf Fr y) x.2)
    (hI : ∀ o, G.oracleAt (x.1.seat x.2).1 = some o →
      SeatIs no book m (x.1.seat x.2).1 (x.1.seat x.2).2 o)
    (hd : ∀ o, G.oracleAt (x.1.seat x.2).1 = some o →
      ∀ e ∈ Fr.all, e.no = (x.1.seat x.2).1 → e.a ≤ o.logLength) :
    HEq (H2K.Pin.strOf cs m.sh e0 (layOf m) (W0 Fr no book y m.t).1 (W0 Fr no book y m.t).2)
      (Sound.wordsOf G cs x.1.l x.1.seat (strsOf Fr y) x.2) := by
  obtain ⟨⟨l, seat⟩, i⟩ := x
  have e1 := (LPFD.CandLaid.wordsOf_eq_symsW G cs l seat (strsOf Fr y) i).trans
    (LPFD.CandLaid.wordsOf_eq_symsW G cs [l.get i] (fun _ => seat i) (strsOf Fr y)
      ⟨0, Nat.zero_lt_one⟩).symm
  have e2 := wordsOf_is_strOf cs G [l.get i] (fun _ => seat i) Fr no book y ⟨0, Nat.zero_lt_one⟩ m
    hF hS hI hd
  have key : ∀ p : OracleShape × ℕ, p = (m.sh, e0) →
      HEq (H2K.Pin.strOf cs m.sh e0 (layOf m) (W0 Fr no book y m.t).1 (W0 Fr no book y m.t).2)
        (H2K.Pin.strOf cs p.1 p.2 (layOf m) (W0 Fr no book y m.t).1 (W0 Fr no book y m.t).2) := by
    rintro _ rfl
    exact HEq.rfl
  exact (key _ hx).trans (heq_of_eq (e1.trans e2).symm)

end Johnson.RunOne.Law.SevenOfParts

#print axioms Johnson.RunOne.Law.SevenOfParts.seven_of_parts
