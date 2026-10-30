-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClosingSame.lean: the kind "the code switch" (K2): THE CLOSING
(`closingFrom`, Honest/K2/Closing.lean) AT ANOTHER FUNCTION OF OWN DATA, MORE STRETCHES AND MORE
CHALLENGES; AND WHEN THE OWN DATA (`ownBy`, Honest/K2/AtPlan.lean) IS THE SAME AT TWO LISTS OF
CHALLENGES. Six statements with their proofs; no definition.

  `at_of_take`      a filling's one call hangs on the challenges only through their first
                    `heardAt` many
  `take_of_prefix`  the first n of a list are the first n of its beginning, where that has n
  `at_of_prefix`    so: the same at a list of challenges and at a beginning of it that is long
                    enough
  `ownBy_of_prefix`   the like of `ownBy` at one segment and message
  `closingFrom_own`   the closing is the same at two functions of own data that agree at the
                    segments' numbers
  `closingFrom_grows`   ALL THREE AT ONCE: `closingFrom_le` (Honest/K2/Law/ClosingGrows.lean) behind
                    `closingFrom_own`

Limits. On texts: no sentence on what a stretch or an element of data holds. That the own data agree
at the segments' numbers, as functions, is a premise of the last two: `ownBy_of_prefix` pays it at
one segment and message where the message has no address or its `heardAt` lies within the beginning;
that this is so at every message is not said here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingGrows
import Johnson.Desc.ProofFile.Honest.K2.AtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left)

/-- A filling's one call hangs on the challenges only through their first `heardAt` many. -/
theorem at_of_take (D : RowData) (R : Readers) {heard heard' : List Fmt.Drawn} (a : MsgAddr)
    (h : heard.take (D.heardAt a) = heard'.take (D.heardAt a)) (r j : Nat) :
    D.at_ R heard a r j = D.at_ R heard' a r j := by
  unfold RowData.at_
  rw [h]

theorem take_of_prefix {α : Type} {l l' : List α} (hp : l <+: l') {n : Nat} (hn : n ≤ l.length) :
    l'.take n = l.take n := by
  obtain ⟨t, rfl⟩ := hp
  exact List.take_append_of_le_length hn

theorem at_of_prefix (D : RowData) (R : Readers) {heard₀ heard : List Fmt.Drawn}
    (hp : heard₀ <+: heard) (a : MsgAddr) (hn : D.heardAt a ≤ heard₀.length) (r j : Nat) :
    D.at_ R heard a r j = D.at_ R heard₀ a r j :=
  at_of_take D R a (take_of_prefix hp hn) r j

/-- The like of `ownBy`, at one segment and message. -/
theorem ownBy_of_prefix (D : RowData) (R : Readers) (addrs : Nat → Nat → Option MsgAddr)
    (shapes : Nat → Nat → OnBytes.OracleShape) {heard₀ heard : List Fmt.Drawn}
    (hp : heard₀ <+: heard) (seg m : Nat)
    (hn : ∀ a, addrs seg m = some a → D.heardAt a ≤ heard₀.length) (b j : Nat) :
    ownBy D R addrs shapes heard seg m b j = ownBy D R addrs shapes heard₀ seg m b j := by
  unfold ownBy
  cases ha : addrs seg m with
  | none => rfl
  | some a =>
    show asRow _ (D.at_ R heard a b j) = asRow _ (D.at_ R heard₀ a b j)
    rw [at_of_prefix D R hp a (hn a ha) b j]

/-- The closing at two functions of own data that agree at the segments' numbers. -/
theorem closingFrom_own (table : FreshTable) {own own' : Nat → Nat → Nat → Nat → Cb.Gl.E}
    (heard : List Fmt.Drawn) (k : Nat → Except String Stretch) :
    ∀ (segs : List SegmentPub) (j base : Nat) (prev : Option (Left × List OnBytes.OracleShape)),
      (∀ i, i < segs.length → own (j + i) = own' (j + i)) →
      closingFrom table own heard k segs j base prev =
        closingFrom table own' heard k segs j base prev
  | [], _, _, _, _ => rfl
  | S :: rest, j, base, prev, h => by
    have h0 : own j = own' j := h 0 (Nat.succ_pos _)
    show (segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard k
        base).bind (fun W =>
          closingFrom table own heard k rest (j + 1) (base + S.messages) (some W)) =
      (segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own' j) heard k
        base).bind fun W =>
          closingFrom table own' heard k rest (j + 1) (base + S.messages) (some W)
    rw [h0]
    congr 1
    funext W
    refine closingFrom_own table heard k rest (j + 1) (base + S.messages) (some W) fun i hi => ?_
    have e : j + 1 + i = j + (i + 1) := by omega
    rw [e]
    exact h (i + 1) (Nat.succ_lt_succ hi)

/-- **ALL THREE AT ONCE.** -/
theorem closingFrom_grows (table : FreshTable) {own own' : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard heard' : List Fmt.Drawn} {k k' : Nat → Except String Stretch} (hk : GivesAll k k')
    (segs : List SegmentPub) (j base : Nat) (prev : Option (Left × List OnBytes.OracleShape))
    (ho : ∀ i, i < segs.length → own (j + i) = own' (j + i))
    (hg : ∀ S ∈ segs, challengesOr0 heard S.gamma = challengesOr0 heard' S.gamma) :
    OkLe (closingFrom table own heard k segs j base prev)
      (closingFrom table own' heard' k' segs j base prev) := by
  rw [closingFrom_own table heard k segs j base prev ho]
  exact closingFrom_le table own' hk segs j base prev hg

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.at_of_take
#print axioms ProofFile.Honest.K2.Law.take_of_prefix
#print axioms ProofFile.Honest.K2.Law.at_of_prefix
#print axioms ProofFile.Honest.K2.Law.ownBy_of_prefix
#print axioms ProofFile.Honest.K2.Law.closingFrom_own
#print axioms ProofFile.Honest.K2.Law.closingFrom_grows
