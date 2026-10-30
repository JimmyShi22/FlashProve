-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FrontMsg.lean: THE MESSAGE ON THE LINK's GROUP's TABLES, AS ONE TERM: what the
first stage of the link's proximity test holds where a prover has sent the two tables' folds.
Definitions, statements and proofs, in the library's typed terms (OnBytes/Slice/LinkAt.lean,
BatSem.lean).

  membMsg S u fr   one member's message: the coefficients u of a fold's polynomial (tail, then
                   message) at the entries where the library's putAt lays them; fr elsewhere (the
                   entries between and behind, the sample's pad among them). A member has no mask
                   row, by type (S.MJ's right side is empty)
  membMsg_putAt    membMsg S u fr (S.putAt k) = u k
  mu0 S t m        the group's message: member a's message on its block's real rows; 0 on the rows
                   that no member has; 0 ON THE CARRIED MASK ROW
  mu0_atJ          mu0 S t m (atJ S t a j) = m a j
  free_mu0         FreeZero S t (mu0 S t m)
  mu0_mask         mu0 S t m (.inr j) = 0

Not shown here. That any written oracle holds this message's code words. Nothing on a decision;
nothing on soundness; nothing on what any entry discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlockBat
import OnBytes.Slice.SimLink

set_option autoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice Cb

/-- One member's message. THE LAST ARM IS THE ONE DOOR OF fr, and so of the sample's pad, whose
place is S.padJ: the last place of the last row, entry R * C.l - 1. Of the room the structure Sz
asks T.l ≤ R * C.l (fitM) and t0 + T.r ≤ R * C.l (fitT): neither strictly. At two shapes that entry
falls into an arm in front, and fr is read at S.padJ nowhere: (1) 0 < T.r and t0 + T.r = R * C.l:
the tail's last coefficient stands there;
(2) T.r = 0 and T.l = t0 = R * C.l: the message's last. Nothing here tests for them. The programs'
public test on the link's shape (linkOk, OnBytes/Iop/Link.lean) holds, at the first side, foldeqOk's
clause entries ≤ vectorRoom (OnBytes/Iop/Foldeq.lean); the two sides differ in their numbers of
columns alone. No law of this file ties that clause to these two shapes; two laws in files that do
not ship are stated to tie it: padRoom_of_ran
(Johnson/Prover/Link/PadRoomOfRan.lean [not in this library]) and padRoom_msg_of_ran
(Johnson/Prover/Link/PadRoomMore.lean [not in this library]). -/
def membMsg (S : Sz) (u : S.Co → GE) (fr : S.MJ → GE) : S.MJ → GE
  | .inl x =>
    if h : x.1.val * S.P.C.l + x.2.val < S.P.T.l then
      u ⟨S.P.T.r + (x.1.val * S.P.C.l + x.2.val), Nat.add_lt_add_left h _⟩
    else if h2 : S.P.t0 ≤ x.1.val * S.P.C.l + x.2.val ∧
        x.1.val * S.P.C.l + x.2.val < S.P.t0 + S.P.T.r then
      u ⟨x.1.val * S.P.C.l + x.2.val - S.P.t0, by omega⟩
    else fr (.inl x)
  | .inr x => x.1.elim

theorem membMsg_putAt (S : Sz) (u : S.Co → GE) (fr : S.MJ → GE) (k : S.Co) :
    membMsg S u fr (S.putAt k) = u k := by
  have he : S.entryOf k / S.P.C.l * S.P.C.l + S.entryOf k % S.P.C.l = S.entryOf k :=
    Nat.div_add_mod' _ _
  have hl := le_t0 S.P
  have hk := k.isLt
  show (if h : S.entryOf k / S.P.C.l * S.P.C.l + S.entryOf k % S.P.C.l < S.P.T.l then _ else _) = _
  by_cases c : k.val < S.P.T.r
  · have e1 : S.entryOf k = S.P.t0 + k.val := by unfold Sz.entryOf; rw [if_pos c]
    rw [dif_neg (by rw [he, e1]; omega), dif_pos (by rw [he, e1]; omega)]
    exact congrArg u (Fin.ext (by show _ - S.P.t0 = k.val; rw [he, e1]; omega))
  · have e1 : S.entryOf k = k.val - S.P.T.r := by unfold Sz.entryOf; rw [if_neg c]
    rw [dif_pos (by rw [he, e1]; omega)]
    exact congrArg u (Fin.ext (by show S.P.T.r + _ = k.val; rw [he, e1]; omega))

/-- **The group's message.** Member a's message on its block's real rows; THE WRITTEN 0 on the rows
that no member has and on the carried mask row (mu0_mask). -/
def mu0 (S : Sz) (t : ℕ) (m : Bool → S.MJ → GE) : (S.sg t).cIn.J → GE
  | .inl x =>
    if h : Sz.rowNo x.1 % 2 ^ S.P.aR < S.P.R then
      m (decide (2 ^ S.P.aR ≤ Sz.rowNo x.1)) (.inl (⟨Sz.rowNo x.1 % 2 ^ S.P.aR, h⟩, x.2))
    else 0
  | .inr _ => 0

theorem mu0_mask (S : Sz) (t : ℕ) (m : Bool → S.MJ → GE) (j) : mu0 S t m (.inr j) = 0 := rfl

theorem rowNo_split (S : Sz) (t : ℕ) (a : Bool) (i : ℕ) (hi : i < 2 ^ S.P.aR) :
    Sz.rowNo (memRow S t a i) % 2 ^ S.P.aR = i ∧
      decide (2 ^ S.P.aR ≤ Sz.rowNo (memRow S t a i)) = a := by
  rw [rowNo_memRow S t a i hi]
  cases a
  · have : S.blk false = 0 := rfl
    rw [this, Nat.zero_add]
    exact ⟨Nat.mod_eq_of_lt hi, decide_eq_false (by omega)⟩
  · have : S.blk true = 2 ^ S.P.aR := rfl
    rw [this]
    exact ⟨by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hi], decide_eq_true (by omega)⟩

theorem mu0_atJ (S : Sz) (t : ℕ) (m : Bool → S.MJ → GE) (a : Bool) (j : S.MJ) :
    mu0 S t m (atJ S t a j) = m a j := by
  rcases j with x | x
  · have hi : x.1.val < 2 ^ S.P.aR := lt_of_lt_of_le x.1.isLt (le_two_pow_clog S.P.R)
    obtain ⟨h1, h2⟩ := rowNo_split S t a x.1.val hi
    show (if h : Sz.rowNo (memRow S t a x.1.val) % 2 ^ S.P.aR < S.P.R then _ else _) = _
    rw [dif_pos (by rw [h1]; exact x.1.isLt)]
    simp only [h2]
    exact congrArg (m a) (congrArg Sum.inl (Prod.ext (Fin.ext h1) rfl))
  · exact x.1.elim

theorem free_mu0 (S : Sz) (t : ℕ) (m : Bool → S.MJ → GE) : FreeZero S t (mu0 S t m) := by
  intro a i j hR hi
  show (if h : Sz.rowNo (memRow S t a i) % 2 ^ S.P.aR < S.P.R then _ else _) = _
  rw [dif_neg (by rw [(rowNo_split S t a i hi).1]; omega)]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.membMsg
#print axioms Johnson.Prover.Link.membMsg_putAt
#print axioms Johnson.Prover.Link.mu0
#print axioms Johnson.Prover.Link.mu0_mask
#print axioms Johnson.Prover.Link.rowNo_split
#print axioms Johnson.Prover.Link.mu0_atJ
#print axioms Johnson.Prover.Link.free_mu0
