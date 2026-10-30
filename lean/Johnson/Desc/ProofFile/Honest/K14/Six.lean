-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Six.lean: kind K14: THE KIND's SIX HALVES AS ONE LIST, FROM ONE
LIST OF PUBLIC DATA: the plan's parameters and the shared chain's own list of sub-protocols. THIS IS
WHERE THE HALVES ARE LAID: so three public tests are evaluated HERE, and sixOf returns an error,
with a message that says which test rejects, where one of them does. The numbers of the two
challenges that the parts read are made here, by dataOf (Honest/K14/Parts.lean), for the four own
halves and for the two sendings alike: whoever calls sixOf types no number. Definitions with code;
no theorem.

  tiedTo          the list's first member stands at none of the eight's places, and its members
                  number 1 to 8 stand, IN THIS ORDER, at the places of the eight sub-protocols that
                  the library makes of the plan, with their declared rounds; it rejects where the
                  library makes none of the plan. ("Eight" is the length of the library's list,
                  which the text reads and does not fix.)
  rejection         the three tests in a row: the message of the first that rejects; none where all
                  accept. IT REJECTS WHERE
                    the library's test on the linear part's shape WITH ITS CODES rejects (linOk,
                      OnBytes/Iop/Lin.lean: among its clauses: the matrix's places lie in front of
                      the pads, without which rowsOf lays an entry of the matrix where a pad is due;
                      the vectors have room in their messages, without which a vector is cut)
                    sendingsFit rejects (Honest/K14/SendingsShapes.lean: the nine numbered clauses
                      (1) to (9) of that file's head, spread over its definitions; sendingsFit's own
                      text is a conjunction of five)
                    tiedTo rejects
  sixOf           the four own halves (three where the shape does not split) and the two sendings'
                  halves; or rejection's message

Limits. As those of Honest/K14/Parts.lean and Sendings.lean. The tests read public data alone: the
plan's codes and shape, and of the list the places and the declared rounds of its first nine
members. tiedTo TIES NO MORE THAN THAT: not the sub-protocols' decide functions, oracle messages or
tests on the plan; a plan that differs from the list's own in a field that no declared round shows
passes. What stands in the list behind its ninth member is not read. Where all three accept, "LIN
point" and "LIN zeta" stand in the list, so dataOf returns: sixOf's last arm, for a list without
them, is there because dataOf returns an Option; no list reaches it (by reading; no lemma for a
general list: at a list that begins as the shared chain's flat list does, dataOf_flat, tiedTo_flat
and sixOf_flat, Honest/K14/DataMade.lean, show that dataOf returns, that tiedTo accepts, and what
sixOf returns where its two tests on the shapes accept). Whether a shape that does not split passes
sendingsFit is shown nowhere. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block)

variable {W₀ Rc Ky X S Cl : Type}

/-- **The list begins as the plan's chain does**: its first member stands at none of the eight's
places; its members number 1 to 8 stand, in this order, at the places of the eight sub-protocols
that the library makes of the plan, with their declared rounds. Where the library makes none of the
plan (the arm `none`) it rejects. "Eight" is `l.length`, the length of the library's own list. -/
def tiedTo (P : Desc.K14.P14) (bs : List (Block S Cl)) : Bool :=
  match Desc.K14.blocks P with
  | some l =>
    ((bs.take 1).all fun x => l.all fun b => b.place != x.place) &&
      ((bs.drop 1).take l.length).map (fun x => (x.place, x.rounds)) ==
        l.map fun b => (b.place, b.rounds)
  | none => false

/-- **The three public tests in a row**: the message of the first that rejects. -/
def rejection (P : Desc.K14.P14) (bs : List (Block S Cl)) : Option String :=
  if !OnBytes.linOk P.codes P.S then
    some "K14: the test on the linear part's shape and codes rejects"
  else if !sendingsFit P then some "K14: the test on the two sendings' shapes rejects"
  else if !tiedTo P bs then some "K14: the list of sub-protocols does not begin as the plan's"
  else none

/-- **The six halves, or the message of the public test that rejects.** bs: the shared chain's own
list of sub-protocols, whole, from its first. weights, rand: the readers of the index and of the
index committer's coins. -/
def sixOf (P : Desc.K14.P14) (bs : List (Block S Cl)) (weights : W₀ → Weights)
    (rand : Rc → TableRand) : Except String (List (Placed Empty (Common W₀ Rc Ky) X)) :=
  match rejection P bs with
  | some e => .error e
  | none =>
    match dataOf P.S bs with
    | none => .error "K14: \"LIN point\" or \"LIN zeta\" is not in the list"
    | some d => .ok (proverSidesOfSharedRounds d weights ++ proverSidesOfSharedSendings { P := P, atPoint := d.atPoint } weights rand)

end ProofFile.Honest.K14
