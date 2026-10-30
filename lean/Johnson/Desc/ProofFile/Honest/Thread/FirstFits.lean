-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstFits.lean: THE FIRST CHAIN's FORWARD ROWS PASS `fwdFit`
(Honest/Thread/Thr.lean) WHEREVER THEY PASS THE TEST IN ONE PASS. `fwdFit` makes the open set at
each border anew, from the start: so many steps as the square of the list's length. At the full size
Honest/Thread/FirstRows.lean evaluates another test: along `opens`, which walks the list once; that
`opens` is `fwdOpen`, border by border, is evaluated there at three segments alone. Here it is
shown, at every list of segments, every list of places and every start. Lemmas; no definition.

  `fwdOpen_cons`   the open set behind b + 1 members of p :: ps is the one behind b members of ps,
     from the open set behind p
  `asks_open`   where the test in one pass says yes: at EVERY border's number what the row asks or
     shuts is open in front of it: beyond the list the rows are empty
  `fwdFit_of_opens`   so `fwdFit` says yes AT EVERY n: no equation between the list's length and a
     description's is wanted

Limits. Lists alone: nothing on what an item says. None is one of the library's goals. This file
proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstRows
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Item)

theorem fwdOpen_cons (links : List ModelPart) (p : Place) (ps : List Place) (O : List Item) : ∀ b,
    fwdOpen O (rows links (p :: ps)) (b + 1) =
      fwdOpen (fwdStep O (rowAt links p)) (rows links ps) b
  | 0 => rfl
  | b + 1 => by
    have e : rows links (p :: ps) (b + 1) = rows links ps b := rfl
    show fwdStep (fwdOpen O (rows links (p :: ps)) (b + 1)) (rows links (p :: ps) (b + 1)) =
      fwdStep (fwdOpen (fwdStep O (rowAt links p)) (rows links ps) b) (rows links ps b)
    rw [fwdOpen_cons links p ps O b, e]

theorem asks_open (links : List ModelPart) : ∀ (ps : List Place) (O : List Item),
    (((opens links ps O).zip ps).all fun x =>
      ((rowAt links x.2).asks ++ (rowAt links x.2).shuts).all x.1.contains) = true →
    ∀ b, (((rows links ps b).asks ++ (rows links ps b).shuts).all
      (fwdOpen O (rows links ps) b).contains) = true
  | [], _, _, _ => rfl
  | p :: ps, O, h, b => by
    have h' : (((rowAt links p).asks ++ (rowAt links p).shuts).all O.contains &&
        ((opens links ps (fwdStep O (rowAt links p))).zip ps).all fun x =>
          ((rowAt links x.2).asks ++ (rowAt links x.2).shuts).all x.1.contains) = true := h
    rw [Bool.and_eq_true] at h'
    cases b with
    | zero => exact h'.1
    | succ b =>
      have e : rows links (p :: ps) (b + 1) = rows links ps b := rfl
      rw [e, fwdOpen_cons]
      exact asks_open links ps _ h'.2 b

/-- **THE TEST IN ONE PASS GIVES `fwdFit` AT EVERY n.** -/
theorem fwdFit_of_opens {links : List ModelPart} {ps : List Place} {O : List Item}
    (h : (((opens links ps O).zip ps).all fun x =>
      ((rowAt links x.2).asks ++ (rowAt links x.2).shuts).all x.1.contains) = true) (n : Nat) :
    fwdFit O (rows links ps) n = true :=
  List.all_eq_true.2 fun b _ => asks_open links ps O h b

end ProofFile.Honest.FirstRows

#print axioms ProofFile.Honest.FirstRows.fwdOpen_cons
#print axioms ProofFile.Honest.FirstRows.asks_open
#print axioms ProofFile.Honest.FirstRows.fwdFit_of_opens
