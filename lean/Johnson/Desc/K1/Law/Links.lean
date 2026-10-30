-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/Links.lean: the two equations that put a place of the kind K1 on a written record ("its codes
and its messages are the record's": Johnson/Desc/K1/Law/CondReal.lean: PlaceOk, placeOk_of), at the places of a
proof file's first chain that hang on the request's shape: the first segment's opening, the two later
moments of every link, and the code switches of the last group's test.

The shape is A LETTER here: sh : ReqShape. What is asked of it is one test with code, linksTest sh:
what the kind's own texts announce at sh is, sending by sending, what the written records hold.
  laterSent sh l m     what K1/Places.lean's parLater announces at link l, moment m
  firstSent sh         what K1/First.lean's firstPar announces
  recOf l m            the record's number on the first chain: three sendings a link
  linksTest sh         the first place; both later moments of every link; the last test's switches
  parLater_sent, firstPar_sent     the places' messages are these functions of q.shape alone
  k01_first, k01_later, k01_last   PlaceOk at the records 0, recOf l m, 3 * links + 1 + j

What is not claimed. That a shape passes the test: no written value of a request's shape lies yet; a
run evaluates the test at the description's own shape.

(Where this and lean/THEOREM.md differ, the page holds.)
That the description's parameters have the
written codes. The sendings at a link's moment 0 behind the first (the code switches between the
links) and the last group's opening. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.CondReal
import Johnson.Desc.K1.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params Johnson.G Desc.Plain

/-- The frame at a link, out of the shape alone. -/
def frameAt (sh : ReqShape) (l : Nat) : ReqFrame := { shape := sh, groups := reqGroups sh, link := l }

/-- What a segment's later moment announces. -/
def laterSent (sh : ReqShape) (l m : Nat) : List OracleNotice :=
  (ReqFrame.notices ((frameAt sh l).atMoment m)).toList

/-- What the first segment's opening announces. -/
def firstSent (sh : ReqShape) : List OracleNotice :=
  (ReqFrame.notices ((frameAt sh 0).atMoment 0)).toList ++
    [foldMaskNotice ((frameAt sh 0).foldShape 0 {})] ++ sh.atStart

/-- The number of the record of link l's moment m on the first chain. -/
def recOf (l m : Nat) : Nat := 3 * l + m

theorem parLater_sent (q : Params.First) (gp : GPar) (l piece m : Nat) :
    (parLater q gp l piece m).sent.toList = laterSent q.shape l m := by
  simp [Par.sent, parLater, noticesAt, laterSent, frameAt]

theorem firstPar_sent (q : Params.First) (gp : GPar) :
    (firstPar q gp).sent.toList = firstSent q.shape := by
  simp [Par.sent, firstPar, firstParts, firstLaid, firstSent, frameAt, frame₀]

/-- **The test on the shape.** -/
def linksTest (sh : ReqShape) : Bool :=
  decide ((sentOf 2 0)[0]? = some (firstSent sh)) &&
    ((List.range sh.link.length).all fun l => [1, 2].all fun m =>
      decide ((sentOf 2 0)[recOf l m]? = some (laterSent sh l m))) &&
    decide (((sentOf 2 0).drop (3 * sh.link.length + 1)).take (switchesOf sh.answers sh.last).length =
      switchesOf sh.answers sh.last)

theorem k01_first {sh : ReqShape} (ht : linksTest sh = true) (q : Params.First) (gp : GPar)
    (hc : q.codes = codesFull2) (hs : q.shape = sh) : PlaceOk 2 0 0 (firstPar q gp) := by
  simp only [linksTest, Bool.and_eq_true, decide_eq_true_eq] at ht
  exact placeOk_of (by decide) ht.1.1 _ hc (by rw [firstPar_sent, hs])

theorem k01_later {sh : ReqShape} (ht : linksTest sh = true) (q : Params.First) (gp : GPar)
    (hc : q.codes = codesFull2) (hs : q.shape = sh) (l piece m : Nat) (hl : l < sh.link.length)
    (hm : m = 1 ∨ m = 2) : PlaceOk 2 0 (recOf l m) (parLater q gp l piece m) := by
  simp only [linksTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at ht
  have h := ht.1.2 l hl m (by rcases hm with h | h <;> simp [h])
  exact placeOk_of (by decide) h _ hc (by rw [parLater_sent, hs])

theorem k01_last {sh : ReqShape} (ht : linksTest sh = true) (P : Par) (j : Nat)
    (s : List OracleNotice) (hc : P.codes = codesFull2) (hs : P.sent.toList = s)
    (hj : (switchesOf sh.answers sh.last)[j]? = some s) :
    PlaceOk 2 0 (3 * sh.link.length + 1 + j) P := by
  simp only [linksTest, Bool.and_eq_true, decide_eq_true_eq] at ht
  refine placeOk_of (by decide) (s := s) ?_ P hc hs
  have hlt : j < (switchesOf sh.answers sh.last).length := (List.getElem?_eq_some_iff.1 hj).1
  rw [← ht.2, List.getElem?_take_of_lt hlt, List.getElem?_drop] at hj
  exact hj

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k01_first
#print axioms VerifiableInference.Desc.K1.k01_later
#print axioms VerifiableInference.Desc.K1.k01_last
