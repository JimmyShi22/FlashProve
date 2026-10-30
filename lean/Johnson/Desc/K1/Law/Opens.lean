-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/Opens.lean: beside Johnson/Desc/K1/Law/Links.lean: the sendings at moment 0 of every link behind the first,
and of the last group: the code switches between the links. They are no places of the kind K1's own
lot: the kind that switches hands its sending to K1's text. So, as Johnson/HB/LLHARD/K01Real.lean
does for the switches of the proximity tests: EVERY place with the written codes that announces what
the switch into group l announces is PlaceOk at the record 3 * l.
  openSent sh l    the target, the kept messages' copies, the link's messages of moment 0, the fold's
                   fresh mask: Tw.L9.switchNotices at the group's target
  opensTest sh     at every l from 1 to the number of links: it is the record's list
  k01_open

What is not claimed. That the switching kind's place announces openSent: an equation for that kind's files to show. That a
shape passes the test (see Johnson/Desc/K1/Law/Links.lean). Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Links

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params Johnson.G Desc.Plain

/-- What the code switch into group l announces. -/
def openSent (sh : ReqShape) (l : Nat) : List OracleNotice :=
  let f := frameAt sh l
  (Tw.L9.switchNotices (f.groups.getD l {}).target
    (ReqFrame.notices (f.atMoment 0) ++ #[foldMaskNotice (f.foldShape l {})])).toList

/-- **The test on the shape.** -/
def opensTest (sh : ReqShape) : Bool :=
  (List.range sh.link.length).all fun i =>
    decide ((sentOf 2 0)[3 * (i + 1)]? = some (openSent sh (i + 1)))

theorem k01_open {sh : ReqShape} (ht : opensTest sh = true) (P : Par) (l : Nat)
    (hc : P.codes = codesFull2) (hs : P.sent.toList = openSent sh l) (h1 : 1 ≤ l)
    (h2 : l ≤ sh.link.length) : PlaceOk 2 0 (3 * l) P := by
  simp only [opensTest, List.all_eq_true, List.mem_range, decide_eq_true_eq] at ht
  obtain ⟨i, rfl⟩ : ∃ i, l = i + 1 := ⟨l - 1, by omega⟩
  exact placeOk_of (by decide) (ht i (by omega)) P hc hs

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k01_open
