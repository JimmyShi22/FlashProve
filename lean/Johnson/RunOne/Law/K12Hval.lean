-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Hval.lean: "ON A MEMBER's TABLES THE TUPLE's WORDS ARE WHAT THE TABLES' READER READS OFF THE LAID WITNESS": A CHAIN OF FIVE LINKS AS ONE LEMMA. GENERAL: no key file stands in it. IT MOVES THE WEIGHT INTO THREE NAMED PREMISES; IT PAYS NONE.
OBJECT. The premise hval of GrowsOfAllSay.lean's holds_of_allSay | grows_of_allSay, at one member o.
USER. Whoever pays «back»'s law at a proximity test's row of the key file's tables.
LETTERS. cs · mem · rd · m: the composition's over the proximity test's law (Johnson/Desc/Sound/SeamFacts.lean: core_at): the codes · which member of the list sits at a message's number · the reader of a typed message's tables · the tuple. K · R · w': the tables' (Johnson/Desc/Key/KeyMeaning.lean), AT M := Fill.Tab, the tables' files' filling's own type of a message.
  hval_of_links: wordsT cs mem rd m o part i = readE (valOf K R w' o part i), at every part and index.
THE FIVE LINKS: wordsT's text at hmem · hrd (core_at's own premise) · ofU_eq_tabP (TabBridge.lean) · hread · hof with valOf's text at hnum.
THE THREE PREMISES THAT HOLD THE WEIGHT, EACH ON THE TABLES' FILES' LETTERS: hnum: the plan numbers the message o as k · hof: the laid witness's message k IS the candidate's table (reads_layAt, under its ties) · hread: the reader's value of that table, read in the field, is the table (the tables' files' "a candidate can be laid", third conjunct).
Limits. As empty as its premises. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.TabBridge
import Johnson.Desc.K14.Law.LedgerSay
import Johnson.Desc.Key.KeyMeaning

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Hval
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open Cb Johnson.Pack OnBytes OnBytes.Maker OnBytes.Slice
open H2K.Pin (tabP)

/-- **The tuple's words are what the tables' reader reads off the laid witness, at one member.** -/
theorem hval_of_links {Cells : Type} (cs : Codes) (K : KPlan) (R : KRead Cells Fill.Tab) (mem : ℕ → Option Mem)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg) (w' : Wit Cells Unit Fill.Tab) (o k : ℕ) (x : Mem)
    (hmem : mem o = some x) (hnum : K.num o = some k)
    (hof : R.of w' k = ofU cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 (m x))
    (hread : ∀ part i, readE (R.val (ofU cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 (m x)) part i) =
      ofU cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 (m x) part i) :
    ∀ part i, _root_.Desc.K14.Law.wordsT cs mem rd m o part i = readE (valOf K R w' o part i) := by
  intro part i
  have e1 : _root_.Desc.K14.Law.wordsT cs mem rd m o part i = rd x (m x) part i := by
    unfold _root_.Desc.K14.Law.wordsT
    rw [hmem]
  have e2 : valOf K R w' o part i = R.val (R.of w' k) part i := by
    unfold valOf
    rw [hnum]
  rw [e1, hrd, e2, hof, hread, TabBridge.ofU_eq_tabP]

end Johnson.RunOne.Law.K12Hval

#print axioms Johnson.RunOne.Law.K12Hval.hval_of_links
