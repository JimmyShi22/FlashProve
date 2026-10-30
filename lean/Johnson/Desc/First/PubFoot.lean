-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/PubFoot.lean: which parts of the verifier's state does a public test read? One
rule, for every kind of sub-protocol, by which a public item that a sub-protocol neither makes nor
drops stays true across it. Definitions with code and theorems. No Mathlib.
Why. Between two sub-protocols of a request's own rounds the table
(Johnson/Desc/First/Borders.lean) asks public items of the verifier's state. An item that is open
in front of a sub-protocol and behind it must be shown to stay true. Here each ITEM says once
what it reads, each KIND says once what its accepting run leaves, and "the item stays" is a test
on two lists.

  `Rdr`: sixteen readers of the verifier's state. `Rdr.same D r s s'`: the reader r gives one
    value at s and s' (D: one reader, `run m piece name`, is the answer of D's reader of the
    claims on linear forms). `SameOn D R s s'`: so for every reader of the list R.
  `footBy runs q`, `footOf D q := footBy D.runs q`: the readers that the test at the public item q
    reads; none: NOT BOOKED HERE.
  `pubAll_same`: **where `footOf D q = some R`, s and s' agree on R, and base has one value at q,
    the composed test (`pubAll`, Johnson/Desc/First/PubAll.lean) at q has one value at s and s'.**
    (base: at an item whose own part's test "is it mine" fails, `pubAll` hands on to base; at the
    closed base the premise is rfl.)
  `ridesB runs keeps Q`: every item of the list Q is booked, and all that it reads is in the list
    `keeps`. `rides_of_B`: then, across a step that leaves `keeps` and at which base has one
    value at each item of Q, every item of Q that was true stays true.
HOW A KIND USES IT. Its authors show ONE lemma: "my accepting run from s to s' leaves these
readers" (`SameOn D keeps s s'`); `ridesB runs keeps Q = true`, at the list Q of the items that
are open on both sides of their place and are none of theirs, is then for the kernel; `rides_of_B`
gives the keeping of all of them.
BOOKED: ledger, freeAbove, unheard, linkFresh, hasRow, noneSent, indexIs, indexThere, lookIn,
lookOut, left, leftOn (their test is "true": it reads nothing), formsIn, formsInT, totalIn, and
the names "frame.sentIs", "frame.sentIs1", "ledger.treesAre", "K5.okAt", "K5.plain", "K5.liveReq",
"K5.readsThere". The lemmas on lookIn, lookOut, formsIn, formsInT, totalIn are another author's
(Johnson/Desc/First/Foot/LookSame.lean, FormsSame.lean).
Limits. (1) IT SPEAKS OF THE TESTS WITH CODE (pub) ALONE: the SENTENCES at left, leftOn (pubP)
pass by their own authors' lemma. (2) IT IS THE EQUATIONS' FORM: right for a sub-protocol that
leaves a reader untouched; it says nothing where the reader's value grows (a ledger with more
slots filled): there the test stays for another reason, and the kind shows the keeping by hand.
(3) THE READERS ARE COARSE: `link` is the whole link context: every sub-protocol inside a segment
that writes any field of it "does not leave" it, though "frame.sentIs" or linkFresh read other
fields; `here` is the whole of where the verifier stands. (4) `row` BOOKS NOTHING: `Rdr.same D
.row` IS the keeping of hasRow, at every parameter: it only lets hasRow stand in one list with the
rest. (5) NOT BOOKED: tokenSmall, frontOk, evalLaid, "K13.wSits" (each passes a place or two:
unread here); look, callerIn, "K4.rowsBare", "K4.lookLeft" (by an evaluation at the two written
lists they pass no place: a handshake between neighbours); request. (6) No kind's `keeps` is shown
here. No soundness is claimed.

-/
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.Foot.FormsSame
import Johnson.Desc.First.Foot.LookSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Look (linkFreshC k3Item k3SortAt lookInC_same lookOutC_same)
open VerifiableInference.Desc.First.FillSent (sentIsB treesAreB)
open VerifiableInference.Desc.K13 (noneSentC indexIsC indexThereC)

/-- Readers of the verifier's state. -/
inductive Rdr where
  /-- the statement -/
  | st
  /-- what goes on to the later chains -/
  | out
  /-- the frame between segments -/
  | frame
  /-- the open segment's link context -/
  | link
  /-- the open segment's ledger -/
  | fork
  /-- the open segment's parameters of the approximate range proof -/
  | tl
  /-- whether the pending claim on the weights can be made, at given public numbers -/
  | row
  /-- what was heard at the lookup on the calls -/
  | lookHeard
  /-- the rows that are owed -/
  | rowsOwed
  /-- what was heard at the attention caller's place -/
  | heard5
  /-- where the verifier stands: between segments, or in which sort of segment -/
  | here
  /-- the book of the oracle messages' places -/
  | book
  /-- the open segment's part, as the claims on linear forms read it -/
  | seg
  /-- the slot whose scalar is masked elsewhere -/
  | merge
  /-- the batching's own view of the state -/
  | atS
  /-- what the reader of segment m's claims on linear forms answers at a piece's named run -/
  | run (m piece : Nat) (name : String)
  deriving DecidableEq, Repr

/-- The reader gives one value at the two states. -/
def Rdr.same (D : PubData) : Rdr → S → S → Prop
  | .st, s, s' => s'.st = s.st
  | .out, s, s' => s'.out = s.out
  | .frame, s, s' => s'.check.frame = s.check.frame
  | .link, s, s' => s'.link? = s.link?
  | .fork, s, s' => s'.fork? = s.fork?
  | .tl, s, s' => s'.tl? = s.tl?
  | .row, s, s' => ∀ lay n lin,
    Johnson.Desc.First.Walk.Law.hasRow lay n lin s' = Johnson.Desc.First.Walk.Law.hasRow lay n lin s
  | .lookHeard, s, s' => s'.lookHeard? = s.lookHeard?
  | .rowsOwed, s, s' => s'.rowsOwed = s.rowsOwed
  | .heard5, s, s' => s'.heard5? = s.heard5?
  | .here, s, s' => s'.here = s.here
  | .book, s, s' => s'.book = s.book
  | .seg, s, s' => K9.segAt? s' = K9.segAt? s
  | .merge, s, s' => K9.mergeOf s' = K9.mergeOf s
  | .atS, s, s' => K9.atS.get? s' = K9.atS.get? s
  | .run m piece name, s, s' => (D.Rd m).forms piece name s' = (D.Rd m).forms piece name s

/-- The two states agree on every reader of the list. -/
def SameOn (D : PubData) (R : List Rdr) (s s' : S) : Prop := ∀ r ∈ R, r.same D s s'

/-- What the test at a public item reads; none: not booked here. runs: the map of names of the
claims on linear forms. -/
def footBy (runs : Nat → Nat → String → List (Nat × String)) : Pub → Option (List Rdr)
  | .ledger _ => some [.fork]
  | .freeAbove _ => some [.fork]
  | .unheard => some [.out]
  | .linkFresh _ => some [.tl, .link]
  | .hasRow _ => some [.row]
  | .noneSent => some [.st, .frame, .out]
  | .indexIs => some [.out]
  | .indexThere => some [.st, .out]
  | .lookIn _ _ => some [.tl, .lookHeard, .rowsOwed, .fork, .link]
  | .lookOut _ _ => some [.tl, .lookHeard, .fork]
  | .left _ => some []
  | .leftOn _ => some []
  | .formsIn m k r => some ([.seg, .merge] ++ (runs m k r).map fun p => .run m p.1 p.2)
  | .formsInT m k r => some ([.seg, .merge] ++ (runs m k r).map fun p => .run m p.1 p.2)
  | .totalIn _ => some [.atS]
  | .more (some _) name =>
    if name == "frame.sentIs" || name == "frame.sentIs1" then some [.link]
    else if name == "ledger.treesAre" then some [.fork]
    else if name == "K5.okAt" || name == "K5.plain" then some [.fork, .heard5]
    else if name == "K5.liveReq" then some [.link]
    else if name == "K5.readsThere" then some [.here, .book]
    else none
  | _ => none

/-- The same, at a structure of parameters. -/
def footOf (D : PubData) : Pub → Option (List Rdr) := footBy D.runs

/-- At a name that is none of its two, the feed-forward sub-protocol's test "is it mine" fails. -/
theorem leftItem_off (links : List ModelPart) (m : Nat) (n : String)
    (h : (n == "K4.rowsBare" || n == "K4.lookLeft") = false) :
    FillBare.leftItem links (.more (some m) n) = false := by
  show (links[m]? == some .layers && (n == "K4.rowsBare" || n == "K4.lookLeft")) = false
  rw [h]
  exact Bool.and_false _

/-- Two tests that agree at every member of a list agree on the list. -/
theorem all_eq_of_mem {α : Type} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a (List.mem_cons_self ..),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

section
variable {P : Type} (D : PubData) (base : Pub → P × S → Bool)

/-- **Where the two states agree on what the item's test reads, the test has one value.** -/
theorem pubAll_same (q : Pub) (R : List Rdr) (h : footOf D q = some R) (z : P) (s s' : S)
    (hs : SameOn D R s s') (hb : base q (z, s') = base q (z, s)) :
    pubAll D base q (z, s') = pubAll D base q (z, s) := by
  cases q with
  | ledger m =>
    obtain rfl : [Rdr.fork] = R := Option.some.inj h
    have e : s'.fork? = s.fork? := hs .fork (by simp)
    rw [pubAll_ledger, pubAll_ledger]
    show ledgerB s' = ledgerB s
    unfold ledgerB
    rw [e]
  | freeAbove m =>
    obtain rfl : [Rdr.fork] = R := Option.some.inj h
    have e : s'.fork? = s.fork? := hs .fork (by simp)
    rw [pubAll_freeAbove, pubAll_freeAbove]
    show ((D.nsOf m).any fun n => freeAboveB n s') = ((D.nsOf m).any fun n => freeAboveB n s)
    unfold freeAboveB
    rw [e]
  | unheard =>
    obtain rfl : [Rdr.out] = R := Option.some.inj h
    have e : s'.out = s.out := hs .out (by simp)
    rw [pubAll_unheard, pubAll_unheard]
    show unheardB s' = unheardB s
    unfold unheardB
    rw [e]
  | linkFresh m =>
    obtain rfl : [Rdr.tl, Rdr.link] = R := Option.some.inj h
    have e1 : s'.tl? = s.tl? := hs .tl (by simp)
    have e2 : s'.link? = s.link? := hs .link (by simp)
    rw [pubAll_linkFresh, pubAll_linkFresh]
    show linkFreshC D.d3 m s' = linkFreshC D.d3 m s
    unfold linkFreshC
    rw [e1, e2]
  | hasRow m =>
    obtain rfl : [Rdr.row] = R := Option.some.inj h
    rw [pubAll_hasRow, pubAll_hasRow]
    exact hs .row (by simp) _ _ _
  | noneSent =>
    obtain rfl : [Rdr.st, Rdr.frame, Rdr.out] = R := Option.some.inj h
    have e1 : s'.st = s.st := hs .st (by simp)
    have e2 : s'.check.frame = s.check.frame := hs .frame (by simp)
    have e3 : s'.out = s.out := hs .out (by simp)
    rw [pubAll_noneSent, pubAll_noneSent]
    show noneSentC D.N s' = noneSentC D.N s
    unfold noneSentC
    rw [e1, e2, e3]
  | indexIs =>
    obtain rfl : [Rdr.out] = R := Option.some.inj h
    have e : s'.out = s.out := hs .out (by simp)
    rw [pubAll_indexIs, pubAll_indexIs]
    show indexIsC D.N.indexNo s' = indexIsC D.N.indexNo s
    unfold indexIsC
    rw [e]
  | indexThere =>
    obtain rfl : [Rdr.st, Rdr.out] = R := Option.some.inj h
    have e1 : s'.st = s.st := hs .st (by simp)
    have e2 : s'.out = s.out := hs .out (by simp)
    rw [pubAll_indexThere, pubAll_indexThere]
    show indexThereC s' = indexThereC s
    unfold indexThereC
    rw [e1, e2]
  | lookIn m pc =>
    obtain rfl : [Rdr.tl, Rdr.lookHeard, Rdr.rowsOwed, Rdr.fork, Rdr.link] = R := Option.some.inj h
    have e1 : s'.tl? = s.tl? := hs .tl (by simp)
    have e2 : s'.lookHeard? = s.lookHeard? := hs .lookHeard (by simp)
    have e3 : s'.rowsOwed = s.rowsOwed := hs .rowsOwed (by simp)
    have e4 : s'.fork? = s.fork? := hs .fork (by simp)
    have e5 : s'.link? = s.link? := hs .link (by simp)
    cases hk : k3SortAt D.d3.X m pc with
    | some dg =>
      rw [pubAll_lookIn D base m pc dg hk, pubAll_lookIn D base m pc dg hk]
      exact lookInC_same D.d3 m dg e1 e2 e3 e4 e5
    | none =>
      have h8 : k3Item D.d3 (.lookIn m pc) = false := by
        show (k3SortAt D.d3.X m pc).isSome = false
        rw [hk]
        rfl
      rw [pubAll_else D base _ rfl rfl h8 rfl rfl rfl rfl rfl rfl rfl rfl,
        pubAll_else D base _ rfl rfl h8 rfl rfl rfl rfl rfl rfl rfl rfl]
      exact hb
  | lookOut m pc =>
    obtain rfl : [Rdr.tl, Rdr.lookHeard, Rdr.fork] = R := Option.some.inj h
    have e1 : s'.tl? = s.tl? := hs .tl (by simp)
    have e2 : s'.lookHeard? = s.lookHeard? := hs .lookHeard (by simp)
    have e4 : s'.fork? = s.fork? := hs .fork (by simp)
    cases hk : k3SortAt D.d3.X m pc with
    | some dg =>
      rw [pubAll_lookOut D base m pc dg hk, pubAll_lookOut D base m pc dg hk]
      exact lookOutC_same D.d3 m dg e1 e2 e4
    | none =>
      have h8 : k3Item D.d3 (.lookOut m pc) = false := by
        show (k3SortAt D.d3.X m pc).isSome = false
        rw [hk]
        rfl
      rw [pubAll_else D base _ rfl rfl h8 rfl rfl rfl rfl rfl rfl rfl rfl,
        pubAll_else D base _ rfl rfl h8 rfl rfl rfl rfl rfl rfl rfl rfl]
      exact hb
  | left m => rw [pubAll_left, pubAll_left]
  | leftOn m => rw [pubAll_leftOn, pubAll_leftOn]
  | formsIn m k r =>
    obtain rfl : ([Rdr.seg, Rdr.merge] ++ (D.runs m k r).map fun p => Rdr.run m p.1 p.2) = R :=
      Option.some.inj h
    have e1 : K9.segAt? s' = K9.segAt? s := hs .seg (by simp)
    have e3 : K9.mergeOf s' = K9.mergeOf s := hs .merge (by simp)
    rw [pubAll_formsIn, pubAll_formsIn]
    refine all_eq_of_mem _ _ _ fun p hp => ?_
    have e2 : (D.Rd m).forms p.1 p.2 s' = (D.Rd m).forms p.1 p.2 s :=
      hs (.run m p.1 p.2) (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩))
    show (if D.ah p.1 p.2 = true then _ else _) = (if D.ah p.1 p.2 = true then _ else _)
    split
    · exact K9.formsInA_same _ _ _ _ _ e1 e2 e3
    · exact K9.formsIn_same _ _ _ _ e1 e2 e3
  | formsInT m k r =>
    obtain rfl : ([Rdr.seg, Rdr.merge] ++ (D.runs m k r).map fun p => Rdr.run m p.1 p.2) = R :=
      Option.some.inj h
    have e1 : K9.segAt? s' = K9.segAt? s := hs .seg (by simp)
    have e3 : K9.mergeOf s' = K9.mergeOf s := hs .merge (by simp)
    rw [pubAll_formsInT, pubAll_formsInT]
    refine all_eq_of_mem _ _ _ fun p hp => ?_
    have e2 : (D.Rd m).forms p.1 p.2 s' = (D.Rd m).forms p.1 p.2 s :=
      hs (.run m p.1 p.2) (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩))
    exact K9.formsInT_same _ _ _ _ e1 e2 e3
  | totalIn m =>
    obtain rfl : [Rdr.atS] = R := Option.some.inj h
    have e : K9.atS.get? s' = K9.atS.get? s := hs .atS (by simp)
    rw [pubAll_totalIn, pubAll_totalIn]
    exact K9.totalIn_same _ e
  | more sg name =>
    cases sg with
    | none => simp [footOf, footBy] at h
    | some m =>
      by_cases h1 : name = "frame.sentIs"
      · subst h1
        obtain rfl : [Rdr.link] = R := Option.some.inj h
        have e : s'.link? = s.link? := hs .link (by simp)
        rw [pubAll_more_sentIs, pubAll_more_sentIs]
        show sentIsB D.dS m s' = sentIsB D.dS m s
        unfold sentIsB
        rw [e]
      · by_cases h2 : name = "frame.sentIs1"
        · subst h2
          obtain rfl : [Rdr.link] = R := Option.some.inj h
          have e : s'.link? = s.link? := hs .link (by simp)
          rw [pubAll_more_sentIs1, pubAll_more_sentIs1]
          show sentIsB D.dS1 m s' = sentIsB D.dS1 m s
          unfold sentIsB
          rw [e]
        · by_cases h3 : name = "ledger.treesAre"
          · subst h3
            obtain rfl : [Rdr.fork] = R := Option.some.inj h
            have e : s'.fork? = s.fork? := hs .fork (by simp)
            rw [pubAll_more_treesAre, pubAll_more_treesAre]
            show treesAreB D.dS m s' = treesAreB D.dS m s
            unfold treesAreB
            rw [e]
          · by_cases h4 : name = "K5.okAt"
            · subst h4
              obtain rfl : [Rdr.fork, Rdr.heard5] = R := Option.some.inj h
              have e1 : s'.fork? = s.fork? := hs .fork (by simp)
              have e2 : s'.heard5? = s.heard5? := hs .heard5 (by simp)
              cases hA : D.d5.isAtt m with
              | true =>
                rw [pubAll_more_okAt D base m hA, pubAll_more_okAt D base m hA]
                show ((D.d5.W.A[m / 2]?).any fun p => H2K5.Door.okThereB (Att.P.geoOf p.S) s') =
                  ((D.d5.W.A[m / 2]?).any fun p => H2K5.Door.okThereB (Att.P.geoOf p.S) s)
                unfold H2K5.Door.okThereB
                rw [e1, e2]
              | false =>
                have h5 : H2K5.Door.k5Item D.d5 (.more (some m) "K5.okAt") = false := by
                  show (D.d5.isAtt m && _) = false
                  rw [hA]
                  rfl
                rw [pubAll_else D base _ rfl rfl rfl rfl rfl rfl h5 rfl rfl
                  (leftItem_off D.links m _ rfl) rfl,
                  pubAll_else D base _ rfl rfl rfl rfl rfl rfl h5 rfl rfl
                  (leftItem_off D.links m _ rfl) rfl]
                exact hb
            · by_cases h5 : name = "K5.plain"
              · subst h5
                obtain rfl : [Rdr.fork, Rdr.heard5] = R := Option.some.inj h
                have e1 : s'.fork? = s.fork? := hs .fork (by simp)
                have e2 : s'.heard5? = s.heard5? := hs .heard5 (by simp)
                cases hA : D.d5.isAtt m with
                | true =>
                  rw [pubAll_more_plain D base m hA, pubAll_more_plain D base m hA]
                  show ((D.d5.W.A[m / 2]?).any fun p => H2K5.Door.plainThereB p.iU3 p.nW s') =
                    ((D.d5.W.A[m / 2]?).any fun p => H2K5.Door.plainThereB p.iU3 p.nW s)
                  unfold H2K5.Door.plainThereB
                  rw [e1, e2]
                | false =>
                  have h6 : H2K5.Door.k5Item D.d5 (.more (some m) "K5.plain") = false := by
                    show (D.d5.isAtt m && _) = false
                    rw [hA]
                    rfl
                  rw [pubAll_else D base _ rfl rfl rfl rfl rfl rfl h6 rfl rfl
                  (leftItem_off D.links m _ rfl) rfl,
                    pubAll_else D base _ rfl rfl rfl rfl rfl rfl h6 rfl rfl
                  (leftItem_off D.links m _ rfl) rfl]
                  exact hb
              · by_cases h6 : name = "K5.liveReq"
                · subst h6
                  obtain rfl : [Rdr.link] = R := Option.some.inj h
                  have e : s'.link? = s.link? := hs .link (by simp)
                  cases hA : D.d5.isAtt m with
                  | true =>
                    rw [pubAll_more_liveReq D base m hA, pubAll_more_liveReq D base m hA]
                    show Att.P.liveReqB _ s' = Att.P.liveReqB _ s
                    unfold Att.P.liveReqB
                    rw [e]
                  | false =>
                    have h7 : H2K5.Door.k5Item D.d5 (.more (some m) "K5.liveReq") = false := by
                      show (D.d5.isAtt m && _) = false
                      rw [hA]
                      rfl
                    rw [pubAll_else D base _ rfl rfl rfl rfl rfl rfl h7 rfl rfl
                  (leftItem_off D.links m _ rfl) rfl,
                      pubAll_else D base _ rfl rfl rfl rfl rfl rfl h7 rfl rfl
                  (leftItem_off D.links m _ rfl) rfl]
                    exact hb
                · by_cases h7 : name = "K5.readsThere"
                  · subst h7
                    obtain rfl : [Rdr.here, Rdr.book] = R := Option.some.inj h
                    have e1 : s'.here = s.here := hs .here (by simp)
                    have e2 : s'.book = s.book := hs .book (by simp)
                    cases hA : D.d5.isAtt m with
                    | true =>
                      rw [pubAll_more_readsThere D base m hA, pubAll_more_readsThere D base m hA]
                      show H2K5.Door.readsThereB _ _ s' = H2K5.Door.readsThereB _ _ s
                      unfold H2K5.Door.readsThereB
                      rw [e1, e2]
                    | false =>
                      have h8 : H2K5.Door.k5Item D.d5 (.more (some m) "K5.readsThere") = false := by
                        show (D.d5.isAtt m && _) = false
                        rw [hA]
                        rfl
                      rw [pubAll_else D base _ rfl rfl rfl rfl rfl rfl h8 rfl rfl
                  (leftItem_off D.links m _ rfl) rfl,
                        pubAll_else D base _ rfl rfl rfl rfl rfl rfl h8 rfl rfl
                  (leftItem_off D.links m _ rfl) rfl]
                      exact hb
                  · simp [footOf, footBy, h1, h2, h3, h4, h5, h6, h7] at h
  | _ => simp [footOf, footBy] at h

/-- Every item of the list is booked, and all that it reads is left. -/
def ridesB (runs : Nat → Nat → String → List (Nat × String)) (keeps : List Rdr) (Q : List Pub) :
    Bool :=
  Q.all fun q => (footBy runs q).any fun R => R.all keeps.contains

/-- **Across a step that leaves `keeps`, every item of Q that was true stays true.** -/
theorem rides_of_B (keeps : List Rdr) (Q : List Pub) (h : ridesB D.runs keeps Q = true) (z : P)
    (s s' : S) (hs : SameOn D keeps s s') (hb : ∀ q ∈ Q, base q (z, s') = base q (z, s)) (q : Pub)
    (hq : q ∈ Q) (ht : pubAll D base q (z, s) = true) :
    pubAll D base q (z, s') = true := by
  have h1 := List.all_eq_true.1 h q hq
  cases hf : footBy D.runs q with
  | none => simp [hf] at h1
  | some R =>
    rw [hf] at h1
    have h2 : R.all keeps.contains = true := h1
    rw [pubAll_same D base q R hf z s s' (fun r hr => hs r (by
      have := List.all_eq_true.1 h2 r hr
      simpa using this)) (hb q hq)]
    exact ht

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.all_eq_of_mem
#print axioms VerifiableInference.Desc.First.pubAll_same
#print axioms VerifiableInference.Desc.First.rides_of_B
