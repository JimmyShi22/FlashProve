-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookHeld.lean: two counts of the coins of an oracle message are shown equal: the count from
which the key file's book of coins is made (`msgCoins`, E2E/KeyBook.lean) and the count of the part
that sends the message (`dueMsg`, Johnson/Desc/ProofFile/Honest/K1/Coins.lean). A book (`ProverCoinCounts`) is a
structure of the frame (Johnson/Desc/ProofFile/Honest/Frame.lean: the types in which an honest
prover is written): the public table of how many coins (random field elements) each part of the
prover has. Three main theorems, general in the list of codes, in the notice and in a place's
parameters; then tests (`#guard`) at the written sizes of the full size (`keyFull`,
Johnson/Goal/PlanValues/KeySizedReturns.lean).

Why. The frame returns an error for a part that takes more or fewer coins than the book has for it
(`lendPart`). The two counts are two separate definitions, and neither calls the other, on purpose:
the docstring of `ProverCoinCounts` says that a book is a check only if it is computed independently of the
definitions of the prover's sides. This file shows that the two agree.

Terms. A count (`Due`) is a number of coins in each of the two fields. A notice (`OracleNotice`) is
an oracle message as it is announced: its shape and its class of leaves. A sending (`Sending`) is
the list of the oracle messages of one prover's message, each with its counts of coins (`MsgCoins`).
A fill (`Fill`) says how a message's mask table is made of coins. `all`: every entry is a coin.
`fresh k`: a fold's fresh table, made of the 2 k + 1 coefficients of the hiding polynomial of a fold
of k rounds. `room c`: the oracle message that a code switch sends: all entries but c of them are
coins. A place (`Place`) is the label of a sub-protocol. P is a `K1.Par`
(Johnson/Desc/K1/Send.lean): the parameters of a sending at a place, among them its list of codes
`P.codes` and its notices `P.sent`. The sender is the frame's part for a sending, `sendPart`
(Johnson/Desc/ProofFile/Honest/K1/Part.lean, not imported here); its counts are in K1/Coins.lean. A
`Ride` (same file) is a table in a sending whose mask rows are computed from fewer coins than they
have entries: a fold's fresh table, given by the fold's rounds `k` and a number `h` (2 ^ h rows).
The sender's counts take an `Option Ride` for each message.

  `due_held`: at every list of codes, every notice n and every fill but `room c`: where `msgCoins`
    returns counts m, the count `m.due` is `dueMsg` at the shape of n and at `rideOf` of the fill
  `starts_held`: at every P and k, where `sendingOf` returns a sending l at the codes and notices of
    P: for every j up to the number of notices, the count of the first j messages of l
    (`startAt l j`) is the sender's `startR P (ridesOf P k) j`. So each message's coins begin at the
    same numbers in both
  `sending_held`: under the same hypothesis the sending's whole count `l.due` is
    `dueR P (ridesOf P k)`. `dueR P ride` is the count in the type of the sender's part at the
    parameters P and the tables `ride`
  `sending_at`: where `sendingOf` returns l at a list of notices: l is as long as that list, and its
    message number j is what `msgCoins` returns at notice number j and the fill that `fillOf k`
    gives it
  `fill_not_room`: `fillOf` returns no `room c`
  `rideOf`, `ridesOf P k`: definitions: a fill as an `Option Ride`: `fresh k` is the `Ride` of k
    rounds with `h` at 0, every other fill is `none`; and, for each message's number at P, `rideOf`
    of the fill that `fillOf k` gives its notice
  `heldAt codes k l`: a definition: the executable test that, at every notice of l and the fill that
    `fillOf k` gives it, `msgCoins` returns counts whose `due` is the sender's `dueMsg`

Tests, at `keyFull` and at one answer to a sample. The notices are those of `sentAt`
(E2E/KeyBook.lean), which lists nine places there. `heldAt` is true at the five sendings outside the
proximity tests; at the fresh table that the first fold of Omega's test sends itself; and, at all
four tests, at what is sent along with each code switch's own message (a later fold's fresh table,
or the masking word). One more test shows that the comparison can fail: with k rounds on the book's
side and k + 1 on the sender's, the counts of the multiplicities' sending are not all equal.

By what. `due_held` unfolds both definitions: `msgCoins` with `mainDue`, `maskDue`, `mainOf`,
`maskOf` and `RowsDue.tails` (E2E/RowCode.lean), and `dueMsg` with `stepsOf`, `Steps.main` and
`Ride.count` (K1/Coins.lean); then it goes through the fills. `sending_at` is by induction on the
notices. `starts_held` is by induction on j, from `sending_at`, `due_held` and `fill_not_room`;
`shapeAt` (Johnson/Prover/Send/Core.lean), which `startR` calls, is the shape of notice number j.
`sending_held` is `starts_held` at the number of notices. `atFull` (E2E/KeyBookAtWritten.lean)
applies a test to what the book is made of at `keyFull`, and is false where that is not made.

Hypotheses. Of `due_held`: hf: the fill is no `room c`. h: `msgCoins` returns m. It returns nothing
where a sort of rows that the message has names a code that the list lacks: there the theorem is
vacuous, while `dueMsg` is total and reads the default code. Of `starts_held` and `sending_held`: h:
`sendingOf` returns l, that is, `msgCoins` returns counts at every notice of P.

Limits.
- The fill `room c` (the oracle message that a code switch sends) has no counterpart in the sender's
  definitions: it is compared in no theorem and in no test. The tests drop the first message of each
  code switch's sending.
- Counts only. That the two definitions put the coins in the same order inside a count is not shown
  here.
- `ridesOf` is computed from the book's own `fillOf`, and `rideOf` sets `h` to 0; `Ride.count` reads
  `k` only. Which tables a job of the sender's names (`SendJob.ride`) is not compared here:
  `takes_held` (E2E/KeyBookHeldK1.lean) has that as a hypothesis.
- The sender's counts (`stepsOf`, `dueMsg`, `startR`, `dueR`) are taken from K1/Coins.lean, and
  `shapeAt` from Johnson/Prover/Send/Core.lean, which K1/Coins.lean imports. If the sender's count
  of a message changes, `due_held` no longer compiles: that is its use.
- The tests are run by Lean's evaluator, not checked by its kernel, and at the one value `keyFull`.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookAtWritten
import Johnson.Desc.ProofFile.Honest.K1.Coins

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open OnBytes
open AtPublicFiles.RowCode (RowsDue mainDue maskDue mainOf maskOf)
open ProofFile.Honest (Due)
open ProofFile.Honest.K1 (Ride dueMsg stepsOf Steps startR dueR)
open Johnson.Prover.Send (shapeAt)
open Lk6.AtPlan (keyFull)

/-- A fill as the sender's counts take it: `fresh k` is a fold's fresh table of k rounds, with `h`
at 0 (`Ride.count` does not read `h`); at every other fill there is no `Ride`. -/
def rideOf : Fill → Option Ride
  | .fresh k => some ⟨k, 0⟩
  | _ => none

/-- **Where `msgCoins` returns a count, it is the sender's `dueMsg`.** Hypothesis hf: the fill is no
`room c`. -/
theorem due_held (codes : Codes) (n : OracleNotice) (fill : Fill) (hf : ∀ c, fill ≠ .room c)
    (m : MsgCoins) (h : msgCoins codes n fill = some m) :
    m.due = dueMsg codes n.shape (rideOf fill) := by
  unfold msgCoins at h
  split at h
  · rename_i a b ha hb
    obtain rfl := Option.some.inj h
    have hA : (a.map RowsDue.tails).sum =
          n.shape.mainRows * (codes.base.getD n.shape.code default).r ∧
        (a.map fun d => d.rows * d.code.ell).sum =
          n.shape.mainRows * (codes.base.getD n.shape.code default).ell := by
      unfold mainDue at ha
      split at ha
      · rename_i h0
        obtain rfl := Option.some.inj ha
        simp [h0]
      · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 ha
        have : codes.base.getD n.shape.code default = c := by
          unfold mainOf at hc
          rw [Array.getD_eq_getD_getElem?, hc]
          rfl
        simp [RowsDue.tails, this]
    have hB : (b.map RowsDue.tails).sum =
          n.shape.maskRows * (codes.mask.getD n.shape.maskCode default).r ∧
        (b.map fun d => d.rows * d.code.ell).sum =
          n.shape.maskRows * (codes.mask.getD n.shape.maskCode default).ell := by
      unfold maskDue at hb
      split at hb
      · rename_i h0
        obtain rfl := Option.some.inj hb
        simp [h0]
      · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hb
        have : codes.mask.getD n.shape.maskCode default = c := by
          unfold maskOf at hc
          rw [Array.getD_eq_getD_getElem?, hc]
          rfl
        simp [RowsDue.tails, this]
    have hp : (if n.shape.maskRows == 0 then
          (if n.shape.mainDeg == 3 then 1 else 3) * n.shape.answers
        else 0) = (if n.shape.maskRows == 0 && n.shape.answers != 0 then
          (if n.shape.mainDeg == 3 then 1 else 3) * n.shape.answers else 0) := by
      by_cases h1 : n.shape.maskRows = 0 <;> by_cases h2 : n.shape.answers = 0 <;> simp [h1, h2]
    cases fill with
    | room c => exact absurd rfl (hf c)
    | all =>
      simp only [MsgCoins.due, dueMsg, stepsOf, Steps.main, rideOf, hA.1, hA.2, hB.1, hB.2, hp,
        Option.map_none, Option.getD_none]
      split <;> simp [Nat.add_assoc]
    | fresh k =>
      simp only [MsgCoins.due, dueMsg, stepsOf, Steps.main, rideOf, hA.1, hA.2, hB.1, hp,
        Option.map_some, Option.getD_some, Ride.count]
      split <;> simp [Nat.add_assoc]
  · cases h

/-! ## A whole sending -/

theorem fill_not_room (k : Nat) (n : OracleNotice) : ∀ c, fillOf k n ≠ .room c := by
  intro c
  unfold fillOf
  split <;> exact fun h => Fill.noConfusion h

/-- What `sendingOf` returns, message by message: as many messages as notices, and message number j
is what `msgCoins` returns at notice number j. -/
theorem sending_at (codes : Codes) (k : Nat) : ∀ (ns : List OracleNotice) (l : Sending),
    sendingOf codes k ns = some l → l.length = ns.length ∧
      ∀ j (hj : j < ns.length), ∃ m, l[j]? = some m ∧ msgCoins codes ns[j] (fillOf k ns[j]) = some m
  | [], l, h => by
    obtain rfl : [] = l := by simpa [sendingOf] using h
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | n :: ns, l, h => by
    unfold sendingOf at h
    rw [List.mapM_cons] at h
    cases hm : msgCoins codes n (fillOf k n) with
    | none => simp [hm] at h
    | some m =>
      cases hr : ns.mapM (fun n => msgCoins codes n (fillOf k n)) with
      | none => simp [hm, hr] at h
      | some r =>
        obtain rfl : m :: r = l := by simpa [hm, hr] using h
        obtain ⟨i1, i2⟩ := sending_at codes k ns r hr
        refine ⟨by rw [List.length_cons, List.length_cons, i1], fun j hj => ?_⟩
        cases j with
        | zero => exact ⟨m, rfl, hm⟩
        | succ j => exact i2 j (Nat.lt_of_succ_lt_succ hj)

/-- For each message's number at a place: its `Ride`, if the book's fill of the message is a fresh
table. This is the form in which the sender's counts take it. k: the rounds of the fold that spends
the fresh table that is sent along in the sending. -/
def ridesOf (P : VerifiableInference.Desc.K1.Par) (k : Nat) (j : Nat) : Option Ride :=
  rideOf (fillOf k (P.sent.getD j default))

/-- **In a sending, each message's coins begin where the sender's `startR` has them.** -/
theorem starts_held (P : VerifiableInference.Desc.K1.Par) (k : Nat) (l : Sending)
    (h : sendingOf P.codes k P.sent.toList = some l) :
    ∀ j, j ≤ P.sent.size → startAt l j = startR P (ridesOf P k) j := by
  obtain ⟨hl, hm⟩ := sending_at P.codes k _ l h
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hj' : j < P.sent.toList.length := by simpa using hj
    obtain ⟨m, e1, e2⟩ := hm j hj'
    have hjl : j < l.length := by rw [hl]; exact hj'
    have hn : P.sent.toList[j] = P.sent.getD j default := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hj')]
      simp
    unfold startAt startR at ih ⊢
    rw [List.take_add_one, List.foldl_append, ih (Nat.le_of_succ_le hj), List.range_succ,
      List.foldl_append, e1]
    show Due.plus _ m.due = Due.plus _ (dueMsg P.codes (shapeAt P j) (ridesOf P k j))
    rw [due_held P.codes _ _ (fill_not_room k _) m e2, hn]
    rfl

/-- **A sending's whole count is `dueR`, the count in the type of the sender's part.** -/
theorem sending_held (P : VerifiableInference.Desc.K1.Par) (k : Nat) (l : Sending)
    (h : sendingOf P.codes k P.sent.toList = some l) : l.due = dueR P (ridesOf P k) := by
  have hl := (sending_at P.codes k _ l h).1
  unfold Sending.due dueR
  rw [hl, Array.length_toList]
  exact starts_held P k l h _ (Nat.le_refl _)

/-- The test: at every notice of the list `msgCoins` returns a count, and it is the sender's
`dueMsg`. k: the rounds of the fold that spends the fresh table that is sent along in it. -/
def heldAt (codes : Codes) (k : Nat) (l : List OracleNotice) : Bool :=
  l.all fun n => (msgCoins codes n (fillOf k n)).map (·.due) ==
    some (dueMsg codes n.shape (rideOf (fillOf k n)))

-- `sentAt` lists nine places; then the five sendings outside the proximity tests
#guard ((sentAt keyFull 1).getD []).length == 9
#guard atFull fun K =>
  [(idxPlace, 0), (msgPlace, firstK K.rng), (wPlace, firstK K.own), (foldedPlace, firstK K.folded),
    (omegaPlace, 0)].all fun x =>
      ((((sentAt keyFull 1).getD []).lookup x.1).getD []).all (heldAt keyFull.codes x.2)
-- sent along with a code switch's own message: the later folds' fresh tables, the masking words
#guard atFull fun K =>
  [(rngPlace, K.rng), (foldedTestPlace, K.folded), (ownTestPlace, K.own)].all fun x =>
    ((((sentAt keyFull 1).getD []).lookup x.1).getD []).zipIdx.all fun s =>
      heldAt keyFull.codes (x.2.getD (s.2 + 1) default).k (s.1.drop 1)
-- Omega's test: its first sending is the fresh table that its first fold sends itself; then its
-- code switches, as above
#guard atFull fun K =>
  match (((sentAt keyFull 1).getD []).lookup omegaTestPlace).getD [] with
  | own :: switches =>
    heldAt keyFull.codes (firstK K.omega) own &&
      switches.zipIdx.all fun s =>
        heldAt keyFull.codes (K.omega.getD (s.2 + 1) default).k (s.1.drop 1)
  | [] => false
-- the test can fail: the book's count at k rounds of the fold, the sender's at k + 1 rounds
#guard atFull fun K => !((Wf.messageOf keyFull.ranges.x).toList.all fun n =>
  (msgCoins keyFull.codes n (fillOf (firstK K.rng) n)).map (·.due) ==
    some (dueMsg keyFull.codes n.shape (rideOf (fillOf (firstK K.rng + 1) n))))

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.due_held
#print axioms AtPublicFiles.KeyBook.starts_held
#print axioms AtPublicFiles.KeyBook.sending_held
#print axioms AtPublicFiles.KeyBook.rideOf
#print axioms AtPublicFiles.KeyBook.fill_not_room
#print axioms AtPublicFiles.KeyBook.sending_at
#print axioms AtPublicFiles.KeyBook.ridesOf
#print axioms AtPublicFiles.KeyBook.heldAt
