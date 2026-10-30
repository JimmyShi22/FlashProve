-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookHeldK1.lean: the part of an honest prover that sends a sending (the kind of sub-protocol
that is named K1), `sendPart` (Johnson/Desc/ProofFile/Honest/K1/Part.lean), states exactly what the
key file's book of coins has for it (`Stated`, E2E/KeyBookLends.lean), at the three sendings of the
first chain: the index-mask message, the multiplicities and W. Two theorems are general in the job
and in what the book is made of; three are at the written sizes of the full size (`keyFull`,
Johnson/Goal/PlanValues/KeySizedReturns.lean). The book and the part are two separate definitions,
and neither calls the other. `Stated` is the hypothesis on each part under which `key_lends`
(E2E/KeyBookLendsNamed.lean) shows that the frame (Johnson/Desc/ProofFile/Honest/Frame.lean: the
types in which an honest prover is written, and the functions that run it) gives the parts at a
place their coins. E2E/KeyBookHeldK1Jobs.lean applies the three theorems to the key file's own jobs.
Definitions and theorems.

Terms. A book (`ProverCoinCounts`, in the frame) is the public table of how many coins (random field elements)
each part of a prover has; here it is `keyBook K` (E2E/KeyBook.lean), computed from the public data
K (`KeyPub`). A count (`Due`) is a number of coins in each of the two fields. A place (`Place`) is
the label of a sub-protocol; an address (`Addr`) is a place and the number of a part there. An entry
(`Ahead`) is a block of the coins of one part, its owner, that one other part, its spender, is given
too. A part (`Part`) states its own count (`takes`) and the names and counts of the entries that it
spends and carries. `Stated B rows a p` says that these three fields of p are what B has for the
address a: the count of a's row in the table rows (0 if it has none), and the names and counts of
the spent and of the carried entries whose spender is a. A notice (`OracleNotice`) is an oracle
message as it is announced. A sending (`Sending`) is the list of the oracle messages of one prover's
message, each with its counts of coins; `sendingOf` computes it from a list of codes, a number of
rounds k and a list of notices. A fill (`Fill`) says how a message's mask table is made of coins;
`fillOf k` gives a notice its fill. A face (`K3.Face`) holds a lookup's public numbers. A job
(`SendJob`) is what a caller gives `sendPart`: among its fields are `P`, the sending's parameters
(`K1.Par`, Johnson/Desc/K1/Send.lean, with the codes `P.codes` and the notices `P.sent`), and
`ride`, an `Option Ride` for each message's number. A `Ride`
(Johnson/Desc/ProofFile/Honest/K1/Coins.lean) is a table in a sending whose mask rows are computed
from fewer coins than they have entries: a fold's fresh table, given by the fold's rounds `k` and a
number `h` (2 ^ h rows). It has 2 k + 1 coins (`Ride.count`).

  `takes_held`: at every job J, number k and sending l, under hl and hr below: the part's own count
    `(sendPart J).takes` is the book's count `l.due` of the sending
  `k1_stated_of`: under hl and hr, at every K with two faces, every table rows and every address a
    that is at neither lookup's place, is the spender of no entry of `K.others` (the book's entries
    that are not the lookups') and has the count `l.due` in rows: `sendPart J` is `Stated` at
    `keyBook K`, rows and a
  `idx_stated`, `msg_stated`, `w_stated`: at the K of the written sizes, and at every job whose
    codes are those of `keyFull`, whose notices are those of the message at `keyFull` and whose
    `ride` passes `ridesOk`: `sendPart J` is `Stated` at `keyBook K`, at the first chain's table
    `(keyBook K).first` and at the address ⟨idxPlace, 0⟩ (the index-mask message), ⟨msgPlace, 0⟩
    (the multiplicities), ⟨wPlace, 0⟩ (W)
  `full_k1`: at the written sizes the book's three sendings are what `sendingOf` returns at the
    codes of `keyFull`: `K.sIdx` at the one notice `keyFull.once.input` and k = 0; `K.sMsg` at
    `Wf.messageOf keyFull.ranges.x` and `kRanges`; `K.sW` at what
    `linMessageW keyFull.once.shape` returns and `kOwn`. By evaluation in Lean's kernel
    (`decide +kernel`)
  `dueMsg_congr`, `startR_congr`: the part's count of a message (`dueMsg`) is the same at two
    `Option Ride` that are both `none` or have the same `count`; the count of the first n messages
    (`startR`) is the same at two families that agree in this way at every j below n
  `rides_of_ok`: where ns is `J.P.sent` and `ridesOk J.ride ns k` is true, hr holds
  `sendingPar_sent`: the notices (`sent`) of the parameters that the key file's description builds
    for a sending (`sendingPar`, Johnson/Desc/Key/One.lean) are the array msg that it is given
  `ridesOk ride ns k`: a definition: the executable test that, at every j below the size of ns,
    `ride j` and `rideOf` of the fill that `fillOf k` gives notice number j are both `none` or have
    the same `count`
  `kRanges`, `kOwn`: definitions: at `keyFull`, the rounds of the first fold of the ranges' test and
    of the own test. In the book these two folds spend the fresh tables that are sent along with the
    multiplicities and with W

By what. `(sendPart J).takes` is `dueR J.P J.ride` by definition. `sending_held`
(E2E/KeyBookHeld.lean) gives `l.due` as `dueR J.P (ridesOf J.P k)`, and `startR_congr` goes from the
job's tables to `ridesOf`: that is `takes_held`. `k1_stated_of`: `mine_off_looks` and `others_none`
(E2E/KeyBookLendsNamed.lean) show that the book has no entry whose spender is a; the part's `spends`
and `carries` are empty by definition; the count is `takes_held`. The three theorems are
`k1_stated_of` at `full_k1`, `rides_of_ok` and `full_two` (there are two lookups), brought to K by
`of_atFull` (both in E2E/KeyBookPassesNamed.lean); the hypotheses on the address hold by `decide`,
the one on the row by `rfl`. Definitions: `hasFor` (E2E/KeyBookLends.lean); `firstK`
(E2E/KeyBook.lean); `rideOf`, `ridesOf` (E2E/KeyBookHeld.lean); `fullPub`, `atFull`
(E2E/KeyBookAtWritten.lean); `KeyPub.others` (E2E/KeyBookPasses.lean); `toyPub`
(E2E/KeyBookTests.lean); the places (E2E/KeyPlaces.lean); `dueMsg`, `stepsOf`, `startR`, `dueR`
(K1/Coins.lean); `dueAt` (the frame); `Wf.messageOf` (OnBytes/Iop/Wf.lean); `linMessageW`
(OnBytes/Iop/Lin.lean).

Hypotheses. Of `takes_held` and `k1_stated_of`: hl: `sendingOf` returns l at the job's codes, k and
the job's notices. It returns nothing where a message has rows whose code the list lacks: there the
theorems are vacuous. hr: at every j below the number of the job's notices, `J.ride j` and the
book's `ridesOf J.P k j` are both `none` or have the same `count`. Of `k1_stated_of` only: hf: K has
exactly two faces. h0, h1: the place of a is neither `lookPlace 0` nor `lookPlace 1`. hrow:
`dueAt rows a` is `l.due`; rows is a free parameter, and nothing asks that it be a table of the
book. hn: a is not among the spenders of `toyPub.others`; by `others_spenders`
(E2E/KeyBookLendsNamed.lean) these are the spenders of `K.others` at every K. Of the three theorems:
hK: `fullPub = some K`. hc: the job's codes are `keyFull.codes`. hs: the job's notices are those
named at `full_k1`. hr: `ridesOk` is true at the job's `ride`, these notices and the same k. Of
`w_stated` also hw: `linMessageW keyFull.once.shape` returns w.

Limits.
- Counts only: a sending's part spends and carries nothing. Which coin the part puts where in its
  rows is not compared with the book's order here. Where each message's coins begin is compared in
  `starts_held` (E2E/KeyBookHeld.lean), at the tables `ridesOf P k`; no theorem here states it at a
  job's own tables.
- `ridesOk` compares `count` only, which reads the rounds `k` of a `Ride` and not `h`, the number
  that gives how many rows it has. It does not read `ride` from the size of ns on.
- Of a job the theorems read `P.codes`, `P.sent` and `ride` only. Nothing says that the job's own
  place `P.place` is the place of the address, or that the job passes `sendFits` (K1/Coins.lean),
  without which both moves of `sendPart` return an error.
- `sendPart` and `SendJob` are taken from K1/Part.lean, and the part's counts from K1/Coins.lean,
  which K1/Part.lean imports. If the count in the part's type is no longer `dueR J.P J.ride`,
  `takes_held` no longer compiles, and with it the four theorems on `Stated`.
- `full_k1` and the three theorems are at the one value `keyFull`. `k1_stated_of` is for two
  lookups.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookLendsNamed
import E2E.KeyBookHeld
import Johnson.Desc.ProofFile.Honest.K1.Part
import Johnson.Desc.Key.One

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyBook
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K3 (Face)
open ProofFile.Honest (Addr Due Part dueAt)
open ProofFile.Honest.K1 (Ride dueMsg stepsOf startR dueR SendJob sendPart)
open Johnson.Prover.Send (shapeAt)
open Lk6.AtPlan (keyFull)

variable {V W X : Type}

/-! ## 1 General in the job -/

theorem dueMsg_congr (codes : Codes) (s : OracleShape) (r r' : Option Ride)
    (h : r.map (·.count) = r'.map (·.count)) : dueMsg codes s r = dueMsg codes s r' := by
  unfold dueMsg stepsOf
  simp only [h]

theorem startR_congr (P : VerifiableInference.Desc.K1.Par) (ride ride' : Nat → Option Ride) :
    ∀ n, (∀ j, j < n → (ride j).map (·.count) = (ride' j).map (·.count)) →
      startR P ride n = startR P ride' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    unfold startR at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      ih fun j hj => h j (Nat.lt_succ_of_lt hj)]
    show Due.plus _ _ = Due.plus _ _
    rw [dueMsg_congr P.codes _ _ _ (h n (Nat.lt_succ_self n))]

/-- **The part's own count is the count of the book's sending.** Hypotheses: hl: `sendingOf` returns
l at the job's codes and notices. hr: at each message the job's `ride` and the book's `ridesOf` are
both `none` or have the same `count`. -/
theorem takes_held (J : SendJob W X) (k : Nat) (l : Sending)
    (hl : sendingOf J.P.codes k J.P.sent.toList = some l)
    (hr : ∀ j, j < J.P.sent.size → (J.ride j).map (·.count) = (ridesOf J.P k j).map (·.count)) :
    (sendPart (V := V) J).takes = l.due := by
  show dueR J.P J.ride = _
  rw [sending_held J.P k l hl]
  exact startR_congr J.P _ _ _ hr

/-- **The part states exactly what the book has for it**, at an address a that is at neither
lookup's place (h0, h1), is the spender of no entry of `K.others` (hn) and has the count `l.due` in
the table rows (hrow). hl and hr are those of `takes_held`; hf: K has two faces. -/
theorem k1_stated_of {K : KeyPub} {f₀ f₁ : Face} (hf : K.faces = [f₀, f₁]) (J : SendJob W X)
    (k : Nat) (l : Sending) (hl : sendingOf J.P.codes k J.P.sent.toList = some l)
    (hr : ∀ j, j < J.P.sent.size → (J.ride j).map (·.count) = (ridesOf J.P k j).map (·.count))
    (rows : List (Addr × Due)) (a : Addr) (h0 : a.place ≠ lookPlace 0) (h1 : a.place ≠ lookPlace 1)
    (hrow : dueAt rows a = l.due) (hn : (toyPub.others.map (·.spender)).contains a = false) :
    Stated (keyBook K) rows a (sendPart (V := V) J) := by
  unfold Stated hasFor
  rw [mine_off_looks hf a h0 h1, others_none K a hn, hrow]
  show ((sendPart (V := V) J).takes, ([] : List (String × Due)), ([] : List (String × Due))) = _
  rw [takes_held J k l hl hr]
  rfl

/-! ## 2 At the written sizes -/

/-- An executable test on a job's tables: at every j below the size of ns, `ride j` and `rideOf` of
the book's fill of notice number j are both `none` or have the same `count`. k: the rounds of the
fold that spends the fresh table. -/
def ridesOk (ride : Nat → Option Ride) (ns : Array OracleNotice) (k : Nat) : Bool :=
  (List.range ns.size).all fun j =>
    (ride j).map (·.count) == (rideOf (fillOf k (ns.getD j default))).map (·.count)

theorem rides_of_ok {J : SendJob W X} {ns : Array OracleNotice} {k : Nat} (hs : J.P.sent = ns)
    (h : ridesOk J.ride ns k = true) :
    ∀ j, j < J.P.sent.size → (J.ride j).map (·.count) = (ridesOf J.P k j).map (·.count) := by
  intro j hj
  unfold ridesOf
  rw [hs] at hj ⊢
  exact beq_iff_eq.1 (List.all_eq_true.1 h j (List.mem_range.2 hj))

/-- The rounds of the first fold of the ranges' test at `keyFull`. In the book this fold spends the
fresh table that is sent along with the multiplicities. -/
def kRanges : Nat := firstK keyFull.ranges.x.stages
/-- The same for the own test: its first fold spends the fresh table that is sent along with W. -/
def kOwn : Nat := firstK keyFull.once.shape.testOwn

theorem full_k1 : atFull (fun K =>
    sendingOf keyFull.codes 0 #[keyFull.once.input].toList == some K.sIdx &&
      sendingOf keyFull.codes kRanges (Wf.messageOf keyFull.ranges.x).toList == some K.sMsg &&
      ((linMessageW keyFull.once.shape).bind fun w => sendingOf keyFull.codes kOwn w.toList) ==
        some K.sW) = true := by decide +kernel

section Full
variable (K : KeyPub) (hK : fullPub = some K) (J : SendJob W X) (hc : J.P.codes = keyFull.codes)
include hK hc

/-- **The part of a job that has the index-mask message's notice is `Stated` at ⟨idxPlace, 0⟩.** -/
theorem idx_stated (hs : J.P.sent = #[keyFull.once.input])
    (hr : ridesOk J.ride #[keyFull.once.input] 0 = true) :
    Stated (keyBook K) (keyBook K).first ⟨idxPlace, 0⟩ (sendPart (V := V) J) := by
  obtain ⟨f₀, f₁, hf⟩ := List.length_eq_two.1 (by simpa using of_atFull full_two hK)
  have h := of_atFull full_k1 hK
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact k1_stated_of hf J 0 K.sIdx (by rw [hc, hs]; exact h.1.1) (rides_of_ok hs hr) _ _
    (by decide) (by decide) rfl (by decide)

/-- **The part of a job that has the multiplicities' notices is `Stated` at ⟨msgPlace, 0⟩.** -/
theorem msg_stated (hs : J.P.sent = Wf.messageOf keyFull.ranges.x)
    (hr : ridesOk J.ride (Wf.messageOf keyFull.ranges.x) kRanges = true) :
    Stated (keyBook K) (keyBook K).first ⟨msgPlace, 0⟩ (sendPart (V := V) J) := by
  obtain ⟨f₀, f₁, hf⟩ := List.length_eq_two.1 (by simpa using of_atFull full_two hK)
  have h := of_atFull full_k1 hK
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact k1_stated_of hf J kRanges K.sMsg (by rw [hc, hs]; exact h.1.2) (rides_of_ok hs hr) _ _
    (by decide) (by decide) rfl (by decide)

/-- **The part of a job that has the notices w of W's message is `Stated` at ⟨wPlace, 0⟩.** w: what
`linMessageW` returns at the shape `keyFull.once.shape`. -/
theorem w_stated (w : Array OracleNotice) (hw : linMessageW keyFull.once.shape = some w)
    (hs : J.P.sent = w) (hr : ridesOk J.ride w kOwn = true) :
    Stated (keyBook K) (keyBook K).first ⟨wPlace, 0⟩ (sendPart (V := V) J) := by
  obtain ⟨f₀, f₁, hf⟩ := List.length_eq_two.1 (by simpa using of_atFull full_two hK)
  have h := of_atFull full_k1 hK
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have h3 := h.2
  rw [hw] at h3
  exact k1_stated_of hf J kOwn K.sW (by rw [hc, hs]; exact h3) (rides_of_ok hs hr) _ _
    (by decide) (by decide) rfl (by decide)

end Full

/-- The notices of the parameters that the description builds for a sending (`sendingPar`) are the
array msg that it is given. -/
theorem sendingPar_sent (one : OneTime) (piece : Nat) (what : String) (msg : Array OracleNotice)
    (groups : List (List Nat)) :
    (VerifiableInference.Desc.Key.sendingPar one piece what msg groups).sent = msg := by
  show ([(what, msg)].flatMap (·.2.toList)).toArray = msg
  simp

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.takes_held
#print axioms AtPublicFiles.KeyBook.k1_stated_of
#print axioms AtPublicFiles.KeyBook.full_k1
#print axioms AtPublicFiles.KeyBook.idx_stated
#print axioms AtPublicFiles.KeyBook.msg_stated
#print axioms AtPublicFiles.KeyBook.w_stated
#print axioms AtPublicFiles.KeyBook.sendingPar_sent
#print axioms AtPublicFiles.KeyBook.dueMsg_congr
#print axioms AtPublicFiles.KeyBook.startR_congr
#print axioms AtPublicFiles.KeyBook.ridesOk
#print axioms AtPublicFiles.KeyBook.rides_of_ok
#print axioms AtPublicFiles.KeyBook.kRanges
#print axioms AtPublicFiles.KeyBook.kOwn
