-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Bridge.lean: the honest sender at public parameters P and ride, written as an
instance (sender P ride) of the general model of a sending, with every row, coin and answer read
over the base field; and seven statements, each under public premises, that connect the sender with
the instance.
Terms: Johnson/SendSim/At/Sim.lean; for the general model, Johnson/SendSim/Defs.lean; the terms of
the instance have their home here, in the paragraph "Terms of the instance" below. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file has. Definitions and statements only.
  sender P ride   The instance, of the type Sender GF, where GF is the base field. Its rows, message
                  coins and answers are named by the types RowN, CoinN and AnsN. Its field lay, the
                  message coins' contribution to the rows' messages, is the honest sender's own
                  function rowsR at no data, at the coins that hold s at their names and 0 elsewhere
                  (put s). So no second definition of how the sender places its coins is written.
  readC, dataOf, wOf, asksOf   The translation. The sender's coins, its data, the seeds in the
                  challenge ds and the queried positions become the instance's coins, data, weights
                  and list of queries (row, point).
  RidesAdd, RidesZero   Two premises on ride alone, at the 2 ^ h rows of each table that is sent
                  along. RidesAdd: the table's entries (Ride.lay) are additive in the table's coins.
                  RidesZero, which requires less: coins that are all 0 give entries that are 0.
                  Neither is proved here; both hold for every ride (ridesAdd, ridesZero).
The seven statements are named propositions. Each is proved under the same name without "Spec.".
Each speaks of all P and ride at which the job fits its place (sendFits). "The two premises on the
seeds" are that the challenge consists of exactly the seeds (seedsFit) and that no seed's factor is
0.
  Spec.shownTie   Under RidesZero and the two premises on the seeds, there is one function back such
                  that, for all data and all coins c, what the sender discloses in its two rounds
                  (shownR) is back applied to what the instance discloses (Sender.shown) at dataOf
                  data and readC c.
  Spec.readUnif   Under readC the uniform distribution on the sender's coins has as its image the
                  uniform distribution on the instance's coins.
  Spec.readOnto   readC is surjective.
  Spec.withinOf   If the queried positions are within the bound budAt, then the list asksOf is
                  within the model's bound (Sender.Within): of each row at most as many distinct
                  points as the row's tail has entries.
  Spec.mendsOf    Under RidesZero and the two premises on the seeds, the premise Mends of
                  Spec.sendExact holds at the weights wOf: for any values of the answers there is a
                  family of message coins, at which lay is additive, that contributes them.
  Spec.padsOf     Under the same premises the instance has pads in the sense of Sender.Pads: each
                  answer has a coin of its own.
  Spec.additiveOf   Under RidesAdd, lay is additive.

Limits. Where the job does not fit its place, sender P ride is still a term of its type, and no
statement here says anything about it.

Terms of the instance.
  read over the base field   An element of the extension field GE is written as its three
                  coordinates over GF with respect to 1, θ, θ² (crd,
                  Johnson/SendSim/Tie/Coord.lean). So a row over GE is three rows over GF at the
                  same evaluation points, a coin of GE is three coins, and an answer is three
                  answers, each a linear form over GF in the rows' entries.
  name            An element of RowN, CoinN or AnsN. RowN: an oracle message, one of its main or
                  mask rows, and a coordinate. CoinN: an oracle message, one of its coins that are
                  in rows' messages, and a coordinate. AnsN: an oracle message, one of its answers,
                  and a coordinate. A row or coin over GF has the one coordinate 0. A tail coin has
                  no name in CoinN: as in the model, it is given by its row and its number in the
                  tail (TailN, Johnson/SendSim/At/Onto.lean).
  slot            Seat (Johnson/Desc/ProofFile/Honest/K1/Seat.lean): a location in an oracle message
                  that holds a coin. There are five kinds: an entry of a main row's tail; an entry
                  of a main row, in an oracle message that has main rows and no answer; an entry of
                  a pad that is in a main row; a mask coin, which is an entry of a mask row or, in a
                  table that is sent along, one of its 2k + 1 coins; an entry of a mask row's tail.
  number          The sender's coins, of the type Cs (dueR P ride), are two arrays, one for each
                  field. A coin's number is its index in its array. Seat.no gives the number of the
                  coin at a slot.
  put s           the sender's coins that hold each value of s, a family indexed by CoinN, at its
                  name's number and coordinate, and 0 everywhere else.
  the instance's answers   Let y be an answer of the sender and β, not 0, its seed's factor. The
                  instance's three answers are the coordinates of y / β, not of y. So each of the
                  three coins over GF of the answer's pad contributes 1 to one of the three and 0 to
                  the others, and each answer of the instance has one coin of its own, as
                  Sender.Pads (Johnson/SendSim/Pads.lean) requires.

How it fits. A bare file name in this paragraph and in the Notes is a file of Johnson/SendSim/At/.
The seven proofs are in Shown.lean, ReadUnif.lean, Onto.lean, Within.lean, MendsOf.lean, PadsOf.lean
and Additive.lean, in the order of the list above; ridesAdd and ridesZero are in RideLay.lean.
Paid.lean restates shownTie, mendsOf, padsOf and additiveOf without RidesZero or RidesAdd.
JoinRows.lean applies the general model's two theorems, sendExact and sendFresh
(Johnson/SendSim/CoreProofs.lean), to the instance and carries the result over to shownR. rowsExact
(RowsExact.lean) uses shownTie, readUnif, withinOf and mendsOf. rowsFresh (RowsFresh.lean) and
rowsFreshAny (FreshWideProofs.lean) use shownTie, readUnif, withinOf and, for the model's premise
MendsOff, additiveOf. readOnto serves readUnif and spentUnif (SpentUnif.lean). Only pads_paid
(Paid.lean), which nothing uses, applies padsOf. The proofs must know which coin is an answer's pad,
and use share_of (PadsOf.lean) or padsAt (PadSeat.lean) instead. rowsR is defined in
Johnson/Desc/ProofFile/Honest/K1/Coins.lean.

The other names.
  dg, stp, co     the number of coordinates of a main row's entries (3 or 1); an oracle message's
                  five numbers of coins, one for each kind of slot; a natural number as a
                  coordinate.
  seatC, seatT    the slot and coordinate of a message coin's name; of an entry of a row's tail.
  coinAt          the coordinate of the sender's coin at a slot.
  entry, tailEntry   an entry of a row's message, and of its tail, read over the base field, in a
                  family of values of the type Rows (Johnson/Prover/Send/Core.lean), one for each
                  oracle message.
  codeAt, seedAt  a row's code; the seed of an answer, by the answer's number in its oracle message.
  treeOf          the tree of an oracle message, if it is in one (Own.treesMade,
                  Johnson/Desc/Own/Trees.lean). asksOf has no query for a row whose oracle message
                  is in no tree.

Notes: default values, and where they can end up.
  - co reduces a number modulo 3. It is applied only to numbers below 3 (dg_le, seatC_lt, seatT_lt,
    Put.lean).
  - cf and ce (Johnson/Desc/ProofFile/Honest/K1/Coins.lean) read 0 at a number beyond the sender's
    number of coins. No message coin's name and no tail coin has its number there (seat_in,
    Johnson/Desc/ProofFile/Honest/K1/Seat.lean; seatC_ok, seatT_ok, Put.lean).
  - seedAt gives the default seed where the list of seeds is too short. At an answer of an oracle
    message that does not happen: an oracle message has at most as many answers as P has seeds
    (seedAt_get, Seeds.lean).
  - The inverse of a factor 0 is 0, by the field's convention. It can end up only in the weights
    wOf, and the statements of this file that name wOf have the premise that no factor is 0.
  - In two places coins are set to 0 by design: dataOf reads the sender's rows at coins that are all
    0, and put has 0 at the number of every tail coin. Neither is in a simulator. The purpose is to
    write a row's message as the sum of dataOf data and lay (readC c).1, if the job fits its place
    and RidesZero holds (entry_split, Split.lean). The coins themselves are read by readC, at their
    own numbers. By inspection, not proved: no other default value takes the place of a coin.
-/
import Johnson.Desc.ProofFile.Honest.K1.Seat
import Johnson.Desc.K1.Law.Law
import Johnson.SendSim.At.Sim
import Johnson.SendSim.Tie.SymF
import Johnson.SendSim.Tie.Coord
import Johnson.SendSim.Pads

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc Prob
open Johnson.Prover.Send (Rows shapeAt)

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- The number of coordinates over the base field of an entry of a main row of oracle message k: 3
if the main rows are over the extension field, else 1. -/
def dg (k : ℕ) : ℕ := if (shapeAt P k).mainDeg == 3 then 3 else 1

/-- Oracle message k's five numbers of coins, one for each kind of slot (Steps,
Johnson/Desc/ProofFile/Honest/K1/Coins.lean). -/
def stp (k : ℕ) : Steps := stepsOf P.codes (shapeAt P k) (ride k)

/-- A natural number as a coordinate, reduced modulo 3. -/
def co (t : ℕ) : Fin 3 := ⟨t % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The names of the instance's rows: an oracle message k, and either one of its main rows with one
of dg P k coordinates or one of its mask rows with one of 3 coordinates. -/
abbrev RowN : Type :=
  (k : Fin P.sent.size) × ((Fin (shapeAt P k).mainRows × Fin (dg P k)) ⊕
    (Fin (shapeAt P k).maskRows × Fin 3))

/-- The names of the instance's message coins: an oracle message k, and either a coin in its main
rows (an entry of the main rows of an oracle message without an answer, or an entry of a pad) with
one of dg P k coordinates, or a mask coin with one of 3 coordinates. The tail coins are not among
them. -/
abbrev CoinN : Type :=
  (k : Fin P.sent.size) × (((Fin (stp P ride k).word ⊕ Fin (stp P ride k).pad) × Fin (dg P k)) ⊕
    (Fin (stp P ride k).mask × Fin 3))

/-- The names of the instance's answers: an oracle message k, one of its answers, and one of 3
coordinates. -/
abbrev AnsN : Type := (k : Fin P.sent.size) × (Fin (shapeAt P k).answers × Fin 3)

/-- The slot (Seat) and the coordinate of a message coin's name. -/
def seatC (n : CoinN P ride) : Seat × ℕ :=
  match n.2 with
  | .inl (.inl i, t) =>
    (.word (i.val / (P.codes.base.getD (shapeAt P n.1).code default).ell)
      (i.val % (P.codes.base.getD (shapeAt P n.1).code default).ell), t.val)
  | .inl (.inr i, t) => (.pad i.val, t.val)
  | .inr (i, t) => (.mask i.val, t.val)

/-- The slot and the coordinate of entry q of the tail of the row ρ. -/
def seatT (ρ : RowN P) (q : ℕ) : Seat × ℕ :=
  match ρ.2 with
  | .inl (r, t) => (.tail r.val q, t.val)
  | .inr (r, t) => (.maskTail r.val q, t.val)

/-- What the sender's coins c hold, over the base field, at a slot x.1 of oracle message k and a
coordinate x.2. If the slot's coin is in the extension field, it is that coordinate of the coin with
the slot's number; else it is the base field's coin with that number, whatever x.2 is. -/
def coinAt (c : Cs (dueR P ride)) (k : ℕ) (x : Seat × ℕ) : GF :=
  if x.1.inE (shapeAt P k) then crd (co x.2) (ce c (x.1.no P ride k)) else cf c (x.1.no P ride k)

/-- Coins of the sender made from values s at the names in CoinN: each value is at its name's number
and coordinate, and everything else, so every tail coin, is 0. That each value is read back at its
name is coinAt_put (Johnson/SendSim/At/Put.lean). -/
def put (s : CoinN P ride → GF) : Cs (dueR P ride) where
  f := fun i => ∑ n : CoinN P ride,
    if (seatC P ride n).1.inE (shapeAt P n.1) = false ∧ (seatC P ride n).1.no P ride n.1 = i.val
    then s n else 0
  e := fun i => against fun t => ∑ n : CoinN P ride,
    if (seatC P ride n).1.inE (shapeAt P n.1) = true ∧ (seatC P ride n).1.no P ride n.1 = i.val ∧
      co (seatC P ride n).2 = t
    then s n else 0

/-- Entry j of the message of the row ρ, read over the base field, where V gives the rows of each
oracle message (Rows, Johnson/Prover/Send/Core.lean). -/
def entry (V : ℕ → Rows) (ρ : RowN P) (j : ℕ) : GF :=
  match ρ.2 with
  | .inl (r, t) =>
    if (shapeAt P ρ.1).mainDeg == 3 then crd (co t.val) ((V ρ.1).mainE r.val j)
    else (V ρ.1).mainF r.val j
  | .inr (r, t) => crd t ((V ρ.1).mask r.val j)

/-- Entry q of the tail of the row ρ, read over the base field, in the same V. -/
def tailEntry (V : ℕ → Rows) (ρ : RowN P) (q : ℕ) : GF :=
  match ρ.2 with
  | .inl (r, t) =>
    if (shapeAt P ρ.1).mainDeg == 3 then crd (co t.val) ((V ρ.1).mainTlE r.val q)
    else (V ρ.1).mainTlF r.val q
  | .inr (r, t) => crd t ((V ρ.1).maskTl r.val q)

/-- The code of the row ρ: its oracle message's base code for a main row, its mask code for a mask
row. -/
def codeAt (ρ : RowN P) : Fmt.M1.Code :=
  match ρ.2 with
  | .inl _ => codeOf (P.codes.base.getD (shapeAt P ρ.1).code default)
  | .inr _ => codeOf (P.codes.mask.getD (shapeAt P ρ.1).maskCode default)

/-- The instance of the general model at P and ride. A row's tail and message have the lengths r and
l of the row's code. lay s is the honest sender's rowsR at no data and at the coins put P ride s,
read row by row through entry. -/
def sender : Sender GF where
  Row := RowN P
  r := fun ρ => (codeAt P ρ).r
  l := fun ρ => (codeAt P ρ).l
  Cn := CoinN P ride
  lay := fun s => entry P (rowsR P ride (fun _ _ _ => none) (put P ride s))
  Ans := AnsN P

/-- The honest sender's coins c as coins of the instance: the value at a message coin's name, and at
an entry of a row's tail, is what c holds at that slot and coordinate (coinAt). -/
def readC (c : Cs (dueR P ride)) : (sender P ride).Coins :=
  (fun n => coinAt P ride c n.1 (seatC P ride n),
    fun ρ q => coinAt P ride c ρ.1 (seatT P ρ q.val))

/-- The honest sender's data as data of the instance: the entries of the sender's own rows rowsR at
the data and at coins that are all 0. -/
def dataOf (data : Nat → Nat → Nat → Option (GF ⊕ GE)) : RowN P → ℕ → GF :=
  entry P (rowsR P ride data ⟨fun _ => 0, fun _ => 0⟩)

/-- The seed (a point and a factor) of answer number i of an oracle message: entry i of seedsAt P
ds, or the default seed if the list is shorter. -/
def seedAt (ds : List Fmt.Drawn) (i : ℕ) : List E × E := (seedsAt P ds).getD i default

/-- The instance's weights: the coefficient of entry j of the row ρ in the answer a. At a row of the
answer's own oracle message it is the answer's coordinate a.2.2 of this product: the inverse of the
seed's factor, times K1's weight at the entry (K1.Msg.weight, Johnson/Desc/K1/Law/Law.lean), times
the power of θ of the row's coordinate. At a row of another oracle message it is 0. -/
def wOf (ds : List Fmt.Drawn) (a : AnsN P) (ρ : RowN P) (j : ℕ) : GF :=
  if ρ.1 = a.1 then
    match ρ.2 with
    | .inl (r, t) =>
      crd a.2.2 ((readE (seedAt P ds a.2.1.val).2)⁻¹ *
        ((K1.Msg.of P.codes (shapeAt P a.1)).weight (readL (seedAt P ds a.2.1.val).1)
          (readE (seedAt P ds a.2.1.val).2) a.2.1.val .main
          (r.val + j * 2 ^ K1.clog (shapeAt P a.1).mainRows) * readE (thetaE t.val)))
    | .inr (r, t) =>
      crd a.2.2 ((readE (seedAt P ds a.2.1.val).2)⁻¹ *
        ((K1.Msg.of P.codes (shapeAt P a.1)).weight (readL (seedAt P ds a.2.1.val).1)
          (readE (seedAt P ds a.2.1.val).2) a.2.1.val .mask
          (r.val + j * 2 ^ K1.clog (shapeAt P a.1).maskRows) * readE (thetaE t.val)))
  else 0

/-- The number of the tree that holds oracle message k, if there is one. -/
def treeOf (k : ℕ) : Option ℕ := ((Own.treesMade P.codes P.sent).getD {}).tree[k]?

/-- The queried positions as the model's list of queries (row, point): for each row whose oracle
message is in a tree, every position queried of that tree, as the position's evaluation point in the
row's code (ptF). A row whose oracle message is in no tree adds nothing to the list. -/
def asksOf (asks : List (List (List Nat))) : List (RowN P × GF) :=
  (Finset.univ : Finset (RowN P)).toList.flatMap fun ρ =>
    match treeOf P ρ.1 with
    | some τ => (asked asks τ).map fun p => (ρ, ptF (codeAt P ρ).a p)
    | none => []

/-- A premise on ride alone: for each table that is sent along, the entries Ride.lay are additive in
the table's coins, at the table's 2 ^ h rows. It holds for every ride: ridesAdd
(Johnson/SendSim/At/RideLay.lean). -/
def RidesAdd : Prop :=
  ∀ k R, ride k = some R → ∀ (c c' : ℕ → GE) (r j : ℕ), r < 2 ^ R.h →
    R.lay (c + c') r j = R.lay c r j + R.lay c' r j

/-- A premise on ride alone: for each table that is sent along, coins that are all 0 give entries
Ride.lay that are 0, at the table's 2 ^ h rows. It holds for every ride: ridesZero
(Johnson/SendSim/At/RideLay.lean). -/
def RidesZero : Prop :=
  ∀ k R, ride k = some R → ∀ r j : ℕ, r < 2 ^ R.h → R.lay 0 r j = 0

/-- If the job fits its place (sendFits) and RidesAdd holds, the instance's lay is additive.
Statement only; proved as additiveOf in Johnson/SendSim/At/Additive.lean. -/
def Spec.additiveOf : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride), sendFits P ride = true → RidesAdd ride →
    (sender P ride).Additive

open Classical in
/-- If the job fits its place (sendFits) and the queried positions are within the bound budAt, the
list asksOf P asks is within the model's bound Sender.Within. Statement only; proved as withinOf in
Johnson/SendSim/At/Within.lean. -/
def Spec.withinOf : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride) (asks : List (List (List Nat))),
    sendFits P ride = true → budAt P asks → (sender P ride).Within (asksOf P asks)

/-- If the job fits its place (sendFits), RidesZero holds, the challenge consists of exactly the
seeds (seedsFit) and no seed's factor is 0, then Sender.Mends holds at the weights wOf P ds: for any
values of the answers there is a family of message coins, at which lay is additive, that contributes
them. Statement only; proved as mendsOf in Johnson/SendSim/At/MendsOf.lean. -/
def Spec.mendsOf : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride) (ds : List Fmt.Drawn),
    sendFits P ride = true → RidesZero ride → seedsFit P ds = true →
    (∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) → (sender P ride).Mends (wOf P ds)

/-- Under the premises of Spec.mendsOf, each answer of the instance has a coin of its own, in the
sense of Sender.Pads (Johnson/SendSim/Pads.lean). Statement only; proved as padsOf in
Johnson/SendSim/At/PadsOf.lean. -/
def Spec.padsOf : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride) (ds : List Fmt.Drawn),
    sendFits P ride = true → RidesZero ride → seedsFit P ds = true →
    (∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) → Nonempty ((sender P ride).Pads (wOf P ds))

/-- If the job fits its place (sendFits), readC is surjective: every value of the instance's coins
is readC of some value of the sender's coins. Statement only; proved as readOnto in
Johnson/SendSim/At/Onto.lean. -/
def Spec.readOnto : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride), sendFits P ride = true →
    Function.Surjective (readC P ride)

/-- If the job fits its place (sendFits), the image under readC of the uniform distribution on the
sender's coins is the uniform distribution on the instance's coins. Statement only; proved as
readUnif in Johnson/SendSim/At/ReadUnif.lean. -/
def Spec.readUnif : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride), sendFits P ride = true →
    (unif (Cs (dueR P ride))).map (readC P ride) = unif (sender P ride).Coins

/-- Under the premises of Spec.mendsOf there is one function back, the same for all data and coins,
such that what the sender discloses in its two rounds (shownR) is back applied to what the instance
discloses at dataOf data and readC c. Statement only; proved as shownTie in
Johnson/SendSim/At/Shown.lean. -/
def Spec.shownTie : Prop :=
  ∀ (P : K1.Par) (first : Nat) (ride : Nat → Option Ride) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))), sendFits P ride = true → RidesZero ride →
    seedsFit P ds = true → (∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) →
    ∃ back : List GF × (AnsN P → GF) → List Shown,
      ∀ (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c : Cs (dueR P ride)),
        shownR P first ride data ds asks c =
          back ((sender P ride).shown (wOf P ds) (asksOf P asks) (dataOf P ride data)
            (readC P ride c))

end OnBytes.SendSim.At
