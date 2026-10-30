-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/BatMeans.lean: what the claim at which the law of the proximity test starts is
worth to whoever hands the test its rows: the batching. Statements and proofs.

It joins two things: the law of the batching in Johnson/Desc/Means/Combine.lean (`combine_means`,
`combine_all`, over Johnson/Desc/Means/Says.lean, with its test as a Bool in
Johnson/Desc/Means/TestsB.lean and `combineAt_gives` in Johnson/Desc/Means/TestsLaw.lean) and the
bridge of Johnson/Desc/K12/Law/ClaimSays.lean (`short_eq`, `groupSays_iff`).
Main names:
  `combine_claim`: at one statement S, from `combineAt S g input = true`, `Bat.combine S g input x =
    some row`, the layout's four numbers being the stage's, and `row.kept = #[]`: for all words m,
    (∑ j, (stmG s row).2 j * msgOf s (tablesOf S input.layout m) j) − (stmG s row).1 = hornerSum
    (readE x) (what the rows are short of their targets on m).
  `combine_holds`: if all rows hold of the words, the claim holds of the message that the words
    make: `(Slf.idf).Holds (stmG s row) (msgOf …)`.
  `bat_ok` (Johnson/Desc/K12/Law/BatOk.lean; spent here): what a yes of the batching's plain text
    (`bat`, Johnson/Desc/First/Close/Closing.lean) holds: the group G in front; the layout in front;
    the statement behind is `begun S g G`; "BAT" draws just one element x; `Bat.combine` at the
    statement behind, at the layout in front and `runRows S G`, gives the row.
  `bat_means`: the two joined, of that `bat`.
Limits:
(1) The converse (if the claim holds then all rows hold, but for few x) is a fact on polynomials in
x and on when x is drawn. It is not here: this file has the honest direction and the equation. The
step that soundness spends is owed. It is to be carried, not proved anew: the library has the
batching as a block that is taken off: `BatSem` (OnBytes/Slice/ChainSem.lean), spent by
`closes_many` (OnBytes/Slice/ManyCloses.lean). What its caller wants: a link's sizes S : Sz with the
first stage S.sg t₀; `WordTie S t₀ d2 o f` (the word f is the reading of the written tree of the
round d2); a claim x of the link without a witness (¬ S.lk.j4.cf.relR …); `IsRows S t₀ x tg vs` (the
rows' targets and vectors in the field are the link's); and it hands on `sumStm S t₀ tg vs θ` at the
drawn θ. It is typed for the link's group (one written tree); three of the four proximity tests of a
proof batch a group of several members from several trees. A form of `BatSem` over a group's tables
(with `combine_claim` as the equation between the like of `sumStm` and `stmG s row`) is stated in
Johnson/Desc/K12/Law/BatJoint.lean (`BatCatchesAt`), proved in
Johnson/Desc/Means/BatCatchesProof.lean (`batCatchesAt`, `batCatches_bare`) and spent in
Johnson/Desc/K12/Law/NoneNearCand.lean: as a count of the drawn element's values; the game's form is
owed.
(2) `combineAt` is asked at the statement behind (the ledgers closed, the group marked) with the
layout taken in front. That the two layouts are one is inside `combineAt` (its clause on the
layout): held by a run, not by a theorem here. It has been evaluated at that very term (at the
statement that `beginRunP` leaves and at the input that it returns, which by `beginRunP_ok` are
`begun S g G` and ⟨S.layout g, runRows S G⟩): true at the four proximity tests of each of the two
example proofs.
(3) That the words are the committed ones, and 0 where nobody sent anything (`Padded`,
Johnson/Desc/Means/Says.lean), is left to whoever uses this file.
(4) The six files under Johnson/Desc/Means that lie beneath compile beneath this file, and
Lean's print of axioms at `bat_means`
covers them.
No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `combine_means`, `combine_all`,
`combineAt_gives`; `short_eq`, `groupSays_iff`; `bat_ok`.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.ClaimSays
import Johnson.Desc.K12.Law.BatOk
import Johnson.Desc.K12.Law.SwUnfold
import Johnson.Desc.Means.Combine
import Johnson.Desc.Means.TestsLaw

set_option autoImplicit false
namespace H2K.ClaimSays
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc
open OnBytes.Means
open H2K.FoldLaw (bind_ok)

/-- What the batched row is worth, at one statement: the claim q := stmG s row is short, on the
group's tables as the words fill them (read as one message of the stage's tables), of the Horner sum
of what the rows are short of on the words. -/
theorem combine_claim (s : Sg) (S : Statement) (g : Nat) (input : RunInput) (x : E) (row : GroupRow)
    (ht : combineAt S g input = true) (h : Bat.combine S g input x = some row)
    (hk : input.layout.k = s.h + s.g) (hh : input.layout.h = s.h)
    (hl : 2 ^ input.layout.logEll = s.C.l) (hz : 2 ^ input.layout.logEllZk = s.Z.l)
    (h0 : row.kept = #[]) (m : Words GE) :
    (∑ j : s.cIn.J, (stmG s row).2 j * msgOf s (tablesOf S input.layout m) j) - (stmG s row).1 =
      hornerSum (readE x) (input.rows.toList.map fun r => short rdE S r m) := by
  obtain ⟨G, hG, hL, hOk, hr⟩ := combineAt_gives ht
  obtain ⟨out, h1, _, _, e⟩ := combine_means rdE S g G input.layout input.rows x hG hL hOk hr
  have h' : Bat.combine S g ⟨input.layout, input.rows⟩ x = some row := h
  rw [h'] at h1
  obtain rfl := Option.some.inj h1
  rw [← short_eq s S input.layout row _ hk hh hl hz h0]
  exact e m

/-- If all rows hold of the words, the claim holds of the message that the words make. -/
theorem combine_holds (s : Sg) (S : Statement) (g : Nat) (input : RunInput) (x : E) (row : GroupRow)
    (ht : combineAt S g input = true) (h : Bat.combine S g input x = some row)
    (hk : input.layout.k = s.h + s.g) (hh : input.layout.h = s.h)
    (hl : 2 ^ input.layout.logEll = s.C.l) (hz : 2 ^ input.layout.logEllZk = s.Z.l)
    (h0 : row.kept = #[]) (m : Words GE) (hs : AllSay rdE S input.rows.toList m) :
    (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmG s row) (msgOf s (tablesOf S input.layout m)) :=
        by
  obtain ⟨G, hG, hL, hOk, hr⟩ := combineAt_gives ht
  exact (groupSays_iff s S input.layout row _ hk hh hl hz h0).1
    (combine_all rdE S g G input.layout input.rows x row hG hL hOk hr h m hs)

/-- The batching in front: what a yes of the batching's text returns is worth this: with x the
one element that the round "BAT" draws and the rows that the test takes in (runRows, in their fixed
order): under the test combineAt at the statement behind, the layout's four numbers and
"no kept form": for all words m the claim q := stmG s row is short, on the message that the words
make, of the Horner sum at x of what the rows are short of. -/
theorem bat_means (s : Sg) (S S' : Statement) (g : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) (row :
           GroupRow)
    (L : GroupLayout) (h : First.Close.bat S g e r = .ok (row, L, S')) :
    ∃ (G : Group) (x : E), S.groups[g]? = some G ∧ S' = begun S g G ∧
      r.drawn.elems.map E.ofTriple = [x] ∧
      (combineAt S' g ⟨L, runRows S G⟩ = true → L.k = s.h + s.g → L.h = s.h → 2 ^ L.logEll = s.C.l →
        2 ^ L.logEllZk = s.Z.l → row.kept = #[] → ∀ m : Words GE,
        ((∑ j : s.cIn.J, (stmG s row).2 j * msgOf s (tablesOf S' L m) j) - (stmG s row).1 =
          hornerSum (readE x) ((runRows S G).toList.map fun r => short rdE S' r m)) ∧
        (AllSay rdE S' (runRows S G).toList m →
          (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmG s row) (msgOf s (tablesOf S' L m)))) := by
  obtain ⟨G, x, h1, _, h3, h4, h5⟩ := bat_ok S S' g e r row L h
  refine ⟨G, x, h1, h3, h4, fun ht hk hh hl hz h0 m => ⟨?_, fun hs => ?_⟩⟩
  · exact combine_claim s S' g ⟨L, runRows S G⟩ x row ht h5 hk hh hl hz h0 m
  · exact combine_holds s S' g ⟨L, runRows S G⟩ x row ht h5 hk hh hl hz h0 m hs

end H2K.ClaimSays

#print axioms H2K.ClaimSays.bat_means
#print axioms H2K.ClaimSays.combine_claim
