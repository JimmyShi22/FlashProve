-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookHeldHash.lean: three theorems: parts of an honest prover, as three files of the frame's
folder define them, state exactly the coins that the key file's book of coins has for them. Each
part is `Stated` (E2E/KeyBookLends.lean) in `keyBook K` (E2E/KeyBook.lean) at its address. The parts
are those for the batching of the rows on the table, which is the kind K13, "the members' batching"
(`k13Row`, Johnson/Desc/ProofFile/Honest/K13/Part.lean); for the four sub-protocols of the kind K14
in the shared chain that have a round (`proverSidesOfSharedRounds`, Johnson/Desc/ProofFile/Honest/K14/Parts.lean); and
for the shared chain's two sendings (`proverSidesOfSharedSendings`, Johnson/Desc/ProofFile/Honest/K14/Sendings.lean).
That every part of a list is `Stated` is a hypothesis of `lendRow_ok` (E2E/KeyBookLends.lean) and of
`key_lends` (E2E/KeyBookLendsNamed.lean), which conclude that the frame's `lendRow` returns coins
for the list. The book and the parts are written separately: none of the three files is among the
direct or indirect imports of E2E/KeyBook.lean, and E2E/KeyBook.lean is not among theirs; the limits
say what the two sides share. The first two theorems are general in the book's counts and in the two
lookups' faces; the third is at the library's sizes of the full size only.

Terms. The frame (Johnson/Desc/ProofFile/Honest/Frame.lean) has the types in which an honest prover
is written. A part (`Part`) is the prover's moves for some consecutive rounds of one sub-protocol.
It states three things on coins (random field elements): `takes`, the count of its own coins;
`spends` and `carries`, the names and counts of the ranges of other parts' coins that it is given. A
count (`Due`) is a number of coins in each of the two fields. A place (`Place`,
Johnson/Desc/Block.lean) is a sub-protocol's label: chain, link, piece, kind. An address (`Addr`) is
a place and the number of a part there. A `Placed` is a place with the list of the prover's parts
for the sub-protocol there. A book (`ProverCoinCounts`) is a public table: for each of the three chains, rows of
an address and its count; and entries. An entry (`Ahead`) is a named range of the coins of one part,
its owner (`owner`), that one other part, its spender (`spender`), is given too; `once` marks it as
spent (true) or as carried (false). `Stated B rows a p` says: `p.takes` is the count of the first
row at the address a in the table rows, or 0 if there is none; `p.spends` is the list of the names
and counts of the entries of B that have the spender a and are marked as spent, in the book's order;
`p.carries` is the same for those marked as carried. K (`KeyPub`, E2E/KeyBook.lean) is the public
data from which the key file's book is computed. A face (`K3.Face`,
Johnson/Desc/First/Look/K3LookupGeneral.lean) holds a lookup's public numbers. A sending is a sub-protocol
of two rounds in which the prover sends oracle messages and then their out-of-domain answers; in K,
a `Sending` is the list of such messages' counts of coins.

  `k13_stated`: under hf, hc, hp and hk: part number i of `K13.k13Row weights pile p`, a list of two
    parts, is `Stated` in `keyBook K` at the first chain's rows and at the address `⟨battPlace, i⟩`.
    Part 0, one round in which nothing is sent, takes, spends and carries nothing, and the book has
    nothing for it. Part 1, a masked sumcheck, takes and carries nothing and spends one range of
    `1 + 2 * K.kCol` coins of the extension field, under the name of the book's one entry for it.
    General in K, in p (`K13.Where`, Johnson/Desc/K13/Kind.lean), in weights and in pile
  `k14_stated`: under hf and hs: every part of every element h of `K14.proverSidesOfSharedRounds P weights` is `Stated`
    in `keyBook K` at the shared chain's rows and at the address of `h.place` and the part's number.
    There are four elements, of one part each. The parts at "LIN point", "LOC" and "LIN zeta" take,
    spend and carry nothing. The part at "SPLIT" takes and carries nothing and spends one coin of
    the extension field, under the name of the book's one entry for it. General in K, in P
    (`K14.Data`) and in weights
  `k14_sends_stated`: under hK, hc and hS: the same for the two elements of
    `K14.proverSidesOfSharedSendings A weights rand`, "send o_u" and "send o_omega", of one part each. The part takes
    the count of the book's row at its address (`K.sFolded.due`, `K.sOmega.due`) and spends and
    carries nothing
  `full_sends`: at `fullPub` (E2E/KeyBookAtWritten.lean) the two sendings' parts at `sendFull` take
    `K.sFolded.due` and `K.sOmega.due`. The counts on the two sides are defined separately and are
    compared by an evaluation in Lean's kernel (`decide +kernel`). `atFull f` (same file) is false
    where `fullPub` returns nothing, so the theorem also says that `fullPub` returns a value
  `full_sends_no`: a negative test, by the same kind of evaluation: the part of "send o_u" does not
    take the count `K.sOmega.due`. By `full_sends` it is not false merely because `fullPub` returns
    nothing
  `takes_same`: at every A (`K14.SendPub`) whose codes and shape are those of `keyFull`, the two
    sendings' parts take the same counts as at `sendFull`
  `sendFull`: a definition: a `K14.SendPub` with the setting, the codes and the shape of `keyFull`
  `run_k13`: `ownRun (K13.k13Shape k) = 1 + 2 * k`: the count that part 1 of the batching states for
    its range, as a formula in the number k of variables
  `others_batt`, `others_split`: among the book's entries that are not the lookups' (`K.others`,
    E2E/KeyBookPasses.lean) exactly one has the spender `⟨battPlace, 1⟩`, and exactly one the
    spender `⟨splitPlace, 0⟩`; each is written out

By what. For a part that states nothing: `stated_nothing` (E2E/KeyBookLendsNamed.lean). For the two
parts that spend: `mine_off_looks` (same file: at two faces and at an address a at neither lookup's
place, the book's entries with the spender a are those of `K.others` with the spender a), then
`others_batt` or `others_split`, which hold by unfolding. The batching's count is rewritten by
`run_k13`, which calls `ownSlots_eq` (E2E/KeyBookFace.lean). `k14_sends_stated` takes the two faces
from `full_two` and the two counts from `full_sends`, both through `of_atFull`
(E2E/KeyBookPassesNamed.lean), and calls `takes_same`, `mine_off_looks` and `others_none`
(E2E/KeyBookLendsNamed.lean: no entry of `K.others` has a spender outside the list of their
spenders, which does not depend on K). That the parts' places are the book's (`battPlace`,
`pointPlace`, `locPlace`, `zetaPlace`, `splitPlace`, `foldedPlace`, `omegaPlace`:
E2E/KeyPlaces.lean) holds by unfolding, at the batching after rewriting by hc and hp. Definitions:
`hasFor` (E2E/KeyBookLends.lean); `spend`, `tableAt` (E2E/KeyBook.lean); `KeyPub.top`
(E2E/KeyBookPasses.lean); `keyFull` (Johnson/Goal/PlanValues/KeySizedReturns.lean); `ownRun`,
`sumPart` (Johnson/Desc/ProofFile/Honest/Sum.lean); `runName`, `indexMaskRun`, `splitMaskRun`
(Johnson/Desc/ProofFile/Honest/ForKinds.lean).

Hypotheses. hf (`k13_stated`, `k14_stated`): `K.faces = [f₀, f₁]`: K has exactly two lookups, at any
faces. hc and hp (`k13_stated`): `p.chain = 1` and `p.piece = 13`: the place of the batching's parts
(`K13.k13Place p`) is `battPlace`. hk: `p.lin.kCol = K.kCol`: the parts' shape and K have the same
number of variables of the matrix's columns. hs: `P.S.sharedSplitNeeded = true`: the shape splits,
so that "SPLIT" has a round. hK: `fullPub = some K`: K is the value at the library's sizes of the
full size (`keyFull`). hc and hS (`k14_sends_stated`, `takes_same`): the codes and the shape of A
are those of `keyFull`; the other fields of A are free.

Limits.
- `Stated` compares names, counts and order only. Which coin of a range a part uses for which value
  is not compared here.
- The two sides share the frame's types and the functions for names. On both sides a name is built
  by `runName` from `indexMaskRun` or `splitMaskRun`: what is compared in a name is the owner's
  word, the spender's address and the use. The counts are separate definitions. The book has
  `1 + 2 * K.kCol`, 1, and the sendings' counts by the rows' codes (`msgCoins`, E2E/KeyBook.lean);
  the parts have `ownRun` of the call's shape, 1, and `takesOf`
  (Johnson/Desc/ProofFile/Honest/K14/Sendings.lean).
- `k14_sends_stated` is at the full size only: the counts are compared by an evaluation at one
  value, `fullPub`, not by a proof that is general in the sizes.
- Two lookups only (hf). Where the shape does not split, `K14.proverSidesOfSharedRounds` has three elements: nothing is
  stated there.
- That a prover of the key file has these parts, at parameters that meet the hypotheses, is not
  shown here: it has to be shown where such a prover is assembled. No other file under E2E/ calls
  the three theorems.
- Coins only. That a list of parts has as many rounds as its sub-protocol and is cut as the book
  says are other tests of the frame's (`chainSteps`): see the limits of E2E/KeyBookLends.lean. The
  limits of E2E/KeyBook.lean on the book's counts apply.
- The parts' names, counts and places are those of the three files named at the top: K13/Part.lean
  and K14/Sendings.lean are imported here, K14/Parts.lean through the latter. The three rest on
  Frame.lean, Side.lean, Sum.lean and ForKinds.lean of the same folder. If a name, a count or a
  place changes in these files and not in the book, or in the book and not in these files, a proof
  of this file fails: a step by unfolding, or the evaluation `full_sends`.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookLendsNamed
import Johnson.Desc.ProofFile.Honest.K13.Part
import Johnson.Desc.ProofFile.Honest.K14.Sendings

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyBook
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K3 (Face)
open VerifiableInference.Desc.Part
open ProofFile.Honest
open Lk6.AtPlan (keyFull)

/-! ## 1 The batching of the rows on the table -/

theorem run_k13 (k : Nat) : ownRun (K13.k13Shape k) = 1 + 2 * k := by
  show 0 + MaskedSum.ownSlots (List.replicate k (MaskedSum.Var.plain 3)) = _
  rw [ownSlots_eq, List.map_replicate, List.sum_replicate]
  show 0 + (1 + k * 2) = _
  omega

theorem others_batt (K : KeyPub) : K.others.filter (fun e => e.spender == ⟨battPlace, 1⟩) =
    [spend indexMaskRun "sum" ⟨idxPlace, 0⟩ K.top.2 (1 + 2 * K.kCol) ⟨battPlace, 1⟩] := rfl

theorem others_split (K : KeyPub) : K.others.filter (fun e => e.spender == ⟨splitPlace, 0⟩) =
    [spend splitMaskRun "split" ⟨omegaPlace, 0⟩ (tableAt K.sOmega 1) 1 ⟨splitPlace, 0⟩] := rfl

section K13
variable {W₀ Rc Xi Tr X : Type}

/-- **Both parts for the batching state exactly what the book has for them.** Part 0 states nothing;
part 1 spends one range of `1 + 2 * K.kCol` coins of the extension field. -/
theorem k13_stated {K : KeyPub} {f₀ f₁ : Face} (hf : K.faces = [f₀, f₁])
    (p : VerifiableInference.Desc.K13.Where) (hc : p.chain = 1) (hp : p.piece = 13)
    (hk : p.lin.kCol = K.kCol) (weights : W₀ → Weights) (pile : K13.PileOf Xi) :
    ∀ i q, (K13.k13Row (Rc := Rc) (Tr := Tr) (X := X) weights pile p)[i]? = some q →
      Stated (keyBook K) (keyBook K).first ⟨battPlace, i⟩ q := by
  intro i q hq
  match i, hq with
  | 0, hq =>
    obtain rfl := Option.some.inj hq
    exact stated_nothing hf _ _ _ (by decide) (by decide) rfl (by decide) rfl
  | 1, hq =>
    obtain rfl := Option.some.inj hq
    unfold Stated hasFor
    rw [mine_off_looks hf _ (by decide) (by decide), others_batt]
    have hpl : K13.k13Place p = battPlace := by
      unfold K13.k13Place battPlace
      rw [hc, hp]
    show ((⟨0, 0⟩ : Due), [(runName indexMaskRun ⟨K13.k13Place p, 1⟩ "sum",
      (⟨0, ownRun (K13.k13Shape p.lin.kCol)⟩ : Due))], ([] : List (String × Due))) = _
    rw [hpl, run_k13, hk]
    rfl
  | i + 2, hq => cases hq

end K13

/-! ## 2 The shared chain's four sub-protocols of the kind K14 that have a round -/

section K14
variable {W₀ Rc Ky X : Type}

/-- **The parts for the four sub-protocols state exactly what the book has for them.** hs: the shape
splits. Three parts state nothing; the part at "SPLIT" spends one coin of the extension field. -/
theorem k14_stated {K : KeyPub} {f₀ f₁ : Face} (hf : K.faces = [f₀, f₁]) (P : K14.Data)
    (hs : P.S.sharedSplitNeeded = true) (weights : W₀ → Weights) :
    ∀ h ∈ K14.proverSidesOfSharedRounds (Rc := Rc) (Ky := Ky) (X := X) P weights, ∀ i q, h.parts[i]? = some q →
      Stated (keyBook K) (keyBook K).shared ⟨h.place, i⟩ q := by
  intro h hh i q hq
  unfold K14.proverSidesOfSharedRounds at hh
  simp only [hs, if_true, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
    or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl
  · match i, hq with
    | 0, hq =>
      obtain rfl := Option.some.inj hq
      exact stated_nothing hf _ ⟨pointPlace, 0⟩ _ (by decide) (by decide) rfl (by decide) rfl
    | i + 1, hq => cases hq
  · match i, hq with
    | 0, hq =>
      obtain rfl := Option.some.inj hq
      exact stated_nothing hf _ ⟨locPlace, 0⟩ _ (by decide) (by decide) rfl (by decide) rfl
    | i + 1, hq => cases hq
  · match i, hq with
    | 0, hq =>
      obtain rfl := Option.some.inj hq
      exact stated_nothing hf _ ⟨zetaPlace, 0⟩ _ (by decide) (by decide) rfl (by decide) rfl
    | i + 1, hq => cases hq
  · match i, hq with
    | 0, hq =>
      obtain rfl := Option.some.inj hq
      show Stated (keyBook K) (keyBook K).shared ⟨splitPlace, 0⟩ _
      unfold Stated hasFor
      rw [mine_off_looks hf ⟨splitPlace, 0⟩ (by decide) (by decide), others_split]
      rfl
    | i + 1, hq => cases hq

/-! ## 3 The shared chain's two sendings -/

/-- Public parameters of the two sendings with the setting, the codes and the shape of `keyFull`. By
`takes_same` the two counts are the same at every value of the other fields. -/
def sendFull : K14.SendPub :=
  ⟨⟨keyFull.set, .once, keyFull.codes, keyFull.once.shape, 0, []⟩, 0⟩

theorem full_sends : atFull (fun K =>
    (K14.sendingPart (K14.jobU sendFull)).takes == K.sFolded.due &&
      (K14.sendingPart (K14.jobOmega sendFull)).takes == K.sOmega.due) = true := by decide +kernel

/-- A negative test: the part of "send o_u" does not take the count of the book's row for the
sending of Omega. -/
theorem full_sends_no : atFull (fun K =>
    (K14.sendingPart (K14.jobU sendFull)).takes == K.sOmega.due) = false := by decide +kernel

theorem takes_same (A : K14.SendPub) (hc : A.P.codes = keyFull.codes)
    (hS : A.P.S = keyFull.once.shape) :
    (K14.sendingPart (K14.jobU A)).takes = (K14.sendingPart (K14.jobU sendFull)).takes ∧
      (K14.sendingPart (K14.jobOmega A)).takes =
        (K14.sendingPart (K14.jobOmega sendFull)).takes := by
  obtain ⟨⟨set, scope, codes, S, item, bp⟩, at_⟩ := A
  simp only at hc hS
  subst hc hS
  exact ⟨rfl, rfl⟩

/-- **The parts for the shared chain's two sendings state exactly what the book has for them**, at
the library's sizes of the full size. -/
theorem k14_sends_stated (K : KeyPub) (hK : fullPub = some K) (A : K14.SendPub)
    (hc : A.P.codes = keyFull.codes) (hS : A.P.S = keyFull.once.shape) (weights : W₀ → Weights)
    (rand : Rc → TableRand) :
    ∀ h ∈ K14.proverSidesOfSharedSendings (Ky := Ky) (X := X) A weights rand, ∀ i q, h.parts[i]? = some q →
      Stated (keyBook K) (keyBook K).shared ⟨h.place, i⟩ q := by
  have h2 := of_atFull full_two hK
  obtain ⟨f₀, f₁, hf⟩ := List.length_eq_two.1 (by simpa using h2)
  have ht := of_atFull full_sends hK
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at ht
  obtain ⟨t1, t2⟩ := takes_same A hc hS
  intro h hh i q hq
  unfold K14.proverSidesOfSharedSendings at hh
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hh
  rcases hh with rfl | rfl
  · match i, hq with
    | 0, hq =>
      obtain rfl := Option.some.inj hq
      show Stated (keyBook K) (keyBook K).shared ⟨foldedPlace, 0⟩ _
      unfold Stated hasFor
      rw [mine_off_looks hf ⟨foldedPlace, 0⟩ (by decide) (by decide),
        others_none K ⟨foldedPlace, 0⟩ (by decide)]
      show ((K14.sendingPart (K14.jobU A)).takes, ([] : List (String × Due)),
        ([] : List (String × Due))) = (K.sFolded.due, [], [])
      rw [t1, ht.1]
    | i + 1, hq => cases hq
  · match i, hq with
    | 0, hq =>
      obtain rfl := Option.some.inj hq
      show Stated (keyBook K) (keyBook K).shared ⟨omegaPlace, 0⟩ _
      unfold Stated hasFor
      rw [mine_off_looks hf ⟨omegaPlace, 0⟩ (by decide) (by decide),
        others_none K ⟨omegaPlace, 0⟩ (by decide)]
      show ((K14.sendingPart (K14.jobOmega A)).takes, ([] : List (String × Due)),
        ([] : List (String × Due))) = (K.sOmega.due, [], [])
      rw [t2, ht.2]
    | i + 1, hq => cases hq

end K14

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.k13_stated
#print axioms AtPublicFiles.KeyBook.k14_stated
#print axioms AtPublicFiles.KeyBook.full_sends
#print axioms AtPublicFiles.KeyBook.full_sends_no
#print axioms AtPublicFiles.KeyBook.k14_sends_stated
#print axioms AtPublicFiles.KeyBook.run_k13
#print axioms AtPublicFiles.KeyBook.others_batt
#print axioms AtPublicFiles.KeyBook.others_split
#print axioms AtPublicFiles.KeyBook.sendFull
#print axioms AtPublicFiles.KeyBook.takes_same
