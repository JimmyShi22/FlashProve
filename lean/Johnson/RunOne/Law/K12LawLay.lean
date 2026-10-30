-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12LawLay.lean: The key file's
tables: the rows that a proximity test closes (1.15 · 2.9 · 2.10 · 3.2): THE ENGINE OF THEIR «law»
(the premise of that name of `relAt_back_to`, KeyQuietSub.lean): general in the chain and the row,
at the tables' bare letters (F · G · at_ · K · R · ρ). It names no term of the proximity test.
Statements; each proof is a few calls.
  `pin_laid`: a table that is a member of its committed word's list and meets the out-of-domain
  (OOD)
    sample is PINned at the witness in which it is laid.
  `ride_is`: at a member of the test's group that the row does NOT lay (it rides, under the row's
    ctx): the witness's own message at that seat IS the tuple's table there: two members that meet
    one sample are one, by the promise's NoColl.
  `reads_all`: so the laid witness reads, at every member of the group, the tuple's table.
  `rows_of_tuple`: the rows that hold of a tuple's words at one statement hold at the laid witness
  at
    another statement with tables of the same sizes, where the words are the laid witness's at the
    messages that the rows name.
Called: `msgOf_layAt` | `reads_layAt` | `reads_layAt_off` (Johnson/Desc/Key/KeyLay.lean) ·
`rowsHold_iff_allSay` (KeyNums.lean) · `says_reads` (KeyRideTools.lean):
the tables' files'. KIN, NAMED: of `ride_is`: `pin_one`
(Johnson/Desc/Msg.lean: two PINs under NoColl are one message) · of `pin_laid`:
`cand_gives_pin` (KeyCandTie.lean) and `pin_laid` at one number (K12Law15.lean: this one's case
l := [k]) · of `rows_of_tuple`: `run_holds` | `holds_of_allSay` (GrowsOfAllSay.lean), which pay its
hoff · hsz · hW from «the statement is in order»: AT THE ROWS 2.9 | 2.10 THAT FILE's ARE CALLED.
What it is not. Where the tables come from (the test's law), that they are members, NoColl, the
letters' ties (ArrOk · LayIdem · ReadsPinned · SeatsApart) and OffTables are premises. It pays no
field of the tables. No soundness is claimed. Nothing on hiding.

-/
import Johnson.RunOne.Law.KeyRideTools
import Johnson.Desc.Key.KeyNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12LawLay
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Key

section
variable {XI A Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading A Cells M Smp Rec)
  (at_ : Where)

/-- **A member that is laid is PINned at the laid witness.** -/
theorem pin_laid (l : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M) (ha : ArrOk G at_ l)
    (hi : LayIdem G) (hs : SeatsApart at_ l l) (a : A) (y : Strs) (k : Nat) (hk : k ∈ l)
    (hm : ∃ o z, F.oracleAt (at_ k).1 = some o ∧ G.smp a (at_ k).1 (at_ k).2 = some z ∧
      Member F G o (at_ k).1 (at_ k).2 y z (tbl k)) :
    PIN F G (at_ k).1 (at_ k).2 a y (layAt at_ l tbl w) := by
  obtain ⟨o, z, ho, hz, hmem⟩ := hm
  exact ⟨o, z, ho, hz, by rw [msgOf_layAt G at_ l tbl w ha hi hs k hk]; exact hmem⟩

/-- **The riding member**: the witness's own message at its seat is the tuple's table there. -/
theorem ride_is (tbl : Nat → M) (w : Wit Cells Unit M) (a : A) (y : Strs) (k : Nat)
    (hn : NoColl F G (at_ k).1 (at_ k).2 a y) (hp : PIN F G (at_ k).1 (at_ k).2 a y w)
    (hm : ∃ o z, F.oracleAt (at_ k).1 = some o ∧ G.smp a (at_ k).1 (at_ k).2 = some z ∧
      Member F G o (at_ k).1 (at_ k).2 y z (tbl k)) :
    msgOf G w (at_ k).1 (at_ k).2 = tbl k := by
  obtain ⟨o, z, ho, hz, h1⟩ := hp
  obtain ⟨o', z', ho', hz', h2⟩ := hm
  obtain rfl := Option.some.inj (ho.symm.trans ho')
  obtain rfl := Option.some.inj (hz.symm.trans hz')
  exact hn o z ho hz _ _ h1 h2

/-- **At every member of the group, laid or riding, the laid witness reads the tuple's table.** -/
theorem reads_all (R : KRead Cells M) (l l' : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M)
    (ha : ArrOk G at_ l) (ha' : ArrOk G at_ l') (hr : ReadsPinned G at_ R l)
    (hr' : ReadsPinned G at_ R l') (hi : LayIdem G) (hs : SeatsApart at_ l l)
    (hd : ∀ k' ∈ l', k' ∉ l) (hs' : SeatsApart at_ l l') (a : A) (y : Strs)
    (hn : ∀ k ∈ l', NoColl F G (at_ k).1 (at_ k).2 a y)
    (hp : ∀ k ∈ l', PIN F G (at_ k).1 (at_ k).2 a y w)
    (hm : ∀ k ∈ l', ∃ o z, F.oracleAt (at_ k).1 = some o ∧
      G.smp a (at_ k).1 (at_ k).2 = some z ∧ Member F G o (at_ k).1 (at_ k).2 y z (tbl k)) :
    ∀ k, k ∈ l ∨ k ∈ l' → R.of (layAt at_ l tbl w) k = tbl k := by
  rintro k (hk | hk)
  · exact reads_layAt G at_ R l tbl w ha hr hi hs k hk
  · rw [reads_layAt_off G at_ R l l' tbl w ha' hr' hd hs' k hk, hr' w k hk]
    exact ride_is F G at_ tbl w a y k (hn k hk) (hp k hk) (hm k hk)

end

section
variable {GE : Type} [CommRing GE] (ρ : Model.Reading GE) {Cells M : Type} (K : KPlan)
  (R : KRead Cells M)

/-- **The rows that hold of the tuple's words hold at the laid witness.** -/
theorem rows_of_tuple (hs : R.same = fun a b => ρ.val a = ρ.val b) (St' St : Statement)
    (w' : Wit Cells Unit M) (rs : List OnBytes.Row) (W : Means.Words GE)
    (hall : Means.AllSay ρ St' rs W) (hoff : ∀ r ∈ rs, OffTables ρ St r)
    (hsz : ∀ r ∈ rs, ∀ o ∈ r.oracles, ∀ pt, Means.tableSize St' o pt = Means.tableSize St o pt)
    (hW : ∀ r ∈ rs, ∀ o ∈ r.oracles, W o = wordsOf ρ K R w' o) :
    ∀ r ∈ rs, RowHolds R.same St (valOf K R w') r :=
  (rowsHold_iff_allSay ρ K R hs St w' rs hoff).2 fun r hr =>
    (KeyRideTools.says_reads ρ St' St r W _ (hsz r hr) (hW r hr)).1 (hall r hr)

end

end Johnson.RunOne.Law.K12LawLay

#print axioms Johnson.RunOne.Law.K12LawLay.pin_laid
#print axioms Johnson.RunOne.Law.K12LawLay.ride_is
#print axioms Johnson.RunOne.Law.K12LawLay.reads_all
#print axioms Johnson.RunOne.Law.K12LawLay.rows_of_tuple
