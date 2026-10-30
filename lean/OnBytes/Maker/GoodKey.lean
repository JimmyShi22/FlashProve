-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/GoodKey.lean: what a good reading of a key file (`KeyGood`, OnBytes/TieK/Good.lean)
gives for the typing of the whole file, at the reading's own values and at plain data that are made
once, from the public files.

A typing at one public input stands at one set of plain data. A good reading d has its own three
lists of rounds: the first two from dry runs of the program's blocks at the key of d's table, the
third under the roots that were read. This file shows that the data made of them, with the third
list at made-up names, are those made at any fixed key that fits: so one set of data serves all good
readings. Then it carries four laws of OnBytes/Maker/ to d's values.

  `readPlace_places`   the binding tree as read has 2 ^ logLeaves leaves
  `good_chains`        at a good reading: the flat record of the three chains (`ThreeChains`,
                       OnBytes/TieK/Chains.lean) at d's values, with the file, the place behind the
                       table and the description's equation
  `keyRefusal_of_chains`   the program's decision on the three chains as read is a yes
  `good_rounds`        the three lists made at a fixed key that fits are d's first two and a third
                       that has the stored tables, items and openings' shapes of d's third
  `GoodPays`, `good_pays`   at a good reading, from tests on the data: the data fit what was read;
                       the first chain has the data's number of roots and ends in a seal; the
                       decision is a yes; the key is the program's key of the table; the binding
                       tree's number of leaves
  `good_returns`       the typing returns at a good reading, from the tests and one hypothesis on
                       that reading (`SameTwice`)

To be minded. A good reading is the reading of ANY key file that the program accepts at these public
files, whoever wrote it. The reader ties two openings of one position by digests alone. So
`SameTwice` is a hypothesis on one reading; asked of all good readings it would be a statement on
the hash's collisions.

Not claimed. That the tests pass at any public files. `SameTwice` at any reading. Nothing on
soundness.


-/
import OnBytes.Maker.TypeFileOfRead
import OnBytes.Maker.OfThreeChains
import OnBytes.Maker.FilesFree
import OnBytes.TieK.CutsOfChains

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Proof OnBytes.TieK
open _root_.Run _root_.Run.PQ
open OnBytes.Params (Rounds)

/-- The binding tree as read has 2 ^ logLeaves leaves. -/
theorem readPlace_places {s : Params.LinBindingShape} {cfg closing b : ByteArray} {i : ℕ}
    {pl : Place} (h : readPlace s cfg closing b i = some pl) : pl.places = 2 ^ s.logLeaves := by
  obtain ⟨-, w, i1, salt, path, -, -, -, -, -, rfl⟩ := readPlace_open _ _ _ _ _ _ h
  rfl

/-- **At a good reading the flat record of the three chains holds at the reading's own values.**
file: a key file whose fixed reading is d; j: the place behind its table. -/
theorem good_chains (u : KeyPub) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned u.pol u.KL (some u.lay) = .ok p)
    (d : Params.TableName × ChainsData) (hg : KeyGood u d) :
    ∃ file j real real2, readKeyChains u.pol u.lay u.KL file = some d ∧
      Key.readTable p.chains.key.oneTime.lin.fold.index p.chains.key.oneTime.given.cfg file =
        .ok (d.1, j) ∧
      p.chains.key.oneTime.describe d.1 d.2.rounds1 = some d.2.S1 ∧
      ThreeChains (Key.tailPublic p.chains.key d.1) (Key.oneTime p.chains.key.oneTime)
        (Key.startOf p.chains.key.oneTime) file j d.2.rounds1 d.2.dry d.2.S1 d.2.r d.2.seal1
        d.2.seal2 d.2.rounds2 d.2.dry2 d.2.S2 d.2.rounds3 d.2.S3 real real2 := by
  obtain ⟨F, e1, e2, e3, ho, hd⟩ := hg
  obtain ⟨p', j, d', real, real2, hp', ht, hd', hS, T, -, -⟩ := readKeyChains_of F d.1 ho
  rw [e1, e2, e3] at hp' hd'
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  obtain rfl : d.2 = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  exact ⟨F.key, j, real, real2, hd, ht, hS, T⟩

/-- The program's decision on a key file's three chains as read is a yes, where the three runs end
well. -/
theorem keyRefusal_of_chains {k : Params.KeyChains} {table : Params.TableName} {file : ByteArray}
    {j : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead}
    {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds}
    {S₃ : Fmt.SpecX} {real : FirstEnd} {real2 : SharedEnd}
    (T : ThreeChains (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ real real2) :
    Key.keyRefusal k table r = none := by
  unfold Key.keyRefusal
  dsimp only
  rw [judge_of_yes "one-time-chain-" T.first_yes]
  exact tailRefusal_none T.shared_yes T.second_yes

section
variable (u : KeyPub) (p : Model.Verify.Planned)
  (hp : Model.Verify.planned u.pol u.KL (some u.lay) = .ok p) (key₀ : TableKey)
  (h0 : key₀.item = 0)
  (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
  (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R)
  (d : Params.TableName × ChainsData) (hg : KeyGood u d)
include hp h0 hf hR hg

/-- **The three lists made at a fixed key that fits are the reading's first two, and a third with
the stored tables, the items and the openings' shapes of the reading's third.** -/
theorem good_rounds :
    ∃ R₃, R = (d.2.rounds1, d.2.rounds2, R₃) ∧ StoredAlike d.2.rounds3 R₃ ∧
      d.2.rounds3.map (·.1.items) = R₃.map (·.1.items) ∧
      d.2.rounds3.map (fun x => x.1.opens.map (·.1)) = R₃.map (fun x => x.1.opens.map (·.1)) := by
  obtain ⟨file, j, real, real2, -, -, hS, T⟩ := good_chains u p hp d hg
  have hS' : Params.describeWith p.chains.key.oneTime.given Params.labelOneTime
      (Params.OneTime.statement d.1) .inFile d.2.rounds1 0 = some d.2.S1 := hS
  obtain ⟨R₃, h3, hA, hI, hSh⟩ := dry3_alike T.toRead hS'
  obtain ⟨seeds, -, hk, hfit⟩ := tableKey_open _ _ _ _ _ _ T.key_made
  have hi : d.2.r.key.item = 0 := by rw [hk]
  have ka : TwoLaws.KeyAlike key₀ d.2.r.key :=
    keyAlike_of_fits (Key.tailPublic p.chains.key noTable).lin.fold.index (h0.trans hi.symm) hf hfit
  have e : dryKey p.chains.key d.2.r.key = some (d.2.rounds1, d.2.rounds2, R₃) := by
    unfold dryKey
    rw [T.first_dry]
    exact h3
  rw [dryKey_keyAlike ka, e] at hR
  exact ⟨R₃, (Option.some.inj hR).symm, hA, hI, hSh⟩

/-- What a good reading pays, at the plain data made of R. -/
structure GoodPays (a : ℕ) : Prop where
  /-- the data fit what was read, the first chain has the data's number of roots and ends in a
  seal, the key and the three views pass the tests on the words: at the reading's own three
  descriptions -/
  gives : PortGives a R d.2.r d.2.S1 d.2.S2 d.2.S3
  /-- the program's decision on the three chains as read is a yes -/
  yes : Key.keyRefusal p.chains.key d.1 d.2.r = none
  /-- the key in the reading is the program's key of the reading's table -/
  key : tableKey p.chains.key.shared.given.plan.field p.chains.key.shared.given.cfg
    (Key.tailPublic p.chains.key noTable).lin.fold.index d.1 0 = some d.2.r.key
  /-- the binding tree as read has the parameters' number of leaves -/
  places : d.2.r.place.places = 2 ^ p.chains.key.oneTime.binding.logLeaves

/-- **A good reading pays**, from tests on the data. -/
theorem good_pays (a : ℕ) (hok : okAt a (some R) = true)
    (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hb : sealBare (Three.Whole.of R.1 R.2.1 R.2.2) = true) : GoodPays p R d a := by
  obtain ⟨R₃, rfl, hA, hI, hSh⟩ := good_rounds u p hp key₀ h0 hf R hR d hg
  obtain ⟨file, j, real, real2, -, -, hS, T⟩ := good_chains u p hp d hg
  have hS' : Params.describeWith p.chains.key.oneTime.given Params.labelOneTime
      (Params.OneTime.statement d.1) .inFile d.2.rounds1 0 = some d.2.S1 := hS
  exact
    { gives := gives_of_chains a T hS' R₃ hA hok hsh hb
      yes := keyRefusal_of_chains T
      key := T.key_made
      places := readPlace_places T.place_read }

/-- **The typing returns at a good reading**, from tests on the data and one hypothesis on that
reading. -/
theorem good_returns (a sb : ℕ) (cfg : ByteArray) (C : CK) (hok : okAt a (some R) = true)
    (s₁ : p.chains.key.oneTime.given.plan.salt = sb) (s₂ : p.chains.key.shared.given.plan.salt = sb)
    (s₃ : p.chains.key.second.given.plan.salt = sb)
    (hT : SameTwice (Three.Whole.of R.1 R.2.1 R.2.2) d.2.r) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) sb cfg d.2.r = true := by
  obtain ⟨R₃, rfl, hA, hI, hSh⟩ := good_rounds u p hp key₀ h0 hf R hR d hg
  obtain ⟨file, j, real, real2, -, -, hS, T⟩ := good_chains u p hp d hg
  have hS' : Params.describeWith p.chains.key.oneTime.given Params.labelOneTime
      (Params.OneTime.statement d.1) .inFile d.2.rounds1 0 = some d.2.S1 := hS
  exact returns_of_read C a sb cfg T.toRead hS' (fun e => by cases e) R₃ hA hI hSh hok s₁ s₂ s₃ hT

end

end OnBytes.Maker
