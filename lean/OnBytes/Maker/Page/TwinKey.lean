-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/TwinKey.lean: the key file's like of OnBytes/Maker/Page/TwinClose.lean: from the
record of a key file's reading to the equation of the reader that is written over a monad with the
hash as a letter (`M.Key.readKey`, OnBytes/ChecksWithHashAsArgument/M/Key/File.lean); and, where the verifier program
has said yes, the dry runs at a fixed key return three lists and four tests on their plain data
pass, that the six parts of the typing return or the key file shows a collision of the hash over the
realised oracle. The second arm's reader and collision stand at that hash; the first arm's reading
and the plan are the program's, at its own hash.

Statements and proofs. A key file's reader and a proof file's share the named reading of a chain and
the reading of the tail, so the laws `ret_readNamed` and `ret_readTail` of TwinClose.lean serve
here. OnBytes/Tie/PlaceDom.lean has that the reading of the place in the binding tree and the making
of the table's key give at `Fmt.HO Fmt.oracle` what the program's give, from 32 bytes of the
configuration's digest and of the table's root.

Main names:
  `twinKey_returns`: at a letter h: the first description, the record, the three readings at h
    (`ReadAt h`), the place at h and the table's key at h give
    `fromStart (M.Key.readKey (m := Id) h ..) = .ok r`.
  `shared_cfg32`: at the record of a reading the shared chain's configuration digest has 32 bytes.
  `twinKey_returns_O`: at `Fmt.HO Fmt.oracle`, from the record, the bounds `SmallThree` and 32 bytes
    of the table's root.
  `port_key_orMO`: at the files to which the program has said yes: the second arm is
    `keyCollidesAtM (Fmt.HO Fmt.oracle) F table` (OnBytes/Maker/Page/CollidesM.lean).
Under "there is": the letters of `keyCollidesAtM` alone (the head of
OnBytes/Maker/Page/CollidesM.lean has each with its equation).
Limits: one direction. The four tests (`okAt`, `shapesFit`, `oneShapeB`, `saltsFit`) are not shown
here. The equation of the dry runs at the fixed key is a premise too. In the second arm the plan is
made by the program's planner, at the format's hash; whether the dry runs hash is not looked at (the
head of CollidesM.lean). `twinKey_returns` can be called only at an h that agrees with `Fmt.formatHash` on
every call of this file's reading, since its record holds these calls' outcomes at `Fmt.formatHash`; its
proof reads none of the record's five hashed fields. Nothing at a drawn function. Nothing on
opening-form binding, no two openings of a commitment, correctness of extraction, what a root fixes
or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.TwinClose
import OnBytes.Tie.LeafCall
import OnBytes.Maker.Page.CollidesM
import OnBytes.Maker.EntriesPlan

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)
open OnBytes.TwoPort

section
variable (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray) (j : ℕ)
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃ : Rounds} {S₃ : Fmt.SpecX}

/-- **At a letter: the record, with its five hashing steps at h, gives the twin's equation at h.**
-/
theorem twinKey_returns (h : HId) (hS : k.oneTime.describe table R₁ = some S₁)
    (T : ThreeRead (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃)
    (A : ReadAt h S₁ S₂ S₃ file j r)
    (place : M.Proof.readPlace (m := Id) h (Key.tailPublic k table).binding
      (Key.tailPublic k table).shared.given.cfg seal1 file r.first.next =
        (some r.place : Option Place))
    (key : M.tableKey (m := Id) h (Key.tailPublic k table).shared.given.plan.field
      (Key.tailPublic k table).shared.given.cfg (Key.tailPublic k table).lin.fold.index
      (Key.tailPublic k table).table 0 = (some r.key : Option TableKey)) :
    M.Proof.Reading.fromStart (M.Key.readKey (m := Id) h k table file j) =
      (Except.ok r : Except String TailRead) := by
  have R : Ret (M.Key.readKey (m := Id) h k table file j) Session.start r
      ⟨r.second.out.seen⟩ := by
    unfold M.Key.readKey
    dsimp only
    refine ret_bind (ret_need _ _ T.first_dry) ?_
    refine ret_bind (ret_need _ _ hS) ?_
    refine ret_bind (ret_readNamed h _ _ _ _ _ r.first A.first T.first_view) ?_
    refine ret_bind (ret_readTail h T.first_seal place key T.shared_dry T.shared_spec A.shared
      T.shared_view T.shared_seal T.second_rounds T.second_spec A.second T.second_view) ?_
    refine ret_guard _ (by
      have hw : r.next = file.size := T.whole
      simp [hw]) ?_
    exact ret_pure _ _
  unfold M.Proof.Reading.fromStart
  show Except.map _ (M.Key.readKey (m := Id) h k table file j Session.start).run = _
  rw [R]
  rfl

end

/-- At the record of a reading the shared chain's configuration digest has 32 bytes. -/
theorem shared_cfg32 {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray}
    {i : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead}
    {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃ : Rounds}
    {S₃ : Fmt.SpecX}
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃) :
    p.shared.given.cfg.size = 32 :=
  described_cfg32 (g := p.shared.given) (label := p.lab₂)
    (st := Params.Shared.statement p.table r.place.root) (rand := .given r.place.root) (R := R₂)
    (ft := 0) (S := S₂) T.shared_spec

/-- **At the hash over the realised oracle.** -/
theorem twinKey_returns_O (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray)
    (j : ℕ) {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead}
    {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃ : Rounds}
    {S₃ : Fmt.SpecX} (hS : k.oneTime.describe table R₁ = some S₁)
    (T : ThreeRead (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃)
    (hsm : SmallThree S₁ S₂ S₃ file) (hr : table.root.size = 32) :
    M.Proof.Reading.fromStart (M.Key.readKey (m := Id) (Fmt.HO Fmt.oracle) k table file j) =
      (Except.ok r : Except String TailRead) :=
  twinKey_returns k table file j (Fmt.HO Fmt.oracle) hS T (readAt_O T hsm)
    ((Tie.readPlaceM_O _ _ _ _ _ (shared_cfg32 T)).trans T.place_read)
    ((Tie.tableKeyM_O _ _ _ _ _ hr (shared_cfg32 T)).trans T.key_made)

/-- **A key file, both the reading and the collision at the hash over the realised oracle.** d: the
fixed reading of F's key file; key₀: a fixed key at which the three lists R were made. -/
theorem port_key_orMO (F : K.Files) (id : String) (table further : Params.TableName)
    (h : K.PortYesAt F id table further) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) (d : ChainsData)
    (hd : readKeyChains F.pol F.lay F.KL F.key = some (table, d)) (key₀ : TableKey)
    (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R) (C : CK) (a : ℕ)
    (cfg : ByteArray) (hok : okAt a (some R) = true)
    (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hsalts : saltsFit p.chains.key.oneTime.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) =
      true) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) p.chains.key.oneTime.given.plan.salt cfg
        d.r = true ∨ keyCollidesAtM (Fmt.HO Fmt.oracle) F table := by
  have ho := port_key_chains F id table further h
  have hg : KeyGood ⟨F.pol, F.lay, F.KL⟩ (table, d) := ⟨F, rfl, rfl, rfl, ho, hd⟩
  obtain ⟨p', j, d', real, real2, hp', ht, hd', hS, T, -, -⟩ := readKeyChains_of F table ho
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  obtain ⟨-, s₂, s₃⟩ := setting_keyGood hg hp
  have hsm := small_port_key F id table further h p hp d hd key₀ h0 hf R hR a hok hsh
  have Tr := T.toRead
  have hS' : Params.describeWith p.chains.key.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile d.rounds1 0 = some d.S1 := hS
  have hR' : dryKey p.chains.key d.r.key = some R :=
    good_dry3 ⟨F.pol, F.lay, F.KL⟩ p hp key₀ h0 hf R hR (table, d) hg
  have hR2 := hR'
  unfold dryKey at hR2
  rw [Tr.first_dry] at hR2
  have hd3 : Three.dry3 (Key.tailPublic p.chains.key table) d.r.key (d.rounds1, d.dry) =
      some R := hR2
  obtain ⟨R₃, rfl⟩ := dry3_shape hd3 Tr.shared_dry
  obtain ⟨o₁, b₁⟩ := key_own p.chains.key.oneTime Tr.first_dry
  rcases returns_or_collidesInB (Fmt.HO Fmt.oracle) C a p.chains.key.oneTime.given.plan.salt cfg
    p.chains.key.shared.given.cfg Tr (readAt_O Tr hsm) hS' (fun e => by cases e) o₁ b₁ R₃ hd3 hok
    (okAt_parts hok).fits (okAt_parts hok).stored rfl s₂.salt.symm s₃.salt.symm s₂.cfg rfl
    (s₃.cfg.symm.trans s₂.cfg) hB (oneSaltB_of_saltsFit hsalts) with hr | hc
  · exact Or.inl hr
  · obtain ⟨e₁, e₂⟩ := shapes_of_read a p.chains.key.oneTime.given.plan.salt Tr hS' b₁ R₃ hd3
      (okAt_parts hok).fits (okAt_parts hok).stored rfl s₂.salt.symm s₃.salt.symm hB
    have e₃ := sizesOne_of_read a p.chains.key.oneTime.given.plan.salt Tr hS' b₁ R₃ hd3
      (okAt_parts hok).fits (okAt_parts hok).stored rfl s₂.salt.symm s₃.salt.symm hB
      (oneSaltB_of_saltsFit hsalts)
    exact Or.inr ⟨p, j, hp, ht, d.r, _, twinKey_returns_O p.chains.key table F.key j hS Tr hsm
      (Tie.keyTable_root ht), hR', e₁, e₂, e₃, hc⟩

end OnBytes.Maker.Page
