-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/GoodCollides.lean: at a good reading of a key file or of a proof file (`KeyGood`,
`ProofGood`, OnBytes/TieK/Good.lean): either the typing of the whole file returns, or the file shows
a collision of the leaf hash (`CollidesIn`, OnBytes/Maker/Page/TwiceOrCollide.lean).

The law itself is `returns_or_collides` (OnBytes/Maker/Page/ReturnsOrCollide.lean), which speaks at
a record of the three chains' reading. Here that record is the one that a good reading has at its
own values (OnBytes/Maker/GoodKey.lean, GoodProof.lean), and the plain data are those made once,
from the public input, at a fixed key that fits.

  `good_dry3`, `good_dry3P`   the dry runs at the reading's own key give the three lists R
  `good_returns_or_collides`, `good_returns_or_collidesP`   the statement

The second arm. `CollidesIn Fmt.formatHash W d.2.r cfgS` says: among the openings that were read off this
file there are two of one tree (or two of stored tables) that list one position with two different
pairs of a column and a salt, and the two pairs have one leaf hash at one shape, one start and that
position. It speaks of pairs: that two different pairs are two different inputs of the hash is
another law (OnBytes/Maker/Page/LeafInputs.lean).

Premises. The planner's value p and, for a proof file, so, cov, links: named by their equations at
the public input. Of the fixed key: the item 0, and that it fits the shape of the shared chain's
index. That the dry runs at it return R. Tests on the data: `okAt`, `oneShapeB` (all stored tables
that the rounds open have one shape). `OneSetting`: the three chains have one digest of the public
files and one number of bytes of a salt.

Not claimed. That the tests pass at any public input. That the second arm is rare or cannot be met.
The split into the two arms is classical; `typeReturns` is the Boolean that tells them apart.
Nothing on soundness. The two statements have no caller; OnBytes/Maker/Page/GoodCollidesB.lean and
GoodCollidesBP.lean hold the like with a collision on bytes.


-/
import OnBytes.Maker.Page.Collides
import OnBytes.Maker.GoodProof
import OnBytes.Maker.ProofOwn

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

section Key
variable (u : KeyPub) (p : Model.Verify.Planned)
  (hp : Model.Verify.planned u.pol u.KL (some u.lay) = .ok p) (key₀ : TableKey)
  (h0 : key₀.item = 0)
  (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
  (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R)
  (d : Params.TableName × ChainsData) (hg : KeyGood u d)
include hp h0 hf hR hg

/-- The dry runs at the reading's own key give the three lists that were made at the fixed key. -/
theorem good_dry3 : dryKey p.chains.key d.2.r.key = some R := by
  obtain ⟨file, j, real, real2, -, -, -, T⟩ := good_chains u p hp d hg
  obtain ⟨seeds, -, hk, hfit⟩ := tableKey_open _ _ _ _ _ _ T.key_made
  have hi : d.2.r.key.item = 0 := by rw [hk]
  rw [← dryKey_keyAlike (keyAlike_of_fits (Key.tailPublic p.chains.key noTable).lin.fold.index
    (h0.trans hi.symm) hf hfit)]
  exact hR

/-- **A key file: at a good reading either the typing's six parts return, or the file shows a
collision of the leaf hash.** cfg: the typing's letter. -/
theorem good_returns_or_collides (C : CK) (a sb : ℕ) (cfg cfgS : ByteArray)
    (hok : okAt a (some R) = true) (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hs : OneSetting p.chains.key.oneTime.given p.chains.key.shared.given
      p.chains.key.second.given cfgS sb) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) sb cfg d.2.r = true ∨
      CollidesIn Fmt.formatHash (Three.Whole.of R.1 R.2.1 R.2.2) d.2.r cfgS := by
  have hR' := good_dry3 u p hp key₀ h0 hf R hR d hg
  obtain ⟨file, j, real, real2, -, -, hS, T0⟩ := good_chains u p hp d hg
  have T := T0.toRead
  have hS' : Params.describeWith p.chains.key.oneTime.given Params.labelOneTime
      (Params.OneTime.statement d.1) .inFile d.2.rounds1 0 = some d.2.S1 := hS
  unfold dryKey at hR'
  rw [T.first_dry] at hR'
  have hd : Three.dry3 (Key.tailPublic p.chains.key d.1) d.2.r.key (d.2.rounds1, d.2.dry) =
      some R := hR'
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  have hfit := (okAt_parts hok).fits
  have hst : storedFit a (Three.Whole.of d.2.rounds1 d.2.rounds2 R₃) = true :=
    (okAt_parts hok).stored
  obtain ⟨o₁, b₁⟩ := key_own p.chains.key.oneTime T.first_dry
  obtain ⟨a₁, a₂, a₃⟩ := storedAt_of_fit hst
  have N := named_of_read T hS' b₁ R₃ hd
  have F : FileFits (Three.Whole.of d.2.rounds1 d.2.rounds2 R₃) sb a d.2.S1 d.2.S2 d.2.S3 :=
    fileFits_of hfit hS' T.shared_spec T.second_spec (alike_shapes N) (alike_stored N) hs.s₁ hs.s₂
      hs.s₃ a₁ a₂ a₃
  have sE : ShapeOneE (Three.Whole.of d.2.rounds1 d.2.rounds2 R₃) d.2.r :=
    shapeOneE_of hB (tables_fit _ sb a d.2.S1 d.2.S2 d.2.S3 F d.2.r file _ _ _ _ _ _ _ _ _
      T.first_read T.shared_read T.second_read).2.2.1
  exact returns_or_collides C a sb cfg cfgS T hS' (fun e => by cases e) o₁ b₁ R₃ hd hok hfit hst
    hs.s₁ hs.s₂ hs.s₃ hs.c₁ hs.c₂ hs.c₃ sE

end Key

section Proof
variable (u : ProofPub) (p : Model.Verify.Planned)
  (hp : Model.Verify.planned u.pol u.KL (some u.lay) = .ok p) (so : Model.Head.StOwn)
  (hso : Model.Head.stFromCall (Model.Verify.words32 u.request) (Model.Verify.words32 u.y) p.X.T =
    .ok so)
  (cov : Model.Head.Covered) (hcov : Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov)
  (links : Array Model.Stages.LinkH) (hl : Model.Verify.linksOf p.X cov = .ok links)
  (d : Params.TableName × ChainsData) (hg : ProofGood u d) (key₀ : TableKey) (h0 : key₀.item = 0)
  (hf : key₀.fits (tailPublic p.chains.proof noTable).lin.fold.index = true)
  (R : Rounds × Rounds × Rounds)
  (hR : dryProof p.chains.proof key₀ (blockAt p links so.y) = some R)
include hp hso hcov hl hg h0 hf hR

/-- The dry runs at the reading's own key give the three lists that were made at the fixed key. -/
theorem good_dry3P : dryProof p.chains.proof d.2.r.key (blockAt p links so.y) = some R := by
  obtain ⟨ent, copy, file, i, item, real, real2, -, -, -, -, -, T⟩ :=
    good_chainsP u p hp so hso cov hcov links hl d hg
  obtain ⟨seeds, -, hk, hfit⟩ := tableKey_open _ _ _ _ _ _ T.key_made
  have hi : d.2.r.key.item = 0 := by rw [hk]
  rw [← dryProof_keyAlike (keyAlike_of_fits (tailPublic p.chains.proof noTable).lin.fold.index
    (h0.trans hi.symm) hf hfit)]
  exact hR

/-- **A proof file: at a good reading either the typing's six parts return, or the file shows a
collision of the leaf hash.** -/
theorem good_returns_or_collidesP (C : CK) (a sb : ℕ) (cfg cfgS : ByteArray)
    (hok : okAt a (some R) = true) (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hs : OneSetting p.chains.proof.first.given p.chains.proof.shared.given
      p.chains.proof.second.given cfgS sb) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) sb cfg d.2.r = true ∨
      CollidesIn Fmt.formatHash (Three.Whole.of R.1 R.2.1 R.2.2) d.2.r cfgS := by
  have hR' := good_dry3P u p hp so hso cov hcov links hl d hg key₀ h0 hf R hR
  obtain ⟨ent, copy, file, i, item, real, real2, -, -, -, -, hS, T0⟩ :=
    good_chainsP u p hp so hso cov hcov links hl d hg
  have T := T0.toRead
  have hS' : Params.describeWith p.chains.proof.first.given Params.labelFirst
      (Params.First.statement d.1 copy item u.request) .inFile d.2.rounds1 0 = some d.2.S1 := hS
  unfold dryProof at hR'
  rw [T.first_dry] at hR'
  have hd : Three.dry3 (tailPublic p.chains.proof d.1) d.2.r.key (d.2.rounds1, d.2.dry) =
      some R := hR'
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  have hfit := (okAt_parts hok).fits
  have hst : storedFit a (Three.Whole.of d.2.rounds1 d.2.rounds2 R₃) = true :=
    (okAt_parts hok).stored
  obtain ⟨o₁, b₁⟩ := proof_own_program p.X hl p.built.links p.chains.proof.first
    p.X.layers.wsLay (Model.ofNat so.y) T.first_dry
  obtain ⟨a₁, a₂, a₃⟩ := storedAt_of_fit hst
  have N := named_of_read T hS' b₁ R₃ hd
  have F : FileFits (Three.Whole.of d.2.rounds1 d.2.rounds2 R₃) sb a d.2.S1 d.2.S2 d.2.S3 :=
    fileFits_of hfit hS' T.shared_spec T.second_spec (alike_shapes N) (alike_stored N) hs.s₁ hs.s₂
      hs.s₃ a₁ a₂ a₃
  have sE : ShapeOneE (Three.Whole.of d.2.rounds1 d.2.rounds2 R₃) d.2.r :=
    shapeOneE_of hB (tables_fit _ sb a d.2.S1 d.2.S2 d.2.S3 F d.2.r file _ _ _ _ _ _ _ _ _
      T.first_read T.shared_read T.second_read).2.2.1
  exact returns_or_collides C a sb cfg cfgS T hS' (fun e => by cases e) o₁ b₁ R₃ hd hok hfit hst
    hs.s₁ hs.s₂ hs.s₃ hs.c₁ hs.c₂ hs.c₃ sE

end Proof

end OnBytes.Maker.Page
