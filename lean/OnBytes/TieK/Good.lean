-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/Good.lean: the good readings of a key file and of a proof file, and all that holds at
the data of a good reading.

A reading is good at a public input if some file whose three chains the program's check has read and
judged under that input (`KeyOpened`; `EntryGave` and `ProofOpened`) is read to it by
`readKeyChains` or `readProofChains` (OnBytes/TieK/ReadThreeDefs.lean). This is less than a yes of
the whole program. A hypothesis that is to become a theorem is said of all good readings, before a
file is known.

Main names:
  `KeyPub`, `ProofPub`: the public input of a key file's and of a proof file's reading.
  `KeyGood u d`, `ProofGood u d`: d is a good reading at u.
  `KeyGood.of_opened`, `ProofGood.of_opened`: a file whose chains were read and judged is read to
    one.
  `KeyGood.facts`, `ProofGood.facts`: at a good reading d: the file, the planner's value, the flat
    record `ThreeChains` at d's values, the first chain's description, the facts on the salt and the
    siblings of the binding tree's leaf, the number of the stored copy, both seals' 32 bytes, that
    the table's key fits the table's shape (that `tableKey` made it stands in the record;
    `tableKey_open` opens it), and one digest of the public files in all chains.
Limits: it claims nothing on soundness. The program does not import this file.
All is said at the program's own fixed hash functions; no hash is an argument here; nothing at a
drawn function.

-/
import OnBytes.TieK.HolesOfChains
import OnBytes.TieK.SealSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK
open Proof

/-- The public input of a key file's reading: the three public files. -/
structure KeyPub where
  pol : ByteArray
  lay : ByteArray
  KL : ByteArray

/-- A good reading of a key file: at some key file, the program's three chains were read and judged
and the fixed reading returns this table and these data. -/
def KeyGood (u : KeyPub) (d : Params.TableName × ChainsData) : Prop :=
  ∃ F : K.Files, F.pol = u.pol ∧ F.lay = u.lay ∧ F.KL = u.KL ∧ KeyOpened F d.1 ∧
    readKeyChains u.pol u.lay u.KL F.key = some d

/-- The public input of a proof file's reading: the three public files, the request, the reply. -/
structure ProofPub where
  pol : ByteArray
  lay : ByteArray
  KL : ByteArray
  request : ByteArray
  y : ByteArray

/-- A good reading of a proof file: at some files, the entry file has given the further table, the
program's three chains were read and judged, and the fixed reading returns these data. -/
def ProofGood (u : ProofPub) (d : Params.TableName × ChainsData) : Prop :=
  ∃ (F : K.Files) (table : Params.TableName), F.pol = u.pol ∧ F.lay = u.lay ∧ F.KL = u.KL ∧
    F.request = u.request ∧ F.y = u.y ∧ EntryGave F table d.1 ∧ ProofOpened F d.1 ∧
    readProofChains u.pol u.lay u.KL u.request u.y F.ent F.entry F.proof = some d

/-- A key file whose three chains were read and judged is read by `readKeyChains` to a good reading
at its public files. -/
theorem KeyGood.of_opened {F : K.Files} {table : Params.TableName} (h : KeyOpened F table) :
    ∃ d, readKeyChains F.pol F.lay F.KL F.key = some (table, d) ∧
      KeyGood ⟨F.pol, F.lay, F.KL⟩ (table, d) := by
  obtain ⟨_, _, d, _, _, -, -, hd, -⟩ := readKeyChains_of F table h
  exact ⟨d, hd, F, rfl, rfl, rfl, h, hd⟩

/-- A proof file whose three chains were read and judged, beside an entry file that gave the table,
is read by `readProofChains` to a good reading at its public input. -/
theorem ProofGood.of_opened {F : K.Files} {table further : Params.TableName}
    (he : EntryGave F table further) (h : ProofOpened F further) :
    ∃ d, readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof = some (further, d) ∧
      ProofGood ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ (further, d) := by
  obtain ⟨_, _, _, _, _, _, d, _, _, -, -, -, -, -, -, hd, -⟩ :=
    readProofChains_of F table further he h
  exact ⟨d, hd, F, table, rfl, rfl, rfl, rfl, rfl, he, h, hd⟩

/-- **All that holds at a good reading of a key file.** -/
theorem KeyGood.facts {u : KeyPub} {d : Params.TableName × ChainsData} (h : KeyGood u d) :
    ∃ (F : K.Files) (p : Model.Verify.Planned) (j : Nat) (real : FirstEnd) (real2 : SharedEnd),
      F.pol = u.pol ∧ F.lay = u.lay ∧ F.KL = u.KL ∧ KeyOpened F d.1 ∧
      readKeyChains u.pol u.lay u.KL F.key = some d ∧
      Model.Verify.planned u.pol u.KL (some u.lay) = .ok p ∧
      Tie.SameChains p (Params.configurationDigest [u.pol, u.lay, u.KL]) ∧
      Key.readTable p.chains.key.oneTime.lin.fold.index p.chains.key.oneTime.given.cfg F.key =
        .ok (d.1, j) ∧
      p.chains.key.oneTime.describe d.1 d.2.rounds1 = some d.2.S1 ∧
      ThreeChains (Key.tailPublic p.chains.key d.1) (Key.oneTime p.chains.key.oneTime)
        (Key.startOf p.chains.key.oneTime) F.key j d.2.rounds1 d.2.dry d.2.S1 d.2.r d.2.seal1
        d.2.seal2 d.2.rounds2 d.2.dry2 d.2.S2 d.2.rounds3 d.2.S3 real real2 ∧
      SlotFacts p.chains.key.oneTime.binding p.chains.key.shared.given.cfg d.2.seal1 F.key
        d.2.r.first.next d.2.r.place d.2.salt d.2.path ∧
      d.2.copy = 0 ∧ d.2.seal1.size = 32 ∧ d.2.seal2.size = 32 ∧
      d.2.r.key.fits (Key.tailPublic p.chains.key d.1).lin.fold.index = true := by
  obtain ⟨F, e1, e2, e3, ho, hd⟩ := h
  obtain ⟨p, j, d', real, real2, hp, ht, hd', hs, h3, sf, hc⟩ := readKeyChains_of F d.1 ho
  rw [e1, e2, e3] at hd' hp
  have ed : d = (d.1, d') := Option.some.inj (hd.symm.trans hd')
  have e' : d' = d.2 := (congrArg Prod.snd ed).symm
  subst e'
  have ho' := ho
  obtain ⟨p', _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp', hsame, -⟩ := ho
  rw [e1, e2, e3] at hp' hsame
  have ep : p' = p := Except.ok.inj (hp'.symm.trans hp)
  subst ep
  obtain ⟨_, -, -, hfit⟩ := tableKey_open _ _ _ _ _ _ h3.key_made
  exact ⟨F, p', j, real, real2, e1, e2, e3, ho', hd, hp, hsame, ht, hs, h3, sf, hc, h3.seal1_size,
    h3.seal2_size, hfit⟩

/-- **All that holds at a good reading of a proof file.** -/
theorem ProofGood.facts {u : ProofPub} {d : Params.TableName × ChainsData} (h : ProofGood u d) :
    ∃ (F : K.Files) (table : Params.TableName) (p : Model.Verify.Planned),
      ∃ so cov item links i real real2,
      F.pol = u.pol ∧ F.lay = u.lay ∧ F.KL = u.KL ∧ F.request = u.request ∧ F.y = u.y ∧
      EntryGave F table d.1 ∧ ProofOpened F d.1 ∧
      readProofChains u.pol u.lay u.KL u.request u.y F.ent F.entry F.proof = some d ∧
      Model.Verify.planned u.pol u.KL (some u.lay) = .ok p ∧
      Tie.SameChains p (Params.configurationDigest [u.pol, u.lay, u.KL]) ∧
      Model.Head.stFromCall (Model.Verify.words32 u.request) (Model.Verify.words32 u.y) p.X.T =
        .ok so ∧
      Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov ∧
      Proof.requestItem u.pol u.KL u.request = some item ∧
      Model.Verify.linksOf p.X cov = .ok links ∧
      readProofHead p.chains.proof.first.given.plan.field F.proof = .ok (F.entry, i) ∧
      p.chains.proof.first.describe d.1 F.entry item F.request d.2.rounds1 = some d.2.S1 ∧
      ThreeChains (tailPublic p.chains.proof d.1)
        (firstBlock p.chains.proof.first
          (Model.Stages.runLinksH
            (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
            p.chains.proof.first p.X.layers.wsLay) (Model.ofNat so.y))
        (firstStart p.chains.proof.first) F.proof i d.2.rounds1 d.2.dry d.2.S1 d.2.r d.2.seal1
        d.2.seal2 d.2.rounds2 d.2.dry2 d.2.S2 d.2.rounds3 d.2.S3 real real2 ∧
      SlotFacts p.chains.proof.first.binding p.chains.proof.shared.given.cfg d.2.seal1 F.proof
        d.2.r.first.next d.2.r.place d.2.salt d.2.path ∧
      d.2.copy = F.entry ∧ d.2.seal1.size = 32 ∧ d.2.seal2.size = 32 ∧
      d.2.r.key.fits (tailPublic p.chains.proof d.1).lin.fold.index = true := by
  obtain ⟨F, table, e1, e2, e3, e4, e5, he, ho, hd⟩ := h
  obtain ⟨p, so, cov, item, links, i, d', real, real2, hp, h1, h2, h3, h4, hh, hd', hs, h5, sf,
    hc⟩ := readProofChains_of F table d.1 he ho
  rw [e1, e2, e3, e4, e5] at hd'
  rw [e1, e2, e3] at hp
  rw [e4, e5] at h1
  rw [e1, e3, e4] at h3
  have ed : d = (d.1, d') := Option.some.inj (hd.symm.trans hd')
  have e' : d' = d.2 := (congrArg Prod.snd ed).symm
  subst e'
  have ho' := ho
  obtain ⟨p', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp', hsame, -⟩ := ho
  rw [e1, e2, e3] at hp' hsame
  have ep : p' = p := Except.ok.inj (hp'.symm.trans hp)
  subst ep
  obtain ⟨_, -, -, hfit⟩ := tableKey_open _ _ _ _ _ _ h5.key_made
  exact ⟨F, table, p', so, cov, item, links, i, real, real2, e1, e2, e3, e4, e5, he, ho', hd, hp,
    hsame, h1, h2, h3, h4, hh, hs, h5, sf, hc, h5.seal1_size, h5.seal2_size, hfit⟩

end OnBytes.TieK

#print axioms OnBytes.TieK.KeyGood.of_opened
#print axioms OnBytes.TieK.ProofGood.of_opened
#print axioms OnBytes.TieK.KeyGood.facts
#print axioms OnBytes.TieK.ProofGood.facts
