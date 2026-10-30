-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/ReadThree.lean: one fixed reading of a file with three chains: a function from the
public values and the file's bytes to the data of the flat record `ThreeChains`.

OnBytes/TieK/Chains.lean says what a yes of the program's check establishes, as a relation between
the file and thirteen values. Here eleven of them, all but the two that come from the deciding
runs, are given by a function, `readThree`. It parses and does not search: it makes the dry runs,
the descriptions, and calls the program's own readers (`readChain`, `Proof.readPlace`, `tableKey`)
in the program's order. It runs no block on a view and looks at no verdict. The definitions are in
OnBytes/TieK/ReadThreeDefs.lean; this file has the theorems on them.

Main names:
  `ChainsData`: the three descriptions with their rounds, the two dry ends, the three chains as
    read with the place and the table's key, the two seals, the salt and the siblings of the
    binding tree's leaf, and the number of the stored copy.
  `readThree`: the reading, from the first chain's first byte on.
  `SlotFacts`: what holds of the salt and the siblings of the binding tree's leaf.
  `readThree_of`: where `ThreeChains` holds, `readThree` returns its values, with `SlotFacts`.
  `readKeyChains`: the reading of a key file, from the three public files and the key file's bytes.
  `readKeyChains_of`: where `KeyOpened F table` holds, it returns the table and data at which the
    flat record holds.
  `furtherOf`, `furtherOf_of`: the table of an entry file, by the program's own readers.
  `readProofChains`, `readProofChains_of`: the same for a proof file, from the files' bytes and the
    number of the stored copy.
Limits: it claims nothing on soundness. That `readThree` returns a value does not say that the
program says yes. The program does not import this file.

-/
import OnBytes.TieK.PortChains
import OnBytes.TieK.ReadThreeDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK
open OnBytes.Proof OnBytes.Tie

/-- What holds of the salt and the siblings of the binding tree's leaf. s: the tree's shape; cfg:
the digest under which it is hashed; closing: the first chain's seal; pl: the place as read. -/
structure SlotFacts (s : Params.LinBindingShape) (cfg closing b : ByteArray) (i : Nat) (pl : Place)
    (salt : ByteArray) (path : List ByteArray) : Prop where
  /-- they are the bytes behind the word at i -/
  bytes : slotBytes s b i = some (salt, path)
  /-- the salt as a slice, the siblings as a path, behind the word -/
  parts : ∃ w i1, Fmt.rdWord b i = some (w, i1) ∧ Fmt.slice b i1 s.saltBytes = some salt ∧
    pathAt b s.logLeaves (i1 + s.saltBytes) = some path
  /-- one sibling for each level -/
  pathLen : path.length = s.logLeaves
  /-- the place is the number of a leaf -/
  placeLt : pl.place < 2 ^ s.logLeaves
  /-- the root is the one to which the leaf leads along the siblings -/
  root : pl.root = rootOf cfg (Fmt.bindLeaf s.logLeaves pl.place cfg closing salt) pl.place path

/-- Where `Proof.readPlace` returns, the salt and the siblings are there, with these facts. -/
theorem slotBytes_of {s : Params.LinBindingShape} {cfg closing b : ByteArray} {i : Nat}
    {pl : Place} (h : readPlace s cfg closing b i = some pl) :
    ∃ salt path, SlotFacts s cfg closing b i pl salt path := by
  obtain ⟨-, w, i1, salt, path, h1, h2, h3, h4, h5, h6⟩ := readPlace_open _ _ _ _ _ _ h
  subst h6
  refine ⟨salt, path, ?_, ⟨w, i1, h1, h3, h4⟩, h5, h2, rfl⟩
  unfold slotBytes
  rw [h1]
  dsimp only
  rw [h3]
  dsimp only
  rw [h4]
  rfl

/-- **Where the flat record holds, the reading returns its values.** -/
theorem readThree_of {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray}
    {i : Nat} {rounds1 : Params.Rounds} {dry : FirstEnd} {S1 : Fmt.SpecX} {r : TailRead}
    {seal1 seal2 : ByteArray} {rounds2 : Params.Rounds} {dry2 : SharedEnd} {S2 : Fmt.SpecX}
    {rounds3 : Params.Rounds} {S3 : Fmt.SpecX} {real : FirstEnd} {real2 : SharedEnd}
    (h : ThreeChains p block1 start1 file i rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2 rounds3 S3
      real real2)
    (describe1 : Params.Rounds → Option Fmt.SpecX) (hd : describe1 rounds1 = some S1)
    (copy : Nat) :
    ∃ salt path,
      readThree p block1 start1 describe1 file i copy =
        some ⟨rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2, rounds3, S3, salt, path,
          copy⟩ ∧
      SlotFacts p.binding p.shared.given.cfg seal1 file r.first.next r.place salt path := by
  obtain ⟨salt, path, hf⟩ := slotBytes_of h.place_read
  have hs := hf.bytes
  refine ⟨salt, path, ?_, hf⟩
  have f1 : (⟨r.first.out, viewOf S1 r.first.out, r.first.next⟩ : ChainRead) = r.first := by
    rw [← h.first_view]
  have f2 : (⟨r.shared.out, viewOf S2 r.shared.out, r.shared.next⟩ : ChainRead) = r.shared := by
    rw [← h.shared_view]
  have f3 : (⟨r.second.out, viewOf S3 r.second.out, r.second.next⟩ : ChainRead) = r.second := by
    rw [← h.second_view]
  unfold readThree
  rw [h.first_dry]
  dsimp only
  rw [hd]
  dsimp only
  rw [h.first_read]
  dsimp only
  rw [f1, h.first_seal]
  dsimp only
  rw [h.place_read]
  dsimp only
  rw [hs]
  dsimp only
  rw [h.key_made]
  dsimp only
  rw [h.shared_dry]
  dsimp only
  rw [h.shared_spec]
  dsimp only
  rw [h.shared_read]
  dsimp only
  rw [f2, h.shared_seal]
  dsimp only
  rw [h.second_rounds]
  dsimp only
  rw [h.second_spec]
  dsimp only
  rw [h.second_read]
  dsimp only
  rw [f3, if_pos h.whole]

/-- **Where the key file's three chains were read and judged, the reading returns the program's own
table and data d at which the flat record holds**: the three descriptions, the three chains as read
and the seals are d's, and the three blocks' runs say yes on d's views. -/
theorem readKeyChains_of (F : K.Files) (table : Params.TableName) (h : KeyOpened F table) :
    ∃ p j d real real2,
      Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      Key.readTable p.chains.key.oneTime.lin.fold.index p.chains.key.oneTime.given.cfg F.key =
        .ok (table, j) ∧
      readKeyChains F.pol F.lay F.KL F.key = some (table, d) ∧
      p.chains.key.oneTime.describe table d.rounds1 = some d.S1 ∧
      ThreeChains (Key.tailPublic p.chains.key table) (Key.oneTime p.chains.key.oneTime)
        (Key.startOf p.chains.key.oneTime) F.key j d.rounds1 d.dry d.S1 d.r d.seal1 d.seal2
        d.rounds2 d.dry2 d.S2 d.rounds3 d.S3 real real2 ∧
      SlotFacts (Key.tailPublic p.chains.key table).binding
        (Key.tailPublic p.chains.key table).shared.given.cfg d.seal1 F.key d.r.first.next d.r.place
        d.salt d.path ∧
      d.copy = 0 := by
  obtain ⟨p, j, rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2, rounds3, S3, real, real2, hp,
    -, -, -, -, -, ht, hd, h3⟩ := h
  obtain ⟨salt, path, e, hf⟩ := readThree_of h3 _ hd 0
  refine ⟨p, j, ⟨rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2, rounds3, S3, salt, path, 0⟩,
    real, real2, hp, ht, ?_, hd, h3, hf, rfl⟩
  unfold readKeyChains
  rw [hp]
  dsimp only
  rw [ht]
  dsimp only
  rw [e]
  rfl

/-- Where the program's check of an entry file returns a table, it is the one that `furtherOf`
reads. -/
theorem furtherOf_of {params : ByteArray} {p : Params.Link} {first further : Params.TableName}
    {ent : ByteArray} (hp : Params.Link.read params = some p)
    (h : Entry.check params first ent = .ok further) : furtherOf p ent = some further := by
  unfold Entry.check at h
  rw [hp] at h
  dsimp only at h
  cases hr : Entry.read p first ent with
  | error e => rw [hr] at h; cases h
  | ok r =>
    rw [hr] at h
    dsimp only at h
    have hf : r.further = further := by
      split at h
      · injection h
      · cases h
    unfold Entry.read at hr
    dsimp only at hr
    unfold furtherOf
    split at hr
    · cases hr
    · rename_i i hi
      rw [hi]
      dsimp only
      split at hr
      · cases hr
      · split at hr
        · cases hr
        · rename_i fu j ht
          rw [ht]
          dsimp only
          split at hr
          · split at hr
            · cases hr
            · split at hr
              · cases hr
              · split at hr
                · cases hr
                · injection hr with hr'
                  rw [← hf, ← hr']
          · cases hr

/-- The entry file has given the further table, against the first, at the planner's link. -/
def EntryGave (F : K.Files) (table further : Params.TableName) : Prop :=
  ∃ p, Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
    Entry.check (p.chains.bytes .link) table F.ent = .ok further

/-- **Where the entry file has given the further table and the proof file's three chains were read
and judged, the reading returns that table and data d at which the flat record holds.** -/
theorem readProofChains_of (F : K.Files) (table further : Params.TableName)
    (he : EntryGave F table further) (h : ProofOpened F further) :
    ∃ p so cov item links i d real real2,
      Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y) p.X.T =
        .ok so ∧
      Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov ∧
      Proof.requestItem F.pol F.KL F.request = some item ∧
      Model.Verify.linksOf p.X cov = .ok links ∧
      readProofHead p.chains.proof.first.given.plan.field F.proof = .ok (F.entry, i) ∧
      readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof = some (further, d) ∧
      p.chains.proof.first.describe further F.entry item F.request d.rounds1 = some d.S1 ∧
      ThreeChains (tailPublic p.chains.proof further)
        (firstBlock p.chains.proof.first
          (Model.Stages.runLinksH
            (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
            p.chains.proof.first p.X.layers.wsLay) (Model.ofNat so.y))
        (firstStart p.chains.proof.first) F.proof i d.rounds1 d.dry d.S1 d.r d.seal1 d.seal2
        d.rounds2 d.dry2 d.S2 d.rounds3 d.S3 real real2 ∧
      SlotFacts (tailPublic p.chains.proof further).binding
        (tailPublic p.chains.proof further).shared.given.cfg d.seal1 F.proof d.r.first.next
        d.r.place d.salt d.path ∧
      d.copy = F.entry := by
  obtain ⟨p, so, cov, item, links, i, rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2, rounds3,
    S3, real, real2, hp, hs, -, -, -, h1, h2, h3, h4, hh, hd, h5⟩ := h
  obtain ⟨p', hp', hc⟩ := he
  have ep : p' = p := Except.ok.inj (hp'.symm.trans hp)
  subst ep
  have hfu := furtherOf_of hs.2.2 hc
  obtain ⟨salt, path, e, hf⟩ := readThree_of h5 _ hd F.entry
  refine ⟨p', so, cov, item, links, i,
    ⟨rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2, rounds3, S3, salt, path, F.entry⟩, real,
    real2, hp, h1, h2, h3, h4, hh, ?_, hd, h5, hf, rfl⟩
  unfold readProofChains
  rw [hp]
  dsimp only
  rw [hfu]
  dsimp only
  rw [h1]
  dsimp only
  rw [h2]
  dsimp only
  rw [h3]
  dsimp only
  rw [h4]
  dsimp only
  rw [hh]
  dsimp only
  rw [if_pos rfl, e]
  rfl

end OnBytes.TieK

#print axioms OnBytes.TieK.readProofChains_of
#print axioms OnBytes.TieK.readThree_of
#print axioms OnBytes.TieK.readKeyChains_of
