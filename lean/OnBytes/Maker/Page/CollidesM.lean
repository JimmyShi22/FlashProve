-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/CollidesM.lean: "this file shows a collision of the hash h" with the verifier
program's own reader of the file at h too.

Definitions, statements and proofs. In `KeyCollidesB h` and `ProofCollidesB h`
(OnBytes/Maker/Page/CollidesBytes.lean) the file is read by the program's reader, at the format's
hash, whatever h is. OnBytes/ChecksWithHashAsArgument/M/ has the text of the program's readers over a monad, with the
hash as a letter; at the identity monad and the format's hash they are the program's
(OnBytes/ChecksWithHashAsArgument/M/AtPort/Files.lean). Here the reading stands at h. Three clauses more say that the
entries which are compared have one shape as read, one number of words and one number of bytes of a
salt: with them the second call has the arguments of `leafHash h` at the second entry's own shape,
position, column and salt.

Main names:
  `KeyCollidesM h k table file j`, `ProofCollidesM h c table copy request words block file`.
  `keyCollidesAtM h F table`, `proofCollidesAtM h F further`: at a call's files.
  `readKeyM_H`, `readProofM_H`: at the format's hash the reading is the program's.
  `KeyCollidesM.toB`, `ProofCollidesM.toB`: at the format's hash, to CollidesBytes.lean's forms.
  `shapes_of_read`: the first two of the three clauses, at the record of a reading.
  `keyCollidesM_of_record`, `proofCollidesM_of_record`: from the record of the program's reading.
  `port_key_orM`, `port_proof_orM`: where the program has said yes and three tests on the plain data
    pass, the six parts of the typing return or the file shows a collision, in this form, at the
    format's hash.
Under "there is" in the first two: r, the value of the reader at h and the other arguments; R, the
value of the dry runs at r's key. In the two at a call's files: the plan, the place behind the
table, the request's own data, the covered part, the links and the request's item, each fixed by its
own equation.
Limits: in the two at a call's files not all that hashes stands at h. The plan is made by the
program's planner, which hashes the three public files at the format's hash and, by the second hash
function (`secondHashFunction`, `secondHashFunctionTree`, OnBytes/Hash/SecondHashFunction.lean), the same three files (`hPar`), the public
tables of the model's functions (`tableHeld`) and the lists of lookup calls (`callsDigest`). The
request's item is made by `Proof.requestItem`, which hashes the scale file and the request file by
the second hash function's tree hash (`secondHashFunctionTree`, OnBytes/Hash/SecondHashFunction.lean) and three groups of the
parameter file's lines by `secondHashFunction`: neither is h. Both are values of fixed functions at F's files.
That the reader at h asks the second call for the second entry is not shown here. The theorems of
this file stand at the format's hash; of its names other files call the four definitions and
`shapes_of_read`. Whether the dry runs hash is not looked at here. At a proof file the three lists R
are those of the dry runs at this call's own block. That one of these propositions holds of some
file, or of none, is not shown here. How hard a file is to make that meets one is not said. Nothing
on opening-form binding, no two openings of a commitment, correctness of extraction, what a root
fixes or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.CollidesAt
import OnBytes.Maker.Page.OwesOfPort
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Files

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-! ## The propositions -/

/-- **This key file shows a collision of the hash h**, the reading at h. -/
def KeyCollidesM (h : HId) (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray)
    (j : ℕ) : Prop :=
  ∃ (r : TailRead) (R : Rounds × Rounds × Rounds),
    (TwoPort.M.Key.readKey (m := Id) h k table file j).fromStart =
        (Except.ok r : Except String TailRead) ∧
      dryKey k r.key = some R ∧ ShapeOne (Three.Whole.of R.1 R.2.1 R.2.2) r ∧
      ShapeOneE (Three.Whole.of R.1 R.2.1 R.2.2) r ∧ SizesOne (Three.Whole.of R.1 R.2.1 R.2.2) r ∧
      CollidesInB h (Three.Whole.of R.1 R.2.1 R.2.2) r k.shared.given.cfg

/-- **This proof file shows a collision of the hash h**, the reading at h. -/
def ProofCollidesM (h : HId) (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) : Prop :=
  ∃ (r : TailRead) (R : Rounds × Rounds × Rounds),
    (TwoPort.M.Proof.readProof (m := Id) h c table copy request words block file).fromStart =
        (Except.ok r : Except String TailRead) ∧
      dryProof c r.key block = some R ∧ ShapeOne (Three.Whole.of R.1 R.2.1 R.2.2) r ∧
      ShapeOneE (Three.Whole.of R.1 R.2.1 R.2.2) r ∧ SizesOne (Three.Whole.of R.1 R.2.1 R.2.2) r ∧
      CollidesInB h (Three.Whole.of R.1 R.2.1 R.2.2) r c.shared.given.cfg

/-- The key file of these files shows a collision of the hash h. -/
def keyCollidesAtM (h : HId) (F : K.Files) (table : Params.TableName) : Prop :=
  ∃ (p : Model.Verify.Planned) (j : ℕ),
    Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      Key.readTable p.chains.key.oneTime.lin.fold.index p.chains.key.oneTime.given.cfg F.key =
        .ok (table, j) ∧
      KeyCollidesM h p.chains.key table F.key j

/-- The proof file of these files shows a collision of the hash h. -/
def proofCollidesAtM (h : HId) (F : K.Files) (further : Params.TableName) : Prop :=
  ∃ (p : Model.Verify.Planned) (so : Model.Head.StOwn) (cov : Model.Head.Covered)
    (links : Array Model.Stages.LinkH) (item : ByteArray),
    Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y) p.X.T =
        .ok so ∧
      Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov ∧
      Model.Verify.linksOf p.X cov = .ok links ∧
      Proof.requestItem F.pol F.KL F.request = some item ∧
      ProofCollidesM h p.chains.proof further F.entry item F.request (blockAt p links so.y) F.proof

/-! ## At the format's hash -/

/-- At the format's hash the reading of a key file is the program's. -/
theorem readKeyM_H (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray) (j : ℕ) :
    (TwoPort.M.Key.readKey (m := Id) Fmt.formatHash k table file j).fromStart =
      (Key.readKey k table file j).fromStart := by
  rw [← formatHashFastForm_eq_formatHash]
  exact TwoPort.M.AtPort.fromStart_port (TwoPort.M.AtPort.relP_readKey k table file j)

/-- At the format's hash the reading of a proof file is the program's. -/
theorem readProofM_H (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) :
    (TwoPort.M.Proof.readProof (m := Id) Fmt.formatHash c table copy request words block file).fromStart =
      (readProof c table copy request words block file).fromStart := by
  rw [← formatHashFastForm_eq_formatHash]
  exact TwoPort.M.AtPort.fromStart_port
    (TwoPort.M.AtPort.relP_readProof c table copy request words block file)

theorem KeyCollidesM.toB {k : Params.KeyChains} {table : Params.TableName} {file : ByteArray}
    {j : ℕ} (c : KeyCollidesM Fmt.formatHash k table file j) : KeyCollidesB Fmt.formatHash k table file j := by
  obtain ⟨r, R, hr, hR, -, -, -, hc⟩ := c
  exact ⟨r, R, (readKeyM_H k table file j).symm.trans hr, hR, hc⟩

theorem ProofCollidesM.toB {c : Params.ProofChains} {table : Params.TableName} {copy : ℕ}
    {request words : ByteArray} {block : Blk FirstEnd} {file : ByteArray}
    (e : ProofCollidesM Fmt.formatHash c table copy request words block file) :
    ProofCollidesB Fmt.formatHash c table copy request words block file := by
  obtain ⟨r, R, hr, hR, -, -, -, hc⟩ := e
  exact ⟨r, R, (readProofM_H c table copy request words block file).symm.trans hr, hR, hc⟩

/-! ## From the record of the program's reading -/

/-- The compared openings have one shape as read, at the record of a reading. -/
theorem shapes_of_read {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start}
    {file : ByteArray} {i : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead}
    {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds}
    {S₃ : Fmt.SpecX} {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand} (a sb : ℕ)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃))
    (hfit : Three.Whole.fits R₁ R₂ R₃ 2 = true)
    (hst : storedFit a (Three.Whole.of R₁ R₂ R₃) = true) (s₁ : g₁.plan.salt = sb)
    (s₂ : p.shared.given.plan.salt = sb) (s₃ : p.second.given.plan.salt = sb)
    (hB : oneShapeB (Three.Whole.of R₁ R₂ R₃) = true) :
    ShapeOne (Three.Whole.of R₁ R₂ R₃) r ∧ ShapeOneE (Three.Whole.of R₁ R₂ R₃) r := by
  obtain ⟨a₁, a₂, a₃⟩ := storedAt_of_fit hst
  have N := named_of_read T hS₁ b₁ R₃ hd
  have F : FileFits (Three.Whole.of R₁ R₂ R₃) sb a S₁ S₂ S₃ :=
    fileFits_of hfit hS₁ T.shared_spec T.second_spec (alike_shapes N) (alike_stored N) s₁ s₂ s₃ a₁
      a₂ a₃
  obtain ⟨-, t1, t2, -⟩ := tables_fit _ sb a S₁ S₂ S₃ F r file _ _ _ _ _ _ _ _ _ T.first_read
    T.shared_read T.second_read
  exact ⟨shapeOne_of_rowOK t1, shapeOneE_of hB t2⟩

/-- **A key file: from the record of the program's reading.** r₀: any value that the program's
reader returns at the file. -/
theorem keyCollidesM_of_record (k : Params.KeyChains) (table : Params.TableName)
    (file : ByteArray) (j : ℕ) (r₀ : TailRead)
    (h₀ : (Key.readKey k table file j).fromStart = .ok r₀)
    {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
    {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX} {R₃ : Rounds}
    (T : ThreeRead (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : k.oneTime.describe table R₁ = some S₁)
    (hd : Three.dry3 (Key.tailPublic k table) r.key (R₁, dry) = some (R₁, R₂, R₃)) (a : ℕ)
    (hfit : Three.Whole.fits R₁ R₂ R₃ 2 = true)
    (hst : storedFit a (Three.Whole.of R₁ R₂ R₃) = true)
    (s₂ : k.shared.given.plan.salt = k.oneTime.given.plan.salt)
    (s₃ : k.second.given.plan.salt = k.oneTime.given.plan.salt)
    (hB : oneShapeB (Three.Whole.of R₁ R₂ R₃) = true)
    (hZ : oneSaltB (Three.Whole.of R₁ R₂ R₃) = true)
    (c : CollidesInB Fmt.formatHash (Three.Whole.of R₁ R₂ R₃) r k.shared.given.cfg) :
    KeyCollidesM Fmt.formatHash k table file j := by
  have hS' : Params.describeWith k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R₁ 0 = some S₁ := hS₁
  obtain ⟨-, b₁⟩ := key_own k.oneTime T.first_dry
  obtain ⟨e₁, e₂⟩ := shapes_of_read a k.oneTime.given.plan.salt T hS' b₁ R₃ hd hfit hst rfl s₂ s₃ hB
  have e₃ := sizesOne_of_read a k.oneTime.given.plan.salt T hS' b₁ R₃ hd hfit hst rfl s₂ s₃ hB hZ
  obtain ⟨Q₁, d0, Z₁, _, _, _, _, _, _, _, hZ₁, T₀⟩ := threeRead_of_readKey k table file j r₀ h₀
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (T.first_dry.symm.trans T₀.first_dry))
  obtain rfl : S₁ = Z₁ := Option.some.inj (hS₁.symm.trans hZ₁)
  obtain rfl := threeRead_unique T T₀
  refine ⟨r, (R₁, R₂, R₃), (readKeyM_H k table file j).trans h₀, ?_, e₁, e₂, e₃, c⟩
  unfold dryKey
  rw [T.first_dry]
  exact hd

/-- **A proof file: from the record of the program's reading.** -/
theorem proofCollidesM_of_record (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (r₀ : TailRead)
    (h₀ : (readProof c table copy request words block file).fromStart = .ok r₀) {i : ℕ}
    (hi : readProofHead c.first.given.plan.field file = .ok (copy, i))
    {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
    {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX} {R₃ : Rounds}
    (T : ThreeRead (tailPublic c table) block (firstStart c.first) file i R₁ dry S₁ r seal1 seal2
      R₂ dry2 S₂ R₃' S₃)
    (hS₁ : c.first.describe table copy request words R₁ = some S₁) (b₁ : OwnBook dry.book)
    (hd : Three.dry3 (tailPublic c table) r.key (R₁, dry) = some (R₁, R₂, R₃)) (a : ℕ)
    (hfit : Three.Whole.fits R₁ R₂ R₃ 2 = true)
    (hst : storedFit a (Three.Whole.of R₁ R₂ R₃) = true)
    (s₂ : c.shared.given.plan.salt = c.first.given.plan.salt)
    (s₃ : c.second.given.plan.salt = c.first.given.plan.salt)
    (hB : oneShapeB (Three.Whole.of R₁ R₂ R₃) = true)
    (hZ : oneSaltB (Three.Whole.of R₁ R₂ R₃) = true)
    (e : CollidesInB Fmt.formatHash (Three.Whole.of R₁ R₂ R₃) r c.shared.given.cfg) :
    ProofCollidesM Fmt.formatHash c table copy request words block file := by
  have hS' : Params.describeWith c.first.given Params.labelFirst
      (Params.First.statement table copy request words) .inFile R₁ 0 = some S₁ := hS₁
  obtain ⟨e₁, e₂⟩ := shapes_of_read a c.first.given.plan.salt T hS' b₁ R₃ hd hfit hst rfl s₂ s₃ hB
  have e₃ := sizesOne_of_read a c.first.given.plan.salt T hS' b₁ R₃ hd hfit hst rfl s₂ s₃ hB hZ
  obtain ⟨i', Q₁, d0, Z₁, _, _, _, _, _, _, _, hi', hZ₁, T₀⟩ :=
    threeRead_of_readProof c table copy request words block file r₀ h₀
  obtain rfl : i = i' := by
    have := hi.symm.trans hi'
    injection this with q
    exact (Prod.mk.inj q).2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (T.first_dry.symm.trans T₀.first_dry))
  obtain rfl : S₁ = Z₁ := Option.some.inj (hS₁.symm.trans hZ₁)
  obtain rfl := threeRead_unique T T₀
  refine ⟨r, (R₁, R₂, R₃), (readProofM_H c table copy request words block file).trans h₀, ?_, e₁,
      e₂, e₃,
    e⟩
  unfold dryProof
  rw [T.first_dry]
  exact hd

/-! ## Where the program has said yes -/

/-- **A key file.** d: the fixed reading of F's key file; key₀: a fixed key at which the three
lists R were made. -/
theorem port_key_orM (F : K.Files) (id : String) (table further : Params.TableName)
    (h : K.PortYesAt F id table further) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) (d : ChainsData)
    (hd : readKeyChains F.pol F.lay F.KL F.key = some (table, d)) (key₀ : TableKey)
    (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R) (C : CK) (a : ℕ)
    (cfg : ByteArray) (hok : okAt a (some R) = true)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hsalts : saltsFit p.chains.key.oneTime.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) =
      true) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) p.chains.key.oneTime.given.plan.salt cfg
        d.r = true ∨ keyCollidesAtM Fmt.formatHash F table := by
  have ho := port_key_chains F id table further h
  have hg : KeyGood ⟨F.pol, F.lay, F.KL⟩ (table, d) := ⟨F, rfl, rfl, rfl, ho, hd⟩
  obtain ⟨p', j, d', real, real2, hp', ht, hd', hS, T, -, -⟩ := readKeyChains_of F table ho
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  obtain ⟨-, s₂, s₃⟩ := setting_keyGood hg hp
  have Tr := T.toRead
  have hR' : dryKey p.chains.key d.r.key = some R :=
    good_dry3 ⟨F.pol, F.lay, F.KL⟩ p hp key₀ h0 hf R hR (table, d) hg
  obtain ⟨q, j₀, r₀, hq, ht₀, h₀, -⟩ := port_key_reads h
  obtain rfl : p = q := Except.ok.inj (hp.symm.trans hq)
  obtain rfl : j = j₀ := by
    have := ht.symm.trans ht₀
    injection this with e
    exact (Prod.mk.inj e).2
  rcases chains_returns_or_collidesInB C a cfg p.chains.key table Tr hS s₂ s₃ R hR' hok hB hsalts
    with hr | hc
  · exact Or.inl hr
  · have hR2 := hR'
    unfold dryKey at hR2
    rw [Tr.first_dry] at hR2
    have hd3 : Three.dry3 (Key.tailPublic p.chains.key table) d.r.key (d.rounds1, d.dry) =
        some R := hR2
    obtain ⟨R₃, rfl⟩ := dry3_shape hd3 Tr.shared_dry
    exact Or.inr ⟨p, j, hp, ht, keyCollidesM_of_record p.chains.key table F.key j r₀ h₀ Tr hS hd3 a
      (okAt_parts hok).fits (okAt_parts hok).stored s₂.salt.symm s₃.salt.symm hB
      (oneSaltB_of_saltsFit hsalts) hc⟩

/-- **A proof file.** d: the fixed reading of F's proof file. -/
theorem port_proof_orM (F : K.Files) (id : String) (table further : Params.TableName)
    (h : K.PortYesAt F id table further) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) (so : Model.Head.StOwn)
    (hso : Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y)
      p.X.T = .ok so)
    (cov : Model.Head.Covered) (hcov : Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov)
    (links : Array Model.Stages.LinkH) (hl : Model.Verify.linksOf p.X cov = .ok links)
    (item : ByteArray) (hitem : Proof.requestItem F.pol F.KL F.request = some item)
    (d : ChainsData)
    (hd : readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof =
      some (further, d))
    (key₀ : TableKey) (h0 : key₀.item = 0)
    (hf : key₀.fits (tailPublic p.chains.proof noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds)
    (hR : dryProof p.chains.proof key₀ (blockAt p links so.y) = some R) (C : CK) (a : ℕ)
    (cfg : ByteArray) (hok : okAt a (some R) = true)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hsalts : saltsFit p.chains.proof.first.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) =
      true) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) p.chains.proof.first.given.plan.salt cfg
        d.r = true ∨ proofCollidesAtM Fmt.formatHash F further := by
  obtain ⟨i, real, real2, hh, hS, T, s₂, s₃, hR', -⟩ := port_proof_parts F id table further h p hp
    so hso cov hcov links hl item hitem d hd key₀ h0 hf R hR
  have Tr := T.toRead
  obtain ⟨o₁, b₁⟩ := proof_own_program p.X hl p.built.links p.chains.proof.first
    p.X.layers.wsLay (Model.ofNat so.y) Tr.first_dry
  obtain ⟨q, so₂, cov₂, item₂, links₂, r₀, hq, g1, g2, g3, g4, h₀, -⟩ := port_proof_reads h
  obtain rfl : p = q := Except.ok.inj (hp.symm.trans hq)
  obtain rfl : so = so₂ := Except.ok.inj (hso.symm.trans g1)
  obtain rfl : cov = cov₂ := Except.ok.inj (hcov.symm.trans g2)
  obtain rfl : item = item₂ := Option.some.inj (hitem.symm.trans g3)
  obtain rfl : links = links₂ := Except.ok.inj (hl.symm.trans g4)
  rcases chainsP_returns_or_collidesInB C a cfg p.chains.proof further F.entry item F.request
    (blockAt p links so.y) Tr hS o₁ b₁ s₂ s₃ R hR' hok hB hsalts with hr | hc
  · exact Or.inl hr
  · have hR2 := hR'
    unfold dryProof at hR2
    rw [Tr.first_dry] at hR2
    have hd3 : Three.dry3 (tailPublic p.chains.proof further) d.r.key (d.rounds1, d.dry) =
        some R := hR2
    obtain ⟨R₃, rfl⟩ := dry3_shape hd3 Tr.shared_dry
    exact Or.inr ⟨p, so, cov, links, item, hp, hso, hcov, hl, hitem,
      proofCollidesM_of_record p.chains.proof further F.entry item F.request (blockAt p links so.y)
          F.proof
        r₀ h₀ hh Tr hS b₁ hd3 a (okAt_parts hok).fits (okAt_parts hok).stored s₂.salt.symm
        s₃.salt.symm hB (oneSaltB_of_saltsFit hsalts) hc⟩

end OnBytes.Maker.Page
