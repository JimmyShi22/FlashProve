-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/TypedOracleCompiler/Joined/K/LeftOfChains.lean: from all that the exit code 0 says of a key file or a proof
file to the value yes of the compiled verifier of a file with three joined chains, under fixed
oracle functions: the statement, with what is left as named hypotheses.

`Left` (OnBytes/TypedOracleCompiler/Joined/K/Left.lean) lists what is left to show for a yes at a proof string that
is assembled from three chains as read. Here that string is assembled from the data of one fixed
reading of the file (`TieK.ChainsData`, OnBytes/TieK/ReadThree.lean). What belongs to no chain is
written out: the seal, the binding root, the slot, the path and the string behind the seal are the
reading's own values. The rest of the typing stands as letters (`TypingA`).

Main names:
  `TypingA`: the letters, at one public input: the oracle functions g, the file's rounds, the file
    as it is written into the typed queries, and how a place and a salt are laid behind the seal;
    from the table and the stored copy's number: the outer roots and the instance; from the data:
    the first chain's salt, the three chains as read, the openings of the external strings. All of
    it, g too, may hang on the public files: the theorems at the end take a typing for a call's
    input.
  `TypingA.prf`: the assembled proof string.
  `LeftHoles`: the 17 named hypotheses: `laws`, `wire`, `depth`, `node`, `leaf`, `fits`, `saltLen`,
    and the ten fields of `AfterRuns`, each asked at whatever values the three chains
    have under g (`TypingA.RunsTo`).
  `yes_of_leftHoles`: they give the yes. Three fields of `Left` are proved here from the reading's
    own facts (`TieK.SlotFacts`; `TieK.seal_size`): `slotLt`, `pathLen`, `climb`.
  `key_det`, `proof_det`: the same from `K.PortYesAt`, at a key file and at a proof file, for a
    typing that is a function of the public input: these are the statements to quote. The
    hypotheses are asked at the public inputs at which a good reading exists.
  `key_det_at`, `proof_det_at`: the step beneath them, at one typing and one call. There the typing
    stands behind the files in the statement, so it could be chosen after them.
Limits: every field of `LeftHoles` is a hypothesis. No typing is given here. By its type a typing
makes the file's rounds without the reading's data, so from the public input alone: that the
program's rounds do not hang on a table's values is thereby asked, not shown. `sealAt`, the four
walks and, through the verifier messages, the openings and `accept` rest on how g answers the
chains' and the trees' queries: no hypothesis here names that coding but for the request tree's
(`node`, `leaf`). A proof string has one opening at a position; where a file opens one position at
two lists the program ties the two columns by one leaf digest: `accept` and the walks can hold at
every good reading only if no accepted file has two different columns under one leaf digest: that is
asked within them and named nowhere. The theorem is worth what its typing is worth: at a decision
that says yes to everything `accept` is met. Nothing on soundness. The program does not import this
file.
-/
import OnBytes.TypedOracleCompiler.Joined.K.Left
import OnBytes.TypedOracleCompiler.Joined.K.Request
import OnBytes.TieK.CutsOfChains
import OnBytes.TieK.SealSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace TypedOracleCompiler.Joined.K
open OnBytes TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open _root_.Run (bytesToDig)
open OnBytes.TieK (ChainsData SlotFacts KeyPub ProofPub KeyGood ProofGood)

/-- What one fixed reading of a file gives: a table, and the three chains' data. -/
abbrev Dat : Type := Params.TableName × ChainsData

/-- The letters of a typing at an assembled proof string, at one public input. -/
structure TypingA where
  I : Type
  X : Type
  L : BatchProtocolWithLeafBody I X
  W : QueryLayout 256 L
  Y : Type
  E : ExtSpec
  /-- the two lengths of salts -/
  sMT : ℕ
  sFS : ℕ
  /-- the oracle functions -/
  g : Fam (typedOracleFamily 256 W.K L)
  /-- the file's rounds -/
  G : Chains
  /-- the file as it is written into the typed queries -/
  F : FileW W G Y E
  /-- how a place and a salt are laid behind the seal in the binding tree's leaf -/
  rsOf : ℕ → ByteArray → Bits
  /-- the outer roots and the instance, from the table and the number of the stored copy alone; the
  first chain's salt -/
  cms : Params.TableName → ℕ → List (Dig 256)
  x : Params.TableName → ℕ → Y
  salt : Dat → Bits
  /-- the three chains as read -/
  k₁ : Dat → ChainStr 256 G.c₁
  k₂ : Dat → ChainStr 256 G.c₂
  k₃ : Dat → ChainStr 256 G.c₃
  /-- the openings of the external strings -/
  ext : Dat → E.Pos → Option (Opening 256 E.Sym)

namespace TypingA
variable (T : TypingA)

/-- The outer roots at a reading: from its table and its number of the stored copy. -/
@[reducible] def cmsAt (d : Dat) : List (Dig 256) := T.cms d.1 d.2.copy

/-- The instance at a reading: from its table and its number of the stored copy. -/
@[reducible] def xAt (d : Dat) : T.Y := T.x d.1 d.2.copy

/-- The string behind the seal in the binding tree's leaf. -/
def rsalt (d : Dat) : Bits := T.rsOf d.2.r.place.place d.2.salt

/-- The proof string: the three chains as read, and the reading's own seal's tree: the binding root,
the place, the siblings, the string behind the seal. -/
def prf (d : Dat) : T.F.Prf :=
  T.F.assemble (T.salt d) (T.k₁ d) (T.k₂ d) (T.k₃ d) (T.ext d)
    (bytesToDig d.2.r.place.root) d.2.r.place.place (d.2.path.map bytesToDig) (T.rsalt d)

/-- Under g the three chains have the values a, b, e at the proof string. -/
def RunsTo (d : Dat) (a : Out 256 T.G.c₁) (b : Out 256 T.G.c₂) (e : Out 256 T.G.c₃) : Prop :=
  (run₁ T.F.t T.F.D T.F.wq T.F.embP T.F.xin (T.cmsAt d) (T.xAt d) (T.prf d)).det T.g = some a ∧
  (run₂ T.F.t T.F.D T.F.wq T.F.embP T.F.xin (T.cmsAt d) (T.xAt d) (T.prf d) a).det T.g = some b ∧
  (run₃ T.F.t T.F.D T.F.wq T.F.embP T.F.xin (T.cmsAt d) (T.xAt d) (T.prf d) a b).det T.g = some e

end TypingA

/-- **What is left, as named hypotheses**, at one public input. Good: the readings that are spoken
of. shape, cfg: the binding tree's shape and the digest under which it is hashed. -/
structure LeftHoles (T : TypingA) (Good : Dat → Prop) (shape : Params.LinBindingShape)
    (cfg : ByteArray) : Prop where
  /-- the joining round is a shared round, and its annotation is coherent -/
  laws : T.G.Laws
  /-- the laws of the wire record -/
  wire : T.F.wq.OKG
  /-- the depth of the request tree at the file's tag is the binding tree's -/
  depth : T.W.dReq T.F.t = shape.logLeaves
  /-- g answers the request tree's node oracle with the program's hash of a vertex -/
  node : NodeCoded T.g cfg
  /-- g answers the request tree's leaf oracle with the program's hash of a leaf -/
  leaf : LeafCoded T.g shape.logLeaves cfg shape.saltBytes T.rsOf
  /-- few trees a component, and as many roots read for each chain as its rounds have trees -/
  fits : ∀ d, Good d → Fits T.F (T.k₁ d) (T.k₂ d) (T.k₃ d)
  /-- the first chain's salt has sFS bits -/
  saltLen : ∀ d, Good d → (T.salt d).length = T.sFS
  /-- g answers the query to g that holds the chaining value in which the first chain ends with that
  chain's seal as read -/
  sealAt : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e → ∀ ρ₁, a.2.2 = .loc ρ₁ →
    T.g (OracleName.g T.F.t) (qSeal₁ T.F.t T.F.D T.F.embP (T.prf d) ρ₁ (rtJ T.F.D T.F.wq (T.prf d) a)) =
      bytesToDig d.2.seal1
  /-- the openings at chain 1's rounds -/
  opened₁ : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e →
    Opened T.sMT T.G.c₁ T.G.A₁ (wire₁ T.F.wq) a.2.1 (rd₁ T.F.D T.F.wq (T.xAt d) (T.prf d) a b e)
      (op₁ T.F.D (T.prf d))
  /-- at chain 2's rounds -/
  opened₂ : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e →
    Opened T.sMT T.G.c₂ T.G.A₂ (wire₂ T.F.wq) b.2.1 (rd₂ T.F.D T.F.wq (T.xAt d) (T.prf d) a b e)
      (op₂ T.F.D (T.prf d))
  /-- at chain 3's rounds -/
  opened₃ : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e →
    Opened T.sMT T.G.c₃ T.G.A₃ (wire₃ T.F.wq) e.2.1 (rd₃ T.F.D T.F.wq (T.xAt d) (T.prf d) a b e)
      (op₃ T.F.D (T.prf d))
  /-- the openings of the external strings -/
  openedE : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e →
    OpenedE T.sMT T.F.wq.maxDepth T.F.wq.ext (readE T.F.D T.F.wq (T.xAt d) (glue a b e).1)
      (T.prf d).ext
  /-- the walk of each forest of chain 1's rounds ends, under g, in its trees' roots -/
  walk₁ : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e → ∀ F₁,
    forestsB T.G.c₁ T.G.A₁ (wire₁ T.F.wq) (symb₁ T.F.embS) a.2.1
      (rd₁ T.F.D T.F.wq (T.xAt d) (T.prf d) a b e) (op₁ T.F.D (T.prf d)) = some F₁ →
    ∀ R ∈ F₁, walkP T.g R R.reads = true
  /-- of chain 2's rounds -/
  walk₂ : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e → ∀ F₂,
    forestsB T.G.c₂ T.G.A₂ (wire₂ T.F.wq) (symb₂ T.F.embS) b.2.1
      (rd₂ T.F.D T.F.wq (T.xAt d) (T.prf d) a b e) (op₂ T.F.D (T.prf d)) = some F₂ →
    ∀ R ∈ F₂, walkP T.g R R.reads = true
  /-- of chain 3's rounds -/
  walk₃ : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e → ∀ F₃,
    forestsB T.G.c₃ T.G.A₃ (wire₃ T.F.wq) (symb₃ T.F.embS) e.2.1
      (rd₃ T.F.D T.F.wq (T.xAt d) (T.prf d) a b e) (op₃ T.F.D (T.prf d)) = some F₃ →
    ∀ R ∈ F₃, walkP T.g R R.reads = true
  /-- of the external strings -/
  walkE : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e → ∀ Fe,
    forestExt T.F.wq.ext T.F.embE (T.cmsAt d) (readE T.F.D T.F.wq (T.xAt d) (glue a b e).1)
      (T.prf d).ext = some Fe →
    ∀ R ∈ Fe, walkP T.g R R.reads = true
  /-- over the whole: the decision, at the three chains' transcripts in a row -/
  accept : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e →
    T.F.D.accept (T.xAt d) (T.F.wq.ext.build fun p => ((T.prf d).ext p).map Opening.sym)
      (Tr.app (s := T.G.c₁) (t := T.G.c₂ ++ T.G.c₃) (tr₁ T.F.D T.F.wq (T.prf d) a)
        (Tr.app (s := T.G.c₂) (t := T.G.c₃) (tr₂ T.F.D T.F.wq (T.prf d) b)
          (tr₃ T.F.D T.F.wq (T.prf d) e))) = true

/-- **The named hypotheses give the value yes of the compiled verifier of the file under g**, at
every good reading whose salt and siblings have the facts of the program's own reading of the
place and whose first seal has 32 bytes. -/
theorem yes_of_leftHoles (T : TypingA) (Good : Dat → Prop) (shape : Params.LinBindingShape)
    (cfg : ByteArray) (H : LeftHoles T Good shape cfg) (d : Dat) (hg : Good d) (b : ByteArray)
    (i : ℕ) (sf : SlotFacts shape cfg d.2.seal1 b i d.2.r.place d.2.salt d.2.path)
    (hseal : d.2.seal1.size = 32) :
    (T.F.verify T.sMT T.sFS (T.cmsAt d) (T.xAt d) (T.prf d)).det T.g = true := by
  obtain ⟨w, i1, -, hsalt, hpath⟩ := sf.parts
  have hclimb : climbP (rnodeAt T.g) (d.2.path.map bytesToDig) d.2.r.place.place
      (T.g OracleName.rleaf (List.ofFn (bytesToDig d.2.seal1) ++ T.rsalt d)) =
        bytesToDig d.2.r.place.root := by
    unfold TypingA.rsalt
    rw [H.leaf d.2.r.place.place d.2.seal1 d.2.salt sf.placeLt hseal
      (size_of_slice hsalt), sf.root]
    exact climbP_rootOf H.node d.2.path _ _ (size_bindLeaf _ _ _ _ _)
      (size_of_pathAt b _ _ d.2.path hpath)
  exact yes_of_left (sl := bytesToDig d.2.seal1)
    { laws := H.laws
      wire := H.wire
      fits := H.fits d hg
      saltLen := H.saltLen d hg
      slotLt := by rw [H.depth]; exact sf.placeLt
      pathLen := by rw [H.depth, List.length_map]; exact sf.pathLen
      climb := hclimb
      after := fun a b e h₁ h₂ h₃ =>
        { sealAt := H.sealAt d hg a b e ⟨h₁, h₂, h₃⟩
          opened₁ := H.opened₁ d hg a b e ⟨h₁, h₂, h₃⟩
          opened₂ := H.opened₂ d hg a b e ⟨h₁, h₂, h₃⟩
          opened₃ := H.opened₃ d hg a b e ⟨h₁, h₂, h₃⟩
          openedE := H.openedE d hg a b e ⟨h₁, h₂, h₃⟩
          walk₁ := H.walk₁ d hg a b e ⟨h₁, h₂, h₃⟩
          walk₂ := H.walk₂ d hg a b e ⟨h₁, h₂, h₃⟩
          walk₃ := H.walk₃ d hg a b e ⟨h₁, h₂, h₃⟩
          walkE := H.walkE d hg a b e ⟨h₁, h₂, h₃⟩
          accept := H.accept d hg a b e ⟨h₁, h₂, h₃⟩ } }

/-! ## The two kinds of file -/

/-- The binding tree's shape at a key file, from the three public files. -/
def keyShape (u : KeyPub) : Params.LinBindingShape :=
  match Model.Verify.planned u.pol u.KL (some u.lay) with
  | .ok p => p.chains.key.oneTime.binding
  | .error _ => default

/-- The digest under which a key file's binding tree is hashed. -/
def keyCfg (u : KeyPub) : ByteArray :=
  match Model.Verify.planned u.pol u.KL (some u.lay) with
  | .ok p => p.chains.key.shared.given.cfg
  | .error _ => ByteArray.empty

/-- **A key file, at a typing for its public files.** Where the program says yes, the fixed reading
returns data at which, under the named hypotheses at these public files, the compiled verifier of
the key file has the value yes under g. -/
theorem key_det_at (T : TypingA) (F : OnBytes.K.Files)
    (H : LeftHoles T (KeyGood ⟨F.pol, F.lay, F.KL⟩) (keyShape ⟨F.pol, F.lay, F.KL⟩)
      (keyCfg ⟨F.pol, F.lay, F.KL⟩))
    (id : String) (table further : Params.TableName)
    (h : OnBytes.K.PortYesAt F id table further) :
    ∃ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) ∧ d.copy = 0 ∧
      (T.F.verify T.sMT T.sFS (T.cmsAt (table, d)) (T.xAt (table, d)) (T.prf (table, d))).det T.g =
        true := by
  have ho := TieK.port_key_chains F id table further h
  obtain ⟨p, _, d, _, _, hp, -, hd, -, h3, sf, hc⟩ := TieK.readKeyChains_of F table ho
  have e1 : keyShape ⟨F.pol, F.lay, F.KL⟩ = p.chains.key.oneTime.binding := by
    unfold keyShape
    rw [hp]
  have e2 : keyCfg ⟨F.pol, F.lay, F.KL⟩ = p.chains.key.shared.given.cfg := by
    unfold keyCfg
    rw [hp]
  refine ⟨d, hd, hc, yes_of_leftHoles T (KeyGood ⟨F.pol, F.lay, F.KL⟩) _ _ H (table, d)
    ⟨F, rfl, rfl, rfl, ho, hd⟩ F.key d.r.first.next ?_ h3.seal1_size⟩
  rw [e1, e2]
  exact sf

/-- **A key file, at a typing that is a function of the public input.** -/
theorem key_det (T : KeyPub → TypingA)
    (H : ∀ u, (∃ d, KeyGood u d) → LeftHoles (T u) (KeyGood u) (keyShape u) (keyCfg u))
    (F : OnBytes.K.Files)
    (id : String) (table further : Params.TableName)
    (h : OnBytes.K.PortYesAt F id table further) :
    ∃ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) ∧ d.copy = 0 ∧
      ((T ⟨F.pol, F.lay, F.KL⟩).F.verify (T ⟨F.pol, F.lay, F.KL⟩).sMT (T ⟨F.pol, F.lay, F.KL⟩).sFS
        ((T ⟨F.pol, F.lay, F.KL⟩).cmsAt (table, d)) ((T ⟨F.pol, F.lay, F.KL⟩).xAt (table, d))
        ((T ⟨F.pol, F.lay, F.KL⟩).prf (table, d))).det (T ⟨F.pol, F.lay, F.KL⟩).g = true := by
  have ho := TieK.port_key_chains F id table further h
  obtain ⟨_, _, d, _, _, -, -, hd, -⟩ := TieK.readKeyChains_of F table ho
  exact key_det_at (T ⟨F.pol, F.lay, F.KL⟩) F
    (H ⟨F.pol, F.lay, F.KL⟩ ⟨(table, d), F, rfl, rfl, rfl, ho, hd⟩) id table further h

/-- The binding tree's shape at a proof file, from the three public files. -/
def proofShape (u : ProofPub) : Params.LinBindingShape :=
  match Model.Verify.planned u.pol u.KL (some u.lay) with
  | .ok p => p.chains.proof.first.binding
  | .error _ => default

/-- The digest under which a proof file's binding tree is hashed. -/
def proofCfg (u : ProofPub) : ByteArray :=
  match Model.Verify.planned u.pol u.KL (some u.lay) with
  | .ok p => p.chains.proof.shared.given.cfg
  | .error _ => ByteArray.empty

/-- **A proof file, at a typing for its public input.** Where the program says yes, the fixed
reading returns data at which, under the named hypotheses at the three public files, the request and
the reply, the compiled verifier of the proof file has the value yes under g. -/
theorem proof_det_at (T : TypingA) (F : OnBytes.K.Files)
    (H : LeftHoles T (ProofGood ⟨F.pol, F.lay, F.KL, F.request, F.y⟩)
      (proofShape ⟨F.pol, F.lay, F.KL, F.request, F.y⟩)
      (proofCfg ⟨F.pol, F.lay, F.KL, F.request, F.y⟩))
    (id : String) (table further : Params.TableName)
    (h : OnBytes.K.PortYesAt F id table further) :
    ∃ d, TieK.readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof =
        some (further, d) ∧ d.copy = F.entry ∧
      (T.F.verify T.sMT T.sFS (T.cmsAt (further, d)) (T.xAt (further, d)) (T.prf (further, d))).det
        T.g = true := by
  have ho := TieK.port_proof_chains F id table further h
  have he := TieK.port_entry F id table further h
  obtain ⟨p, _, _, _, _, _, d, _, _, hp, -, -, -, -, -, hd, -, h3, sf, hc⟩ :=
    TieK.readProofChains_of F table further he ho
  have e1 : proofShape ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ = p.chains.proof.first.binding := by
    unfold proofShape
    rw [hp]
  have e2 : proofCfg ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ = p.chains.proof.shared.given.cfg := by
    unfold proofCfg
    rw [hp]
  refine ⟨d, hd, hc, yes_of_leftHoles T (ProofGood ⟨F.pol, F.lay, F.KL, F.request, F.y⟩) _ _ H
    (further, d) ⟨F, table, rfl, rfl, rfl, rfl, rfl, he, ho, hd⟩ F.proof d.r.first.next ?_
    h3.seal1_size⟩
  rw [e1, e2]
  exact sf

/-- **A proof file, at a typing that is a function of the public input.** -/
theorem proof_det (T : ProofPub → TypingA)
    (H : ∀ u, (∃ d, ProofGood u d) → LeftHoles (T u) (ProofGood u) (proofShape u) (proofCfg u))
    (F : OnBytes.K.Files) (id : String) (table further : Params.TableName)
    (h : OnBytes.K.PortYesAt F id table further) :
    ∃ d, TieK.readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof =
        some (further, d) ∧ d.copy = F.entry ∧
      ((T ⟨F.pol, F.lay, F.KL, F.request, F.y⟩).F.verify
        (T ⟨F.pol, F.lay, F.KL, F.request, F.y⟩).sMT (T ⟨F.pol, F.lay, F.KL, F.request, F.y⟩).sFS
        ((T ⟨F.pol, F.lay, F.KL, F.request, F.y⟩).cmsAt (further, d))
        ((T ⟨F.pol, F.lay, F.KL, F.request, F.y⟩).xAt (further, d))
        ((T ⟨F.pol, F.lay, F.KL, F.request, F.y⟩).prf (further, d))).det
          (T ⟨F.pol, F.lay, F.KL, F.request, F.y⟩).g = true := by
  have ho := TieK.port_proof_chains F id table further h
  have he := TieK.port_entry F id table further h
  obtain ⟨_, _, _, _, _, _, d, _, _, -, -, -, -, -, -, hd, -⟩ :=
    TieK.readProofChains_of F table further he ho
  exact proof_det_at (T ⟨F.pol, F.lay, F.KL, F.request, F.y⟩) F
    (H ⟨F.pol, F.lay, F.KL, F.request, F.y⟩
      ⟨(further, d), F, table, rfl, rfl, rfl, rfl, rfl, he, ho, hd⟩) id table further h

end TypedOracleCompiler.Joined.K

#print axioms TypedOracleCompiler.Joined.K.key_det
#print axioms TypedOracleCompiler.Joined.K.proof_det
