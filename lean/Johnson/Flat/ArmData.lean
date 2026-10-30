-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ArmData.lean: values for the letters of data that the statements on the entry's arm
carry, at the object whose link is `linkSibFull` | `linkSibSmall` and whose other parts are the
three files' (`restSibFull` | `restSibSmall`, Johnson/Flat/RestSib.lean, at `threeProtocolsFromDryRunAtFullSize` |
`threeProtocolsFromDryRunAtSmallSize`, OnBytes/Flat/FilesAt.lean).

The bound on the entry's arm (Johnson/Flat/ArmSibMaker.lean) and the tie of the entry file to it
are said for every wire record of the key file's protocol and of the proof file's, every four maps
between symbols and leaves' bodies, every code of a record, and so on. Of these letters nothing is
asked, BUT OF ONE: the tie of the entry file asks that `salt` is the description's length of salts.
A statement "for every wT" says nothing if the type of wT has no member. Here each of these types
is shown to have one, by writing one; and `salt` is no stand-in: at the two sizes it is the length
of salts of the ground's own parameters. Two more are read by the tie's side, though nothing is
asked of them: the arm's run reads the test `dS` of equality of seeds (every such test gives the
same verdict), and the coding of typed queries reads the seed d₁ (the tie holds at every d₁). At the
two sizes both are written terms: the decision that Lean finds for the type of seeds, and the seed
of zeros with the element 1.

The values are STAND-INS, SO THAT THE TYPES ARE NOT EMPTY: THE PLAINEST, NOT THE FILES' OWN. A
round's wire record here names no tree, has no test of work, and makes of the hash blocks one
arbitrary verifier's message (`Classical.arbitrary`). The maps write every symbol as the empty
string and read nothing back. They are not how the programs hash a key file or a proof file, and no
compiled verifier of these two files should be read at them. The entry's arm runs the two seeds'
tests and the link alone: it does not run the key file's or the proof file's verifier.

Main definitions.
 `plainRB`, `plainSB`, `plainQB`   the plainest wire record of a round, of a list of rounds and of a
                  protocol, from the fact that every round's oracle is a string
                  (`Shape.IsPoint`) and a wire record of the external strings.
 `pointWhole`     every round's oracle of a whole file's protocol is a string, as data.
 `ArmData T aT K`  the record of the letters: wT, wB, z, three numbers, four maps, `code`, `num`,
                  `dS`, d₁.
 `ArmData.plain`  its plainest value, at any T with strings for oracles, a given length of salts, a
                  given test of equality of seeds and a given seed.
 `armDataFull`, `armDataSmall`   that at the two sizes, at any number K of blocks.

Not claimed here: soundness or hiding; any law of a wire record; that the programs are wired so.
The claims A with their type X of instances (so a serialiser of X too), the rest R, what the makers
of the two big files take (G), the honest provers P and hL stay parameters. For proofs only; no
program imports this file.


-/
import Johnson.Flat.RestSib
import OnBytes.Flat.FilesAt
import Johnson.Flat.WireAt
import OnBytes.Maker.WholeLocal
import OnBytes.TypedOracleCompiler.Iop.BatchWire
import Johnson.TypedOracleCompiler.RecCompile.Cms
import OnBytes.Tie.EntryGrounds

set_option autoImplicit false

noncomputable section

namespace OnBytes.Flat

open Hiop Cb Cb.Ood OnBytes.Slice OnBytes.Maker TypedOracleCompiler.Iop
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.RunA (RestR LrG)
open OnBytes.Tie (recordGround smallRecordGround)
open VerifiableInference.OnPublicFiles (dataKFull dataPFull dataKSmall dataPSmall)
open _root_.Run (ckP)
open _root_.Run.PQ (SgX CK)

/-! ## The plainest wire records -/

/-- The plainest wire record of a round whose oracle is a string: no tree, no test of work, one
arbitrary verifier's message. -/
def plainRB (lam K : ℕ) (r : Round) (a : RAnn r) (pt : r.IsPoint) : WireRB lam K r a where
  pt := pt
  depth0 := []
  depthJ := []
  tree := fun _ => 0
  place := fun _ => 0
  posAt0 := fun _ _ => none
  posAtJ := fun _ _ => none
  chal := fun _ => Classical.arbitrary r.Chal

/-- The same for a list of rounds. -/
def plainSB (lam K : ℕ) : (s : Shape) → (A : RoundSplits s) → s.IsPoint → RoundsQueryLayout lam K s A
  | [], _, _ => ()
  | r :: s, (a, A), (p, ps) => (plainRB lam K r a p, plainSB lam K s A ps)

/-- The same for a protocol, at a wire record of the external strings. -/
def plainQB (lam K : ℕ) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (pt : Q.loc.shape.IsPoint)
    (ext : WireE E) : ProtocolQueryLayout lam K Q :=
  ⟨plainSB lam K Q.loc.shape Q.ann pt, ext, Classical.decEq _, 0, 0⟩

/-- Every round's oracle of a whole file's protocol is a string. -/
def pointWhole (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) :
    (chainsOf C D tF tJ t3).sh.IsPoint :=
  (pointPlain TF tF, pointApp (pointsT C D.ds₁)
    (pointPlain TJ tJ, pointApp (pointsT C D.ds₂) (pointPlain T3 t3, pointsT C D.ds₃)))

/-! ## The record of the letters -/

section
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed] {a : ℕ}
  {Q : InteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX)}

/-- The letters of data of the statements on the entry's arm, at an object `LrG T`, marks aT on the
key file's rounds and K + 1 blocks. -/
structure ArmData (T : RestR I X RI Seed Ans a Q) (aT : RoundSplits T.test.shape) (K : ℕ) where
  /-- the wire record of the key file's protocol -/
  wT : ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT)
  /-- the wire record of the proof file's protocol -/
  wB : ProtocolQueryLayout 256 (K + 1) T.bat
  /-- the symbol of a stored table where nothing is fixed -/
  z : SgX
  /-- the depths of the request trees of the session and of the key's test -/
  depthReq : ℕ
  depthReqT : ℕ
  /-- the length of salts, in bytes -/
  salt : ℕ
  /-- how a symbol of the key file's oracles is written into a leaf's body, and read back -/
  embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool
  prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p)
  /-- the same for the proof file's -/
  embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool
  prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p)
  /-- a record as digests -/
  code : (LrG T).Rec → List (Dig 256)
  /-- do a session's plain parts hold this number of a stored copy? -/
  num : ℕ → Plains T.bat.loc.shape → Bool
  /-- are two seeds equal? -/
  dS : DecidableEq Seed
  /-- a seed that stands where a description has to name one -/
  d₁ : Seed

/-- **Its plainest value**, where every round's oracle of the key file's and of the proof file's
protocol is a string. -/
def ArmData.plain (T : RestR I X RI Seed Ans a Q) (aT : RoundSplits T.test.shape) (K salt : ℕ)
    (dS : DecidableEq Seed) (d₁ : Seed) (ptT : T.test.shape.IsPoint)
    (ptB : T.bat.loc.shape.IsPoint) : ArmData T aT K where
  wT := plainQB 256 (K + 1) (batTC (LrG T) aT) ptT (WireE.one (2 ^ a) SgX (0, []))
  wB := plainQB 256 (K + 1) T.bat ptB (WireE.one (2 ^ a) SgX (0, []))
  z := (0, [])
  depthReq := 0
  depthReqT := 0
  salt := salt
  embT := fun _ _ => []
  prjT := fun _ _ => none
  embB := fun _ _ => []
  prjB := fun _ _ => none
  code := fun _ => []
  num := fun _ _ => true
  dS := dS
  d₁ := d₁

/-- So the two types of wire records have a member. -/
theorem armData_nonempty (T : RestR I X RI Seed Ans a Q) (aT : RoundSplits T.test.shape) (K : ℕ)
    (ptT : T.test.shape.IsPoint) (ptB : T.bat.loc.shape.IsPoint) : Nonempty (ArmData T aT K) :=
  ⟨ArmData.plain T aT K 0 (Classical.decEq _) (Classical.arbitrary Seed) ptT ptB⟩

end

/-! ## The full size -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (G : FilesParameters X RecFull) (P : (threeProtocolsFromDryRunAtFullSize A R G).Provers)
  (hL : Honest linkSibFull ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ))))

/-- Every round's oracle of the key file's protocol is a string. -/
def pointKeyFull : (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL).test.shape.IsPoint :=
  pointWhole (ckP .two) (dataKFull G) (front₀ G.rec₀) (join₀ G.rec₀) ByteArray.empty

/-- Every round's oracle of the proof file's protocol is a string. -/
def pointProofFull : (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL).bat.loc.shape.IsPoint :=
  pointWhole (ckP .two) (dataPFull G) (front₀ G.z₀.2) (join₀ G.z₀.2) ByteArray.empty

/-- **The data of the entry's arm at this size**, at any number K of blocks: the plainest values,
with the ground's own length of salts. -/
def armDataFull (K : ℕ) :
    ArmData (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL) (threeProtocolsFromDryRunAtFullSize A R G).annT K :=
  ArmData.plain _ _ K recordGround.q.given.plan.salt inferInstance
    (fun _ => (fun _ => 0, ⟨1, one_ne_zero⟩)) (pointKeyFull A R G P hL) (pointProofFull A R G P hL)

/-- Its length of salts is that of the ground's parameters. -/
theorem armDataFull_salt (K : ℕ) :
    (armDataFull A R G P hL K).salt = recordGround.q.given.plan.salt := rfl

end

/-! ## The small size -/

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (R : (srS.toDecR srZ 524285).RelationsAndEncoding A)
  (G : FilesParameters X RecSmall) (P : (threeProtocolsFromDryRunAtSmallSize A R G).Provers)
  (hL : Honest linkSibSmall ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ))))

/-- Every round's oracle of the key file's protocol is a string. -/
def pointKeySmall : (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL).test.shape.IsPoint :=
  pointWhole (ckP .two) (dataKSmall G) (front₀ G.rec₀) (join₀ G.rec₀) ByteArray.empty

/-- Every round's oracle of the proof file's protocol is a string. -/
def pointProofSmall : (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL).bat.loc.shape.IsPoint :=
  pointWhole (ckP .two) (dataPSmall G) (front₀ G.z₀.2) (join₀ G.z₀.2) ByteArray.empty

/-- **The data of the entry's arm at this size**, at any number K of blocks: the plainest values,
with the ground's own length of salts. -/
def armDataSmall (K : ℕ) :
    ArmData (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL) (threeProtocolsFromDryRunAtSmallSize A R G).annT K :=
  ArmData.plain _ _ K smallRecordGround.q.given.plan.salt inferInstance
    (fun _ => (fun _ => 0, ⟨1, one_ne_zero⟩)) (pointKeySmall A R G P hL)
    (pointProofSmall A R G P hL)

/-- Its length of salts is that of the ground's parameters. -/
theorem armDataSmall_salt (K : ℕ) :
    (armDataSmall A R G P hL K).salt = smallRecordGround.q.given.plan.salt := rfl

end

end OnBytes.Flat
