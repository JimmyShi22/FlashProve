-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/FilesAt.lean: the three files' protocols at the two sizes of the default setting. The
key file's and the proof file's are made by the makers of OnBytes/Maker/ from blocks of the verifier
program's type, at letters (see "Limits"); the entry file's is the written link.

Definitions, and what is proved of them. `threeProtocolsFromDryRunAtFullSize A R G`, `threeProtocolsFromDryRunAtSmallSize A R G : Files (DecR.configurationOfStoredTable A
R)` (OnBytes/Flat/Frame.lean; OnBytes/Slice/ConfOf.lean). The entry file's protocol is `linkSibFull`
| `linkSibSmall` (OnBytes/Flat/LinkSibAt.lean): closed terms: the written link of the compiler under
OnBytes/TypedOracleCompiler/, with its own marks (`Run.Twin.allLo`). Its decision is the verifier
program's `linkVerify` at the keys of the two records (`decFullX_recX`; `decRun_full`,
OnBytes/Flat/LinkSibRun.lean); its rounds are written numbers, equal to the lists `frRds` | `srRds`
carried over (`dsFull_eq` | `dsSmall_eq`). It is made by no maker: what OnBytes/Flat/EntryTerm.lean
proves of `entryFull` | `entrySmall` (that term is the maker's link at the parameter bytes, its
rounds the dry run's) is proved of another term. The two have two types of transcripts; no theorem
of this library relates the two protocols. The key file's and the proof file's are `keyIOR` and
`proofIOR` (OnBytes/Maker/Files.lean) at the kit in which a verifier message is blocks of digests,
at the depth of the tables' code, at keys written of a record; what these two makers take beside is
in the structure `FilesParameters X R`: LETTERS, the chains' parameters (`G.k`, `G.c`) and the proof
file's first block (`G.block`) among them. THE DATA OF THE TWO FILES' ROUNDS ARE NO LETTERS OF THEIR
OWN: the makers take them, by definition, from the dry runs of the blocks at these letters at a
sample instance (`G.rec₀`, `G.z₀`), test them, and stand at the empty data, where nothing is
accepted, if a test fails (`dataAt`, `okAt`, OnBytes/Maker/Files.lean).

Main names:
  `Coding A`, `relationsAndEncodingOfClaims A E`: the rest of a configuration; both relations are "in range, and `A.Rel`".
  `FilesParameters X R`: the two files' chains' parameters (`k`, `c`), the proof file's first block as a
    function of the instance, a record and an instance with a record at which the dry runs are made
    (`rec₀`, `z₀`), the depth of the tree of a batch's slots (their number is 2 ^ `depthReq`), and
    which part of an instance is fixed first (`early`).
  `ansL rec`: a record's answers AS A LIST, in the type in which a file as read holds them: the
    entries of the key that is written of the record.
  `silK`, `silP`: the tests on what the three silent rounds send in the clear: a front's and a
    joining round's message hold the answers as such a list. The key file's is the makers'
    `silentOf` (OnBytes/Maker/SilentParts.lean): both copies of the answers are `ansL` of the
    record, and the copy's number is 0. The proof file's tests the two copies of the answers alone.
    The seam's message and the joining round's run's value are tested by neither.
  `threeProtocolsFromDryRunAtFullSize_entrySound`, `threeProtocolsFromDryRunAtSmallSize_entrySound`: the entry file's protocol is round-by-round sound
    with every round's error at most 2^-128, under the theorem on codes alone. The language: the
    first table gives no index with its record, or the copy has a collision at its record's seed, or
    both give the same index; where a way out is open the theorem says nothing, and where
    `A.inRange` holds of nothing it is true for free. The 128 bits count the round's proof of work:
    at six rounds of the full size and four of the small one 32 of them are work, which stands
    inside the written verifier messages as test bits; that work is worth its bits is not shown
    (`linkSibFull_sound`, `linkSibSmall_sound`, OnBytes/Flat/LinkSibAt.lean; which rounds: the heads
    of OnBytes/Slice/FullRecNum.lean and SmallRecNum.lean). The bound is one round's: no bound on
    the chance of a false proof.
  `threeProtocolsFromDryRunAtFullSize_local`, `threeProtocolsFromDryRunAtSmallSize_local`: the three verifiers read their oracles at the declared
    positions alone. `threeProtocolsFromDryRunAtFullSize_coherent`, `threeProtocolsFromDryRunAtFullSize_entryCoherent` and the small twins: the three
    annotations are coherent.

Limits: nothing on the soundness of the key file's and the proof file's protocol. That `G.block` is
the program's first block is not asked here (OnBytes/Flat/BigOf.lean lays it so). That the dry runs
give the same rounds at every record and instance is not said here. That a key file's front holds
the number 0 is taken from the head of OnBytes/Maker/SilentParts.lean: it is not checked here
against the format or a program. THE TWO TESTS COMPARE WORDS, NOT FIELD ELEMENTS: `ansL` writes each
answer with words below the prime (`writeE`, OnBytes/Slice/KeyOfRec.lean), so a list as read is
`ansL` of a record only where it has 2 ^ v * s entries and every word is below the prime. That a
program's reader gives such a list is not shown here.
THE NUMBER OF THE STORED COPY in the front's
plain part of a proof file is tested by no clause of `silP`: an instance holds no such number. The
compiled verifier calls `OutOfDomainSampleQueryLayout.num` on a proof string's number and the proof file's plain parts;
that function is a letter of the inputs (Johnson/Flat/TwoSizes.lean: `T.num`): what it tests is said
nowhere. NOTHING COMES LATE (late := none): where `G.block` is the program's first block (a letter
here; OnBytes/Flat/BigOf.lean lays it so) the reply is the prover's message of the round REPLY,
compared by the decision. To bind the reply is then a load of the hypothesis on the proof file's
protocol (`proofSound`), and at an `early` that drops more than the decision compares with a message
of the prover that hypothesis fails. Not shown: the law that what is got there
is the reply's token; that the links at an instance and at its early part run
alike; that the real protocol meets the batch's clause at these values is shown
nowhere. `early` IS A LETTER: at early := id the reply would be hashed first,
which is NOT the programs' form: the programs' is "the reply's word wiped".
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.EntrySound
import OnBytes.Flat.LinkSibAt
import OnBytes.Flat.Object
import OnBytes.Maker.Files
import OnBytes.Maker.WholeLocal
import OnBytes.Maker.WholeLaws
import OnBytes.Maker.SilentParts
import Compile.Joined.Laws
import Ior.SeqProofs

set_option autoImplicit false

noncomputable section

namespace OnBytes.Flat
open Iop Prob Cb Cb.Ood Hiop _root_.Run OnBytes.Slice OnBytes.Join1 OnBytes.Maker
open scoped ENNReal

/-- How an index is held, encoded and sampled: what a configuration holds for the honest side. -/
structure Coding {D : DecR} {X : Type} (A : D.Claims X) where
  Rnd : Type
  [finRnd : Fintype Rnd]
  [neRnd : Nonempty Rnd]
  enc : (D.ix.Row × D.toDec.En → GE) → Rnd → (Fin (2 ^ D.T.a) → Run.PQ.SgX)
  Pad : Type
  [finPad : Fintype Pad]
  [nePad : Nonempty Pad]
  hold : A.Mat → Pad → (D.ix.Row × D.toDec.En → GE)
  smp : D.Z.D → (D.ix.Row × D.toDec.En → GE) → (D.ix.Row × D.Z.S → GE)

attribute [instance] Coding.finRnd Coding.neRnd Coding.finPad Coding.nePad

/-- The rest of a configuration in which both relations are: THE MATRIX IS IN RANGE, AND THE CLAIM
`A.Rel` of the instance on it holds. There are no cells. (The decoder gives matrices in range alone,
so the first clause costs a proof file's protocol nothing; without it a claim that is an implication
"if the matrix holds an index" would hold emptily at a matrix that holds none.) -/
def relationsAndEncodingOfClaims {D : DecR} {X : Type} (A : D.Claims X) (E : Coding A) : D.RelationsAndEncoding A where
  Cells := Unit
  Ryes := fun M x _ => A.inRange M ∧ A.Rel M x
  Rno := fun M x _ => A.inRange M ∧ A.Rel M x
  Rnd := E.Rnd
  enc := E.enc
  Pad := E.Pad
  hold := E.hold
  smp := E.smp
  trace := fun _ _ => ()
  cells0 := ()

/-- What `threeProtocolsFromDryRunAtFullSize` | `threeProtocolsFromDryRunAtSmallSize` take beside the size: the first five fields go to the two
makers, the last two to the fields `N` and `early` of `Files`. R: the type of records. -/
structure FilesParameters (X R : Type) where
  k     : Params.KeyChains
  c     : Params.ProofChains
  block : X → Blk Proof.FirstEnd
  /-- the record at which the key file's dry runs are made -/
  rec₀  : R
  /-- the instance and the record at which the proof file's dry runs are made -/
  z₀    : X × R
  /-- the number of slots of a batch is 2 ^ depthReq -/
  depthReq : ℕ
  early : X → X

section
variable {v lg s : ℕ}

/-- **The answers of a record as a list**: the entries of the key that is written of the record
(`keyOf`, OnBytes/Slice/KeyOfRec.lean), in the key's order: entry r * s + i is the answer of row r
under seed i. This is the type in which a file as read holds a table's answers
(`Params.TableName.answers`, OnBytes/Params/Chains.lean). Irreducible: it stands inside the shapes
of the two whole files (as a silent round's fixed message), and Lean's type checker should not
unfold an array of 2 ^ v * s entries each time it compares two such shapes. No law on it is stated
here: a proof that needs its length or its entries says `unfold ansL` and uses `keyOf_size`,
`keyOf_record`. That two records with one `ansL` have the same answers is stated nowhere. -/
@[irreducible] def ansL (rec : RecP NZ v lg s) : List OnBytes.E :=
  (keyOf (fun β : NZ => β.val) rec).record.toList

/-- The key file's test on the silent rounds' plain parts: the makers' own, at the copy's number 0.
-/
def silK : RecP NZ v lg s → FrontMsg (List OnBytes.E) →
    Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool :=
  silentOf (fun rec : RecP NZ v lg s => ansL rec) fun _ => 0

/-- The proof file's: both copies of the answers are `ansL` of the record; the copy's number is not
tested. -/
def silP {X : Type} (z : X × RecP NZ v lg s) (f : FrontMsg (List OnBytes.E))
    (j : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) (_ : ByteArray) : Bool :=
  decide (f.answers = ansL z.2) && decide (j.answers = ansL z.2)

theorem silP_answers {X : Type} (z : X × RecP NZ v lg s) (f : FrontMsg (List OnBytes.E))
    (j : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) (t : ByteArray)
    (h : silP z f j t = true) : f.answers = ansL z.2 ∧ j.answers = ansL z.2 := by
  unfold silP at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- The plain parts that stand where a silent round has sent nothing. -/
def front₀ (rec : RecP NZ v lg s) : FrontMsg (List OnBytes.E) := ⟨ansL rec, 0⟩
def join₀ (rec : RecP NZ v lg s) : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray :=
  ⟨ansL rec, ByteArray.empty⟩

end

/-- The makers' two reductions are local. -/
theorem keyIOR_isLocal {R TF TJ T3 : Type} (C : PQ.CK) (a : ℕ) (tF : TF) (tJ : TJ) (t3 : T3)
    (silent : R → TF → TJ → T3 → Bool) (key : R → TableKey) (k : Params.KeyChains) (rec₀ : R) :
    (keyIOR C a tF tJ t3 silent key k rec₀).IsLocal := by
  unfold keyIOR keyIORAt
  exact wholeIOR_isLocal ..

theorem proofIOR_isLocal {X R TF TJ T3 : Type} (C : PQ.CK) (a : ℕ) (tF : TF) (tJ : TJ) (t3 : T3)
    (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey) (c : Params.ProofChains)
    (block : X → Blk Proof.FirstEnd) (z₀ : X × R) :
    (proofIOR C a tF tJ t3 silent key c block z₀).IsLocal := by
  unfold proofIOR proofIORAt
  exact wholeIOR_isLocal ..

/-! ## The full-size files -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (G : FilesParameters X RecFull)

/-- The three files' protocols at the full size. -/
def threeProtocolsFromDryRunAtFullSize : Files (DecR.configurationOfStoredTable A R) where
  key := (keyIOR (ckP .two) frS.P.T.a (front₀ G.rec₀) (join₀ G.rec₀) ByteArray.empty silK
    (keyOf (fun β : NZ => β.val) : RecFull → TableKey) G.k G.rec₀).toInteractiveOracleProof
  entry := linkSibFull
  proof := (proofIOR (ckP .two) frS.P.T.a (front₀ G.z₀.2) (join₀ G.z₀.2) ByteArray.empty silP
    (keyOf (fun β : NZ => β.val) : RecFull → TableKey) G.c G.block G.z₀).toInteractiveOracleProof
  N := 2 ^ G.depthReq
  annT := keyAnn (ckP .two) frS.P.T.a (front₀ G.rec₀) (join₀ G.rec₀) ByteArray.empty silK
    (keyOf (fun β : NZ => β.val) : RecFull → TableKey) G.k G.rec₀
  annL := _root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsFull)
  ann := proofAnn (ckP .two) frS.P.T.a (front₀ G.z₀.2) (join₀ G.z₀.2) ByteArray.empty silP
    (keyOf (fun β : NZ => β.val) : RecFull → TableKey) G.c G.block G.z₀
  early := G.early
  late := none

theorem threeProtocolsFromDryRunAtFullSize_entrySound (hA : BCHKS46At GF GE) :
    ∃ ε, Err.Below ε ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧ (threeProtocolsFromDryRunAtFullSize A R G).entry.Sound
      (fun rr y => (DecR.configurationOfStoredTable A R).D y.1 rr.1 = none ∨ (DecR.configurationOfStoredTable A R).coll y.2 rr.2.1 ∨
        (DecR.configurationOfStoredTable A R).D y.2 rr.2 = (DecR.configurationOfStoredTable A R).D y.1 rr.1) ε :=
  have ⟨ε, hs, hb⟩ := linkSibFull_sound hA A R
  ⟨ε, hb, hs⟩

theorem threeProtocolsFromDryRunAtFullSize_local : (threeProtocolsFromDryRunAtFullSize A R G).key.IsLocal ∧ (threeProtocolsFromDryRunAtFullSize A R G).entry.IsLocal ∧
    (threeProtocolsFromDryRunAtFullSize A R G).proof.IsLocal :=
  ⟨Iop.isLocal_toProto _ _ _ (keyIOR_isLocal ..), linkSibFull_local,
    Iop.isLocal_toProto _ _ _ (proofIOR_isLocal ..)⟩

theorem threeProtocolsFromDryRunAtFullSize_coherent : (threeProtocolsFromDryRunAtFullSize A R G).annT.Coherent ∧ (threeProtocolsFromDryRunAtFullSize A R G).ann.Coherent :=
  ⟨Compile.Joined.Chains.ann_coherent _ (chainsOf_laws ..),
    Compile.Joined.Chains.ann_coherent _ (chainsOf_laws ..)⟩

theorem threeProtocolsFromDryRunAtFullSize_entryCoherent : (threeProtocolsFromDryRunAtFullSize A R G).annL.Coherent := by
  show (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsFull)).Coherent
  rw [_root_.Run.Twin.allLo_eq]
  exact Iop.BatchOne.BAnn.allLocal_coherent _

end

/-! ## The small files -/

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
  (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (G : FilesParameters X RecSmall)

/-- The three files' protocols at the small size. -/
def threeProtocolsFromDryRunAtSmallSize : Files (DecR.configurationOfStoredTable A R) where
  key := (keyIOR (ckP .two) srS.P.T.a (front₀ G.rec₀) (join₀ G.rec₀) ByteArray.empty silK
    (keyOf (fun β : NZ => β.val) : RecSmall → TableKey) G.k G.rec₀).toInteractiveOracleProof
  entry := linkSibSmall
  proof := (proofIOR (ckP .two) srS.P.T.a (front₀ G.z₀.2) (join₀ G.z₀.2) ByteArray.empty silP
    (keyOf (fun β : NZ => β.val) : RecSmall → TableKey) G.c G.block G.z₀).toInteractiveOracleProof
  N := 2 ^ G.depthReq
  annT := keyAnn (ckP .two) srS.P.T.a (front₀ G.rec₀) (join₀ G.rec₀) ByteArray.empty silK
    (keyOf (fun β : NZ => β.val) : RecSmall → TableKey) G.k G.rec₀
  annL := _root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsSmall)
  ann := proofAnn (ckP .two) srS.P.T.a (front₀ G.z₀.2) (join₀ G.z₀.2) ByteArray.empty silP
    (keyOf (fun β : NZ => β.val) : RecSmall → TableKey) G.c G.block G.z₀
  early := G.early
  late := none

theorem threeProtocolsFromDryRunAtSmallSize_entrySound (hA : BCHKS46At GF GE) :
    ∃ ε, Err.Below ε ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧ (threeProtocolsFromDryRunAtSmallSize A R G).entry.Sound
      (fun rr y => (DecR.configurationOfStoredTable A R).D y.1 rr.1 = none ∨ (DecR.configurationOfStoredTable A R).coll y.2 rr.2.1 ∨
        (DecR.configurationOfStoredTable A R).D y.2 rr.2 = (DecR.configurationOfStoredTable A R).D y.1 rr.1) ε :=
  have ⟨ε, hs, hb⟩ := linkSibSmall_sound hA A R
  ⟨ε, hb, hs⟩

theorem threeProtocolsFromDryRunAtSmallSize_local : (threeProtocolsFromDryRunAtSmallSize A R G).key.IsLocal ∧ (threeProtocolsFromDryRunAtSmallSize A R G).entry.IsLocal ∧
    (threeProtocolsFromDryRunAtSmallSize A R G).proof.IsLocal :=
  ⟨Iop.isLocal_toProto _ _ _ (keyIOR_isLocal ..), linkSibSmall_local,
    Iop.isLocal_toProto _ _ _ (proofIOR_isLocal ..)⟩

theorem threeProtocolsFromDryRunAtSmallSize_coherent :
    (threeProtocolsFromDryRunAtSmallSize A R G).annT.Coherent ∧ (threeProtocolsFromDryRunAtSmallSize A R G).ann.Coherent :=
  ⟨Compile.Joined.Chains.ann_coherent _ (chainsOf_laws ..),
    Compile.Joined.Chains.ann_coherent _ (chainsOf_laws ..)⟩

theorem threeProtocolsFromDryRunAtSmallSize_entryCoherent : (threeProtocolsFromDryRunAtSmallSize A R G).annL.Coherent := by
  show (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsSmall)).Coherent
  rw [_root_.Run.Twin.allLo_eq]
  exact Iop.BatchOne.BAnn.allLocal_coherent _

end
end OnBytes.Flat

#print axioms OnBytes.Flat.threeProtocolsFromDryRunAtFullSize_entrySound
#print axioms OnBytes.Flat.threeProtocolsFromDryRunAtFullSize_local
#print axioms OnBytes.Flat.threeProtocolsFromDryRunAtFullSize_coherent
#print axioms OnBytes.Flat.threeProtocolsFromDryRunAtSmallSize_entrySound
