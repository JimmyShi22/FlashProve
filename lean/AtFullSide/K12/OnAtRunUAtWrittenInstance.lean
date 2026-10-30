-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the list of the test on G_u at a run, at an instance written of a sample.
/-
AtFullSide/K12/OnAtRunUAtWrittenInstance.lean: CONDITIONAL: A CONDITIONAL WITH NO KNOWN MEMBER.

Can the hypotheses be met together at a real run? NOT KNOWN. G with hP: a term lies at this G's own
type: `theGAtBase` with `theGAtBase_prover` (E2E/TheG.lean; not imported): its
prover at the return's prover is the return's; BUT its two arguments, the threads' parts and the
kinds' rows, have no known value. The list, a value of `ThreadsP`, ready's and runC's return and
that the part is called have no term and no law known to us: where the part is never called the end
holds for nothing. hrc can be met: it names the run's randomness.

What is here. `onAtRun_U_at_the_committers_instance` (AtFullSide/K12/OnAtRunUAtCommittersKey.lean)
AT THE MATRICES (the filling's input is `matrixInput`, E2E/TheHonestProver.lean) AND AT AN INSTANCE
WRITTEN OF A SAMPLE: `instanceAsPlainRecord` of any request and of the object's sample (`recOf`) at the run's own
matrix, at any online randomness and any seed. Its premise on the instance is paid by the law
`instance_is_committers` (AtFullSide/Honest/InstanceIsCommitters.lean), called as it
lies; the filling's reader of a matrix is ⟨cellsReader M⟩ by `matrixInput`'s own text. No
definition; one statement.

  `onAtRun_U_at_the_written_instance`   the statement.

THE PREMISES, SORTED. PUBLIC: h · hb. THE MAKER: hAr. THE RUN: T · hρ · hR · hrun: the rule's own
letters. WHICH OBJECTS: hP · hA · hJs · hL. THE CROSSING: hrc : rc = `randOf` of the online
randomness: the map by which the online filling reads its randomness (`tableCoins`,
E2E/TheHonestProver.lean, by its text). IT IS A PREMISE: that a run of the online prover is a run of
this prover at that rc is the crossing; no file of ours types it. BESIDE THESE NO
CLAUSE ON VALUES IS LEFT: no premise speaks of what a row, a word, a key, a stand, a carried block
or a lent coin holds. THE FILLING. At W₀ := the matrices, I := `matrixInput`, S' := Sz.ref, O :=
openHonest, `onlineProverPartsInUse I secondHashFunction S' O` is `baseFilling` by its text (E2E/BaseMaker.lean).
Two things are not shown here or beneath: that the own test's rows are ready, and that the lent
o_sp words are tied at the tests on G_u and on G_omega through `OnlineProverParts.through`.
The wide filling is defined in Honest/K1/Law/WSideAtFill.lean.
This file does not show that the maker returns at it.

WHAT LIES BEHIND THE BASE [not held by this file]. The row
of the top statement on index privacy stands at the ONLINE maker's return, at the online
randomness's type, and at a prover whose fields key and stored are the committer's at the object's
types: hP cannot be met at that prover unless two equations hold that say that this leaves the
return's prover as it is. Nothing ties G at the base to G there. That statement's relation writes
the sample by another term than `recOf`: that the two are one term is not held. A relation at this
prover's types is typed nowhere.

What the law called says of itself (its head): "the committer" there is `committerPure` shFull Zp,
the builder of the explicit input; the committer at the object's types is another term, and that the
two committers' keys are one is not typed there; the seed and the bytes stand under "there are" at
the law called here. It was read once by another house's reader at these bytes.

A LIMIT ON THE COMMITTER's RANDOMNESS, BEFORE THE OTHERS:
AtFullSide/K12/OnAtRunUAtCommittersKey.lean's head, whole. HERE THE INSTANCE's KEY IS NO LETTER: it
is the term made of the matrix, the online randomness and the seed: the form that
Johnson/Bind/ForProver/FiveAt.lean's head calls safe at single values. The seed is a letter bound
beside them: in a law over the randomness it has to be the term made of index and randomness.

Through its imports this file stands over files under Johnson/Goal/ (a walk of the import lines).





Limits. All limits of the three files beneath (Sim2/ListU.lean, AtFullSide/K12/OnAtRunUPaid.lean,
AtFullSide/K12/OnAtRunUAtCommittersKey.lean). The rule moves the debt and pays none of it; these
files bring the debt at one list down to hrc and the objects. No later law may take the condition On
as a hypothesis on a run and then speak of the random values as sampled anew. The row's own order of
binders, for whoever states "at every coin": every (w₀, rc, x) of the relation, every k, every
return, one T, then every due list of challenges outside the silent set, every run. At the maker's
return at the wide filling, not at the online maker's. Nothing on completeness, soundness or
hiding.
No property is claimed.
-/
import AtFullSide.K12.OnAtRunUAtCommittersKey
import AtFullSide.Honest.InstanceIsCommitters
import E2E.TheHonestProver

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K12
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.First (S)
open Desc.K14 (St blocks)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles instance_is_committers)
open LPFD.Full (XF instanceAsPlainRecord)

/-- CONDITIONAL: see the head. **The clause of the rule at the list of the test on G_u, at the
maker's return at the wide filling at the matrices and at that return's own book, AT AN INSTANCE
WRITTEN OF ANY REQUEST AND OF THE OBJECT's SAMPLE AT THE RUN's OWN MATRIX, AT ANY ONLINE RANDOMNESS
AND SEED, WHERE THE RUN's RANDOMNESS IS THAT ONLINE RANDOMNESS READ AS ONE TABLE's** (hrc: a
premise: the crossing, which this file does not type). Beside it no clause on values is left. -/
theorem onAtRun_U_at_the_written_instance {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction S' O) = .ok Ar)
    {H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B FullSizeMatrix IndexCommitterCoins TableKey Cells Unit Unit}
    (hP : G.prover H = Ar.H) {M : FullSizeMatrix} {rc : IndexCommitterCoins}
    (online : (protocolAtFiles Z).EncodingRandomness) (seed : (protocolAtFiles Z).OutOfDomainSeed) (request : XF)
    (hrc : rc = ProofFile.Honest.randOf (S := frS) (cut := 402653181) online)
    {k : Coins Ar.B} {ρ : Draws}
    {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) M rc
      (instanceAsPlainRecord (request, (protocolAtFiles Z).recOf M online seed)) k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) M rc
      (instanceAsPlainRecord (request, (protocolAtFiles Z).recOf M online seed)) k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) M rc
      (instanceAsPlainRecord (request, (protocolAtFiles Z).recOf M online seed)) k ρ = .ok r)
    (A : ManyJob (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit)
    (hA : jobRealU (matrixInput.weights Zp)
      (fun w => Bind.ForProver.encW Zp (matrixInput.weights Zp w)) Zp = some A)
    (Js : SimJob TableKey) (hJs : Js = simHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8])
    (L : Lettered Ar.B St ProofFile.Cl Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)
    (hL : IsListAtU Np L A Js) :
    OnAtRun₂ T ρ r L := by
  subst hrc
  obtain ⟨sd, x₁, e⟩ := instance_is_committers Z h.scope h.laid.pub M online seed request
  exact onAtRun_U_at_the_committers_instance h b1 b2 b3 b4 b5 b6 b7 b8 hb matrixInput S' O hAr hP T
    hρ hR hrun A hA Js hJs L hL sd x₁ e

end AtFullSide.K12

#print axioms AtFullSide.K12.onAtRun_U_at_the_written_instance
