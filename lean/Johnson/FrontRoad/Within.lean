-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/Within.lean: upper bounds on the number of queries to the one hash function that
the committer and the prover of the shell frontArg (Front.lean) make on every path, from bounds
that hold at every value d of the type T.D, whether or not the public reading can return it.
Terms and the limits that go with any quote: Spec.lean.

What this file proves, for arbitrary parameters. q₀ bounds the public reading's queries, and Bk the
hash blocks of a typed answer under the coding at every d. commitW and proveW are the committer and
the prover of the scheme with the whole key published (Johnson/WholeKey/Defs.lean).
  queryBound_frontC   If commitW makes at most NC typed queries at every d and index, the committer
                      of frontArg makes at most q₀ + NC * Bk + 1 queries: the reading's, NC typed
                      queries of at most Bk blocks, and one for the ID.
  queryBound_frontP   If proveW makes at most NP typed queries at every d, prover's key and list of
                      requests, the prover of frontArg makes at most NP * Bk queries.
  within_front        Under PremAll at every d (PremAt.lean), both bounds hold for all NC and NP
                      that bound commitN and proveN of the honest side at every d.

Limits. Upper bounds on every path, loose in two ways: chainN (Johnson/Prover/Law/Count.lean) counts
every try of every search up to its limit, and each typed query counts as the largest number of
blocks. q₀, Bk, NC and NP are variables: no number is evaluated. Nothing on index binding is proved
or said here.

How it fits. Why a bound on the honest side's work is wanted next to the errors is said in the head
of Johnson/WholeKey/Work.lean. Its counts commitN and proveN are in typed queries at fixed
parameters; here they become queries to the one hash function. Bundle.lean uses within_front.
-/
import Johnson.FrontRoad.Front
import Johnson.FrontRoad.PremAt
import Johnson.WholeKey.WorkOf
import Rom.OneOfCount

set_option autoImplicit false

noncomputable section

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
  {J : Type} (idx : J → R.Index) (x₀ : R.Instance)
  (Vf : KeyF R → List Token × List Token → RequestProof 256 R.protocol → ZKCP.OComp 256 Bool)

/-- If the public reading makes at most q₀ queries, a typed answer has at most Bk blocks under the
coding at every d, and commitW makes at most NC typed queries at every d and index, then on every
path the committer of frontArg makes at most q₀ + NC * Bk + 1 queries to the hash function. -/
theorem queryBound_frontC (q₀ Bk NC : ℕ) (hq : T.Pub.QueryBound q₀)
    (hB : ∀ d o, (T.m d).blocks o ≤ Bk)
    (hC : ∀ d i, (commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i).QueryBound NC) (w : J) :
    ((frontArg T h idx x₀ Vf).C w).QueryBound (q₀ + NC * Bk + 1) := by
  have hG : ((readTold T h).C (idx w)).QueryBound (q₀ + (NC * Bk + 0 + 0)) :=
    hq.bind fun d =>
      OComp.QueryBound.bind
        (OComp.QueryBound.bind
          (queryBound_overOne (T.m d) (hB d) _ NC (hC d (idx w))) fun _ => trivial)
        fun _ => trivial
  exact ZKCP.OComp.QueryBound.bind _ 1
    (fun keys => ZKCP.OComp.QueryBound.mapO _ _ 1 (ZKCP.queryBound_keyDigest _ _)) _ _
    (queryBound_oneOf_C (readTold T h) (idx w) hG)

/-- If a typed answer has at most Bk blocks under the coding at every d, and proveW makes at most NP
typed queries at every d, prover's key and list of requests, then on every path the prover of
frontArg makes at most NP * Bk queries to the hash function. -/
theorem queryBound_frontP (Bk NP : ℕ) (hB : ∀ d o, (T.m d).blocks o ≤ Bk)
    (hP : ∀ d isk b, (proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk b).QueryBound NP)
    (isk : T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (x' : List Token × List Token) :
    ((frontArg T h idx x₀ Vf).P isk x' ()).QueryBound (NP * Bk) := by
  have hG : ((readTold T h).P isk [(instOf R x₀ x', ())]).QueryBound (NP * Bk) :=
    queryBound_overOne (T.m isk.1) (hB isk.1)
      (proveW R.queryLayout (T.cA isk.1) R.fixedSample (h isk.1) isk.2 [(instOf R x₀ x', ())]) NP (hP isk.1 isk.2 _)
  exact queryBound_oneOf_P (readTold T h) isk (instOf R x₀ x') () hG

/-- Under PremAll at every d, with q₀ and Bk as above: if NC and NP bound commitN and proveN of the
honest side at every d, then both bounds hold for frontArg at the honest sides F.side. -/
theorem within_front (F : SidesAt T) {ok : R.Index → Prop} {Ryes : R.Index → R.Instance → Prop}
    (hP : PremAll F ok Ryes fun _ => True) (q₀ Bk NC NP : ℕ) (hq : T.Pub.QueryBound q₀)
    (hB : ∀ d o, (T.m d).blocks o ≤ Bk) (hNC : ∀ d, commitN R.queryLayout (F.side d) ≤ NC)
    (hNP : ∀ d, proveN R.queryLayout (F.side d) ≤ NP) :
    (∀ w, ((frontArg T F.side idx x₀ Vf).C w).QueryBound (q₀ + NC * Bk + 1)) ∧
      ∀ isk x', ((frontArg T F.side idx x₀ Vf).P isk x' ()).QueryBound (NP * Bk) :=
  ⟨queryBound_frontC T F.side idx x₀ Vf q₀ Bk NC hq hB fun d i =>
      (work_commitW (hP d trivial) i).mono (hNC d),
    queryBound_frontP T F.side idx x₀ Vf Bk NP hB fun d isk b =>
      (work_proveW (hP d trivial) R.fixedSample isk b).mono (hNP d)⟩

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.queryBound_frontC
#print axioms OnBytes.FrontRoad.queryBound_frontP
#print axioms OnBytes.FrontRoad.within_front
