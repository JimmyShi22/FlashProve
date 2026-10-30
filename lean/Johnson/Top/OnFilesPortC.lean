-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/OnFilesPortC.lean: if the argument system `systemArmsC r`, whose verifier runs the three
typed checks that the parameter r holds, is sound in the sense of `SoundForWith` (or
`SoundForWithO`), then so is the system `systemPortC p` whose verifier `port` reads files, at the
error ε (t + n) + δ t, under the three named hypotheses `PortTiesC p`. Every field of p, `port`
among them, is a parameter, and `PortTiesC p` is proved of no p here.

What this file states. It is stated at the wider key of
Johnson/Top/OnFilesArmsC.lean. In the namespace `VerifiableInference.OnPublicFiles`. `PortArmsC r`:
parameters: the type of what a prover hands over (the files), the verifier `port`, the reader that
makes the typed proof of the files (an algorithm over the hash function, without coins) with its
budget n, the exception (likewise an algorithm) with the stated bound δ on its probability, an
honest prover. `systemPortC p`: the argument system whose verifier is `port`, a verifier in the
sense of VerifiableInference/Statements.lean. `verify_sound_portC`, `verify_sound_portC_O`:
soundness of `systemArmsC r` (`SoundForWith`, `SoundForWithO`) is soundness of `systemPortC p`: the
same extractor, the same claim, the error ε (t + n) + δ t; Johnson/Top/SoundVia.lean carries it
across. `accepts_of_armsC`: what `tie` lists is a yes of `systemArmsC r`. `CrossingC p H Served
filesOf`: a definition: the statement that is then left between `port` and the Lean text
`verify-on-bytes`: if a run of its `main` in the library's model of a shell (`Shell.Run`) ends with
code 0 on a served statement, `port` says yes at the fixed function H, at the commitment that the
user's ID names, that prompt and output, and the files as read. `PortSaysC`: a definition: three
things side by side; NO test of saying something (see below):
`PortTiesC`, `CrossingC`, and completeness of `systemPortC p` (`CompleteOn`,
VerifiableInference/Steps.lean) on a domain that is not empty, at an error that is at most the bound
on the exception's probability.

Under which hypotheses. hs: soundness of `systemArmsC r` at the extractor, the claim and ε. T:
`PortTiesC p`: three named hypotheses: `budget` (the reader asks at most n queries), `price` (the
exception's bound over a random function), and `tie`, stated AT EVERY HASH FUNCTION: at every hash
function g, where `port` says yes at a commitment, a prompt, output tokens and files, the reader's
proof at g holds further tokens, a key and typed strings such that the builder makes an instance,
the key has a code, g at that code is the commitment, and each of the three checks says yes at g; or
the exception says yes at g.

What it does not show. `PortTiesC` and `CrossingC` are hypotheses and a definition: nothing here
proves them of any verifier `port`. All of `PortArmsC` are parameters: that `port` is the rewritten
port (the rewriting of the Lean port of the C++ verifier over a monad in which the hash is asked) is
said by `CrossingC` alone, and at one function. The step that is taken as given stays: the fixed
function H (Lean's BLAKE2b) in the place of the random function. A verifier `port` that never says
yes
meets `PortTiesC`; then `CrossingC` fails wherever a served call ends in 0. "The rewritten port" is
a property nowhere here:
`port`, `filesOf`, `Served` and H are unconstrained parameters, and `port` may be chosen after H. At
every r the idle verifier `port` (the files are the typed proof; `port` is the verifier of
`systemArmsC r`; the reader hands the proof on; the exception never holds) meets `PortTiesC` by
definition. What the link at every hash function buys comes only where `port` is one concrete term
(defined in this library, not a parameter): the text of `verify-on-bytes` with its hash function a
parameter. And any verifier `port` under a guard that holds the claim meets `PortTiesC` at a vacuous
input: so that every statement which passes the concrete test `servedAt Z` (OnBytes/K/Served.lean)
is served must appear next to `CrossingC`; no field here requires it. `PortTiesC` and `CrossingC`
can still be met together by something vacuous (by an informal argument, not a theorem): a verifier
`port` that first asks one string, says no unless the answer is BLAKE2b's own value there, and then
decides as `verify-on-bytes` does at BLAKE2b, with the exception "the answer at that string is that
value": the bound on the exception's probability is 2^-256, the link holds at every hash function by
its second disjunct, the crossing holds, and the soundness that follows is of a verifier that all
but never accepts under a random function. Completeness of the system of the verifier `port` over
the random function at a stated small error (`PortSaysC`) shuts that one out and no more: a split
verifier `port` (ask one string; if the answer is H's there, say yes outright; else run the checks'
own verifier on a typed proof; the exception: "the answer at that string is H's") meets all of
`PortSaysC` at the bound 2^-256 on the exception's probability, and the exception "always" meets it
at the bound 1 (shown by a probe in Lean's kernel, outside this library). Completeness tests whether
`port` accepts under a random function, not whether what it does there is what it does at H. The
only guard is that `port` is no parameter; in this file it is one (a field of `PortArmsC`). A second
guard, at the fixed function: a
concrete exception and one honest served call that ends in 0 and at which the exception says no.
At the wider key: that the checks test the key's first part (the public digest that the typed key
holds) against the hash function's own answer is required by no hypothesis, and a bound at each
fixed value of that part gives none at a value that the committer names after its queries
(Johnson/Top/OnFilesArmsC.lean).
`CrossingC` and `PortSaysC` are in the namespace `OnBytes.K`; `accepts_of_armsC` is
Johnson/Top/OnFilesArmsC.lean's. In this file "Lean's BLAKE2b" stands for one fixed function: the
format's realised oracle on bit strings (`Run.oBits ()`: Lean's BLAKE2b read through the format's
byte coding). For proofs only; `verify-on-bytes` does not import this file.

-/
import OnBytes.K.Tokens
import Johnson.Top.OnFilesArmsC
import Johnson.Top.SoundVia

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The parameters of a Lean verifier that reads the files a prover hands over: the files' type, an
honest prover, the verifier `port`, a parser with its budget of queries, and an exception with a
stated bound on the probability that it says yes. Any terms of these types may be given, and nothing
here says that `port` is the text `verify-on-bytes`: only `CrossingC` states that, and this file
proves it of no term.
-/
structure PortArmsC (r : InputArmsC) where
  /-- what a prover hands over -/
  Files : Type
  /-- an honest prover -/
  prove : (systemArmsC r).Weights → (systemArmsC r).CommitmentRandomness → List Token → List Token →
    RandomizedAlgorithm Files
  /-- the verifier: it takes a commitment, a prompt, output tokens and the files, and asks the hash
  function as an oracle -/
  port : Commitment → List Token → List Token → Files → DeterministicAlgorithm Bool
  /-- the reader: the typed proof that it makes of the files -/
  reader : List Token → List Token → Files →
    DeterministicAlgorithm (List Token × ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL))
  /-- the reader's budget of queries -/
  n : ℕ
  /-- the exception -/
  exc : Commitment → List Token → List Token → Files → DeterministicAlgorithm Bool
  /-- the stated bound on the probability that the exception says yes -/
  δ : ℕ → ℝ≥0∞

variable {r : InputArmsC} (p : PortArmsC r)

/-- The named hypotheses on the verifier `port`. -/
structure PortTiesC : Prop where
  budget : ∀ prompt output F, (p.reader prompt output F).toRandomized.QueryBound p.n
  price : ExceptionBound p.exc p.δ
  tie : ∀ (g : Hash) c prompt output F, (p.port c prompt output F).evaluate g = true →
    (∃ aux k π x code, (p.reader prompt output F).evaluate g = (aux, (k, π)) ∧
      r.build (prompt, output) aux = some x ∧ r.enc k = some code ∧ g code = c ∧
      (liftKC r k x π).det (fun _ => g) = true ∧ (liftEC r k x π).det (fun _ => g) = true ∧
      (liftPC r k x π).det (fun _ => g) = true) ∨
      (p.exc c prompt output F).evaluate g = true

/-- The argument system whose verifier is `port`. -/
def systemPortC : ArgumentSystem := (systemArmsC r).withVerifier p.Files p.prove p.port

variable {p}

/-- The premise of Johnson/Top/SoundVia.lean, from the field `tie`. -/
theorem PortTiesC.via (T : PortTiesC p) (g : Hash) (c : Commitment) (prompt output : List Token)
    (F : p.Files) (h : (p.port c prompt output F).evaluate g = true) :
    (systemArmsC r).accepts g c prompt output ((p.reader prompt output F).evaluate g) = true ∨
      (p.exc c prompt output F).evaluate g = true := by
  rcases T.tie g c prompt output F h with ⟨aux, k, π, x, code, e, hb, hc, hd, vK, vE, vP⟩ | he
  · left
    have h2 := accepts_of_armsC g c prompt output aux k π x code hb hc hd vK vE vP
    rw [← e] at h2
    exact h2
  · exact Or.inr he

/-- From soundness of `systemArmsC r` and the hypotheses of `PortTiesC` follows soundness of the
system whose verifier is `port`, at the error ε (t + n) + δ t. -/
theorem verify_sound_portC (T : PortTiesC p)
    {extractor : Commitment → QueryLog → Option r.I}
    {claim : r.I → List Token → List Token → Prop} {ε : ℕ → ℝ≥0∞}
    (hs : SoundForWith (systemArmsC r) extractor claim ε) :
    SoundForWith (systemPortC p) extractor claim fun t => ε (t + p.n) + p.δ t :=
  soundForWith_via (systemArmsC r) p.prove p.port p.reader p.n p.exc T.via T.budget hs T.price

/-- The same for an extractor that may query the hash function. -/
theorem verify_sound_portC_O (T : PortTiesC p)
    {extractor : Commitment → QueryLog → DeterministicAlgorithm (Option r.I)} {q : ℕ}
    {claim : r.I → List Token → List Token → Prop} {ε : ℕ → ℝ≥0∞}
    (hs : SoundForWithO (systemArmsC r) extractor q claim ε) :
    SoundForWithO (systemPortC p) extractor q claim fun t => ε (t + p.n) + p.δ t :=
  soundForWithO_via (systemArmsC r) p.prove p.port p.reader p.n p.exc T.via T.budget hs T.price

end VerifiableInference.OnPublicFiles

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open VerifiableInference VerifiableInference.OnPublicFiles

variable {r : InputArmsC}

/-- What is left between the verifier `port` and the Lean text `verify-on-bytes`: code 0 of a run of
its `main` in the library's model of a shell (`Shell.Run`) on a served statement is `port`'s yes at
the fixed function H. -/
def CrossingC (p : PortArmsC r) (H : Hash) (Served : UserStm → Prop)
    (filesOf : Files → Model.Verify.Options → p.Files) : Prop :=
  ∀ {args : List String} {s s' : World}, Shell.Run (_root_.main args) s 0 s' →
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      (Served (stmOf F a.options) →
        ∃ cm, CommitIs (stmOf F a.options) cm ∧
          (p.port cm (promptOf (stmOf F a.options)) (outputOf (stmOf F a.options))
            (filesOf F a.options)).evaluate H = true)

/-- Three things side by side; no test of saying something (the head): the linking statements at
every hash function, the crossing at the fixed one, and: over a random function an honest committer
and an honest prover are rejected by the verifier `port` with probability at most α, on a domain
that is not empty, with α at most the bound on the exception's probability. "Some α below 1" would
not do: the vacuous verifier `port` of the head accepts honest runs with probability 2^-256. `below`
holds at t = 0 too: α is at most the least such bound; where the bound at 0 is 0 it requires that
honest runs are never rejected. That is intended. -/
structure PortSaysC (p : PortArmsC r) (H : Hash) (Served : UserStm → Prop)
    (filesOf : Files → Model.Verify.Options → p.Files)
    (domain : r.I → List Token → List Token → Prop) (α : ENNReal) : Prop where
  ties : PortTiesC p
  crossing : CrossingC p H Served filesOf
  complete : CompleteOn (systemPortC p) domain α
  below : ∀ t, α ≤ p.δ t
  some : ∃ weights prompt output, domain weights prompt output ∧
    (systemPortC p).IsModelOutput weights prompt output

end OnBytes.K

#print axioms VerifiableInference.OnPublicFiles.verify_sound_portC
#print axioms VerifiableInference.OnPublicFiles.verify_sound_portC_O
