-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Joined/VCWalk.lean: the two calls of the compiled verifier with records for the key file
and for the proof file are the verifier of a file, which walks three hash chains, at files made of
the wire record's own parts.

Statements on the verifier with records, over the second form of the compiler's verifier side, for a
key file's and a proof file's three hash chains, joined by seals. That this verifier writes what is
hashed as the prover's files have it is not shown in this folder.
By a reading of the programs' text it does not: behind the roots, `VC`
(Johnson/TypedOracleCompiler/RecCompile/Cms.lean) puts a code of the whole record, the seed too, into the first
query of each of its three compiled verifiers, while the programs hash the roots and the answers,
and recompute the seeds from the roots (so too the verifier written in Lean:
OnBytes/Params/Chains.lean; OnBytes/Key/Table.lean). `verifyAtFullKey` (Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean) is
the form that has the answers alone there; nothing in this file is stated for it.

The compiled verifier with records (`VC`, Johnson/TypedOracleCompiler/RecCompile/Cms.lean) calls `verifyOneProtocol` once for
the key (`vTC`), once for an entry (`vLC`) and once for a session's proof (`vBC`). The soundness of
a file is said of `FileW.verify` (OnBytes/TypedOracleCompiler/Joined/Verifier.lean). This file says that `vTC` and
`vBC` are that function where the key's and the session's protocols are a file's (two equations, eT
and eB: hypotheses; see Limits).

Main names:
  `writtenT W`, `writtenB W`   the key's and the session's protocol as `VC` writes them: tag, batch
                             protocol, wire record and maps, all of them W's own
  `vTC_eq_written`, `vBC_eq_written`   the two calls are the compiled verifier at these, by
                             unfolding
  `vTC_eq_file`, `vBC_eq_file`   where the key's protocol with its annotation is `DT.batch`, and the
                             session's is `DB.batch`: the two calls are `FileW.verify` at the files
                             `FileW.ofWritten (writtenT W) DT eT` and
                             `FileW.ofWritten (writtenB W) DB eB`
  `batTC_eq`                 eT from an equation between the protocols and one between the
                             annotations
  `VC_eq_files`              `VC` itself, with these two calls written as the verifier of a file

Limits: the two equations eT, eB are hypotheses; eT says also that the annotation of the key's
rounds is that of a file (`GT.ann`). The proof string is carried along them; where they hold by
unfolding nothing is carried. Nothing on the entry's call `vLC`.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.Cms
import OnBytes.TypedOracleCompiler.Joined.OfWritten

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- the key's protocol as `VC` writes it -/
def writtenT : Written W L.Rec (oneExternalString L.wordLength L.Symbol) :=
  ⟨Tag.test, batTC L aT, wTC W, W.embT, id, fun _ => none, W.embE⟩

/-- the session's protocol as `VC` writes it -/
def writtenB : Written W (X × L.Rec) (oneExternalString L.wordLength L.Symbol) :=
  ⟨Tag.onl, L.onlineBatch, wBC W, W.embB, id, xinB, W.embE⟩

/-- the call for the key is the compiled verifier at `writtenT W` -/
theorem vTC_eq_written (p : Params) (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    vTC W S p cm rec π = (writtenT W).verify p.sMT p.sFS (cmsT W S cm rec) rec π := rfl

/-- the call for a session's proof is the compiled verifier at `writtenB W` -/
theorem vBC_eq_written (p : Params) (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    vBC W S p cm x rec π = (writtenB W).verify p.sMT p.sFS (cmsB W S cm rec) (x, rec) π := rfl

/-- The call for the key is the verifier of a file, which walks three chains. -/
theorem vTC_eq_file {GT : Chains} (DT : Desc GT L.Rec (oneExternalString L.wordLength L.Symbol))
    (eT : batTC L aT = DT.batch) (p : Params) (cm : Dig lam) (rec : L.Rec)
    (π : OneProtocolProof lam (batTC L aT)) :
    vTC W S p cm rec π =
      (FileW.ofWritten (writtenT W) DT eT).verify p.sMT p.sFS (cmsT W S cm rec) rec
        (cast (congrArg (fun Q : BatchInteractiveOracleProof L.Rec (oneExternalString L.wordLength L.Symbol) => OneProtocolProof lam Q) eT) π) :=
  (writtenT W).verify_eq_file DT eT p.sMT p.sFS (cmsT W S cm rec) rec π

/-- The call for a session's proof is the verifier of a file, which walks three chains. -/
theorem vBC_eq_file {GB : Chains} (DB : Desc GB (X × L.Rec) (oneExternalString L.wordLength L.Symbol))
    (eB : L.onlineBatch = DB.batch) (p : Params) (cm : Dig lam) (x : X) (rec : L.Rec)
    (π : OneProtocolProof lam L.onlineBatch) :
    vBC W S p cm x rec π =
      (FileW.ofWritten (writtenB W) DB eB).verify p.sMT p.sFS (cmsB W S cm rec) (x, rec)
        (cast (congrArg (fun Q : BatchInteractiveOracleProof (X × L.Rec) (oneExternalString L.wordLength L.Symbol) => OneProtocolProof lam Q) eB) π) :=
  (writtenB W).verify_eq_file DB eB p.sMT p.sFS (cmsB W S cm rec) (x, rec) π

/-- The equation for the key from one between the protocols and one between the annotations. -/
theorem batTC_eq {GT : Chains} (DT : Desc GT L.Rec (oneExternalString L.wordLength L.Symbol)) (hT : L.offline = DT.proto)
    (haT : HEq aT GT.ann) : batTC L aT = DT.batch :=
  batch_eq_of_proto DT L.offline hT aT haT

/-- **The compiled verifier with records, with its calls for the key and for the proof written as
the verifier of a file.** It asks for the seeds of the two tables, runs the key file's verifier, the
entry's call and the proof file's verifier, and takes the conjunction, with the test on the number
of the stored copy. -/
theorem VC_eq_files {GT GB : Chains} (DT : Desc GT L.Rec (oneExternalString L.wordLength L.Symbol))
    (DB : Desc GB (X × L.Rec) (oneExternalString L.wordLength L.Symbol)) (eT : batTC L aT = DT.batch) (eB : L.onlineBatch = DB.batch)
    (p : Params) (v : FullKey lam L aT aL) (x : X) (π : RequestProof lam L) :
    VC W S p v x π =
      match v.piT, v.links[π.leaf]?, π.piB with
      | some πT, some (cmj, recj, some πL), some πB =>
          (outOfDomainSeedIs W S v.cm v.rcd.1).bind fun s0 =>
          (outOfDomainSeedIs W S cmj recj.1).bind fun sj =>
          ((FileW.ofWritten (writtenT W) DT eT).verify p.sMT p.sFS (cmsT W S v.cm v.rcd) v.rcd
            (cast (congrArg (fun Q : BatchInteractiveOracleProof L.Rec (oneExternalString L.wordLength L.Symbol) => OneProtocolProof lam Q) eT)
              πT)).bind fun a =>
          (vLC W S p v.cm cmj v.rcd recj πL).bind fun b =>
          ((FileW.ofWritten (writtenB W) DB eB).verify p.sMT p.sFS (cmsB W S cmj recj) (x, recj)
            (cast (congrArg (fun Q : BatchInteractiveOracleProof (X × L.Rec) (oneExternalString L.wordLength L.Symbol) => OneProtocolProof lam Q) eB)
              πB)).bind fun c =>
          OComp.pure (S.num π.copy πB.plains && s0 && sj && a && b && c)
      | _, _, _ => OComp.pure false := by
  unfold VC
  simp only [vTC_eq_file W S DT eT, vBC_eq_file W S DB eB]
  rfl

end TypedOracleCompiler.Compile.Batch.Cms
