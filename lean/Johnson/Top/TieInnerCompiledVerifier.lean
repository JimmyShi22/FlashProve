-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieInnerCompiledVerifier.lean: the tie between the Lean program `verify-on-bytes`
(OnBytes/Main.lean; "the program" below) and `innerCompiledVerifier r`, the verifier of which
Johnson/Top/InnerCompiledVerifier.lean states soundness under its own named hypotheses.

`innerCompiledVerifier r` is the verifier of the argument system made from the scheme whose verifier is
`verifyAtKeyRoot r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters`: the compiled verifier with records over the
compiler's verifier side (OnBytes/TypedOracleCompiler/, Johnson/TypedOracleCompiler/RecCompile/), with the key cut to a root and its
record, and with roots and answers alone, nothing of a seed, in the first query of each of its three
chains. It runs over one hash function through `r.oracleCoding`; the key stands behind the digest of `r.keyCode`;
the instance is built by `r.buildInstance`. This file fills the parameters of OnBytes/K/TopVC.lean and
Johnson/Top/TieFront.lean with r's own terms.

Main definitions.
 `InnerInputTieData r`    what r does not fix and the tie must write: which statements are served, and
               how a table is read as a record.
 `innerInputTieShape`    the shape at r. Its five parts are the runs of the verifier's own parts at what `r.oracleCoding`
               reads out of Lean's BLAKE2b. The session's part takes the number of the stored copy
               beside the typed string, and holds the verifier's test `r.seedQueries.num` on that number. The
               instance is what `r.buildInstance` makes of the prompt, the output and the further tokens
               that OnBytes/K/Tokens.lean reads off the user's request and reply.
 `innerInputTieFront`    the front at r. A key is the first table's root and record; a proof is the copy's
               number, Test's string, the further root with its record and Link's string, and the
               session's string.
 `TieHoles`    the named hypotheses of the tie at r that speak of the two seeds, the entry file and
               the commitment ID: `EntryPart` (OnBytes/K/Parts.lean) at r's shape, and idHash.

Main theorems.
 `VCA_det`             the run of `verifyAtFullKey` at a key with one entry is the conjunction of its six runs.
 `runs_two`            where the five answers are yes, `(schemeOverTypedOracles r).V` over `r.oracleCoding`, run at Lean's
                       BLAKE2b, says yes. Proved.
 `frontV_is_innerCompiledVerifier` [Johnson/Top/InnerCompiledVerifierParts.lean] `frontV` (Johnson/Top/FrontGeneral.lean) at
                       r's terms is `innerCompiledVerifier r`: by rfl.
 `exit_verifyLinkProof`        under `EntryPart` alone: if the program exits with code 0, there are its own
                       two tables (`PortYesAt`); and on a served statement the entry's arm of the
                       verifier, `VLA` (the two seeds' tests and Link;
                       Johnson/TypedOracleCompiler/RecCompile/LinkAns.lean), run at what `r.oracleCoding` reads out of Lean's
                       BLAKE2b, says yes at these tables' roots and records and at the string that
                       the fixed reading gives of the key file and the entry file.
 `exit_innerCompiledVerifier`      under `TieHoles` and `KeyProofPart`: if the program exits with code 0 on a
                       served statement, then `(innerSystem r).accepts`, at Lean's BLAKE2b as the hash
                       function, at the commitment that the user's ID names, at that prompt and
                       output, and at the proof made of the further tokens, the key and the strings
                       that the fixed reading R gives of the three files, is true.

What is not claimed.
 All of `TieHoles` and `KeyProofPart` are hypotheses; none is proved here at any r. A hypothesis may
 be false, not only unproved. `KeyProofPart` (Test, the session) stands apart from `TieHoles`
 because it has not been weighed at three points where the typed queries meet the strings that the
 prover and the verifiers that ship hash: see the head of OnBytes/K/Parts.lean.
 idHash asks one digest for the code of (root, record) at every served statement and every table
 that `recOf` reads. Its right side hangs on the planner's digest and shape and on the whole table.
 So it asks for collisions of BLAKE2b, unless `Served` pins the three public files to one set of
 bytes and a table is determined by its root's digest and its record.
 `recOf` is free, and a record holds a seed, which is an answer of the hash function. With a `recOf`
 that takes the seed from the typed draw itself, `seed0` and `seed1` hold by unfolding, and that the
 typed seed is the program's own then sits unseen in the other three. So these two say something
 only at a `recOf` whose seed is the program's own.
 That `r.buildInstance` returns an instance at the tokens read off the request and the reply, and that this
 instance is what the program checked, is all inside `session`.
 The reading R is meant to parse and not to search. With an R that searches, `link`, `test` and
 `session` say only that an accepting string exists.
 The soundness of `VLA` (`linkA_pr`, Johnson/TypedOracleCompiler/RecCompile/LinkAnsPr.lean) is stated over typed
 oracles and of a trace; no step from it to one hash function lies here. For `exit_verifyLinkProof` the step
 that is taken as given is therefore larger: what `r.oracleCoding` reads out of BLAKE2b stands for independent
 typed oracles.
 No r and no `InnerInputTieData r` is given. `Served`, `recOf` and the reading R are parameters.
 Evaluating Lean's BLAKE2b for the soundness theorem's random function is one step taken as given;
 another is on the second hash (lean/THEOREM.md, "Two hash functions"). Exit code 0 covers both YES
 and WITHIN LIMITS; which of them a served statement admits is `Served`'s to say. All that the heads
 of OnBytes/K/Top.lean, OnBytes/K/TopVC.lean, OnBytes/K/Parts.lean, Johnson/Top/TieFront.lean and
 Johnson/Top/InnerCompiledVerifier.lean do not claim. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Tokens
import OnBytes.K.Parts
import Johnson.Top.TieFront
import Johnson.Top.InnerCompiledVerifier
import Johnson.Top.InnerCompiledVerifierParts
import Rom.Cache

set_option autoImplicit false

noncomputable section

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open Rom
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)
open VerifiableInference (Token)
open VerifiableInference.OnPublicFiles

variable (r : InnerCompilerInput)

/-- What r does not fix and the tie must write, but for the reading of the files. -/
structure InnerInputTieData where
  /-- the statements that the description covers -/
  Served : UserStm → Prop
  /-- a table as a record -/
  recOf : UserStm → OnBytes.Params.TableName → Option r.protocol.Rec

variable {r} (T : InnerInputTieData r)

/-- The shape at r. -/
def innerInputTieShape : Shape where
  Served := T.Served
  Rec := fun _ => r.protocol.Rec
  Ins := fun _ => r.Instance
  PiT := fun _ => OneProtocolProof 256 (batTC r.protocol r.offlineRoundSplits)
  PiL := fun _ => OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits)
  PiB := fun _ => ℕ × OneProtocolProof 256 r.protocol.onlineBatch
  recOf := T.recOf
  insOf := fun x => r.buildInstance (promptOf x, outputOf x) (auxOf x)
  seed0 := fun _ cm c => (outOfDomainSeedIs r.queryLayout r.seedQueries cm c.1).det (readBlocks r.oracleCoding oBits)
  seed1 := fun _ cm c => (outOfDomainSeedIs r.queryLayout r.seedQueries cm c.1).det (readBlocks r.oracleCoding oBits)
  vT := fun _ cm c π => (verifyOfflineProof r.queryLayout r.answerCode r.compilerParameters cm c π).det (readBlocks r.oracleCoding oBits)
  vL := fun _ cm cm' c c' π => (verifyLinkProof r.queryLayout r.answerCode r.compilerParameters cm cm' c c' π).det (readBlocks r.oracleCoding oBits)
  vB := fun _ cm i c π =>
    r.seedQueries.num π.1 π.2.plains && (verifyOnlineProof r.queryLayout r.answerCode r.fixedSample r.compilerParameters cm i c π.2).det (readBlocks r.oracleCoding oBits)

/-- The front at r. -/
def innerInputTieFront : FrontAt (innerInputTieShape T) where
  I := r.Index
  X := r.Instance
  IVK := KeyRoot 256 r.protocol
  ISK := r.ProverKey
  Pf := OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits
  G := schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r)
  enc := r.keyCode
  bound := r.coinBound
  build := r.buildInstance
  π₀ := r.fallbackProof
  prompt := promptOf
  output := outputOf
  aux := auxOf
  ins := fun _ i => i
  keyOf := fun _ t c => ⟨bytesToDig t.root, c⟩
  prfOf := fun _ πT u cj πL πB => ⟨πB.1, some πT, (bytesToDig u.root, cj, some πL), some πB.2⟩

/-- The run of `verifyAtFullKey` at a key with one entry is the conjunction of its six runs. -/
theorem VCA_det (g : Fam (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))) (cm : Dig 256)
    (c : r.protocol.Rec) (πT : OneProtocolProof 256 (batTC r.protocol r.offlineRoundSplits)) (cmj : Dig 256) (cj : r.protocol.Rec)
    (πL : OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits)) (x : r.Instance) (n : ℕ) (πB : OneProtocolProof 256 r.protocol.onlineBatch) :
    (verifyAtFullKey r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters ⟨cm, c, some πT, [(cmj, cj, some πL)]⟩ x ⟨0, n, some πB⟩).det g =
      (r.seedQueries.num n πB.plains && (outOfDomainSeedIs r.queryLayout r.seedQueries cm c.1).det g &&
        (outOfDomainSeedIs r.queryLayout r.seedQueries cmj cj.1).det g && (verifyOfflineProof r.queryLayout r.answerCode r.compilerParameters cm c πT).det g &&
        (verifyLinkProof r.queryLayout r.answerCode r.compilerParameters cm cmj c cj πL).det g && (verifyOnlineProof r.queryLayout r.answerCode r.fixedSample r.compilerParameters cmj x cj πB).det g) := by
  show ((outOfDomainSeedIs r.queryLayout r.seedQueries cm c.1).bind fun s0 =>
      (outOfDomainSeedIs r.queryLayout r.seedQueries cmj cj.1).bind fun sj =>
      (verifyOfflineProof r.queryLayout r.answerCode r.compilerParameters cm c πT).bind fun a =>
      (verifyLinkProof r.queryLayout r.answerCode r.compilerParameters cm cmj c cj πL).bind fun b =>
      (verifyOnlineProof r.queryLayout r.answerCode r.fixedSample r.compilerParameters cmj x cj πB).bind fun d =>
      OComp.pure (r.seedQueries.num n πB.plains && s0 && sj && a && b && d)).det g = _
  simp only [OComp.det_bind]
  rfl

/-- Where the five answers are yes, the scheme's verifier over `r.oracleCoding`, run at Lean's BLAKE2b, says
yes. -/
theorem runs_two (x : UserStm) (t u : OnBytes.Params.TableName) (c cj : r.protocol.Rec) (i : r.Instance)
    (πT : OneProtocolProof 256 (batTC r.protocol r.offlineRoundSplits)) (πL : OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits)) (πB : ℕ × OneProtocolProof 256 r.protocol.onlineBatch)
    (s0 : (innerInputTieShape T).seed0 x (bytesToDig t.root) c = true)
    (s1 : (innerInputTieShape T).seed1 x (bytesToDig u.root) cj = true)
    (vt : (innerInputTieShape T).vT x (bytesToDig t.root) c πT = true)
    (vl : (innerInputTieShape T).vL x (bytesToDig t.root) (bytesToDig u.root) c cj πL = true)
    (vb : (innerInputTieShape T).vB x (bytesToDig u.root) i cj πB = true) :
    ((innerInputTieFront T).G.V ((innerInputTieFront T).keyOf x t c) ((innerInputTieFront T).ins x i)
      ((innerInputTieFront T).prfOf x πT u cj πL πB)).det (fun _ => oBits ()) = true := by
  show ((verifyAtFullKey r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters
    ⟨bytesToDig t.root, c, some πT, [(bytesToDig u.root, cj, some πL)]⟩ i
    ⟨0, πB.1, some πB.2⟩).overOne r.oracleCoding).det (fun _ => oBits ()) = true
  have e0 : (fun _ => oBits ()) = (oBits : Fam (rom 256)) := rfl
  rw [e0, det_overOne, VCA_det]
  have s0 : (outOfDomainSeedIs r.queryLayout r.seedQueries (bytesToDig t.root) c.1).det (readBlocks r.oracleCoding oBits) = true := s0
  have s1 : (outOfDomainSeedIs r.queryLayout r.seedQueries (bytesToDig u.root) cj.1).det (readBlocks r.oracleCoding oBits) = true := s1
  have vt : (verifyOfflineProof r.queryLayout r.answerCode r.compilerParameters (bytesToDig t.root) c πT).det (readBlocks r.oracleCoding oBits) = true := vt
  have vl : (verifyLinkProof r.queryLayout r.answerCode r.compilerParameters (bytesToDig t.root) (bytesToDig u.root) c cj πL).det
    (readBlocks r.oracleCoding oBits) = true := vl
  have vb : (r.seedQueries.num πB.1 πB.2.plains &&
    (verifyOnlineProof r.queryLayout r.answerCode r.fixedSample r.compilerParameters (bytesToDig u.root) i cj πB.2).det (readBlocks r.oracleCoding oBits)) = true := vb
  rw [Bool.and_eq_true] at vb
  rw [s0, s1, vt, vl, vb.1, vb.2]
  rfl

/-- The named hypotheses of the tie at r on the two seeds, the entry file and the commitment ID. -/
structure TieHoles (R : Reading5 (innerInputTieShape T)) : Prop where
  /-- the two seeds' tests and Link say yes where the program does -/
  entry : EntryPart (innerInputTieShape T) R
  /-- at a served statement, the key made of a table and its record has a code, and the hash of that
  code, at Lean's BLAKE2b, is the table's commitment ID under the planner's shape and digest -/
  idHash : ∀ x t c pl, T.Served x → Model.Verify.planned x.pol x.KL (some x.lay) = .ok pl →
    T.recOf x t = some c →
    ∃ code, r.keyCode ⟨bytesToDig t.root, c⟩ = some code ∧
      oBits () code = bytesToDig (Key.commitmentId pl.chains.tableShape pl.cfg t)

/-- The tie for the entry file at the verifier's own arm `VLA`, under `EntryPart` alone. -/
theorem exit_verifyLinkProof (R : Reading5 (innerInputTieShape T)) (A : EntryPart (innerInputTieShape T) R)
    {args : List String} {s s' : World} (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      ∃ (table further : OnBytes.Params.TableName), PortYesAt F id table further ∧
        (T.Served (stmOf F a.options) →
          ∃ (c cj : r.protocol.Rec) (πL : OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits)),
            T.recOf (stmOf F a.options) table = some c ∧
            T.recOf (stmOf F a.options) further = some cj ∧
            R.ent (stmOf F a.options) F.key F.ent = some (further, πL) ∧
            (VLA r.queryLayout r.seedQueries r.answerCode r.compilerParameters (bytesToDig table.root) (bytesToDig further.root) c cj πL).det
              (readBlocks r.oracleCoding oBits) = true) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table, further,
    hp, hs⟩ := exit_entryPart (innerInputTieShape T) R A h
  refine ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table,
    further, hp, fun hS => ?_⟩
  obtain ⟨c, cj, πL, hc, hcj, he, s0, s1, vl⟩ := hs hS
  refine ⟨c, cj, πL, hc, hcj, he, ?_⟩
  have s0 : (outOfDomainSeedIs r.queryLayout r.seedQueries (bytesToDig table.root) c.1).det (readBlocks r.oracleCoding oBits) = true := s0
  have s1 : (outOfDomainSeedIs r.queryLayout r.seedQueries (bytesToDig further.root) cj.1).det (readBlocks r.oracleCoding oBits) = true :=
    s1
  have vl : (verifyLinkProof r.queryLayout r.answerCode r.compilerParameters (bytesToDig table.root) (bytesToDig further.root) c cj πL).det
    (readBlocks r.oracleCoding oBits) = true := vl
  unfold VLA
  simp only [OComp.det_bind]
  rw [s0, s1, vl]
  rfl

/-- The tie at `innerCompiledVerifier r`, under `TieHoles` and `KeyProofPart` at r's shape. See "What is not
claimed" in the head. -/
theorem exit_innerCompiledVerifier (R : Reading5 (innerInputTieShape T)) (A : TieHoles T R)
    (B : KeyProofPart (innerInputTieShape T) R)
    {args : List String} {s s' : World} (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      (T.Served (stmOf F a.options) →
        ∃ (table further : OnBytes.Params.TableName) (c cj : r.protocol.Rec)
          (πT : OneProtocolProof 256 (batTC r.protocol r.offlineRoundSplits)) (πL : OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits))
          (πB : ℕ × OneProtocolProof 256 r.protocol.onlineBatch) (cm : ZKCP.Digest 256),
          CommitIs (stmOf F a.options) cm ∧ IdIs (stmOf F a.options) table ∧
          T.recOf (stmOf F a.options) table = some c ∧
          T.recOf (stmOf F a.options) further = some cj ∧
          R.key (stmOf F a.options) F.key = some (table, πT) ∧
          R.ent (stmOf F a.options) F.key F.ent = some (further, πL) ∧
          R.prf (stmOf F a.options) F.ent F.proof F.entry = some πB ∧
          (innerSystem r).accepts (oBits ()) cm (promptOf (stmOf F a.options))
            (outputOf (stmOf F a.options))
            (auxOf (stmOf F a.options),
              (⟨bytesToDig table.root, c⟩,
                ⟨πB.1, some πT, (bytesToDig further.root, cj, some πL), some πB.2⟩)) = true) :=
  exit_front (innerInputTieShape T) R (holes5_of_parts A.entry B) (innerInputTieFront T)
    ⟨fun x t u c cj i πT πL πB => runs_two T x t u c cj i πT πL πB, fun _ _ _ hi => hi,
      A.idHash⟩ h

end OnBytes.K
