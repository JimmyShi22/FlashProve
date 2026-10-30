-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieInnerCompiledVerifierServed.lean: the tie of Johnson/Top/TieInnerCompiledVerifier.lean with "served" no
longer a parameter: it is the test `servedAt Z` (OnBytes/K/Served.lean), and the exit code 0 itself
pays it but for three pins and two options. For proofs only; the program does not import this file.

  `tieAt Z recOf`: the `InnerInputTieData r` whose served statements are those that pass `servedAt Z`.
  `exit_innerCompiledVerifier_served`: `exit_innerCompiledVerifier` at `tieAt Z recOf`, with its premise "the statement is
    served" replaced by: the three public files as read are Z's, byte for byte, and the call names
    neither -policy nor -no-proof-of-work. By `pay_served` (OnBytes/K/ServedAny.lean).
  `exit_verifyLinkProof_served`: the same for `exit_verifyLinkProof`, the tie for the entry file alone, by
    `served_any`; the program's own two tables stand before the pins.
What is not claimed: all that the heads of Johnson/Top/TieInnerCompiledVerifier.lean, OnBytes/K/Served.lean and
OnBytes/K/ServedAny.lean do not claim. `servedAt Z` still stands as a premise inside the hypotheses
`TieHoles` and `KeyProofPart`. A call that ends within limits has named -policy: of it nothing is
said. Without -policy the parameter file's own policy is the exact match, or the call is about the
reply alone (r + 1 = e = T, as the head of OnBytes/K/TopServed.lean has it: the last position alone
is covered). Z, recOf and the reading R are still parameters. Both theorems have as a premise that
the program `verify-on-bytes` (OnBytes/Main.lean) ends with the exit code 0: that any call ends so
is not shown here, and where none does they say nothing.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.TieInnerCompiledVerifier
import OnBytes.K.ServedAny

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

variable {r : InnerCompilerInput}

/-- The tie whose served statements are those that pass `servedAt Z`. -/
def tieAt (Z : Pub) (recOf : UserStm → OnBytes.Params.TableName → Option r.protocol.Rec) : InnerInputTieData r :=
  ⟨fun x => servedAt Z x = true, recOf⟩

/-- The tie at `innerCompiledVerifier r`, with "served" paid from the exit code but for three pins and two
options. See "What is not claimed" in the heads of this file and of
Johnson/Top/TieInnerCompiledVerifier.lean. -/
theorem exit_innerCompiledVerifier_served (Z : Pub)
    (recOf : UserStm → OnBytes.Params.TableName → Option r.protocol.Rec)
    (R : Reading5 (innerInputTieShape (tieAt Z recOf))) (A : TieHoles (tieAt Z recOf) R)
    (B : KeyProofPart (innerInputTieShape (tieAt Z recOf)) R)
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
      (F.pol = Z.pol → F.lay = Z.lay → F.KL = Z.KL → a.options.policy = none →
        a.options.noProofOfWork = false →
        ∃ (table further : OnBytes.Params.TableName) (c cj : r.protocol.Rec)
          (πT : OneProtocolProof 256 (batTC r.protocol r.offlineRoundSplits)) (πL : OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits))
          (πB : ℕ × OneProtocolProof 256 r.protocol.onlineBatch) (cm : ZKCP.Digest 256),
          CommitIs (stmOf F a.options) cm ∧ IdIs (stmOf F a.options) table ∧
          recOf (stmOf F a.options) table = some c ∧
          recOf (stmOf F a.options) further = some cj ∧
          R.key (stmOf F a.options) F.key = some (table, πT) ∧
          R.ent (stmOf F a.options) F.key F.ent = some (further, πL) ∧
          R.prf (stmOf F a.options) F.ent F.proof F.entry = some πB ∧
          (innerSystem r).accepts (oBits ()) cm (promptOf (stmOf F a.options))
            (outputOf (stmOf F a.options))
            (auxOf (stmOf F a.options),
              (⟨bytesToDig table.root, c⟩,
                ⟨πB.1, some πT, (bytesToDig further.root, cj, some πL), some πB.2⟩)) = true) :=
  pay_served Z (Served := (tieAt Z recOf).Served) (fun _ hx => hx) h
    (exit_innerCompiledVerifier (tieAt Z recOf) R A B h)

/-- The tie for the entry file at the verifier's own arm `VLA`, with "served" paid likewise, under
`EntryPart` alone. -/
theorem exit_verifyLinkProof_served (Z : Pub)
    (recOf : UserStm → OnBytes.Params.TableName → Option r.protocol.Rec)
    (R : Reading5 (innerInputTieShape (tieAt Z recOf))) (A : EntryPart (innerInputTieShape (tieAt Z recOf)) R)
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
        (F.pol = Z.pol → F.lay = Z.lay → F.KL = Z.KL → a.options.policy = none →
          a.options.noProofOfWork = false →
          ∃ (c cj : r.protocol.Rec) (πL : OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits)),
            recOf (stmOf F a.options) table = some c ∧
            recOf (stmOf F a.options) further = some cj ∧
            R.ent (stmOf F a.options) F.key F.ent = some (further, πL) ∧
            (VLA r.queryLayout r.seedQueries r.answerCode r.compilerParameters (bytesToDig table.root) (bytesToDig further.root) c cj πL).det
              (readBlocks r.oracleCoding oBits) = true) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table, further,
    hp, hs⟩ := exit_verifyLinkProof (tieAt Z recOf) R A h
  refine ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table,
    further, hp, fun p1 p2 p3 o1 o2 => hs ?_⟩
  have hq := served_any h config ivk request y proof a F t h1 h2 o1 o2
  have eZ : (⟨F.pol, F.lay, F.KL⟩ : Pub) = Z := by
    cases Z
    simp only [Pub.mk.injEq]
    exact ⟨p1, p2, p3⟩
  rw [eZ] at hq
  exact hq

end OnBytes.K
