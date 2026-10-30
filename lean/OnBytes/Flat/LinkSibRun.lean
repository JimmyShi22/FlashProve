-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinkSibRun.lean: the decision in `linkSibFull` and `linkSibSmall`
(OnBytes/Flat/LinkSibAt.lean) is the decision of a run (`decRun`,
OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean) at the ground's parameters with any digest in the digest's
place, at the written numbers.

Main names:
  `decRun_eq`: the decision of a run, unfolded, at any parameters.
  `decRun_full`, `decRun_small`: the two decisions are one function: the decision of an entry's
    check at two keys does not read the digest of the public files.
  `ground_q_full`, `ground_q_small`: the grounds' parameters are `Params.recordRead` and
    `Params.smallRecordRead`, by definition.
  `linkSibFull_run`, `linkSibSmall_run`: so the link over pairs of records is `linkSib` at the
    decision of a run.

Limits: definitions unfolded; nothing else.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.LinkSibAt
import OnBytes.TypedOracleCompiler.Slice.EntryRunMain

set_option autoImplicit false

noncomputable section

namespace OnBytes.Flat
open OnBytes.Slice TypedOracleCompiler.Slice OnBytes.Tie
open _root_.Run (ckP)

/-- The decision of a run, unfolded, at any parameters: it does not read the digest. -/
theorem decRun_eq (p : Params.Link) (c : ByteArray) (v lg s : ℕ) (x : XE AnsT lg s) :
    decRun (linkAtCfg p c) v lg s x =
      (linkVerify p.link (keysOfX v lg s (anT v s) x).1 (keysOfX v lg s (anT v s) x).2).decides
        (Entry.start p) := rfl

/-- The full-size ground's parameters. -/
theorem ground_q_full : recordGround.q = Params.recordRead := rfl

/-- The small ground's parameters. -/
theorem ground_q_small : smallRecordGround.q = Params.smallRecordRead := rfl

/-- The decision of a run at the full size's parameters, any digest, and the written numbers. -/
theorem decRun_full (c : ByteArray) :
    decRun (linkAtCfg Params.recordRead c) frS.P.v 29 1 = decFullX :=
  funext fun x => (decRun_eq Params.recordRead c frS.P.v 29 1 x).trans (by unfold decFullX; rfl)

/-- The same at the small example. -/
theorem decRun_small (c : ByteArray) :
    decRun (linkAtCfg Params.smallRecordRead c) srS.P.v 19 1 = decSmallX :=
  funext fun x =>
    (decRun_eq Params.smallRecordRead c srS.P.v 19 1 x).trans (by unfold decSmallX; rfl)

/-- The link over pairs of records is `linkSib` at the decision of a run. -/
theorem linkSibFull_run (c : ByteArray) :
    linkSibFull = linkSib (v := frS.P.v) (ckP .two) dsFull frS.P.T.a frD.xs
      (decRun (linkAtCfg Params.recordRead c) frS.P.v 29 1) := by
  rw [decRun_full]

/-- The same at the small example. -/
theorem linkSibSmall_run (c : ByteArray) :
    linkSibSmall = linkSib (v := srS.P.v) (ckP .two) dsSmall srS.P.T.a srD.xs
      (decRun (linkAtCfg Params.smallRecordRead c) srS.P.v 19 1) := by
  rw [decRun_small]

end OnBytes.Flat
