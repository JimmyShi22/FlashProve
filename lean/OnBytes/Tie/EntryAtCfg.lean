-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryAtCfg.lean: the parameters of an entry's chain with another value in the place of
the digest of the public files: what of the chain's description, its limits and its dry run stays
the same.

The parameter bytes of every chain spell the digest of the public files (`Fmt.paramsBytes`), and
what is read back from them holds it (`Params.Given.cfg`).



A bound under a random oracle for a verifier that forms that digest by the oracle needs facts on
the entry's chain at every value that the oracle can give.
The whole call's text over a monad forms the
digest by the hash that it is handed (`M.Model.Verify.planned`,
OnBytes/ChecksWithHashAsArgument/M/Model/Verify.lean);
nothing is stated of it here. No such bound
for the program stands in OnBytes/: the program forms the digest by BLAKE2b. `linkAtCfg p c` is p
with c in the digest's place and the parameter bytes spelled anew at c.

Main definition: `linkAtCfg`.
Main theorems.
- `entryRounds_linkAtCfg`, `answers_linkAtCfg`, `cfg_linkAtCfg`: the dry run of
  `Params.entryBlock`, the link's block at the keys `Params.plainKey`, does not read the
  digest; nor does the number of answers; the description holds c. All by definition.

- `withinX_reCfg`, `withinX_linkAtCfg`: the limits test (`withinX`) has the same value at c as at
  p's own digest, if the two have one length and p's parameter bytes are spelled from p's plan,
  digest and items. It uses `specOk_reCfg`, `paramsBytes_prefix`, `size_paramsBytes`.
- `fourBounds_linkAtCfg`: so has the library's test `Run.PQ.fourBounds`, without a condition.
  `rds_linkAtCfg`: the rounds' data are the same; no proof here uses it.






What is not claimed. No probability and nothing on soundness. The limits do not read the digest
through its length alone: the format's conditions on a description also ask that the parameter bytes
begin with the spelling of this plan and this digest, so the bytes must be spelled at c.
`Verify.planned_spelled` (OnBytes/Model/VerifyDigest.lean) says that the program's bytes are spelled
under its digest from some plan and items. That these spell the same bytes as the plan and items
that are read back, which `withinX_linkAtCfg` asks:
for the program's own value it is `chainsOf_link_own` (OnBytes/Tie/ChainsAtCfg.lean), for a digest
of 32 bytes and a string of fewer than 2^64 bytes. That the planner spells from the same plan and
items at every digest is `configure_at` (OnBytes/Tie/EntryPlanAtCfg.lean). c may be 32 zero bytes, a
digest at which three tests of the program refuse; no theorem here says that it then refuses every
file.





Only the entry file's chain is spoken of: one of the seven chains of a whole
call. All limits in the heads of the files named above hold here too. Nothing is said of the
program, which is the Lean text `verify-on-bytes`, beyond its functions that are named. For proofs
only; the program does not import this file.

-/
import OnBytes.Slice.OneWorldEntry
import OnBytes.Tie.ZeroAt
import Fmt.M1SpecKnownProofs
import Run.PlanPullM1
import OnBytes.Params.Spell
import OnBytes.Params.ToyDescriptions
import OnBytes.Params.EntryRounds
import OnBytes.Tie.EntryFile
import OnBytes.Params.EntrySizedLaws
import OnBytes.Tie.SpecXBase
import OnBytes.Slice.TopAny
import OnBytes.Slice.BaseAt
import OnBytes.Slice.BatAt
import OnBytes.Slice.CornersAt
import OnBytes.Slice.CsMet
import OnBytes.Slice.LinkSound
import OnBytes.Slice.CodeFacts
import OnBytes.Slice.MembFacts
import OnBytes.Slice.RoundsOf
import OnBytes.Slice.RoundsLink
import OnBytes.Entry.File
import Fmt.M3Items
import OnBytes.Params.EntryRoundsToy
import OnBytes.Slice.BatSem
import OnBytes.Slice.ManyClosesStd
import OnBytes.Slice.ManyHolds
import OnBytes.Params.EntryCheckIff
import OnBytes.Slice.ManyBlkWritten
import OnBytes.Slice.BlkLinkSeat
import OnBytes.Iop.Link
import OnBytes.Iop.Prox
import OnBytes.Slice.BlkJoints
import OnBytes.Slice.BlkSendCs
import OnBytes.Slice.BlkHead
import OnBytes.Slice.BlkHeadTie
import OnBytes.Slice.BlkTieFold
import OnBytes.Slice.ManyBlk
import OnBytes.Slice.ManyView
import OnBytes.Slice.ChainErrAny
import OnBytes.Slice.CsErr
import OnBytes.Slice.NoWorkRatesNum
import OnBytes.Slice.NoWorkRatesRound
import OnBytes.Slice.NoWorkRatesTail
import OnBytes.Slice.NoWorkRatesLink
import OnBytes.Slice.SemLib
import OnBytes.Slice.FoldAt
import OnBytes.Slice.ManyNumLink

set_option autoImplicit false

namespace OnBytes.Tie

/-- The parameters p of a link's chain with c in the place of the digest of the public files, and
the parameter bytes spelled anew from p's plan, c and p's items. -/
def linkAtCfg (p : Params.Link) (c : ByteArray) : Params.Link :=
  { p with given := { p.given with cfg := c,
                                   bytes := Fmt.paramsBytes p.given.plan c p.given.items } }

/-- The dry run of `Params.entryBlock`, the link's block at the keys `Params.plainKey`, does
not read the digest. -/
theorem entryRounds_linkAtCfg (p : Params.Link) (c : ByteArray) :
    Params.entryRounds (linkAtCfg p c) = Params.entryRounds p := rfl

/-- The number of answers that are stored for each row is the same at `linkAtCfg p c` as at p. -/
theorem answers_linkAtCfg (p : Params.Link) (c : ByteArray) :
    (linkAtCfg p c).link.table.answers = p.link.table.answers := rfl

/-- Parameter bytes that are spelled at two digests of one length have one length. -/
theorem size_paramsBytes (P : Fmt.Plan) (c c' : ByteArray) (I : List (String × ByteArray))
    (h : c.size = c'.size) : (Fmt.paramsBytes P c I).size = (Fmt.paramsBytes P c' I).size := by
  unfold Fmt.paramsBytes Fmt.item Fmt.textS Fmt.text
  simp only [ByteArray.size_append, Fmt.size_u64n, h]

/-- Parameter bytes begin with the parameter bytes of the same plan and digest without further
items. -/
theorem paramsBytes_prefix (P : Fmt.Plan) (c : ByteArray) (I : List (String × ByteArray)) :
    (Fmt.paramsBytes P c I).extract 0 (Fmt.paramsBytes P c []).size = Fmt.paramsBytes P c [] := by
  have e0 : Fmt.paramsBytes P c [] = Fmt.paramsHead P ++ Fmt.item Fmt.configName c := by
    unfold Fmt.paramsBytes Fmt.items
    simp only [List.map_nil, Fmt.cat_nil, ByteArray.append_empty]
  rw [e0]
  have h := Fmt.extract_mid ByteArray.empty (Fmt.paramsHead P ++ Fmt.item Fmt.configName c)
    (Fmt.items I)
  rw [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at h
  exact h

/-- The format's conditions on a description (`Fmt.Spec.ok`) read the digest and the parameter bytes
through three tests: the bytes' length, the digest's length, and that the bytes begin with the
spelling of the plan and the digest. If another digest and other bytes have the same two lengths and
the third test has the same value, the conditions have the same value. -/
theorem specOk_reCfg (B : Fmt.Spec) (c prm : ByteArray)
    (h1 : prm.size = B.params.size) (h3 : c.size = B.cfg.size)
    (h2 : (prm.extract 0 (Fmt.paramsBytes B.plan c []).size == Fmt.paramsBytes B.plan c []) =
      (B.params.extract 0 (Fmt.paramsBytes B.plan B.cfg []).size ==
        Fmt.paramsBytes B.plan B.cfg [])) :
    ({ B with cfg := c, params := prm } : Fmt.Spec).ok = B.ok := by
  unfold Fmt.Spec.ok Fmt.Spec.small
  dsimp only
  rw [h1, h2, h3]
  rfl

/-- The limits test reads the digest and the parameter bytes through these three tests alone. -/
theorem withinX_reCfg (S : Fmt.SpecX) (c prm : ByteArray)
    (h1 : prm.size = S.base.params.size) (h3 : c.size = S.base.cfg.size)
    (h2 : (prm.extract 0 (Fmt.paramsBytes S.base.plan c []).size ==
        Fmt.paramsBytes S.base.plan c []) =
      (S.base.params.extract 0 (Fmt.paramsBytes S.base.plan S.base.cfg []).size ==
        Fmt.paramsBytes S.base.plan S.base.cfg [])) :
    withinX { S with base := { S.base with cfg := c, params := prm } } = withinX S := by
  have e1 : Run.PQ.ok (inFile { S.base with cfg := c, params := prm }) =
      Run.PQ.ok (inFile S.base) := by
    unfold Run.PQ.ok
    rw [show (inFile { S.base with cfg := c, params := prm }).ok = (inFile S.base).ok from
      specOk_reCfg (inFile S.base) c prm h1 h3 h2]
    rfl
  have e2 : Run.PQ.rds (inFile { S.base with cfg := c, params := prm }) =
      Run.PQ.rds (inFile S.base) := Run.rds_congr _ _ rfl rfl
  unfold withinX Run.PQ.XD.ok
  show (Run.PQ.ok (inFile { S.base with cfg := c, params := prm }) &&
      Run.PQ.okX (Run.PQ.rds (inFile { S.base with cfg := c, params := prm }))
        (xdOf S fun _ _ => ByteArray.empty).a (xdOf S fun _ _ => ByteArray.empty).xs && _ && _ && _)
    = _
  rw [e1, e2]
  rfl

/-- The limits test has the same value at `linkAtCfg p c` as at p, for every list of rounds and
every statement, if c has the length of p's digest and p's parameter bytes are spelled from p's
plan, digest and items. -/
theorem withinX_linkAtCfg (p : Params.Link) (c : ByteArray) (rs : Params.Rounds) (st : ByteArray)
    (hc : c.size = p.given.cfg.size)
    (hp : p.given.bytes = Fmt.paramsBytes p.given.plan p.given.cfg p.given.items) :
    withinX (Params.entrySpecOf (linkAtCfg p c) rs st) = withinX (Params.entrySpecOf p rs st) := by
  refine withinX_reCfg (Params.entrySpecOf p rs st) c
    (Fmt.paramsBytes p.given.plan c p.given.items) ?_ hc ?_
  · show _ = p.given.bytes.size
    rw [hp]
    exact size_paramsBytes _ _ _ _ hc
  · show ((Fmt.paramsBytes p.given.plan c p.given.items).extract 0
        (Fmt.paramsBytes p.given.plan c []).size == Fmt.paramsBytes p.given.plan c []) =
      (p.given.bytes.extract 0 (Fmt.paramsBytes p.given.plan p.given.cfg []).size ==
        Fmt.paramsBytes p.given.plan p.given.cfg [])
    rw [hp, paramsBytes_prefix, paramsBytes_prefix, Run.PQ.bytes_beq_self,
      Run.PQ.bytes_beq_self]

/-- The library's four bounds on numbers, at the number of blocks that the description gives, have
the same value at `linkAtCfg p c` as at p: they read neither the digest nor the parameter bytes. -/
theorem fourBounds_linkAtCfg (p : Params.Link) (c : ByteArray) (rs : Params.Rounds)
    (x0 : ByteArray) :
    Run.PQ.fourBounds (inFile (Slice.entryS0 (linkAtCfg p c) rs x0).base)
        (xdOf (Slice.entryS0 (linkAtCfg p c) rs x0) bareStatement).K =
      Run.PQ.fourBounds (inFile (Slice.entryS0 p rs x0).base)
        (xdOf (Slice.entryS0 p rs x0) bareStatement).K := by
  have e : Run.PQ.kOf (inFile (Slice.entryS0 (linkAtCfg p c) rs x0).base) =
      Run.PQ.kOf (inFile (Slice.entryS0 p rs x0).base) := by
    unfold Run.PQ.kOf
    rw [Run.rds_congr (inFile (Slice.entryS0 (linkAtCfg p c) rs x0).base)
      (inFile (Slice.entryS0 p rs x0).base) rfl rfl]
    rfl
  show Run.PQ.fourBounds _ (Run.PQ.kOf (inFile (Slice.entryS0 (linkAtCfg p c) rs x0).base)) =
    Run.PQ.fourBounds _ (Run.PQ.kOf (inFile (Slice.entryS0 p rs x0).base))
  rw [e]
  rfl

/-- The description at `linkAtCfg p c` holds c as its digest. -/
theorem cfg_linkAtCfg (p : Params.Link) (c : ByteArray) (rs : Params.Rounds) (x0 : ByteArray) :
    (Slice.entryS0 (linkAtCfg p c) rs x0).base.cfg = c := rfl

/-- The rounds' data that the library makes of the description are the same at `linkAtCfg p c` as at
p. -/
theorem rds_linkAtCfg (p : Params.Link) (c : ByteArray) (rs : Params.Rounds) (x0 : ByteArray) :
    Run.PQ.rds (inFile (Slice.entryS0 (linkAtCfg p c) rs x0).base) =
      Run.PQ.rds (inFile (Slice.entryS0 p rs x0).base) :=
  Run.rds_congr _ _ rfl rfl

end OnBytes.Tie
