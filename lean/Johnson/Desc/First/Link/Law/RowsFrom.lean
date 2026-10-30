-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/RowsFrom.lean: THE SECOND READING OF THE THREE PUBLIC FILES
(`Johnson.G.sendRowsOf`, Johnson/G/LinkSig.lean) AS A FUNCTION OF JUST WHAT IT READS OF THE
PLANNER's VALUE. Definitions with code (second texts), and theorems by unfolding. A law file; no
running text imports it.
Arm, armOf, nArm, nMomentsA, nFrameA and callsFrom stand in the running file
Johnson/Desc/First/Link/RowsRun.lean, which this file imports.
Arm bears no instances there: they are derived here.

Why. sendRowsOf calls Model.Verify.planned three times and reads the files nowhere else: it is a
function of the planner's value p and of the layout file. But p holds the eight free numbers of the
parameter file and the scales, so two sets of files in scope have two values p: a congruence in p
never fires. OF p IT READS: (i) p.chains.made; (ii) of shapesOf p.X (some lay): sub.openRows and
sub.pendingRows; (iii) p.X through
`nLink` alone (Johnson/G/Calls.lean): for each link one of three noted routines with its sizes.
  `Arm`, `armOf X link`   (iii) as plain data, with decidable equality: the head's, a layers' or an
                    attention's routine with its arguments; or none.
  `nArm`, `nLink_arm`   nLink X link moment = nArm (armOf X link) moment.
  `nMomentsA`, `nFrameA`, `nMoments_arm`, `nFrame_arm`   the two routines above it, over a table of
                    arms.
  `callsFrom c openRows pendingRows A`, `callsOf_of`   callsOf's text behind its planner.
  `packFrom`, `packListOf_of` · `rowsFrom`, `sendRowsOf_of`   where planned returns p and shapesOf
                    returns shapes: sendRowsOf pol lay KL =
                    rowsFrom p.chains.made shapes.sub.openRows shapes.sub.pendingRows (armOf p.X).
  `rows_congr`      so two sets of files at which these four agree have one second reading.

Limits. SECOND TEXTS of Calls.lean's nMoments | nFrame | callsOf, PackList.lean's packListOf and
LinkSig.lean's sendRowsOf: tied to them by the theorems here; they will have to be turned with them.
That the four arguments are the same at all files in scope is NOT shown. That rowsFrom returns is
shown nowhere. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.Link.RowsRun
import Johnson.G.LinkSig
import Johnson.Desc.Ok.NumberPrices.AtDigest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open VerifiableInference.Number (sendsFrom)

deriving instance DecidableEq, Repr, Inhabited for Arm

theorem nLink_arm (X : OnBytes.Model.Verify.Public) (link moment : Nat) :
    nLink X link moment = nArm (armOf X link) moment := by
  unfold nLink armOf
  dsimp only
  generalize (if X.p4 = true then 2 else 1) = step
  by_cases h1 : (link == step * X.NGr) = true
  · rw [if_pos h1, if_pos h1]
    rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : (link % step == 0) = true
    · rw [if_pos h2, if_pos h2]
      cases X.G[link / step]? <;> rfl
    · rw [if_neg h2, if_neg h2]
      cases X.A[link / step]? <;> rfl

theorem nMoments_arm (X : OnBytes.Model.Verify.Public) (z : ProofSized) (l : Nat)
    (msgs : List ReqMessage) : ∀ fuel moment,
    nMoments X z l msgs fuel moment = nMomentsA (armOf X) z l msgs fuel moment
  | 0, _ => rfl
  | fuel + 1, moment => by
    unfold nMoments nMomentsA
    simp only [nLink_arm, nMoments_arm X z l msgs fuel]

theorem nFrame_arm (X : OnBytes.Model.Verify.Public) (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat)
      (before : GroupSize),
    nFrame X z l gs links open_ before = nFrameA (armOf X) z l gs links open_ before
  | [], _, _, _, _ => by
    unfold nFrame nFrameA
    rfl
  | g :: gs, l, links, open_, before => by
    unfold nFrame nFrameA
    simp only [nLink_arm, nMoments_arm, nFrame_arm X z gs]
    rfl

section
variable {pol lay KL : ByteArray} {p : OnBytes.Model.Verify.Planned}
  {ls : Array OnBytes.Model.Stages.LinkH} {shapes : Shapes}

theorem callsOf_of (hp : OnBytes.Model.Verify.planned pol KL (some lay) = .ok p)
    (hs : OnBytes.Model.Verify.shapesOf p.X (some lay) = .ok (ls, shapes)) :
    callsOf pol lay KL =
      callsFrom p.chains.made shapes.sub.openRows shapes.sub.pendingRows (armOf p.X) := by
  unfold callsOf callsFrom
  rw [hp]
  simp only [bind, Except.bind]
  rw [hs]
  simp only [nFrame_arm]
  rfl

theorem sendsOf_of (hp : OnBytes.Model.Verify.planned pol KL (some lay) = .ok p) :
    sendsOf pol lay KL = sendsFrom p.chains.made := by
  rw [VerifiableInference.Number.sendsOf_eq, hp]
  rfl

end

/-- `packListOf`'s text behind its two readings. -/
def packFrom (c : Configured) (openRows : List Nat) (pendingRows : Nat) (A : Nat → Arm) :
    Except String (List (Codes × List (OracleShape × Nat))) := do
  let (s, chains) ← callsFrom c openRows pendingRows A
  let sends ← sendsFrom c
  let per ← (chains.zip sends).mapM fun (c, d) => do
    let smp := c.calls.flatMap Call.sendSamples
    unless smp.length == d.sends.length do
      throw s!"{c.file} {c.chain}: the calls and the list have not as many sendings"
    (smp.zip d.sends).mapM fun (o, x) => do
      let at_ := s!"{c.file} {c.chain}, entry {x.entry} ({x.label})"
      let sampled := (x.sent.filter fun m => 0 < m.shape.answers).map (·.shape)
      let o' :=
        if o.length == sampled.length then o
        else if o.length == 1 then List.replicate sampled.length (o.headD ⟨0, []⟩) else []
      unless o'.length == sampled.length do
        throw s!"{at_}: the sampled messages and the samples are not as many"
      let l ← (sampled.zip o').mapM fun (sh, sm) => do
        pure (sh, ← radiusFor s d.codes at_ sh sm)
      unless x.behind.answers == l.length * s.samples do
        throw s!"{at_}: (p3) the entry behind takes in another number of answers"
      unless x.seed.drawE == s.samples * (Johnson.Pack.bMax d.codes l + 1) do
        throw s!"{at_}: (p4) the entry draws another number of elements"
      pure (d.codes, l)
  pure per.flatten

/-- `sendRowsOf`'s text behind its two readings. -/
def rowsFrom (c : Configured) (openRows : List Nat) (pendingRows : Nat) (A : Nat → Arm) :
    Except String (List SendRow) := do
  let sends ← sendsFrom c
  let pack ← packFrom c openRows pendingRows A
  let flat := sends.flatMap fun c => c.sends.map fun s => (c, s)
  unless flat.length == pack.length do throw "the two lists have not as many sendings"
  pure ((flat.zip pack).map fun ((c, s), p) =>
    ⟨c.file, c.chain, s.entry, s.label, c.codes, p.2,
      (s.sent.filter fun m => m.shape.answers == 0).map (·.shape)⟩)

section
variable {pol lay KL : ByteArray} {p : OnBytes.Model.Verify.Planned}
  {ls : Array OnBytes.Model.Stages.LinkH} {shapes : Shapes}

theorem packListOf_of (hp : OnBytes.Model.Verify.planned pol KL (some lay) = .ok p)
    (hs : OnBytes.Model.Verify.shapesOf p.X (some lay) = .ok (ls, shapes)) :
    packListOf pol lay KL =
      packFrom p.chains.made shapes.sub.openRows shapes.sub.pendingRows (armOf p.X) := by
  unfold packListOf packFrom
  rw [callsOf_of hp hs, sendsOf_of hp]

/-- **The second reading, as a function of just what it reads.** -/
theorem sendRowsOf_of (hp : OnBytes.Model.Verify.planned pol KL (some lay) = .ok p)
    (hs : OnBytes.Model.Verify.shapesOf p.X (some lay) = .ok (ls, shapes)) :
    sendRowsOf pol lay KL =
      rowsFrom p.chains.made shapes.sub.openRows shapes.sub.pendingRows (armOf p.X) := by
  unfold sendRowsOf rowsFrom
  rw [packListOf_of hp hs, sendsOf_of hp]

end

/-- So two sets of files at which the four agree have one second reading. -/
theorem rows_congr {pol lay KL pol' lay' KL' : ByteArray} {p p' : OnBytes.Model.Verify.Planned}
    {ls ls' : Array OnBytes.Model.Stages.LinkH} {shapes shapes' : Shapes}
    (hp : OnBytes.Model.Verify.planned pol KL (some lay) = .ok p)
    (hs : OnBytes.Model.Verify.shapesOf p.X (some lay) = .ok (ls, shapes))
    (hp' : OnBytes.Model.Verify.planned pol' KL' (some lay') = .ok p')
    (hs' : OnBytes.Model.Verify.shapesOf p'.X (some lay') = .ok (ls', shapes'))
    (e1 : sendsFrom p.chains.made = sendsFrom p'.chains.made)
    (e2 : p.chains.made.sized = p'.chains.made.sized) (e3 : p.chains.made.key = p'.chains.made.key)
    (e4 : p.chains.made.proof = p'.chains.made.proof)
    (e5 : p.chains.made.entry = p'.chains.made.entry)
    (e6 : shapes.sub.openRows = shapes'.sub.openRows)
    (e7 : shapes.sub.pendingRows = shapes'.sub.pendingRows) (e8 : armOf p.X = armOf p'.X) :
    sendRowsOf pol lay KL = sendRowsOf pol' lay' KL' := by
  rw [sendRowsOf_of hp hs, sendRowsOf_of hp' hs']
  unfold rowsFrom packFrom callsFrom
  rw [e1, e2, e3, e4, e5, e6, e7, e8]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.sendRowsOf_of
#print axioms VerifiableInference.Desc.LinkJoin.rows_congr
#print axioms VerifiableInference.Desc.LinkJoin.callsOf_of
#print axioms VerifiableInference.Desc.LinkJoin.nLink_arm
#print axioms VerifiableInference.Desc.LinkJoin.nFrame_arm
