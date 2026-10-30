-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/PreThreePub.lean: one public algorithm for a reading of a call's files: it asks the
digest of the three public files and, at that answer, the digests of the seven chains' parameter
bytes; with the projections that the reading's parts take, what a bound asks of a public algorithm,
and its value under every family of oracle functions.

A bound on arms behind a reading of the files takes a public algorithm as a letter: no coin; public
strings alone; none twice. Here it is a term: `pubN` (Johnson/TypedOracleCompiler/RecCompile/PublicMany.lean) at the
string of the three public files and the strings of seven strings of parameter bytes. Definitions,
statements and proofs.

Main names:
  `D8`: the first answer and the list of the further ones.
  `par7 G pol KL lay c`: the parameter bytes at the bytes c for the digest: the entry's chain's as
    the ground G spells them; then, where the planner's text returns a plan at c, the proof's three
    and the key's three. Where it refuses: the entry's alone.
  `pub8`: THE PUBLIC ALGORITHM. `cfg8`, `ent8`, `prf8`: the projections for the entry file's and the
  proof file's parts.
    `key8`: the three answers for the key file's part.
  `pub8_noCoin`, `pub8_asks169`, `pub8_noRepeat`: what such a bound asks of a public algorithm.
  `pub8_det`: its value under g: g's answer at the string of the public files, and g's answers at
    the strings of the parameter bytes at that answer.
Limits: that the entry's parameter bytes as G spells them are the planner's is not used and not
said. No probability. Nothing on soundness.
A fixed hash, the format's earlier one, stands in `par7`, and so in `pub8`, under every drawn
function. The planner's text (`plannedAt`) hashes with it at seven places, which read the three
public files alone (the head of OnBytes/K/TopG.lean counts them): constants where the three public
files are fixed before g is drawn; here they are letters beside g (a reader's count at `publicOf`'s
text; no theorem). Which strings `pub8` asks hangs on these constants.

-/
import OnBytes.Tie.Decl.ProofPre
import Johnson.Top.Pub.PubMany

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm.Pub
open Rom TypedOracleCompiler.Slice TypedOracleCompiler.Compile.Batch.Cms
open _root_.Run (bytesToBits bytesToDig digToBytes oBits)
open _root_.Iop (Dig)
open OnBytes.Tie
open OnBytes.Model.Verify (planned configuration)

/-- The first answer and the list of the further ones. -/
abbrev D8 : Type := Dig 256 × List (Dig 256)

variable (G : EntryGround) (pol KL lay : ByteArray)

/-- The parameter bytes at the bytes c for the digest. -/
def par7 (c : ByteArray) : List ByteArray :=
  (entryXD G c).base.params ::
    match plannedAt pol KL (some lay) c with
    | .error _ => []
    | .ok p =>
      [p.chains.proof.first.given.bytes, p.chains.proof.shared.given.bytes,
        p.chains.proof.second.given.bytes, p.chains.key.oneTime.given.bytes,
        p.chains.key.shared.given.bytes, p.chains.key.second.given.bytes]

/-- THE PUBLIC ALGORITHM. -/
def pub8 : OComp (rom 256) D8 :=
  pubN Prod.mk (s0Of pol lay KL) (ssOf (par7 G pol KL lay))

/-- The answer at the string of the three public files. -/
def cfg8 (d : D8) : Dig 256 := d.1

/-- The answer at the string of the entry's chain's parameter bytes. -/
def ent8 (d : D8) : Dig 256 := d.2.getD 0 d.1

/-- The four answers that the proof file's part takes. -/
def prf8 (d : D8) : PubD := ⟨d.1, d.2.getD 1 d.1, d.2.getD 2 d.1, d.2.getD 3 d.1⟩

/-- The three answers for the key file's part. -/
def key8 (d : D8) : Dig 256 × Dig 256 × Dig 256 := (d.2.getD 4 d.1, d.2.getD 5 d.1, d.2.getD 6 d.1)

theorem pub8_noCoin : (pub8 G pol KL lay).NoCoin := pubN_noCoin _ _ _

/-- The public algorithm's value under g. -/
theorem pub8_det (g : Fam (rom 256)) : (pub8 G pol KL lay).det g =
    (g () (s0Of pol lay KL),
      (ssOf (par7 G pol KL lay) (g () (s0Of pol lay KL))).map (answerAt g)) :=
  pubN_det Prod.mk _ _ g

theorem pub8_noRepeat : NoRepeat (pub8 G pol KL lay) := pubN_noRepeat _ _ _

/-- Strings of calls with the number 169 alone. -/
theorem pub8_asks169 : (pub8 G pol KL lay).AsksIn
    fun _ (s : List Bool) => OnBytes.Slice.IsCall169 s :=
  pubN_asksIn_of _ _ _ OnBytes.Slice.IsCall169 ⟨0, 0, 2, Fmt.zero32, _, Or.inl rfl, rfl, rfl⟩
    fun c s hs => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hs
      exact ⟨0, 0, 1, Fmt.zero32, _, Or.inl rfl, rfl, rfl⟩

end OnBytes.K.Arm.Pub

#print axioms OnBytes.K.Arm.Pub.pub8_asks169
#print axioms OnBytes.K.Arm.Pub.pub8_det
