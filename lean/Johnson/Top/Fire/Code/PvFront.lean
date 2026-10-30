-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/PvFront.lean


-/
import Johnson.Top.ArmsAtFiles
import Johnson.Top.ArmsAtFilesSmall
import Johnson.Top.PreThreePub
import Johnson.Top.Pub.PubMany
import Johnson.Flat.LedgerClaim
import Johnson.Flat.ClaimsTrue
import OnBytes.Flat.WireBlocks
import Johnson.Top.Fire.Code.PvFrontK
/-! The front of the one command, in one file, with code: what a harness needs before verifyV: the
three public files; four tests to be asked by name first; the two public readings on bytes; the
commitment off ID.txt; the user's prompt and output off the request file and the token file; twelve
letters of DvOf. Every value is a function of the public files' bytes alone, but the readings and
the two functions on the user's files.

`idOf` and `userOf` turn the user's three files into the commitment ID, the prompt and the output
that `verify` takes. `PV.Program.claimOf` (Johnson/PVR/Program.lean) calls them, behind tests of its
own on the two files' sizes and on r, e and the next token. No theorem says that they split the
files as the format page means (docs/format/FORMAT.md, 12.2) or as the C++ verifier `cp_verify`
does: lean/GAPS.md, 37. -/
set_option autoImplicit false
namespace PV.Front
open OnBytes OnBytes.K OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.K.ArmsAtFiles
    OnBytes.K.Arm.Pub
open OnBytes.Tie VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Run (bytesToDig digToBytes)

/-! ### 1. The files -/
def readZ (dir : String) : IO Pub := do
  pure ⟨← IO.FS.readBinFile (dir ++ "/config/policy.txt"), ← IO.FS.readBinFile (dir ++
      "/config/layout.txt"),
    ← IO.FS.readBinFile (dir ++ "/config/KL.bin")⟩

def hex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    String.ofList [Nat.digitChar (x.toNat / 16), Nat.digitChar (x.toNat % 16)])

/-- The commitment off ID.txt: 64 hex signs, then at most a newline. none at any other text. -/
def idOf (txt : ByteArray) : Option ByteArray :=
  let h := (txt.extract 0 64).toList
  let rest := (txt.extract 64 txt.size).toList
  if h.length = 64 ∧ h.all (fun b => (48 ≤ b && b ≤ 57) || (97 ≤ b && b ≤ 102)) ∧ rest.length ≤ 1 ∧
      rest.all (· == 10) then
    some (Fmt.unhex (String.ofList (h.map fun b => Char.ofNat b.toNat)))
  else none

/-! ### 2. The two public readings, on bytes -/
def cBytes (Z : Pub) : ByteArray := Params.configurationDigest [Z.pol, Z.lay, Z.KL]
def parBytes (G : EntryGround) (Z : Pub) (c : ByteArray) : List ByteArray := par7 G Z.pol Z.KL Z.lay
    c
def moreBytes (G : EntryGround) (Z : Pub) (c : ByteArray) : List ByteArray :=
  (parBytes G Z c).map fun b => Fmt.formatHash 169 0 1 Fmt.zero32 b

/-! ### 3. Four tests for a print's first lines, each by name -/
/-- The planner returns. Where it refuses, every letter off bigZ… is a stand-in's, in silence. -/
def planOkB (Z : Pub) : Bool := match planOf Z with | .ok _ => true | .error _ => false
/-- What is hashed is within the hash's bound on lengths: the premises of the two equations. -/
def sizesB (G : EntryGround) (Z : Pub) (c : ByteArray) : Bool :=
  decide ((Fmt.configBytes [Z.pol, Z.lay, Z.KL]).size ≤ 2 ^ 32 - 144) &&
    (parBytes G Z c).all fun b => decide (b.size ≤ 2 ^ 32 - 144)
/-- The entry's parameter bytes as the typed ground spells them are the planner's own for that chain
(a control: it catches a wrong ground). -/
def groundFitsB (G : EntryGround) (Z : Pub) (c : ByteArray) : Bool :=
  match plannedAt Z.pol Z.KL (some Z.lay) c with
  | .ok p => decide ((TypedOracleCompiler.Slice.entryXD G c).base.params.data = (p.chains.bytes .link).data)
  | .error _ => false
/-- Seven strings. -/
def sevenB (G : EntryGround) (Z : Pub) (c : ByteArray) : Bool := (parBytes G Z c).length == 7

/-! ### 4. The user's side -/
/-- The user's side of a claim, off the request file and the token file, at a request of `T` tokens.
Both files are read as words of four bytes, the lowest byte first; bytes after the last whole word
are left out (`Model.Verify.words32`). `none` unless the request file has `T + 2` such words and the
token file one. Else write tok for the first `T` words, tokens 0 to `T` - 1; r and e for the last
two; and y for the token file's word, which counts as token number `T`. The result is three lists.
Where r < e ≤ `T` they are: the prompt, tokens 0 to r; the output, tokens r + 1 to e, which holds y
just where e = `T`; and the tokens of tok after position e, which are no part of the claim.
No test is made here on r, e or y, nor on a file's bytes after its last whole word. Where e ≤ r the
output is empty; where `T` ≤ r the prompt is all of tok and the output is empty; where r < e and
`T` < e the output is shorter than e - r. `PV.Program.claimOf` (Johnson/PVR/Program.lean) asks
`callOk` first, which makes these tests. -/
def userOf (T : ℕ) (req y : ByteArray) : Option ((List Token × List Token) × List Token) :=
  let P := (Model.Verify.words32 req).toList.map (·.toNat)
  let Q := (Model.Verify.words32 y).toList.map (·.toNat)
  if P.length = T + 2 ∧ Q.length = 1 then
    let tok := P.take T
    let r := P.getD T 0
    let e := P.getD (T + 1) 0
    some ((tok.take (r + 1), ((tok ++ Q).drop (r + 1)).take (e - r)), tok.drop (e + 1))
  else none

/-! ### 5. Nine letters of DvOf (K · r₀ · num: PvFrontK.lean, PvFrontNum.lean) -/
def rKSmall (Z : Pub) : RecSmall := (bigZSmall Z).rec₀
def rPSmall (Z : Pub) : RecSmall := (bigZSmall Z).z₀.2
def depthReqSmall (Z : Pub) : ℕ := (bigZSmall Z).depthReq
def depthReqTSmall (Z : Pub) : ℕ := (bigZSmall Z).k.oneTime.binding.logLeaves
def earlySmall (Z : Pub) : ReqAt sizesSmall → ReqAt sizesSmall := (bigZSmall Z).early
def saltSmall (Z : Pub) : ℕ := (bigZSmall Z).k.oneTime.given.plan.salt
def buildSmall' : List Token × List Token → List Token → Option (ReqAt sizesSmall) := buildReqAt
    sizesSmall
def pSmall (Z : Pub) : _root_.Compile.Params := ⟨256 + 8 * saltSmall Z, 256, 0, 0⟩
def rKFull (Z : Pub) : RecFull := (bigZFull Z).rec₀
def rPFull (Z : Pub) : RecFull := (bigZFull Z).z₀.2
def depthReqFull (Z : Pub) : ℕ := (bigZFull Z).depthReq
def depthReqTFull (Z : Pub) : ℕ := (bigZFull Z).k.oneTime.binding.logLeaves
def earlyFull (Z : Pub) : Flat.Req → Flat.Req := (bigZFull Z).early
def saltFull (Z : Pub) : ℕ := (bigZFull Z).k.oneTime.given.plan.salt
def buildFull : List Token × List Token → List Token → Option Flat.Req := Flat.buildReq
def pFull (Z : Pub) : _root_.Compile.Params := ⟨256 + 8 * saltFull Z, 256, 0, 0⟩
/- K · r₀ · numNoTest (A STAND-IN): PvFrontK.lean. The test of the stored copy's number: numCopy,
  PvFrontNum.lean. -/

/-! ### 5b. The test on the number of blocks: no round of the three
  files asks
more than K blocks, and the record's seed has blocks enough in K + 1 -/
/-- The blocks that the record's seed reads: (seedBS 19 1).b | (seedBS recLg recS).b, by
  seedBS_b. -/
def seedBlocksSmall : ℕ := Fmt.blocksFor (1 * (19 * 18 + 36))
def seedBlocksFull : ℕ := Fmt.blocksFor (recS * (recLg * 18 + 36))
theorem seedBlocksSmall_eq : seedBlocksSmall = (seedBS 19 1).b := (seedBS_b 19 1).symm
theorem seedBlocksFull_eq : seedBlocksFull = (seedBS recLg recS).b := (seedBS_b recLg recS).symm
def blocksFitSmallB (DK DP : WholeD) (K : ℕ) : Bool :=
  decide (kThree .two DK srD.ds DP ≤ K) && decide (seedBlocksSmall ≤ K + 1)
def blocksFitFullB (DK DP : WholeD) (K : ℕ) : Bool :=
  decide (kThree .two DK frD.ds DP ≤ K) && decide (seedBlocksFull ≤ K + 1)

/-! ### 6. A print's first lines -/
def firstLines (name dir : String) (G : EntryGround) (T : ℕ)
    (builds : List Token × List Token → List Token → Bool) (standIns : String) : IO Bool := do
  let Z ← readZ dir
  let c := cBytes Z
  let id := idOf (← IO.FS.readBinFile (dir ++ "/ID.txt"))
  let u := userOf T (← IO.FS.readBinFile (dir ++ "/example.req")) (← IO.FS.readBinFile (dir ++
      "/example.y"))
  let t := [("planOkB", planOkB Z), ("sizesB", sizesB G Z c), ("groundFitsB", groundFitsB G Z c),
    ("sevenB", sevenB G Z c), ("c has 32 bytes", c.size == 32), ("the ID reads", id.isSome),
    ("the request reads", u.isSome), ("the request builds", (u.map fun v => builds v.1 v.2).getD
        false)]
  IO.println s!"[{name}] files: policy.txt {Z.pol.size} · layout.txt {Z.lay.size} · \
      KL.bin {Z.KL.size} bytes | c {hex c} | ID {(id.map hex).getD "-"}"
  IO.println s!"[{name}] THE FRONT's TESTS, EACH DUE true: {t}"
  IO.println s!"[{name}] STAND-INS OF THE FRONT, AS THE CALLER NAMES THEM: {standIns}"
  pure (t.all (·.2))

end PV.Front
