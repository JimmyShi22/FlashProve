-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Closed.lean: the arguments of the compiled verifier of one slot (verifyOneProtocol,
OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) for the proof file at the small size, as values made of a
planner's answer p, without the letters A, E, P of Johnson/Flat/WireAt.lean. Values for an
evaluation.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Each value is read off wireSmallAt (Johnson/Flat/WireAt.lean), whose third wire record and fourth
pair of maps name G alone. G := bigReqSmall p (Johnson/Flat/SmallAtFiles.lean).

Arguments that stay letters here: p (the planner's answer at the public files that are read from
disk); Kn (the number of blocks but one: KSmallAt has no code, since it reads seedBS's number; any
number that is at least kNeed p serves the proof file's rounds; no theorem here says that Kn is
KSmallAt (Gs p)); salt (the length of a salt in bytes); sMT, sFS.

What the front round and the joining round hold. tF and tJ (with the empty string in the third
place) are the values that stand in the shape where a silent round has sent nothing (plainRound):
they are made of the sample record of zeros and are no message of a file. A file's own front and
joining messages are arguments of typeFile (OnBytes/Maker/TypeFile.lean: pF, pJ, p3); silP tests
them against the instance's own record.

What a run at these values does not say (by reading, where no theorem or run is named).
  xin := some, where the arm has xinBA r₀: the first typed query holds the instance's own record
    where the arm's holds a fixed one: a string changes only if the page reads the record there.
  sizesSmall is typed, not read off p. Where the window of p parts from it, the links' block fails
    and guardP p says no. BY READING, NO TEST OF guardP p ON TOKENS SEES ANOTHER VOCABULARY: at the
    sample of zeros they ask 0 < V alone; guardP at such a plan has not been evaluated.
    Johnson/RunOne/ClosedGuard.lean has the test on the ten sizes (sizesOk), the test on the policy
    (policyOk) and all three in one (guardAll).
  reqOfFiles and xOf RETURN AT FILES THAT THE PROGRAM'S OWN READER OF REQUEST AND REPLY REFUSES:
    the builder takes a request file of fewer words and lays the reply into the window
    (Johnson/Top/InsReqRun.lean, 3, shows it of insReq).
    Johnson/RunOne/ClosedGuard.lean has the forms that refuse there (reqOfFilesG, xOfG): A RUN TAKES
    THOSE.
  THE HASH IS NOT AN ARGUMENT EVERYWHERE: the first of the two strings that the page reads out of
    the first query's instance (reqS) is the statement's item "request", five of whose groups of
    words are digests by the second hash function, a fixed function (secondHashFunction, secondHashFunctionTree,
    OnBytes/Hash/SecondHashFunction.lean), the request file's among them. At an oracle other than the programs'
    own that string is still made at the fixed function. The second string is rebuilt from the
    instance's tokens and numbers.
  p is a letter: whoever calls lays the planner's answer; that the planner's twin at an oracle and
    the program's planner agree is another file's.
  run1P, run2P, run3P are the right sides of inner steps in the proofs of det_run₁, det_run₂,
    det_run₃: the equations to run₁, run₂, run₃ at oracle functions are stated by no theorem
    of this library, and nothing here ties them to chainWhole or verifyP; cmsL, xo, salt, rtreq,
    ph, rts, pls are free.
  In the chains' half nothing hangs on x or on cms beyond its head: the record is tied in the
    decision alone.
  recOfKey pads and cuts silently; it does not test that the key fits the shape.

Limits. At the hollow carrier (Johnson/RunOne/Hollow.lean): the carrier of no theorem. The arm
(VBA, Johnson/TypedOracleCompiler/RecCompile/ProofAns.lean) asks the seed's test beside this slot's verifier: not
here. cm and the record come out of the entry file, not from the user: they are tied to the user's
commitment ID by the other parts of a whole verifier, not by this slot. Nothing on soundness.
The program does not import this file.

-/
import Johnson.Flat.SmallAtFiles
import Johnson.Flat.WireAt
import OnBytes.Flat.WireBlocks
import OnBytes.Flat.RecordCode
import OnBytes.K.Tokens
import Johnson.Flat.ItemOf
import OnBytes.Maker.LineAt
import OnBytes.TypedOracleCompiler.Joined.K.RunsLine
import Johnson.RunOne.Hollow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.RunOne
open VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Flat OnBytes.Slice OnBytes.Maker _root_.Run
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- An instance of the proof file's slot: a request and the record of the table that it names. -/
abbrev Yp : Type := ReqAt sizesSmall × RecSmall

/-- The stored table's depth at the small size. -/
def aS : ℕ := srS.P.T.a

/-- The kit of the format's second field (Fmt.Fld.two). -/
abbrev Cs : PQ.CK := ckP .two

section
variable (p : Model.Verify.Planned)

/-- The written data of the two big files at the small size. -/
def Gs : FilesParameters (ReqAt sizesSmall) RecSmall := bigReqSmall p

/-- The three lists of rounds of the proof file's dry runs at the sample. -/
def Ws : Three.Whole :=
  dataAt aS (dryProof (Gs p).c (keyOf (fun β : NZ => β.val) (Gs p).z₀.2)
    ((Gs p).block (Gs p).z₀.1))

/-- The data of the proof file's rounds. -/
def Ds : WholeD := WholeD.of aS (Ws p)

/-- It is the makers' own. -/
theorem Ds_eq : Ds p = dataPSmall (Gs p) := rfl

/-- The wire of Johnson/Flat/WireAt.lean has the data "at" the stored table's depth: that lays what
lies. -/
theorem Ds_at : (dataPSmall (Gs p)).at srS.P.T.a = Ds p := rfl

/-- What stands in the shape where the front round has sent nothing. -/
def tF : FrontMsg (List OnBytes.E) := front₀ (Gs p).z₀.2

/-- The same for the joining round. -/
def tJ : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray := join₀ (Gs p).z₀.2

/-- The proof file's decision: the makers' own. -/
def rn : Yp → PQ.View → PQ.View → PQ.View → Bool := runPSmall (Gs p)

/-- The test on the silent rounds' plain parts. -/
def sil : Yp → FrontMsg (List OnBytes.E) → Compile.Joined.JoinMsg (List OnBytes.E) ByteArray →
    ByteArray → Bool := silP

/-- **The description of the proof file's protocol.** -/
def Dsc := wholeDesc Cs (Ds p) (tF p) (tJ p) ByteArray.empty sil (rn p)

/-- The batch protocol that the compiled verifier runs. -/
def Qs := (Dsc p).batch

/-- The greatest number of blocks that a round of the proof file needs. -/
def kNeed : ℕ := blocksT .two ((Ds p).ds₁ ++ ((Ds p).ds₂ ++ (Ds p).ds₃))

/-- The same number by the format's own count, which walks no draw: (bsRound f e k).b =
blocksFor (wordsAtMost e k) where e.logN ≤ 64 (Run/PlanDraws.lean: planDraws_law). The equation
kFast p = kNeed p is not stated here. -/
def kFast : ℕ :=
  ((Ds p).ds₁ ++ ((Ds p).ds₂ ++ (Ds p).ds₃)).foldl
    (fun a d => max a (Fmt.blocksFor (Fmt.wordsAtMost d.entry d.kind))) 0

/-- **The guard.** Where it says no, Ds p is the data of three empty lists, every chain "returns"
over no round, and rn says no everywhere: a run says nothing. A run asks it, or refuses where one
of the data's three lists is empty (groundC, Johnson/RunOne/ProofGround.lean). -/
def guardP : Bool :=
  okAt aS (dryProof (Gs p).c (keyOf (fun β : NZ => β.val) (Gs p).z₀.2)
    ((Gs p).block (Gs p).z₀.1))

/-- Are there blocks enough? Where not, chalP fills with zero blocks: silently other draws. -/
def knOk (Kn : ℕ) : Bool := decide (kFast p ≤ Kn)

/-- **The wire record.** -/
def wq (Kn : ℕ) : ProtocolQueryLayout 256 (Kn + 1) (Qs p) :=
  wqWhole Cs Kn (chalP .two Kn) (Ds p) (tF p) (tJ p) ByteArray.empty sil (rn p)

/-- What of an instance is written first: the request with the reply 0 (G.early), and the record. -/
def earlyS : Yp → Yp := fun z => ((Gs p).early z.1, z.2)

/-- **The hollow carrier**: early as the three files' own; nothing comes late
(OnBytes/Flat/FilesAt.lean: late := none). -/
def Ls : BatchProtocolWithLeafBody Unit Yp := hollow (Qs p) (0, []) (earlyS p) none

/-- How a symbol of a prover's oracle is written into a leaf's body. -/
def embS (salt : ℕ) : (q : OPos (Qs p).loc.shape) → OSym (Qs p).loc.shape q → List Bool :=
  SCode.emb _ (scWhole salt Cs (Ds p) (tF p) (tJ p) ByteArray.empty)

/-- The depth of the request tree. -/
def depthReq : ℕ := (Gs p).depthReq

end

/-- How a symbol of the stored table is written into a leaf's body. -/
def embE (salt : ℕ) : PQ.SgX → List Bool := (TypedOracleCompiler.Run.PQ.bodyS aS salt).embE

/-- The instance is handed on whole. (The arm has xinBA r₀: the request, with a fixed record in
the record's place: Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean. One string for the first query if the page
reads the request alone.) -/
def xin : Yp → Option Yp := some

/-- The length in bits of an opening's salt: 256 and the wire's bytes of a salt
(Johnson/Maker/TypingAProof.lean [not in this library]: sMT := 256 + 8 * sb). -/
def sMTof (salt : ℕ) : ℕ := 256 + 8 * salt

/-- The length in bits of the chain's salt: the first chain's run value of 32 bytes
(OnBytes/Maker/TypingW.lean). -/
def sFSof : ℕ := 256

/-- The list that the session's chain is handed: the root twice, then the record's answers. -/
def cms (cm : Dig 256) (rec : RecSmall) : List (Dig 256) :=
  cm :: cm :: codeA rec.2

/-- **The record over the field that stands in a program's key**: nothing, unless there is a seed
and its factor is not 0. -/
def recOfKey (k : TableKey) : Option RecSmall :=
  match k.seeds with
  | [] => none
  | sd :: _ =>
    if h : readE sd.beta = 0 then none
    else some (fun _ => (fun t => readE (sd.z.getD t.val zeroE), ⟨readE sd.beta, h⟩),
      fun x => readE (k.record.getD (Sz.rowNo x.1 * 1 + x.2.val) zeroE))

/-- The request of the small size, from the tokens: (prompt, output), then the rest. -/
def reqOf := buildReqAt sizesSmall

/-! ### The user's side of the instance -/

/-- The user's request file and reply file as a statement: the tokens' readers
(OnBytes/K/Tokens.lean) read these two fields alone. -/
def stmOf (request y : ByteArray) : K.UserStm :=
  ⟨ByteArray.empty, ByteArray.empty, ByteArray.empty, request, y, {}⟩

/-- **The request of the small size off the user's two files**: as Flat.insReq at the full size:
the builder at the prompt, the output tokens and the further tokens. IT RETURNS AT FILES THAT THE
PROGRAM'S OWN READER REFUSES: a run takes reqOfFilesG (Johnson/RunOne/ClosedGuard.lean). -/
def reqOfFiles (request y : ByteArray) : Option (ReqAt sizesSmall) :=
  reqOf (K.promptOf (stmOf request y), K.outputOf (stmOf request y)) (K.auxOf (stmOf request y))

/-- **The instance**: the request off the user's files; the record is the parser's. IT RETURNS AT
FILES THAT THE PROGRAM'S OWN READER REFUSES: a run takes xOfG (Johnson/RunOne/ClosedGuard.lean). -/
def xOf (request y : ByteArray) (rec : RecSmall) : Option Yp :=
  (reqOfFiles request y).map fun q => (q, rec)

/-- **What the page reads out of the first query's instance**, two strings. The first: the
statement's item "request" at the instance (itemOf, Johnson/Flat/ItemOf.lean: Proof.requestItem at
the request file that says the instance); no bytes where there is none. The second: that request
file itself (requestBytesOf, Johnson/Flat/WordsBytes.lean), the value of the item "the request
file's words". Both read the request alone, not the record; at the request with the reply 0 they
are the same (itemOf_withoutReply, requestBytesOf_withoutReply). The second string is written from
the instance's tokens and numbers: that it is the user's own request file, byte for byte, holds
behind xOfG (reqOfFilesG_bytes, Johnson/RunOne/ClosedGuard.lean), not behind xOf. pol, KL: the
user's public files.
THE ITEM IS MADE AT THE FORMAT'S SECOND HASH FUNCTION, A FIXED FUNCTION, NOT THE ORACLE ARGUMENT
(secondHashFunction, secondHashFunctionTree, OnBytes/Hash/SecondHashFunction.lean), as are the planner's digests of the public files: five
of the item's groups of words are such digests, the request file's among them.
Fmt/RequestItem.lean has the item with that hash as an argument. -/
def reqS (pol KL : ByteArray) (z : Yp) : ByteArray × ByteArray :=
  ((itemOf pol KL z.1.val).getD ByteArray.empty, requestBytesOf z.1.val)

section
variable (p : Model.Verify.Planned) (Kn salt sMT sFS : ℕ)

/-- **The compiled verifier of the proof file's slot at these values.** -/
def verifyP (cm : Dig 256) (x : Yp) (π : OneProtocolProof 256 (Qs p)) : TypedOracleComputation 256 (Kn + 1) (Ls p) Bool :=
  verifyAt (Qs p) (0, []) (earlyS p) none sMT sFS (wq p Kn) (embS p salt) xin (embE salt)
    (depthReq p) (cms cm x.2) x π

/-- Its first half: the chain alone. -/
def chainWhole (cm : Dig 256) (x : Yp) (π : OneProtocolProof 256 (Qs p)) :=
  chainAt (Qs p) (0, []) (earlyS p) none (wq p Kn) xin (cms cm x.2) x π

end

/-! ## The three chains in the thin form

OnBytes/TypedOracleCompiler/Run/ThinDefs.lean: chainP takes no Shape, BatchInteractiveOracleProof or BatchProtocolWithLeafBody at run time, but a list of
skeleton rounds; the carrier stands behind a function of Unit that is never called. The terms below
are the right sides of inner steps in the proofs of det_run₁, det_run₂, det_run₃
(OnBytes/TypedOracleCompiler/Joined/K/RunsLine.lean), at the letters of chainsOf_line, hw₁, hw₂, hw₃
(OnBytes/Maker/LineAt.lean). No run that we know calls run1P, run2P, run3P. -/

section Thin
open TypedOracleCompiler.Joined.K (annW₂ wireW₂ embL₁ embL₂ embL₃)
open TypedOracleCompiler.Run.PQ (SL wiresSL)
open _root_.Run.Twin (RS up allLo)
variable (p : Model.Verify.Planned) (Kn : ℕ)

/-- The front round, the joining round and the seam as skeletons. -/
abbrev rF : RS := plainRS _ (tF p)
abbrev rJ : RS := plainRS _ (tJ p)
abbrev r3 : RS := plainRS ByteArray ByteArray.empty

/-- The joining round is shared. -/
abbrev aJ : RAnn (rJ p).up := RAnn.ofShared .sh _

/-- The three stretches' data. -/
def d1 : List TypedOracleCompiler.Run.PQ.RD := toRDs (Ds p).ds₁
def d2 : List TypedOracleCompiler.Run.PQ.RD := toRDs (Ds p).ds₂
def d3 : List TypedOracleCompiler.Run.PQ.RD := toRDs (Ds p).ds₃

/-- The typed round at which the second chain begins, and the third. -/
def i2 : ℕ := 1 + (d1 p).length
def i3 : ℕ := 1 + (d1 p).length + (1 + (d2 p).length)

variable (g : Fam (typedOracleFamily 256 (Kn + 1) (Ls p))) (cmsL : List (Dig 256)) (xo : Option Yp)
  (salt : Bits) (rtreq : Dig 256)

/-- **The first chain's value at oracle functions g.** -/
def run1P (rts : List (Dig 256)) (pls : Plains (up (rF p :: SL Cs (d1 p)))) :=
  TypedOracleCompiler.Run.Thin.chainP (fun _ => Ls p) g (earlyS p) none .onl cmsL xo salt rtreq
    (rF p :: SL Cs (d1 p))
    ((rF p).lo, allLo (SL Cs (d1 p)))
    (wireSilent (Kn + 1) _ (tF p) (rF p).lo, wiresSL Cs Kn (chalP .two Kn) (d1 p))
    (embL₁ (L := Ls p) (t := .onl) (rJ := rJ p) (r3 := r3) (aJ := aJ p) (ds₂ := d2 p)
      (ds₃ := d3 p) id) 0 .first rts pls

/-- **The second chain's**, from a phase ph and the roots that are left. -/
def run2P (ph : Phase 256) (rts : List (Dig 256)) (pls : Plains (up (rJ p :: SL Cs (d2 p)))) :=
  TypedOracleCompiler.Run.Thin.chainP (fun _ => Ls p) g (earlyS p) none .onl cmsL xo salt rtreq
    (rJ p :: SL Cs (d2 p))
    (annW₂ Cs (rJ p) (aJ p) (d2 p))
    (wireW₂ Cs Kn (chalP .two Kn) (rJ p) (aJ p) (wireSilent (Kn + 1) _ (tJ p) _) (d2 p))
    (embL₂ (L := Ls p) (t := .onl) (rF := rF p) (r3 := r3) (ds₁ := d1 p) (ds₃ := d3 p) id)
    (i2 p) ph rts pls

/-- **The third chain's.** -/
def run3P (ph : Phase 256) (rts : List (Dig 256)) (pls : Plains (up (r3 :: SL Cs (d3 p)))) :=
  TypedOracleCompiler.Run.Thin.chainP (fun _ => Ls p) g (earlyS p) none .onl cmsL xo salt rtreq
    (r3 :: SL Cs (d3 p))
    (r3.lo, allLo (SL Cs (d3 p)))
    (wireSilent (Kn + 1) _ ByteArray.empty r3.lo, wiresSL Cs Kn (chalP .two Kn) (d3 p))
    (embL₃ (L := Ls p) (t := .onl) (rF := rF p) (rJ := rJ p) (aJ := aJ p) (ds₁ := d1 p)
      (ds₂ := d2 p) id) (i3 p) ph rts pls

end Thin

end Johnson.RunOne
