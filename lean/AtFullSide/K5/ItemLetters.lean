-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K5/ItemLetters.lean: the letters for the clause on the request's item (the field "item" of "StartHeld",
E2E/StartAtFiles.lean) at the stored full-size public files (VerifierAndGoals.storedPublicFiles): the pieces of that clause in forms that
Lean's kernel reduces, each with the law that ties it to the library's own text. Definitions and small laws; nothing is
evaluated here.

Why. The clause says: the request's item is made (Fmt.requestItem), and the comparison of that item with the public
part accepts (Verify.statementHeld). Asked outright at the stored files, the kernel does not get through. By the heads
of the files named below it is slow at a text's bytes and does not reduce String.splitOn or the format's second hash function;
in our own trials it also refused one line that asked the layers' calls off the layout's value, and one that asked the
head's layout whole: why was not looked into. For each the library has a form that it does reduce:
  the parameter file's bytes   the written lists of Johnson/Goal/Meaning/ScopeBytes.lean and ScopeLines.lean
  the earlier hash             its form off the head of a list (Johnson/Unfolds/SecondHashFunctionList.lean)
  the layers' calls            what "takeCalls" takes of the call lines, placed (calls_of_base,
                               Johnson/Goal/Meaning/Pub34Scope.lean)
  the head's calls             "numbers" and "callsOf" (as in LaidW, Johnson/AtFull/Head/LayoutAtFull.lean)

  pol_toList        at all free numbers v: the parameter file's bytes are the written lists
  polL, readL, linesL, read_zFull   the item's reader of the lines at the stored file is the reader at these lists
  olderKF, olderK_fun   the earlier hash is its list form, as functions
  reqW, reqW_size   a string of the request file's length
  requestItem_eq    general: the item's text with its five digests laid out
  itemBy, requestItem_at   the item at the written lines, at a hash k and a number for the request's size
  layerCalls, layerCalls_eq, headCalls, headCalls_eq   the two lists of calls
  digestsOf, digestsAt, digests_at   the three digests of lists of calls as the public part has them
  heldBy, statementHeld_by   the comparison's own condition as a function of the two fields that it reads
  clauseBy          the whole clause as a yes or no; n: the request's size; f: a turn of the digests, for controls

Limits. One example: VerifierAndGoals.storedPublicFiles. The forms are tied by laws, not by evaluation. "heldBy" repeats the text of
"statementHeld": the law statementHeld_by holds the two together by rfl, so a change of that text breaks this file.
No property of the protocol is claimed: nothing on soundness, completeness or what anything reveals.
-/
import Johnson.Goal.Meaning.ScopeLines
import Johnson.Goal.Meaning.Pub34Scope
import Johnson.Goal.Files.FilesReadProof
import Johnson.AtFull.Public.Join
import Johnson.AtFull.Head.LayoutAtFull
import Johnson.Unfolds.SecondHashFunctionList
import OnBytes.Model.VerifyStatement
import Fmt.RequestItem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K5.Item
open VerifierAndGoals VerifierAndGoals.Lines
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open OnBytes.Road.K4.Trial.Values (PW hW yBase yFull values_W)
open VerifiableInference.Desc.Kinds.Head.Law (Cond.hFull)
open VerifiableInference.PlanWritten (callsDigestO)
open Johnson.Unfolds

/-! ## 1 The parameter file's lines -/

/-- **The bytes of the parameter file at free numbers v are the written lists.** -/
theorem pol_toList (v : FreeLines) :
    (policyFile v).toList = concatenatedWithLineFeeds frameLines ++ (linesAt v).flatten := by
  rw [← linesOf_behind v, ConfigReaders.flatten_linesOf, ← frame_bytes, policyFile_eq,
    K.Left.toList_data, K.Left.toList_data, ByteArray.data_append, Array.toList_append,
    ConfigReaders.bytesOf_data]

/-- The stored parameter file's bytes. -/
def polL : List UInt8 := concatenatedWithLineFeeds frameLines ++ (linesAt storedLines).flatten

/-- The item's reader of the lines, at a list of bytes. -/
def readL (l : List UInt8) : Fmt.ReqLines :=
  ⟨((Fmt.splitAt 0x0A l).filter fun l => !l.isEmpty).map (Fmt.splitAt 0x20)⟩

/-- The stored parameter file's lines, as the item's reader cuts them. -/
def linesL : Fmt.ReqLines := readL polL

theorem read_zFull : Fmt.ReqLines.read storedPublicFiles.pol = linesL := by
  unfold Fmt.ReqLines.read linesL readL polL
  rw [pol_zFull, pol_toList]

/-! ## 2 The hash -/

/-- The format's second hash function, read off the head of a list of bytes. -/
def olderKF (num : Nat) (w : ByteArray) : ByteArray := olderKL num w.size w.data.toList

theorem olderK_fun : secondHashFunction = olderKF := by
  funext num w
  exact olderK_eq_list num w

/-! ## 3 The item -/

/-- A request file's length of zero bytes. -/
def reqW : ByteArray := ⟨Array.replicate 4104 0⟩

theorem reqW_size : reqW.size = 4104 := by
  show (Array.replicate 4104 (0 : UInt8)).size = 4104
  exact Array.size_replicate

/-- General: the item's text with its five digests laid out. -/
theorem requestItem_eq (k : Nat → ByteArray → ByteArray) (pol KL req : ByteArray) :
    Fmt.requestItem k pol KL req =
      Fmt.requestItemOf (Fmt.ReqLines.read pol) req.size ((Fmt.ReqLines.read pol).calls k "call")
        (Fmt.olderTK k KL) ((Fmt.ReqLines.read pol).calls k "callA")
        ((Fmt.ReqLines.read pol).calls k "callH" (some Fmt.callHIfNone)) (Fmt.olderTK k req) := rfl

/-- The item at the written lines, at a hash k. n: the number that stands for the request's size. -/
def itemBy (k : Nat → ByteArray → ByteArray) (n : Nat) : Option ByteArray :=
  Fmt.requestItemOf linesL n (linesL.calls k "call") (Fmt.olderTK k storedPublicFiles.KL)
    (linesL.calls k "callA") (linesL.calls k "callH" (some Fmt.callHIfNone)) (Fmt.olderTK k reqW)

theorem requestItem_at (k : Nat → ByteArray → ByteArray) :
    Fmt.requestItem k storedPublicFiles.pol storedPublicFiles.KL reqW = itemBy k 4104 := by
  unfold itemBy
  rw [requestItem_eq, read_zFull, reqW_size]

/-! ## 4 The three digests of lists of calls -/

/-- The layers' calls, as the first half of the layers' layout places them. -/
def layerCalls : Option (List CallD) :=
  (Layer.takeCalls (Layer.segmentList hW (hW.H * hW.dh + hW.Gk * hW.dh) (hW.Gk * hW.dh))
    (if callsRef.isEmpty then Layer.builtInCalls hW.p3 else callsRef) [] []).toOption.map fun taken =>
      taken.1.map fun c => place c.1 c.2.1 c.2.2 (hW.nmin - hW.ll - hW.lt)

theorem layerCalls_eq : layerCalls = some yFull.calls.toList := by
  obtain ⟨taken, ht, hc⟩ := Meaning.P34.calls_of_base values_W.1
  have e : yFull.calls = yBase.calls := rfl
  unfold layerCalls
  rw [ht, e, hc]
  rfl

/-- The head's calls. -/
def headCalls : Option (List CallD) :=
  (Head.numbers Cond.hFull).toOption.bind fun Lh => (Head.callsOf Cond.hFull Lh).toOption

theorem headCalls_eq {Lh : Head.HL} {calls : List CallD} (hn : Head.numbers Cond.hFull = .ok Lh)
    (hc : Head.callsOf Cond.hFull Lh = .ok calls) : headCalls = some calls := by
  unfold headCalls
  rw [hn]
  show (Head.callsOf Cond.hFull Lh).toOption = some calls
  rw [hc]
  rfl

/-- The three digests, of three lists. -/
def digestsOf (k : Nat → ByteArray → ByteArray) (lc : List CallD) (l : List Attention.Line)
    (hc : List CallD) : Digests :=
  { hCalls := callsDigestO k "call" lc
    hCallsA := VerifiableInference.PlanWritten.Attention.callsDigestO k l
    hCallsH := callsDigestO k "callH" hc }

/-- The three digests as the public part has them, at a hash k. -/
def digestsAt (k : Nat → ByteArray → ByteArray) : Option Digests :=
  match layerCalls, (Attention.readLines PW.polCallsA).toOption, headCalls with
  | some lc, some l, some hc => some (digestsOf k lc l hc)
  | _, _, _ => none

theorem digests_at {l : List Attention.Line} {Lh : Head.HL} {calls : List CallD}
    (hl : Attention.readLines PW.polCallsA = .ok l) (hn : Head.numbers Cond.hFull = .ok Lh)
    (hc : Head.callsOf Cond.hFull Lh = .ok calls) (k : Nat → ByteArray → ByteArray) :
    digestsAt k = some (digestsOf k yFull.calls.toList l calls) := by
  unfold digestsAt
  rw [layerCalls_eq, hl, headCalls_eq hn hc]
  rfl

/-! ## 5 The comparison -/

/-- The comparison's own condition, as a function of the two fields of the public part that it reads. -/
def heldBy (P : PolScan) (d : Digests) (item : ByteArray) : Bool :=
  item.size == 708 &&
      namesHeld P item 2 Proof.names2 && wordsAt item 29 8 == d.hCalls &&
      namesHeld P item 37 Proof.names37 && tableWordsHeld P item 71 .silu &&
      tableWordsHeld P item 79 .sigmoid && tableWordsHeld P item 87 .rope &&
      namesHeld P item 103 Proof.names103 && tableWordsHeld P item 114 .exp &&
      wordsAt item 122 8 == d.hCallsA && namesHeld P item 130 Proof.names130 &&
      wordsAt item 155 8 == d.hCallsH && wordsAt item 172 1 == word32 P.hb &&
      wordsAt item 173 1 == word32 P.lkW && wordsAt item 174 1 == word32 P.frame.tableRowsLog &&
      wordsAt item 175 1 == word32 P.frame.tableLogN &&
      wordsAt item 176 1 == word32 P.frame.tableRandom

theorem statementHeld_by (X : Public) (item : ByteArray) :
    statementHeld X item =
      if heldBy X.P X.digests item then pure () else throw "internal-statement-two-ways" := rfl

/-- **The whole clause at the written letters, as a yes or no.** n: the number that stands for the request's size;
f: a turn of the digests: the identity, or a bend for a control. -/
def clauseBy (k : Nat → ByteArray → ByteArray) (n : Nat) (f : Digests → Digests) : Bool :=
  match itemBy k n, digestsAt k with
  | some item, some d => heldBy PW (f d) item
  | _, _ => false

end AtFullSide.K5.Item

#print axioms AtFullSide.K5.Item.pol_toList
#print axioms AtFullSide.K5.Item.read_zFull
#print axioms AtFullSide.K5.Item.olderK_fun
#print axioms AtFullSide.K5.Item.reqW_size
#print axioms AtFullSide.K5.Item.requestItem_eq
#print axioms AtFullSide.K5.Item.requestItem_at
#print axioms AtFullSide.K5.Item.layerCalls_eq
#print axioms AtFullSide.K5.Item.headCalls_eq
#print axioms AtFullSide.K5.Item.digests_at
#print axioms AtFullSide.K5.Item.statementHeld_by
#print axioms AtFullSide.K5.Item.polL
#print axioms AtFullSide.K5.Item.readL
#print axioms AtFullSide.K5.Item.linesL
#print axioms AtFullSide.K5.Item.olderKF
#print axioms AtFullSide.K5.Item.reqW
#print axioms AtFullSide.K5.Item.itemBy
#print axioms AtFullSide.K5.Item.layerCalls
#print axioms AtFullSide.K5.Item.headCalls
#print axioms AtFullSide.K5.Item.digestsOf
#print axioms AtFullSide.K5.Item.digestsAt
#print axioms AtFullSide.K5.Item.heldBy
#print axioms AtFullSide.K5.Item.clauseBy
