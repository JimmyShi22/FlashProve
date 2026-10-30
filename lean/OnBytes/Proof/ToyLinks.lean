-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Proof/ToyLinks.lean: the links of the small test batches, and the check of their files.

The C++ library comes with a tool (blocks/frame/handover_proof.cpp) that writes proof files of
small test batches on made-up data. Their links (in C++: toy_links, blocks/frame/tests/seam_world.h)
stand in for a model's sub-proofs. A link sends vectors in oracle messages and shows that one of
them is the product of two others, entry by entry; the next link multiplies what the link before has
left. Each link also holds claims on the committed matrix. These leave the link through a batching
whose end value is shown (blocks/iop/batt_shown.h): one row on the matrix, masked by an entry of the
request's index-mask message, and one row on the link's own mask row.

The forms of a link's claims on the matrix (a column point and weights on the rows) are public data
of the test world. The tool writes them beside each proof file, and they are an input here.

Main definitions: `BattShown`, `battShownVerify`, `ToyClaim`, `readClaims`, `toyProduct`,
`toyClaims`, `toyLinks`, `toyCheck`, `toyCall`.

What is not claimed. The claims' forms are taken as given. In the test world they are a function of
the request's bytes, and the C++ verifier computes them from the request that its first hash call
binds. This file does not compute that function, so no hash call binds the forms that `toyCheck` is
given. Here `toyCheck` does not meet the caller's duty on public values that `check` states, and its
yes does not mean that the forms belong to the request. Of the reply the toy links prove nothing.
-/
import OnBytes.Proof.File
import OnBytes.Iop.Req
import OnBytes.Entry.Table
import OnBytes.Proof.RequestItem

namespace OnBytes.Proof

open Params (LinShape)

/-! ## A batching of rows on the matrix whose end value is shown -/

/-- What the batching returns. -/
structure BattShown where
  /-- one row on the matrix, whose only mask entry is in the index-mask message -/
  row : TensorRow
  /-- the mask form of the second row, which is on entries of the link's mask row only -/
  ownMasks : MaskForm
  /-- the target of the second row: the mask form `ownMasks` is claimed to equal it -/
  ownTarget : E

/-- The mask entries that one run takes from the link's mask row. It takes one more from the
index-mask message. -/
def battShownOwnMasks (kCol : Nat) : Nat := 2 + 2 * kCol

/-- The summand of the batching's sumcheck: the value of its one shown map, that is, of the one map
whose end value the prover sends, under a mask. It keeps no map. -/
def battShownSummand : Psc.Summand where
  shown := 1
  kept := 0
  degree := 1
  coeffs := fun _ y => [y.headD zeroE]

/-- The verifier's part in one run on a matrix of 2^kCol columns. rows: rows on the matrix whose
mask entries lie in the link's mask row. own: the oracle message with the link's mask row.
indexMasks: the request's index-mask message. No test on values is made here: the conditions in the
body are public ones. The design's aim is that a false row that comes in makes one of the two rows
that go out false, up to the errors of the draws (blocks/iop/batt_shown.h, ERRORS). No theorem here
says so. By that header's ORDER the aim rests on this: the index-mask message, root and sample's
answer, was sent before beta, the sumcheck's last draw. -/
def battShownVerify (kCol : Nat) (rows : List TensorRow) (own indexMasks : Nat) :
    Blk BattShown := do
  Blk.must (Batt.fits kCol rows)
  let x ← Blk.closeOne "BAT-sigma"
  Blk.requireRows rows.length
  let mine ← takeSlots own (battShownOwnMasks kCol)
  let theirs ← takeSlots indexMasks 1
  let o ← Psc.verify (Batt.claimOf rows x) battShownSummand (mine ++ theirs)
  Blk.must (o.ends.length == 1 && o.rowMaps.isEmpty)
  let e ← Blk.get o.ends.head?
  let a := ((Batt.summandOf rows x).coeffs o.point []).drop 1
  let g := (zipT rows a).flatMap fun p => p.1.g.map fun t => t.scale p.2
  pure { row := { g := g, psi := e.point, masks := e.masks, target := e.value },
         ownMasks := o.rowMasks, ownTarget := o.rowTarget }

/-! ## The claims' forms -/

/-- The form of one claim on the matrix: a column point, and a weight for each row. -/
structure ToyClaim where
  psi : List E
  g : Array E

/-- The number of claims on the matrix that a toy link holds: a constant of the test world (in C++:
CLAIMS, blocks/frame/tests/seam_world.h). -/
def toyClaimsALink : Nat := 2

/-- Reads the file of the claims' forms: two words of eight bytes, the number of links and of claims
in a link; then each claim's point and weights, each a list of elements. Returns one list of claims
for each link. Returns nothing if the second word is not `toyClaimsALink`, if an element is not in
canonical form, or if bytes are missing or left over. -/
def readClaims (f : Fmt.Fld) (b : ByteArray) : Option (List (List ToyClaim)) :=
  let several := rdListT (Fmt.rdExt f)
  match Fmt.rdPair Fmt.rdWord Fmt.rdWord b 0 with
  | none => none
  | some ((links, each), i) =>
    if each.toNat != toyClaimsALink then none else
    match rdManyT (Fmt.rdPair several several) (links.toNat * each.toNat) b i with
    | none => none
    | some (all, j) =>
      if j != b.size then none
      else
        let claims := all.map fun x =>
          (⟨x.1.map E.ofTriple, (x.2.map E.ofTriple).toArray⟩ : ToyClaim)
        some ((List.range links.toNat).map fun l =>
          (claims.drop (l * each.toNat)).take each.toNat)

/-! ## A link's sub-proof -/

/-- The value at a point of the extension of the vector in one row of o, times a scalar, as a
structured vector on o's main table. A vector fills the lower half of a row. -/
def toyVectorAt (st : Statement) (o row : Nat) (point : List E) (scalar : E) : Tensor :=
  ((Tensor.eq point scalar).push oneE zeroE).insertChoice 0 (st.rowBits o .main) row

/-- The summand of the product: Y_1 Y_2 - U_1. The values of the two factors are shown under masks;
the product stays a term of the row that the sumcheck leaves. -/
def toySummand : Psc.Summand where
  shown := 2
  kept := 1
  degree := 2
  coeffs := fun _ y => [mulE (y.headD zeroE) (y.getD 1 zeroE), negE oneE]

/-- The first half of a link's sub-proof: c = x * b, entry by entry. It leaves three rows on the
link's group. In the first link x and b are the two rows of the link's first oracle message. In a
later link x is the product that the link before has left, as the frame has sent it anew. -/
def toyProduct (f : ReqFrame) : Blk Unit := do
  let st ← Blk.statement
  let code ← Blk.get st.codes.base[f.shape.code]?
  Blk.must (decide (1 ≤ code.logEll))
  let b ← Blk.get f.own[0]?
  let c ← Blk.get f.own[1]?
  let x ← if f.link == 0 then pure b else Blk.get f.keptBefore[0]?
  let bRow := if f.link == 0 then 1 else 0
  let zeta ← drawPoint "ZERO" (code.logEll - 1)
  let claim : Psc.Claim :=
    { vars := zeta.map fun z => Psc.Weight.equality z 3, masks := [], target := zeroE }
  let fresh ← takeSlots b (Psc.masksOf claim toySummand)
  let o ← Psc.verify claim toySummand fresh
  let e0 ← Blk.get o.ends[0]?
  let e1 ← Blk.get o.ends[1]?
  Blk.addRow f.group ((({ target := o.rowTarget } : Row).addMasks o.rowMasks).add c .main
    (toyVectorAt st c 0 o.point (o.rowMaps.headD zeroE)))
  Blk.addRow f.group ((({ target := e0.value } : Row).addMasks e0.masks).add x .main
    (toyVectorAt st x 0 e0.point oneE))
  Blk.addRow f.group ((({ target := e1.value } : Row).addMasks e1.masks).add b .main
    (toyVectorAt st b bRow e1.point oneE))

/-- Receives the targets of a link's claims on the matrix. Each is masked by one entry of the link's
mask row. -/
def toyClaimRows (S : LinShape) (own : Nat) : List ToyClaim → Blk (List TensorRow)
  | [] => pure []
  | c :: cs => do
    let g ← Blk.get (memberWeightsOnRows S 0 c.g)
    let target ← Blk.recvE
    let slot ← takeSlots own 1
    let rest ← toyClaimRows S own cs
    pure ({ g := g, psi := c.psi, masks := slot.map fun s => (s, oneE), target := target } :: rest)

/-- The second half of a link's sub-proof: its claims on the matrix leave the link. Returns the row
on the matrix. -/
def toyClaims (S : LinShape) (f : ReqFrame) (claims : List ToyClaim) : Blk TensorRow := do
  let own ← Blk.get f.own[0]?
  let index ← Blk.get f.atStart[0]?
  let rows ← toyClaimRows S own claims
  let left ← battShownVerify S.kCol rows own index
  Blk.addRow f.group (({ target := left.ownTarget } : Row).addMasks left.ownMasks)
  pure left.row

/-- A toy link's sub-proof as the frame of links (OnBytes/Iop/Req.lean) calls it: once after each
moment of the link, that is, each time the link has sent oracle messages and they were sampled. The
product comes after the link's first moment, the claims on the matrix after its last. A toy link has
at most two moments. The reply is the first plain scalar of the link that has one. -/
def toySub (S : LinShape) (claims : List (List ToyClaim)) : ReqSub LinksResult :=
  fun f moment _ r => do
    let L ← Blk.get f.shape.link[f.link]?
    Blk.must (decide (reqMoments L ≤ 2))
    let r := if moment == 0 && L.plain != 0 then { r with reply := f.plain.head? } else r
    if moment == 0 then toyProduct f
    if moment + 1 == reqMoments L then
      let row ← toyClaims S f (← Blk.get claims[f.link]?)
      pure { r with pending := r.pending ++ [row] }
    else pure r

/-- The caller's part of a toy proof's first chain: all links and their last proximity test. -/
def toyLinks (p : Params.First) (claims : List (List ToyClaim)) : Blk LinksResult := do
  Blk.must (claims.length == p.shape.link.length)
  let (f, r) ← reqVerify p.shape (toySub p.lin claims) {}
  let index ← Blk.get f.atStart[0]?
  pure { r with indexMasks := index }

/-! ## A toy proof file -/

/-- Checks a proof file of a test batch. first, shared, second: the parameter bytes of the three
chains. publicFiles: the public files, whose digest all three must hold. claims: the file of the
claims' forms. The other arguments are those of `check`, but for `words`: in a test batch a request
is its own file, so `request` is passed in both places, as in the C++ tool
(blocks/frame/handover_proof.cpp). So a test batch's file cannot tell the two places apart: it would
pass as well if the two were exchanged. -/
def toyCheck (first shared second : ByteArray) (publicFiles : List ByteArray)
    (table : Params.TableName) (copy : Nat) (request : ByteArray) (reply : E)
    (claims file : ByteArray) : Verdict :=
  match Params.ProofChains.read first shared second with
  | none => .refused ⟨.configuration, "proof-parameters"⟩
  | some c =>
    if !c.first.given.under (Fmt.configDigest publicFiles) then
      .refused ⟨.configuration, "public-files-digest"⟩
    else if !c.first.more.isEmpty then .refused ⟨.configuration, "further-parameter-items"⟩
    else
      match readClaims c.first.given.plan.field claims with
      | none => .refused ⟨.configuration, "claims-forms"⟩
      | some l => check c table copy request request reply (toyLinks c.first l) file

/-! ## `toyCheck` on the bytes of the tool's files -/

/-- The number that decimal digits spell, if it is below `bound`. Returns nothing for an empty
numeral, one of more than 20 digits, one of several digits that begins with 0, or one with a
character that is no digit. -/
def decimalBelow (bound : Nat) (w : List UInt8) : Option Nat :=
  if w.isEmpty || decide (20 < w.length) || (w.head? == some 0x30 && decide (1 < w.length)) ||
      w.any (fun c => c < 0x30 || 0x39 < c) then none
  else (some (w.foldl (fun x c => 10 * x + (c.toNat - 0x30)) 0)).filter fun x => decide (x < bound)

/-- An element of the extension field from a line of text: its three coordinates as decimal
numerals below the prime, separated by single blanks, then one line feed and nothing more. -/
def elementOfText (f : Fmt.Fld) (text : ByteArray) : Option E :=
  match Params.cutAt 0x0A text.toList with
  | some (line, []) =>
    match (splitAt 0x20 line).map (decimalBelow f.p) with
    | [some a, some b, some c] => some (E.mk3 (UInt64.ofNat a) (UInt64.ofNat b) (UInt64.ofNat c))
    | _ => none
  | _ => none

/-- The root and the `count` answers of the record that follow the head of a key file or of an entry
file. The file is not checked: only its head is compared, and the root and the answers are taken. -/
def toyTable (f : Fmt.Fld) (count : Nat) (file : ByteArray) : Option Params.TableName :=
  let head :=
    match readHead f .key file with
    | .ok i => some i
    | .error _ => (readHead f .entry file).toOption
  head.bind fun i => (readTable f count file i).toOption.map (·.1)

/-- The number of a record's answers, from the parameter bytes of a proof's three chains: one answer
for each row and seed. It is 0 if the bytes are not those of a proof's chains; `toyCheck` refuses
these. -/
def toyAnswers (first shared second : ByteArray) : Nat :=
  ((Params.ProofChains.read first shared second).map fun c =>
    c.first.lin.fold.index.rows * c.first.lin.fold.index.answers).getD 0

/-- `toyCheck` on the bytes of the files that the tool writes. tableFile: the key file or the entry
file that holds the table's root and its record's answers; it is not checked here. number: the
number under which the caller holds that table, as a decimal numeral. Which of the two kinds the
file has is not compared with the number. replyText: the reply's three coordinates as text. -/
def toyCall (first shared second public1 public2 tableFile : ByteArray) (number : String)
    (request replyText claims file : ByteArray) : Verdict :=
  match toyTable .two (toyAnswers first shared second) tableFile,
      decimalBelow (2 ^ 32) number.toUTF8.toList,
      elementOfText .two replyText with
  | none, _, _ => .refused ⟨.configuration, "table-file-head"⟩
  | _, none, _ => .refused ⟨.request, "stored-copy-number"⟩
  | _, _, none => .refused ⟨.request, "reply-spelling"⟩
  | some table, some copy, some reply =>
    toyCheck first shared second [public1, public2] table copy request reply claims file

/-- The names under which `toyCheck` and `toyCall` refuse. -/
def toyNames : List String :=
  ["proof-parameters", "public-files-digest", "further-parameter-items", "claims-forms",
   "table-file-head", "stored-copy-number", "reply-spelling"] ++ fileNames

end OnBytes.Proof
