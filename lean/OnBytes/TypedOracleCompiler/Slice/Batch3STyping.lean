-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Batch3STyping.lean: THE TYPING OF A PROOF FILE, ITS PURE HALF: FROM WHAT THE
PORT's STRICT READER (OR ITS TWIN) RETURNS TO AN ARGUMENT STRING OF THE BATCH's SKELETON PROTOCOL,
WITH WHOLE PATHS. Definitions that hash nothing; a few equations.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. typeF H files := match the twin's reading with | ok r => assemble r | _ => none. THE READING
ASKS THE HASH; THE ASSEMBLING DOES NOT: it is this file. General in the data D, in the decision, and
in the map from an opening of the file to its tree's number in the whole.
  plJS, plF_plJS, plS_plJS      a stretch's plain parts (PQ.plainsSL's value) laid before a skeleton
    tail's; Batch3S's two cuts give the two back
  BD.plJ3                       the plain parts of a whole string from the three stretches' and the
    front's, the joining round's, the seam's
  OpAt, opsOf c o               an opening as it stands in the file: its chain (1, 2, 3), its
    round's number in the chain, its number in the round, the tree's form, the list of places, what
    was read;   all openings of a chain, in the file's order
  Row, rowsOf op                for each listed place: column, the file's salt, THE WHOLE PATH,
    looked up in the opening's own "seen" (the library's pathFrom: every vertex that the walk has
    met, given or computed); none if a vertex is missing
  tabOf num ops                 the table (tree's number in the whole, place) ↦ row, in the file's
    order: A LOOK-UP FINDS THE FIRST OPENING THAT SHOWS THE PLACE [where a later one shows another
    column: ClashF's matter, not the typing's]
  lookF runOf tab               Batch3SStrings' table of openings: the column as a symbol (none if
    its length is not the tree's width), typed salt := THE SENDER's run, then the file's salt (the
    library's leafSalt), the whole path
  extF a cfg tx                 the stored copy's openings likewise: the symbol (place, column);
    typed salt := cfg, then the file's salt (as in a file of this project that is not in this
    library)
  Own D                         what of a string has D's OWN types, so that the caller makes it: the
    front's openings and plain part, the joining round's plain part (for a proof file: (answers,
    run₂)), the seam's (run₃);   fOpenAll sym zs: every front position opened with its symbol, the
    salt zs (zSalt, a file of this project that is not in this library), no path (trees of depth 0)
  Req, reqOf s b i p            rtreq, slot, path, rsalt: from the place as read and the file's
    bytes: saltAt | sibsAt (Run/ReqClimb.lean): THE VERY TERMS OF reqCheck_of_readPlaceW
  BD.runOf                      the sender's run by the tree's number in the whole
  assemble3 D dec num w q d cfg o₁ o₂ o₃ : Option (OneProtocolProof 256 (BatchPS D dec).up)    salt := bits
    run₁; roots := d :: roots₁ ++ roots₂ ++ roots₃; plains, opens, ext, the request's four as above
  assembleF D dec num w s d cfg b r     the same at r : Proof.TailRead (first | shared | second
    . out; the place begins at r.first.next)
  assemble3_some                what a yes says, field by field
READINGS, HELD BY NO THEOREM AND BY NO RUN: (1) A STRETCH's ROUNDS ARE ITS CHAIN's FIRST |ds|
ROUNDS; what a chain has behind them (a sealing round) is typed by no written round (Batch3's head:
"SEAL 1 is no round of ds₁"). (2) An opening is of the stored copy exactly if its tree's form says
"stored". (3) The path comes from the SAME opening as the column. For "looked up in seen … under the
tree's root" the session's record would serve too; the opening's own list is what the library's
toBPrfFull takes, holds all siblings of its own listed places, and needs no agreement between
openings: with the flags off each position is climbed alone.
WHAT IS NOT SAID. That the verifier accepts the string (the fit). The instance x. The map num (a
renaming is to give it: the port names a tree by its label's number and, if taken over, by (root,
start)). No test of the lengths of salts, digests or paths: the lax verifier tests what it needs.
Nothing on speed: the tables are made once, in front of the functions.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Batch3SWireW
import OnBytes.TypedOracleCompiler.Slice.Batch3SStrings
import OnBytes.TypedOracleCompiler.Run.PlanQSMore
import OnBytes.TypedOracleCompiler.Run.ReqClimb
import Run.ParseFull
import OnBytes.Proof.Tail

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.Twin (RS PS)
open _root_.Run (bytesToBits bytesToDig leafSalt pathFrom rootsB)

/-! ## Plain parts -/

section
variable (C : PQ.CK) (T : List RS)

/-- a stretch's plain parts before a skeleton tail's -/
def plJS : (ds : List PQ.RD) → Plains (PQ.uL C ds) → Plains (_root_.Run.Twin.up T) →
    Plains (shA C T ds)
  | [], _, t => t
  | _ :: ds, (p, a), t => (p, plJS ds a t)

theorem plF_plJS : ∀ (ds : List PQ.RD) (a : Plains (PQ.uL C ds))
    (t : Plains (_root_.Run.Twin.up T)),
    plF C T ds (plJS C T ds a t) = a
  | [], _, _ => rfl
  | _ :: ds, (p, a), t => congrArg (Prod.mk p) (plF_plJS ds a t)

theorem plS_plJS : ∀ (ds : List PQ.RD) (a : Plains (PQ.uL C ds))
    (t : Plains (_root_.Run.Twin.up T)),
    plS C T ds (plJS C T ds a t) = t
  | [], _, _ => rfl
  | _ :: ds, (_, a), t => plS_plJS ds a t

end

/-- the plain parts of a whole string -/
def BD.plJ3 (D : BD) (fp : D.F.r.Plain) (a₁ : Plains (PQ.uL D.G.C D.G.ds₁)) (pJ : D.G.s2.r.Plain)
    (a₂ : Plains (PQ.uL D.G.C D.G.ds₂)) (p3 : D.G.s3.r.Plain) (a₃ : Plains (PQ.uL D.G.C D.G.ds₃)) :
        Plains D.shS :=
  (fp, plJS D.G.C D.SJ D.G.ds₁ a₁ (pJ, plJS D.G.C D.S₃ D.G.ds₂ a₂ (p3, a₃)))

/-! ## The openings, as they stand in the file -/

/-- an opening as it stands in the file -/
structure OpAt where
  /-- 1: the first chain; 2: the shared one; 3: the second -/
  chain : ℕ
  /-- the round's number in its chain, from 0 -/
  round : ℕ
  /-- the opening's number in its round, from 0 -/
  k : ℕ
  /-- the tree's form, as the chain's description has it -/
  sh : _root_.Fmt.Shape
  /-- the places at which it is opened -/
  xs : List ℕ
  /-- what was read -/
  out : _root_.Fmt.OpenOut

/-- all openings of a chain, in the file's order -/
def opsOf (c : ℕ) (o : _root_.Fmt.ChainOut) : List OpAt :=
  o.rounds.toList.zipIdx.flatMap fun r => r.1.opens.zipIdx.map fun x =>
      ⟨c, r.2, x.2, x.1.1, x.1.2.1, x.1.2.2⟩

/-- column, the file's salt, the whole path -/
abbrev Row : Type := List UInt64 × ByteArray × List (Dig 256)

/-- for each listed place its row; none if a vertex of a path was not met -/
def rowsOf (op : OpAt) : Option (List (ℕ × Row)) :=
  (op.xs.zip (op.out.cols.zip op.out.salts)).mapM fun z =>
    (pathFrom op.sh.a op.out.seen z.1).map fun p => (z.1, z.2.1, z.2.2, p)

/-- (the tree's number in the whole, place) ↦ row, in the file's order -/
def tabOf (num : OpAt → ℕ) (ops : List OpAt) : Option (List ((ℕ × ℕ) × Row)) :=
  (ops.mapM fun op => (rowsOf op).map fun l => l.map fun z => ((num op, z.1), z.2)).map List.flatten

/-- The table of openings. -/
def lookF (runOf : ℕ → ByteArray) (tab : List ((ℕ × ℕ) × Row)) : Look 256 := fun n s x =>
  match tab.lookup (n, x.val) with
  | none => none
  | some (col, salt, path) =>
    if h : col.length = s.W then some ⟨fun i => col[i.val]'(by rw [h]; exact i.isLt), leafSalt (runOf n) salt, path⟩
    else none

/-- the stored copy's openings -/
def extF (a : ℕ) (cfg : ByteArray) (tx : List ((ℕ × ℕ) × Row)) (p : Fin (2 ^ a)) :
    Option (Opening 256 PQ.SgX) :=
  (tx.lookup (0, p.val)).map fun z => ⟨(p.val, z.1), leafSalt cfg z.2.1, z.2.2⟩

/-! ## What has the data's own types; the request tree -/

/-- what of a string has D's own types -/
structure Own (D : BD) where
  fOpen : (p : D.F.r.Pos) → Option (Opening 256 (D.F.r.Sym p))
  fPlain : D.F.r.Plain
  pJ : D.G.s2.r.Plain
  p3 : D.G.s3.r.Plain

/-- every front position opened: its symbol, one salt, no path -/
def fOpenAll (D : BD) (sym : (p : D.F.r.Pos) → D.F.r.Sym p) (zs : Bits) :
    (p : D.F.r.Pos) → Option (Opening 256 (D.F.r.Sym p)) := fun p => some ⟨sym p, zs, []⟩

/-- a string's four fields on the request tree -/
structure Req where
  rtreq : Dig 256
  slot : ℕ
  path : List (Dig 256)
  rsalt : Bits

/-- from the place as read, which begins at byte i of b -/
def reqOf (s : OnBytes.Params.LinBindingShape) (b : ByteArray) (i : ℕ)
    (p : OnBytes.Proof.Place) : Req where
  rtreq := bytesToDig p.root
  slot := p.place
  path := (sibsAt b (i + 8 + s.saltBytes) s.logLeaves).map bytesToDig
  rsalt := bytesToBits (saltAt s b i) ++ bytesToBits (_root_.Fmt.u64n p.place)

/-- the sender's run, by the tree's number in the whole -/
def BD.runOf (D : BD) (run₁ run₂ run₃ : ByteArray) (n : ℕ) : ByteArray :=
  if n < nTrees D.G.ds₁ then run₁ else if n - nTrees D.G.ds₁ < nTrees D.G.ds₂ then run₂ else run₃

/-! ## The string -/

variable {X : Type} (D : BD)
  (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool)

/-- From three chains as read to an argument string. -/
def assemble3 (num : OpAt → ℕ) (w : Own D) (q : Req) (d cfg : ByteArray)
    (o₁ o₂ o₃ : _root_.Fmt.ChainOut) :
    Option (OneProtocolProof 256 (BatchPS D dec).up) :=
  match o₁.run, o₂.run, o₃.run with
  | some run₁, some run₂, some run₃ =>
    let ops := opsOf 1 o₁ ++ (opsOf 2 o₂ ++ opsOf 3 o₃)
    match PQ.plainsSL D.G.C D.G.ds₁ (o₁.rounds.toList.take D.G.ds₁.length),
      PQ.plainsSL D.G.C D.G.ds₂ (o₂.rounds.toList.take D.G.ds₂.length),
      PQ.plainsSL D.G.C D.G.ds₃ (o₃.rounds.toList.take D.G.ds₃.length),
      tabOf num (ops.filter fun op => !op.sh.stored),
          tabOf (fun _ => 0) (ops.filter fun op => op.sh.stored) with
    | some a₁, some a₂, some a₃, some tab, some tx =>
      some
        { salt := bytesToBits run₁
          roots := (d :: (rootsB o₁ ++ (rootsB o₂ ++ rootsB o₃))).map bytesToDig
          plains := D.plJ3 w.fPlain a₁ w.pJ a₂ w.p3 a₃
          opens := D.opSS w.fOpen (lookF (D.runOf run₁ run₂ run₃) tab)
          ext := extF D.G.a cfg tx
          rtreq := q.rtreq
          slot := q.slot
          path := q.path
          rsalt := q.rsalt }
    | _, _, _, _, _ => none
  | _, _, _ => none

/-- From a tail as read. -/
def assembleF (num : OpAt → ℕ) (w : Own D) (s : OnBytes.Params.LinBindingShape)
    (d cfg b : ByteArray)
    (r : OnBytes.Proof.TailRead) : Option (OneProtocolProof 256 (BatchPS D dec).up) :=
  assemble3 D dec num w (reqOf s b r.first.next r.place) d cfg r.first.out r.shared.out r.second.out

/-- What a yes says. -/
theorem assemble3_some {num : OpAt → ℕ} {w : Own D} {q : Req} {d cfg : ByteArray}
    {o₁ o₂ o₃ : _root_.Fmt.ChainOut}
    {π : OneProtocolProof 256 (BatchPS D dec).up} (h : assemble3 D dec num w q d cfg o₁ o₂ o₃ = some π) :
    ∃ run₁ run₂ run₃ a₁ a₂ a₃ tab tx,
      o₁.run = some run₁ ∧ o₂.run = some run₂ ∧ o₃.run = some run₃ ∧
      PQ.plainsSL D.G.C D.G.ds₁ (o₁.rounds.toList.take D.G.ds₁.length) = some a₁ ∧
      PQ.plainsSL D.G.C D.G.ds₂ (o₂.rounds.toList.take D.G.ds₂.length) = some a₂ ∧
      PQ.plainsSL D.G.C D.G.ds₃ (o₃.rounds.toList.take D.G.ds₃.length) = some a₃ ∧
      tabOf num ((opsOf 1 o₁ ++ (opsOf 2 o₂ ++ opsOf 3 o₃)).filter fun op => !op.sh.stored) = some
          tab ∧
      tabOf (fun _ => 0) ((opsOf 1 o₁ ++ (opsOf 2 o₂ ++ opsOf 3 o₃)).filter fun op =>
          op.sh.stored) = some tx ∧
      π.salt = bytesToBits run₁ ∧
      π.roots = (d :: (rootsB o₁ ++ (rootsB o₂ ++ rootsB o₃))).map bytesToDig ∧
      π.plains = D.plJ3 w.fPlain a₁ w.pJ a₂ w.p3 a₃ ∧
      π.opens = D.opSS w.fOpen (lookF (D.runOf run₁ run₂ run₃) tab) ∧
      π.ext = extF D.G.a cfg tx ∧
      π.rtreq = q.rtreq ∧ π.slot = q.slot ∧ π.path = q.path ∧ π.rsalt = q.rsalt := by
  unfold assemble3 at h
  split at h
  · rename_i run₁ run₂ run₃ h1 h2 h3
    dsimp only at h
    split at h
    · rename_i a₁ a₂ a₃ tab tx e1 e2 e3 e4 e5
      obtain rfl := Option.some.inj h
      exact ⟨run₁, run₂, run₃, a₁, a₂, a₃, tab, tx, h1, h2, h3, e1, e2, e3, e4, e5, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl,
        rfl, rfl⟩
    · cases h
  · cases h

end TypedOracleCompiler.Slice
