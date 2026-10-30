-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
TWO: OnBytes/TypedOracleCompiler/Run/ThinBits.lean: THE LIBRARY's FILE OF THE SAME NAME SAID AGAIN OVER OnBytes/TypedOracleCompiler
(a list of trees a round; a leaf's body a parameter of the interface). It is the first of the three
later run forms of the evaluable verifier: verifyPB, with its tie verifyPB_eq to OnBytes/TypedOracleCompiler's
verifyP (OnBytes/TypedOracleCompiler/Run/ThinDefs.lean).
WHY. By the library's own count (below) OnBytes/TypedOracleCompiler's verifyP does not
come home with a real hash.
WHAT IS SAID AGAIN, AS TEXT BUT FOR THE FIVE NAMED BELOW (the names here mean OnBytes/TypedOracleCompiler's Forest,
Check, BatchProtocolWithLeafBody, typedOracleFamily, ProtocolQueryLayout, OneProtocolProof, chainP, strictP, forestsOfP): nodeB, rnodeB; runForestB,
runForestsB; reqCheckB, reqPartB; afterPB, verifyPB; nodeB_ofFn, rnodeB_ofFn; runForestB_eq,
runForestsB_eq, reqCheckB_eq, reqPartB_eq, afterPB_eq, verifyPB_eq. Nothing had to be turned for the
list of trees: a forest is walked alike whichever tree of a round it came from; the list of trees is
met earlier, in forestsP.
TURNED WITH THE ROAD (the string rs behind the slot's value in the request tree's leaf; as reqCheckP
| reqPartP | afterP in ThinDefs.lean): reqCheckB, reqPartB, afterPB, reqCheckB_eq, reqPartB_eq:
these five are not the library's text.
WHAT IS LEFT TO THE LIBRARY's OWN MODULE (imported beside; it stands on no turned type): headD_map,
loneF_map, stepF_sib, stepF_lone, stepF_map, octF_map, climbF_map (the walks commute with a map of
digests); dfltB; decide_ofFn.
WHAT IS NOT SAID. THE COUNTS IN THE HEAD BELOW ARE THE LIBRARY's, OF THE LIBRARY's FUNCTIONS:
OnBytes/TypedOracleCompiler's are not counted. Run/ThinBitsGuard.lean, which the head names, is not said again;
OnBytes/TypedOracleCompiler's test, with a made-up hash, is not in this library. The head below is the
library's, kept; where it says Run/… read OnBytes/TypedOracleCompiler's file of that name if there is one.

Run/ThinBits.lean: THE EVALUABLE FORM OF THE COMPILED VERIFIER (Run/ThinDefs.lean: verifyP; "thin"
in names: a function that computes the same verdict at given oracle functions and can be evaluated
at rounds with very many possible verifier messages) WITH THE TREES' WALKS ON DIGESTS AS DATA (LISTS
OF BITS), SO THAT THE EVALUATOR ASKS THE ORACLE ONCE A VERTEX; AND THE TIE: IT IS THAT FORM.
Definitions that compute; theorems with proofs.
WHY. A digest (Dig lam) is a FUNCTION of the bit's number. A function that returns one (nodeP a b :=
the oracle at the bits of a and of b) is, compiled, a closure that waits for the bit's number: AT
EVERY BIT THAT IS READ it makes the bits of a, the bits of b and the oracle's answer anew; a and b
are such closures themselves: the work multiplies from level to level. COUNTED (scratch files
outside this development; digests of 256 bits; the format's hash with a trace; all bits of the
result read): nodeP once: 256 asks; two levels: not back in 120 seconds; the pruned walk at depth 2
on four leaves: not back in 120 seconds. WITH DIGESTS AS LISTS OF BITS, THROUGH THIS FILE'S OWN
runForestB (the family: Run/CodingFnThin.lean's famP): depth 2, four leaves: 7 asks (4 leaves, 3
vertices); depth 4, sixteen leaves: 31 (16 and 15); depth 4, pruned, three positions: 12 (3 and 9):
ONE ASK A LEAF, ONE A VERTEX. (runForestP at depth 2, four leaves, a false root, so that the
comparison ends at the first bit that differs: more than 2,000.) NOT COUNTED: reqCheckB (that family
has no call for the request tree), verifyPB as a whole; verifyPB HAS BEEN RUN as a whole:
Run/ThinBitsGuard.lean (depth 15, 74 positions, digests of 256 bits).
THE RULE FOLLOWED IN THESE FILES: NO FUNCTION ON THE RUN'S PATH RETURNS OR HANDS ON A DIGEST AS A
FUNCTION WHERE IT HAS BEEN COMPUTED: ITS BITS AS DATA.
 THE LIBRARY'S WALKS ARE GENERIC IN THE TYPE OF DIGESTS (Hash/Octopus.lean: the pruned walk;
 Compile/MerkleList.lean: the walk along one path). So they are used as they are, at lists of bits.
    headD_map, loneF_map, stepF_sib, stepF_lone, stepF_map, octF_map, climbF_map both walks commute
    with any map φ of digests that carries the one node function to the other (and, for the pruned
    walk, the one default to the other)
    dfltB lam            the bits of the digest that stands where none is there (the pruned walk
                         reads it off an empty list)
    nodeB, rnodeB Lf g a b      a vertex on bits: the bits of the oracle's answer at (a, b): DATA:
                                computed where it stands
    runForestB, runForestsB     a forest's walk: the leaves' answers as bits; the given digests as
                                bits, made once; the roots compared as bits
    reqCheckB, reqPartB         the request tree's check
    afterPB, verifyPB           verifyP's text, differing in these walks alone
    nodeB_ofFn, rnodeB_ofFn, decide_ofFn; runForestB_eq, runForestsB_eq, reqCheckB_eq, reqPartB_eq,
    afterPB_eq, verifyPB_eq: each = its namesake with P: for every Lf, g and all arguments: no
    hypothesis
WHAT IS NOT SAID. How often the evaluator computes what is a fact about this compiler, no theorem.
The family g must itself give its answers as data first (Run/CodingFnThin.lean: famP). That verifyP
is the run of the library's verifier: Run/ThinTie*.lean. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library: a test by Lean's evaluator, which
   leaves no declaration. So nothing that is checked of declarations is checked of such a run. No
   clause of a soundness theorem of this library speaks of a run. -/
import Run.ThinBits
import OnBytes.TypedOracleCompiler.Run.ThinDefs

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Thin
export _root_.Run.Thin (headD_map loneF_map stepF_sib stepF_lone stepF_map octF_map climbF_map
    dfltB decide_ofFn)

/-! ## Digests as bits -/

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X) (g : Fam (typedOracleFamily lam K (Lf ())))

/-- A vertex, on bits.  Its result is data: it is computed where it stands -/
def nodeB (a b : Bits) : Bits := List.ofFn (g OracleName.node ((a, b) : Bits × Bits) : Dig lam)
def rnodeB (a b : Bits) : Bits := List.ofFn (g OracleName.rnode ((a, b) : Bits × Bits) : Dig lam)

/-- One forest's walk, on bits. -/
def runForestB (F : Forest lam (Lf ())) (s : List (Dig lam)) : Bool :=
  ((Octopus.upN F.depth (idxP Lf F)).zip
      (@Octopus.octF Bits ⟨dfltB lam⟩ (nodeB Lf g) F.depth (idxP Lf F)
        (F.cs.map fun e => List.ofFn (g OracleName.leaf e.2.inp : Dig lam)) (s.map List.ofFn))).all
    fun m => decide (m.2 = List.ofFn (F.treeRoot m.1))

def runForestsB : List (Forest lam (Lf ())) → List (Dig lam) → Bool
  | [], _ => true
  | F :: Fs, s => runForestB Lf g F (s.take (needP Lf F)) && runForestsB Fs (s.drop (needP Lf F))

/-- The request tree's check, on bits. -/
def reqCheckB (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam)) (c : Dig lam)
    (rs : Bits) : Bool :=
  if path.length = depthReq ∧ slot < 2 ^ depthReq then
    decide (climbF (rnodeB Lf g) (path.map List.ofFn) slot
        (List.ofFn (g OracleName.rleaf (List.ofFn c ++ rs : Bits) : Dig lam)) = List.ofFn rtreq)
    else false

def reqPartB (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam)) (rs : Bits)
    (ph : Phase lam) : Bool :=
  match ph.slotVal with
  | none => true
  | some c => reqCheckB Lf g depthReq rtreq slot path c rs

variable {Y : Type} {E : ExtSpec}

/-- what follows the chain and the format's test: the thin verifier's text, the two walks on bits -/
def afterPB (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  match forestsOfP Lf P wq embS embE cms x π ρ rts with
  | some Fs =>
      if (flatP Lf Fs).length ≤ wq.nOpen ∧
          (flatP Lf Fs).all (fun c => wellP Lf c && decide (c.depth ≤ wq.maxDepth)) then
        runForestsB Lf g Fs (readsP Lf Fs) && reqPartB Lf g depthReq π.rtreq π.slot
            π.path π.rsalt ph &&
          P.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
            (trP P.S P.ann wq.sh rts π.plains ρ π.opens)
      else false
  | none => false

/-- THE VERIFIER, ITS WALKS ON BITS. -/
def verifyPB (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) : Bool :=
  match chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => false
  | some (ρ, rts, ph) =>
    if strictP sMT sFS P wq depthReq x π ρ rts ph then
      afterPB Lf g P wq embS embE depthReq cms x π ρ rts ph
    else false

/-! ## The ties -/

theorem nodeB_ofFn (a b : Dig lam) :
    List.ofFn (nodeP Lf g a b) = nodeB Lf g (List.ofFn a) (List.ofFn b) := rfl
theorem rnodeB_ofFn (a b : Dig lam) :
    List.ofFn (rnodeP Lf g a b) = rnodeB Lf g (List.ofFn a) (List.ofFn b) := rfl

/-- One forest. -/
theorem runForestB_eq (F : Forest lam (Lf ())) (s : List (Dig lam)) :
    runForestB Lf g F s = runForestP Lf g F s := by
  unfold runForestB runForestP
  have e : ∀ l : List (ℕ × Check lam (Lf ())),
      (l.map fun e => List.ofFn (g OracleName.leaf e.2.inp : Dig lam)) =
        (l.map fun e => (g OracleName.leaf e.2.inp : Dig lam)).map List.ofFn := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => exact congrArg (List.cons _) ih
  rw [e]
  letI : Inhabited Bits := ⟨dfltB lam⟩
  rw [octF_map (D := Dig lam) (D' := Bits) List.ofFn (nodeP Lf g)
        (nodeB Lf g) rfl (nodeB_ofFn Lf g),
    List.zip_map_right, List.all_map]
  congr 1
  funext m
  exact decide_ofFn _ _

theorem runForestsB_eq :
    ∀ (Fs : List (Forest lam (Lf ()))) (s : List (Dig lam)),
      runForestsB Lf g Fs s = runForestsP Lf g Fs s
  | [], _ => rfl
  | F :: Fs, s => by
      show (runForestB Lf g F (s.take (needP Lf F)) && runForestsB Lf g Fs (s.drop (needP Lf F))) =
        (runForestP Lf g F (s.take (needP Lf F)) && runForestsP Lf g Fs (s.drop (needP Lf F)))
      rw [runForestB_eq, runForestsB_eq Fs]

theorem reqCheckB_eq (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ)
    (path : List (Dig lam)) (c : Dig lam) (rs : Bits) :
    reqCheckB Lf g depthReq rtreq slot path c rs = reqCheckP Lf g depthReq rtreq slot
        path c rs := by
  unfold reqCheckB reqCheckP
  split
  · rw [climbF_map List.ofFn (rnodeP Lf g) (rnodeB Lf g) (rnodeB_ofFn Lf g), decide_ofFn]
  · rfl

theorem reqPartB_eq (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ)
    (path : List (Dig lam)) (rs : Bits) (ph : Phase lam) :
    reqPartB Lf g depthReq rtreq slot path rs ph = reqPartP Lf g depthReq rtreq slot
        path rs ph := by
  unfold reqPartB reqPartP
  cases ph.slotVal with
  | none => rfl
  | some c => exact reqCheckB_eq Lf g _ _ _ _ _ _

theorem afterPB_eq (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) :
    afterPB Lf g P wq embS embE depthReq cms x π ρ rts ph =
      afterP Lf g P wq embS embE depthReq cms x π ρ rts ph := by
  unfold afterPB afterP
  cases forestsOfP Lf P wq embS embE cms x π ρ rts with
  | none => rfl
  | some Fs => simp only [runForestsB_eq, reqPartB_eq]

/-- THE TIE: THE VERIFIER WITH ITS WALKS ON BITS IS THE THIN VERIFIER. -/
theorem verifyPB_eq (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) :
    verifyPB Lf g early late sMT sFS t P wq embS embP xin embE depthReq cms x π =
      verifyP Lf g early late sMT sFS t P wq embS embP xin embE depthReq cms x π := by
  unfold verifyPB verifyP
  cases chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => rfl
  | some r =>
      obtain ⟨ρ, rts, ph⟩ := r
      simp only [afterPB_eq]

end TypedOracleCompiler.Run.Thin
