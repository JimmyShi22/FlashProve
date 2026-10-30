-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ThinBits.lean: the evaluable form of the compiled verifier (`verifyP`, Run/ThinDefs.lean) with
the trees' walks on digests as data (lists of bits), so that the evaluator asks the oracle once a
vertex (`verifyPB`); and the theorem that it is that form (`verifyPB_eq`).

Definitions that compute; theorems with proofs.
The evaluable form ("thin" in names) is a function that computes the same verdict as the compiled
verifier of one slot (`Compile.Batch.verifyOneProtocol`) at given oracle functions (at what: `thin_verify`,
Run/ThinTie.lean) and can be evaluated at rounds with very many possible verifier messages. The
walks are its passes up the Merkle trees, from opened leaves to the roots; a vertex is an inner node
of such a tree.

Why: a digest (`Dig lam`) is a function of the bit's number. A function that returns one
(`nodeP a b` := the oracle at the bits of a and of b) is, compiled, a closure that waits for the
bit's number: at every bit that is read it makes the bits of a, the bits of b and the oracle's
answer anew; a and b are such closures themselves: the work multiplies from level to level.
Counted (scratch files outside this development; digests of 256 bits; the format's hash with a
trace; all bits of the result read): `nodeP` once: 256 queries; two levels: not back in 120 seconds;
the pruned walk at depth 2 on four leaves: not back in 120 seconds. With digests as lists of bits,
through this file's own `runForestB` (the family: `famP`, Run/CodingFnThin.lean): depth 2, four
leaves: 7 queries (4 leaves, 3 vertices); depth 4, sixteen leaves: 31 (16 and 15); depth 4, pruned,
three positions: 12 (3 and 9): one query a leaf, one a vertex. (`runForestP` at depth 2, four
leaves, a false root, so that the comparison ends at the first bit that differs: more than 2,000.)
Not counted: `reqCheckB` (that family has no call for the request tree), `verifyPB` as a whole;
`verifyPB` has been run as a whole: Run/ThinBitsGuard.lean (depth 15, 74 positions, digests of 256
bits).
The rule followed in this file's walks: no function of a walk returns or hands on as a function a
digest that it has itself computed: its bits as data.
The library's walks are generic in the type of digests (Hash/Octopus.lean: the pruned walk;
Compile/MerkleList.lean: the walk along one path). So they are used as they are, at lists of bits.

Main names:
  `headD_map`, `loneF_map`, `stepF_map`, `octF_map`, `climbF_map`: both walks commute with any map φ
    of digests that carries the one node function to the other (and, for the pruned walk, the one
    default to the other).
  `dfltB lam` (the pruned walk reads it off an empty list).
  `runForestB`, `runForestsB`: the walk of a forest: the leaves' answers as bits; the given digests
    as bits, made once; the roots compared as bits.
  `reqCheckB`, `reqPartB`: the request tree's check.
  `afterPB`, `verifyPB`: the definitions of `afterP`, `verifyP`, differing in these walks alone.
  `runForestB_eq`, `runForestsB_eq`, `reqCheckB_eq`, `reqPartB_eq`, `afterPB_eq`, `verifyPB_eq`:
    each function with B is its namesake with P: for every `Lf`, g and all arguments: no hypothesis
    beside whatever the arguments hold as proofs.

Limits: how often the evaluator computes what is a fact about this compiler, no theorem. The family
g must itself give its answers as data first (`famP`, Run/CodingFnThin.lean). This file does not say
that `verifyP` is the run of the library's verifier: Run/ThinTie.lean, Run/ThinTieProofs.lean. It
says nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.ThinDefs

set_option autoImplicit false

namespace Run.Thin
open Iop Rom Compile Compile.Batch Run.Twin

/-! ## The walks commute with a map of digests -/

section Nat
variable {D D' : Type} [Inhabited D] [Inhabited D'] (φ : D → D')
  (hN : D → D → D) (hN' : D' → D' → D')

theorem headD_map (hd : φ default = default) (l : List D) :
    (l.map φ).headD default = φ (l.headD default) := by
  cases l with
  | nil => exact hd.symm
  | cons _ _ => rfl

omit [Inhabited D] [Inhabited D'] in
theorem loneF_map (h : ∀ a b, φ (hN a b) = hN' (φ a) (φ b)) (i : ℕ) (a s : D) :
    φ (Octopus.loneF hN i a s) = Octopus.loneF hN' i (φ a) (φ s) := by
  unfold Octopus.loneF
  split
  · exact h a s
  · exact h s a

theorem stepF_sib (i j : ℕ) (l : List ℕ) (v s : List D) (hs : Octopus.sib i j) :
    Octopus.stepF hN (i :: j :: l) v s =
      hN (v.headD default) (v.tail.headD default) :: Octopus.stepF hN l v.tail.tail s := by
  simp only [Octopus.stepF, Octopus.stepC, if_pos hs]
  rfl

theorem stepF_lone (i j : ℕ) (l : List ℕ) (v s : List D) (hs : ¬ Octopus.sib i j) :
    Octopus.stepF hN (i :: j :: l) v s =
      Octopus.loneF hN i (v.headD default) (s.headD default) ::
        Octopus.stepF hN (j :: l) v.tail s.tail := by
  simp only [Octopus.stepF, Octopus.stepC, if_neg hs]
  rfl

/-- Under `hd` and `h`: one level of the pruned walk commutes with the map φ of digests. -/
theorem stepF_map (hd : φ default = default) (h : ∀ a b, φ (hN a b) = hN' (φ a) (φ b)) :
    ∀ (js : List ℕ) (v s : List D),
      Octopus.stepF hN' js (v.map φ) (s.map φ) = (Octopus.stepF hN js v s).map φ
  | [], _, _ => rfl
  | [i], v, s => by
      show [Octopus.loneF hN' i ((v.map φ).headD default) ((s.map φ).headD default)] =
        [φ (Octopus.loneF hN i (v.headD default) (s.headD default))]
      rw [headD_map φ hd, headD_map φ hd, loneF_map φ hN hN' h]
  | i :: j :: l, v, s => by
      by_cases hs : Octopus.sib i j
      · rw [stepF_sib hN' i j l _ _ hs, stepF_sib hN i j l v s hs, List.map_cons, headD_map φ hd,
          ← List.map_tail, headD_map φ hd, ← List.map_tail, stepF_map hd h l, h]
      · rw [stepF_lone hN' i j l _ _ hs, stepF_lone hN i j l v s hs, List.map_cons,
          headD_map φ hd, headD_map φ hd, ← List.map_tail, ← List.map_tail,
          stepF_map hd h (j :: l), loneF_map φ hN hN' h]

/-- Under `hd` and `h`: the pruned walk commutes with the map φ of digests. -/
theorem octF_map (hd : φ default = default) (h : ∀ a b, φ (hN a b) = hN' (φ a) (φ b)) :
    ∀ (d : ℕ) (js : List ℕ) (v s : List D),
      Octopus.octF hN' d js (v.map φ) (s.map φ) = (Octopus.octF hN d js v s).map φ
  | 0, _, _, _ => rfl
  | d + 1, js, v, s => by
      show Octopus.octF hN' d (Octopus.up js) (Octopus.stepF hN' js (v.map φ) (s.map φ))
          ((s.map φ).drop (Octopus.need1 js)) =
        (Octopus.octF hN d (Octopus.up js) (Octopus.stepF hN js v s)
          (s.drop (Octopus.need1 js))).map φ
      rw [stepF_map φ hN hN' hd h, ← List.map_drop, octF_map hd h d]

omit [Inhabited D] [Inhabited D'] in
/-- Under `h`: the walk along one path commutes with the map φ of digests. -/
theorem climbF_map (h : ∀ a b, φ (hN a b) = hN' (φ a) (φ b)) :
    ∀ (path : List D) (j : ℕ) (c : D), climbF hN' (path.map φ) j (φ c) = φ (climbF hN path j c)
  | [], _, _ => rfl
  | s :: ss, j, c => by
      rw [List.map_cons, climbF_cons, climbF_cons, ← climbF_map h ss]
      congr 1
      split
      · exact (h c s).symm
      · exact (h s c).symm

end Nat

/-! ## Digests as bits -/

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X) (g : Fam (spec lam K (Lf ())))

/-- The bits of the digest that stands where none is there. -/
def dfltB (lam : ℕ) : Bits := List.ofFn (default : Dig lam)

/-- A vertex, on bits. Its result is data: it is computed where it stands. -/
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
def reqCheckB (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam)) (c : Dig lam) :
    Bool :=
  if path.length = depthReq ∧ slot < 2 ^ depthReq then
    decide (climbF (rnodeB Lf g) (path.map List.ofFn) slot
        (List.ofFn (g OracleName.rleaf (List.ofFn c : Bits) : Dig lam)) = List.ofFn rtreq)
    else false

def reqPartB (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam)) (ph : Phase lam) :
    Bool :=
  match ph.slotVal with
  | none => true
  | some c => reqCheckB Lf g depthReq rtreq slot path c

variable {Y : Type} {E : ExtSpec}

/-- What follows the chain and the format's test: the definition of `afterP` (Run/ThinDefs.lean),
the two walks on bits. -/
def afterPB (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  match forestsOfP Lf P wq embS embE cms x π ρ rts with
  | some Fs =>
      if (flatP Lf Fs).length ≤ wq.nOpen ∧
          (flatP Lf Fs).all (fun c => wellP Lf c && decide (c.depth ≤ wq.maxDepth)) then
        runForestsB Lf g Fs (readsP Lf Fs) && reqPartB Lf g depthReq π.rtreq π.slot π.path ph &&
          P.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
            (trP P.S P.ann wq.sh rts π.plains ρ π.opens)
      else false
  | none => false

/-- The verifier, its walks on bits. -/
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

/-! ## The equations with the functions of Run/ThinDefs.lean -/

theorem nodeB_ofFn (a b : Dig lam) :
    List.ofFn (nodeP Lf g a b) = nodeB Lf g (List.ofFn a) (List.ofFn b) := rfl
theorem rnodeB_ofFn (a b : Dig lam) :
    List.ofFn (rnodeP Lf g a b) = rnodeB Lf g (List.ofFn a) (List.ofFn b) := rfl

theorem decide_ofFn (a b : Dig lam) : decide (List.ofFn a = List.ofFn b) = decide (a = b) := by
  by_cases h : a = b
  · subst h
    simp
  · rw [decide_eq_false h, decide_eq_false fun e => h (List.ofFn_injective e)]

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
    (path : List (Dig lam)) (c : Dig lam) :
    reqCheckB Lf g depthReq rtreq slot path c = reqCheckP Lf g depthReq rtreq slot path c := by
  unfold reqCheckB reqCheckP
  split
  · rw [climbF_map List.ofFn (rnodeP Lf g) (rnodeB Lf g) (rnodeB_ofFn Lf g), decide_ofFn]
  · rfl

theorem reqPartB_eq (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ)
    (path : List (Dig lam)) (ph : Phase lam) :
    reqPartB Lf g depthReq rtreq slot path ph = reqPartP Lf g depthReq rtreq slot path ph := by
  unfold reqPartB reqPartP
  cases ph.slotVal with
  | none => rfl
  | some c => exact reqCheckB_eq Lf g _ _ _ _ _

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

/-- The verifier with its walks on bits is `verifyP`, at all arguments. -/
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

end Run.Thin
