-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/CodingFnThin.lean.
Run/CodingFnThin.lean: the functions of Run/CodingFn.lean (from a typed query to the hash call of
the format of the programs (the C++ implementation that comes with this Lean code); the typed oracle
functions that a function on the format's strings induces) in a form made for the evaluator: the
interface behind a function of Unit; every answer's hash computed once. And their ties to the
present ones. Definitions that compute; five theorems.
Why, first. A round carries, as data, the list of all its verifier messages; the ambient interface
(BatchProtocolWithLeafBody) holds shapes, so rounds. Compiled Lean is strict: a function that has the interface as a
parameter, even an implicit one that stands in types alone, may get it built at the call: hopeless
for one drawn field element. The principle followed in these files: no function on the run's path
has a parameter of the type of a round, a shape, a protocol or the interface. In its place: the
interface behind a function of Unit, an explicit argument Lf, the types written at Lf (). A closure
is handed on and never called.
Why, second. A digest is a function of the bit's number. Where a branch of a match has a function's
type, the compiler puts the whole branch under a λ (seen in its output): the call of the hash with
it: so the hash is computed anew for every bit that is asked: 256 calls for one digest. A "let" in
the branch, a match on the bytes' number, an inlined helper: none of them helps: all go under the λ.
What helps: the answer first as data (famB: an array of byte strings, whose type is no function's),
computed in a function whose result type the compiler cannot see to be a function's (famP: the
oracle's name is a variable there), and only then decoded (decP).
    fbCallP Lf D K q j, leafCallP Lf D q  the texts of fbCall, leafCall, with D : PageD (Lf ()) (a
        record's projections have no such parameter)
    digS b  32 bytes as a digest; no byte: zeros
    bytesP O c  the answer of O at a call, as bytes; no byte where there is no call
    blocksP  the K + 1 blocks of a chain answer, as bytes
    famB Lf O D K o q  the answer to a typed query as an array of byte strings: one for a leaf or a
        node, K + 1 for a chain query under the tag of the data D (a parameter tg: any of the three
        tags), none under another tag
    decP Lf K o a  the bytes as a typed answer
    famP Lf O D K  the typed oracle functions: o, q ↦ decP o (famB o q)
    fbCallP_eq, leafCallP_eq  at Lf := fun _ => L they are fbCall, leafCall (by definition; by cases
        on the query's body)
    digS_eq, ansP_eq, famP_eq  digS = bytesToDig; digS (bytesP O c) = ansOf O c; famP (fun _ => L) O
        D K = famOf O D K
What was tried (in files outside this library, each run from another file than this one; a round
with a trace in its instance; an oracle with a trace). How often the oracle is asked when all 256
bits of each digest are read: a node: famP 1, famOf 256; a node and a leaf in a list: famP 2; a
chain answer of three blocks: famP 3, famOf more than 400 (the count was cut off); the same values.
The list of verifier messages: built by famP at a node, a leaf, a chain query of round 0 and of
round 1: never. But in these tests famOf did not build it either (the compiler drops the unused
parameter); a control that reads a field of the interface did. So for the list these tests show no
difference between the two forms: the form of this file rests on the principle, which holds whatever
the compiler does.
What is not said. What the evaluator builds or computes how often is a fact about this compiler, no
theorem. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library: a test by Lean's evaluator, which
   leaves no declaration. So nothing that is checked of declarations is checked of such a run. No
   clause of a soundness theorem of this library speaks of a run. -/
import Run.CodingFnThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
import OnBytes.TypedOracleCompiler.Run.CodingFnTag

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
export _root_.Run (digS bytesP digS_eq ansP_eq)

variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) {tg : Tag}

/-- A chain query and a block of its answer. -/
def fbCallP (D : PageD (Lf ()) tg) (K : Nat) (q : FbIn 256 (Lf ()) tg) (j : Fin (K + 1)) :
    Option _root_.Fmt.OQ :=
  match q.round, q.head with
  | 0, .f1 [pd] x salt =>
      if j.val = K then
        some ⟨0, 160, 0, D.label, _root_.Fmt.zero32, firstBytes (digToBytes pd) (D.stm x) salt⟩
      else none
  | i + 1, .f2 none ρ =>
      let b := blockNo (D.work (i + 1)) K j
      some ⟨UInt8.ofNat (b % 2),
        162, D.label, i + 1, bitsToBytes ρ,
        roundBytes (D.msg (i + 1) (q.rt.map digToBytes) q.plain) (D.kind (i + 1)) (D.work (i + 1))
          (b / 2) (D.nonce (i + 1) q.plain)⟩
  | _, _ => none

/-- A leaf query. -/
def leafCallP (D : PageD (Lf ()) tg) (q : LeafIn (Lf ())) : Option _root_.Fmt.OQ :=
  (D.leaf q.body).map fun z =>
    ⟨0, 164, z.1, z.2.1, bitsToBytes (q.salt.take 256), z.2.2 ++ bitsToBytes (q.salt.drop 256)⟩

/-- the K + 1 blocks of a chain answer as bytes, computed once -/
def blocksP (O : ByteArray → ByteArray) (D : PageD (Lf ()) tg) (K : Nat) (q : FbIn 256 (Lf ()) tg) :
    Array ByteArray :=
  Array.ofFn (n := K + 1) fun j => bytesP O (fbCallP Lf D K q j)

/-- THE ANSWER TO A TYPED QUERY AS BYTES: data: one string for a leaf or a node, K + 1 for a chain
query, none elsewhere. IT IS COMPUTED WHERE IT STANDS -/
def famB (O : ByteArray → ByteArray) (D : PageD (Lf ()) tg) (K : Nat) :
    (o : (typedOracleFamily 256 K (Lf ())).ι) → (typedOracleFamily 256 K (Lf ())).Dom o → Array ByteArray
  | .leaf, q => #[bytesP O (leafCallP Lf D q)]
  | .node, q => #[bytesP O (nodeCallC D.cfg q)]
  | .fb t', q =>
      match castTag (F := fun t => FbIn 256 (Lf ()) t) tg t' q with
      | some q => blocksP Lf O D K q
      | none => #[]
  | _, _ => #[]

/-- the bytes as a typed answer -/
def decP (K : Nat) : (o : (typedOracleFamily 256 K (Lf ())).ι) → Array ByteArray → (typedOracleFamily 256 K (Lf ())).Rng o
  | .leaf, a => digS (a.getD 0 ByteArray.empty)
  | .node, a => digS (a.getD 0 ByteArray.empty)
  | .fb _, a => (fun k => digS (a.getD k.val ByteArray.empty), digS (a.getD K ByteArray.empty))
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .rleaf, _ => fun _ => false
  | .rnode, _ => fun _ => false
  | .g _, _ => fun _ => false
  | .ann, _ => ()
  | .other, _ => fun _ => false

/-- The typed oracle functions that a function on the format's strings induces. -/
def famP (O : ByteArray → ByteArray) (D : PageD (Lf ()) tg) (K : Nat) : Fam (typedOracleFamily 256 K (Lf ())) :=
  fun o q => decP Lf K o (famB Lf O D K o q)

variable {L : BatchProtocolWithLeafBody I X}

theorem fbCallP_eq (D : PageD L tg) (K : Nat) (q : FbIn 256 L tg) (j : Fin (K + 1)) :
    fbCallP (fun _ => L) D K q j = fbCall D K q j := rfl

theorem leafCallP_eq (D : PageD L tg) (q : LeafIn L) :
    leafCallP (fun _ => L) D q = leafCall D q := rfl

/-- THE TIE. -/
theorem famP_eq (O : ByteArray → ByteArray) (D : PageD L tg) (K : Nat) :
    famP (fun _ => L) O D K = famOf O D K := by
  funext o q
  cases o with
  | leaf =>
      show digS (bytesP O (leafCallP (fun _ => L) D q)) = ansOf O (leafCall D q)
      rw [leafCallP_eq, ansP_eq]
  | node =>
      show digS (bytesP O (nodeCallC D.cfg q)) = ansOf O (nodeCallC D.cfg q)
      rw [ansP_eq]
  | fb t =>
      by_cases ht : t = tg
      · subst ht
        have e1 : famB (fun _ => L) O D K (.fb t) q = blocksP (fun _ => L) O D K q := by
          simp only [famB, castTag_self]
        have e2 : famOf O D K (.fb t) q =
            ((fun k : Fin K => ansOf O (fbCall D K q k.castSucc)),
              ansOf O (fbCall D K q (Fin.last K))) :=
          famOf_fb_self O D K q
        show ((fun k : Fin K =>
              digS ((famB (fun _ => L) O D K (.fb t) q).getD k.val ByteArray.empty)),
            digS ((famB (fun _ => L) O D K (.fb t) q).getD K ByteArray.empty)) = _
        rw [e1, e2]
        have hb : ∀ j : Fin (K + 1),
            digS ((blocksP (fun _ => L) O D K q).getD j.val ByteArray.empty) =
              ansOf O (fbCall D K q j) := by
          intro j
          unfold blocksP
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos j.isLt]
          exact ansP_eq O _
        refine Prod.ext ?_ ?_
        · funext k
          exact hb k.castSucc
        · exact hb (Fin.last K)
      · have e1 : famB (fun _ => L) O D K (.fb t) q = #[] := by
          simp only [famB, castTag_ne ht]
        have e2 : famOf O D K (.fb t) q = ((fun _ _ => false), fun _ => false) :=
          famOf_fb_ne O D K ht q
        show ((fun k : Fin K =>
              digS ((famB (fun _ => L) O D K (.fb t) q).getD k.val ByteArray.empty)),
            digS ((famB (fun _ => L) O D K (.fb t) q).getD K ByteArray.empty)) = _
        rw [e1, e2]
        rfl
  | fbw _ _ => rfl
  | rleaf => rfl
  | rnode => rfl
  | g _ => rfl
  | ann => rfl
  | other => rfl

end TypedOracleCompiler.Run
