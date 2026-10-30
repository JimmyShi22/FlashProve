-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingFnThin.lean: the functions of Run/CodingFn.lean in a form made for the evaluator: the
interface behind a function of `Unit`; every answer's hash computed once; and theorems that they
equal those of Run/CodingFn.lean. The evaluator: what runs the tests (`#guard`) when a file is
compiled; not the kernel.

Definitions that compute; five theorems.
The functions of Run/CodingFn.lean send a typed query to the hash call of the format of the programs
(the C++ implementation that comes with this Lean code); `famOf` there gives the typed oracle
functions that a function on the format's strings induces.

Why, first: a round carries, as data, the list of all its verifier messages (`Round.finChal`,
Iop/Shape.lean), and the ambient interface (`BatchProtocol`, Iop/Batch.lean) holds shapes, so rounds. Compiled
Lean is strict: a function that has the interface as a parameter, even an implicit one that stands
in types alone, may get it built at the call. That is hopeless for one drawn field element. The
principle followed in this file is that no function of this file has a parameter of the type of a
round, a shape, a protocol or the interface. In its place stands the interface behind a function of
`Unit`, an explicit argument Lf, with the types written at Lf (). A closure is handed on and never
called.

Why, second: a digest is a function of the bit's number. Where a branch of a match has a function's
type, the compiler puts the whole branch under a λ (seen in its output), and the call of the hash
with it; so the hash is computed anew for every bit that is asked: 256 calls for one digest. A "let"
in the branch, a match on the bytes' number, an inlined helper: none of them helps, since all go
under the λ. What helps is the answer first as data (`famB`: an array of byte strings, whose type is
no function's), computed in a function whose result type the compiler cannot see to be a function's
(`famP`: the oracle's name is a variable there), and only then decoded (`decP`).

Main names:
  `fbCallP Lf D K q j`, `leafCallP Lf D q`: the texts of `fbCall`, `leafCall`, with D :
    PageD (Lf ()) tg (a record's projections are no functions of this file; by Lean's signatures
    those of `PageD` have the interface as an implicit parameter).
  `famP Lf O D K`: the typed oracle functions.
  `fbCallP_eq`, `leafCallP_eq`: at Lf := fun _ => L they are `fbCall`, `leafCall` (by definition; by
    cases on the query's body).
  `famP_eq`: famP (fun _ => L) O D K = famOf O D K.

What was tried: the trials are scratch files outside this development, each run from another file
than this one. They use a round with a trace in its instance and an oracle with a trace. They count
how often the oracle is asked when all 256 bits of each digest are read. At a node famP asked 1 time
and famOf 256 times. At a node and a leaf in a list famP asked 2 times. At a chain answer of three
blocks famP asked 3 times and famOf more than 400 times (the count was cut off). The values were the
same. At a node, a leaf, a chain query of round 0 and of round 1 famP never built the list of
verifier messages. But in these trials famOf did not build it either (the compiler drops the unused
parameter); a control that reads a field of the interface did. So for the list these trials show no
difference between the two forms. The form of this file rests on the principle, which holds whatever
the compiler does.

Limits: what the evaluator builds or computes how often is a fact about this compiler, no theorem.
This file says nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.CodingFnTag

set_option autoImplicit false

namespace Run
open Compile Compile.Batch Iop Rom

variable {I X : Type} (Lf : Unit → BatchProtocol I X) {tg : Tag}

/-- The call of a chain query and a block of its answer, if there is one. -/
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

/-- The call of a leaf query, if there is one. -/
def leafCallP (D : PageD (Lf ()) tg) (q : LeafIn (Lf ())) : Option _root_.Fmt.OQ :=
  match q.body with
  | some (.inr ⟨t', s⟩) =>
      (castTag (F := fun t => SymAny (shapeOf (Lf ()) t)) tg t' s).map fun s =>
        ⟨0, 164, (D.leaf s).1, (D.leaf s).2.1, bitsToBytes (q.salt.take 256),
          (D.leaf s).2.2 ++ bitsToBytes (q.salt.drop 256)⟩
  | _ => none

/-- 32 bytes as a digest, the bytes forced first; no byte: zeros. -/
def digS (b : ByteArray) : Dig 256 :=
  match b.size with
  | 0 => fun _ => false
  | _ + 1 => fun i => _root_.Fmt.bitAt b i.val

/-- The answer of O at a call, as bytes: data, so it is computed where it stands; no byte where
there is no call. -/
def bytesP (O : ByteArray → ByteArray) : Option _root_.Fmt.OQ → ByteArray
  | some c => O (strOf c)
  | none => ByteArray.empty

/-- The K + 1 blocks of a chain answer as bytes, computed once. -/
def blocksP (O : ByteArray → ByteArray) (D : PageD (Lf ()) tg) (K : Nat) (q : FbIn 256 (Lf ()) tg) :
    Array ByteArray :=
  Array.ofFn (n := K + 1) fun j => bytesP O (fbCallP Lf D K q j)

/-- The answer to a typed query as bytes: data: one string for a leaf or a node, K + 1 for a chain
query under the tag of the data D, none elsewhere. It is computed where it stands. -/
def famB (O : ByteArray → ByteArray) (D : PageD (Lf ()) tg) (K : Nat) :
    (o : (spec 256 K (Lf ())).ι) → (spec 256 K (Lf ())).Dom o → Array ByteArray
  | .leaf, q => #[bytesP O (leafCallP Lf D q)]
  | .node, q => #[bytesP O (nodeCallC D.cfg q)]
  | .fb t', q =>
      match castTag (F := fun t => FbIn 256 (Lf ()) t) tg t' q with
      | some q => blocksP Lf O D K q
      | none => #[]
  | _, _ => #[]

/-- The bytes as a typed answer. -/
def decP (K : Nat) : (o : (spec 256 K (Lf ())).ι) → Array ByteArray → (spec 256 K (Lf ())).Rng o
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
def famP (O : ByteArray → ByteArray) (D : PageD (Lf ()) tg) (K : Nat) : Fam (spec 256 K (Lf ())) :=
  fun o q => decP Lf K o (famB Lf O D K o q)

variable {L : BatchProtocol I X}

theorem fbCallP_eq (D : PageD L tg) (K : Nat) (q : FbIn 256 L tg) (j : Fin (K + 1)) :
    fbCallP (fun _ => L) D K q j = fbCall D K q j := rfl

theorem leafCallP_eq (D : PageD L tg) (q : LeafIn L) :
    leafCallP (fun _ => L) D q = leafCall D q := by
  obtain ⟨body, salt⟩ := q
  rcases body with _ | (_ | ⟨t, s⟩) <;> rfl

theorem digS_eq (b : ByteArray) : digS b = bytesToDig b := by
  unfold digS
  split
  · rename_i h
    funext i
    have hd : b.data.size = 0 := h
    simp [bytesToDig, _root_.Fmt.bitAt, _root_.Fmt.byteAt_eq, Array.getD, hd]
  · rfl

theorem ansP_eq (O : ByteArray → ByteArray) (c : Option _root_.Fmt.OQ) :
    digS (bytesP O c) = ansOf O c := by
  cases c with
  | none => rfl
  | some c => exact digS_eq _

/-- At the constant function Lf := fun _ => L, `famP` is `famOf` (Run/CodingFn.lean). -/
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

end Run
