-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQXFast.lean: the run function for entry files (Run/PlanQXRun.lean: `runEntry`) in a form
made for evaluation, with a proof that the verdict is the same.

Why this file exists. A digest is a function of the bit's number. Where a branch of a match has a
function's type, the compiler puts the call of the hash under a λ, and the hash is computed again
for every bit that is asked (Run/CodingFnThin.lean explains this at length). Run/PlanQXRun.lean's
`famX` has that form. The remedy is Run/CodingFnThin.lean's: form the answer first as data (an array
of byte strings), then decode it (`decP`); and make the K + 1 blocks of a later round from one kept
state of the hash (Run/CodingFnKeep.lean: `blocksK`, which is generic in the tag).

1. What the file contains.
   `famXB D dec K o q`: the answer to a typed query, as bytes. For a leaf (stored or own) or a node
     (`.leaf`, `.node`) it has one string. Under the tag "link" (`.fb .link`) it has K + 1 strings
     for the first query (round 0), and those of `blocksK` for a later round. Elsewhere: no string
     (the empty array).
   `famXK D dec K`: the typed oracle functions.
   `VXK`, `runEntryK`: the verifier and the run function at `famXK`.

2. What is checked when the file compiles. Only the types and the proofs.

3. Theorems.
   `famXK_eq`: famXK D dec K = famX D dec Fmt.oracle K.
   `vxk_eq`, `runEntryK_eq`: VXK = VX and runEntryK = runEntry, at all arguments.

Notation:
  `D`: the description of the proof's rounds, statement and stored tables' openings (`XD`,
    Run/PlanQXRun.lean);
  `r0`, `r1`: the two roots of `VPX`, as bytes (Run/PlanQX.lean);
  `.limits`: the outcome where `D.ok` is false (`Who`, Run/PlanQRun.lean);
  `.reader`: the outcome where `readHead`, `wholeChainX` or `toBPrfX` gives `none`;
  `.verifier`: the outcome where `VXK` is false.

4. What is not claimed. How often the evaluator computes what is a fact about this compiler, not a
   theorem.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQXRun

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch

/-- The answer to a typed query as bytes. -/
def famXB (D : XD) (dec : View → Bool) (K : Nat) :
    (o : (spec 256 K (D.L dec)).ι) → (spec 256 K (D.L dec)).Dom o → Array ByteArray
  | .leaf, q => #[bytesP _root_.Fmt.oracle (leafX D dec q)]
  | .node, q => #[bytesP _root_.Fmt.oracle (nodeCallC D.base.cfg q)]
  | .fb .link, q =>
      if q.round = 0 then
        Array.ofFn (n := K + 1) fun j => bytesP _root_.Fmt.oracle (firstX D dec K q j)
      else blocksK (tg := .link) (fun _ => D.L dec) (PDX D dec) K q
  | _, _ => #[]

/-- The typed oracle functions. -/
def famXK (D : XD) (dec : View → Bool) (K : Nat) : Fam (spec 256 K (D.L dec)) :=
  fun o q => decP (fun _ => D.L dec) K o (famXB D dec K o q)

/-- The verifier. -/
def VXK (D : XD) (dec : View → Bool) (r0 r1 : ByteArray)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) : Bool :=
  VPX (I := Unit) (RI := Unit) D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec
    (fun _ _ p => (p.val, [])) (fun _ => some ()) (famXK D dec (D.K + 1))
    (256 + 8 * D.base.plan.salt) (bytesToDig r0) (bytesToDig r1) π

/-- The run function at `VXK`: from an entry file to an outcome. -/
def runEntryK (D : XD) (dec : View → Bool) (r0 file : ByteArray) : Who :=
  if D.ok then
    match readHead file with
    | none => .reader
    | some (r1, rest) =>
      match (_root_.Fmt.wholeChainX (m := Id) _root_.Fmt.formatHash (D.atR r0 r1) rest).bind
          (toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec) with
      | none => .reader
      | some π => if VXK D dec r0 r1 π then .accepted else .verifier
  else .limits

namespace Spec

def famXK_eq : Prop :=
  ∀ (D : XD) (dec : View → Bool) (K : Nat), famXK D dec K = famX D dec _root_.Fmt.oracle K

def vxk_eq : Prop :=
  ∀ (D : XD) (dec : View → Bool) (r0 r1 : ByteArray)
      (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up),
    VXK D dec r0 r1 π = VX D dec r0 r1 π

def runEntryK_eq : Prop :=
  ∀ (D : XD) (dec : View → Bool) (r0 file : ByteArray),
    runEntryK D dec r0 file = runEntry D dec r0 file

end Spec

theorem firstX_later (D : XD) (dec : View → Bool) (K : Nat) (q : FbIn 256 (D.L dec) .link)
    (j : Fin (K + 1)) (h : q.round ≠ 0) :
    firstX D dec K q j = fbCall (PDX D dec) K q j := by
  unfold firstX
  split
  · exact absurd (by assumption) h
  · exact absurd (by assumption) h
  · rfl

theorem famXK_eq : Spec.famXK_eq := by
  intro D dec K
  funext o q
  cases o with
  | leaf =>
      show digS (bytesP _root_.Fmt.oracle (leafX D dec q)) = ansOf _root_.Fmt.oracle (leafX D dec q)
      rw [ansP_eq]
  | node =>
      show digS (bytesP _root_.Fmt.oracle (nodeCallC D.base.cfg q)) =
        ansOf _root_.Fmt.oracle (nodeCallC D.base.cfg q)
      rw [ansP_eq]
  | fb t =>
      cases t with
      | link =>
          have hb : ∀ j : Fin (K + 1),
              digS ((famXB D dec K (.fb .link) q).getD j.val ByteArray.empty) =
                ansOf _root_.Fmt.oracle (firstX D dec K q j) := by
            intro j
            by_cases h0 : q.round = 0
            · have e : famXB D dec K (.fb .link) q =
                  Array.ofFn (n := K + 1) fun j => bytesP _root_.Fmt.oracle (firstX D dec K q j) :=
                if_pos h0
              rw [e, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos j.isLt]
              exact ansP_eq _ _
            · have e : famXB D dec K (.fb .link) q =
                  blocksK (tg := .link) (fun _ => D.L dec) (PDX D dec) K q := if_neg h0
              rw [e, blocksK_eq, firstX_later D dec K q j h0]
              unfold blocksP
              rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos j.isLt]
              exact ansP_eq _ _
          show ((fun k : Fin K => digS ((famXB D dec K (.fb .link) q).getD k.val ByteArray.empty)),
              digS ((famXB D dec K (.fb .link) q).getD K ByteArray.empty)) =
            ((fun k : Fin K => ansOf _root_.Fmt.oracle (firstX D dec K q k.castSucc)),
              ansOf _root_.Fmt.oracle (firstX D dec K q (Fin.last K)))
          refine Prod.ext ?_ ?_
          · funext k
            exact hb k.castSucc
          · exact hb (Fin.last K)
      | test => rfl
      | onl => rfl
  | fbw _ _ => rfl
  | rleaf => rfl
  | rnode => rfl
  | g _ => rfl
  | ann => rfl
  | other => rfl

theorem vxk_eq : Spec.vxk_eq := fun D dec r0 r1 π => by
  unfold VXK VX
  rw [famXK_eq]

theorem runEntryK_eq : Spec.runEntryK_eq := fun D dec r0 file => by
  unfold runEntryK runEntry
  simp only [vxk_eq D dec]
  rfl

end Run.PQ
