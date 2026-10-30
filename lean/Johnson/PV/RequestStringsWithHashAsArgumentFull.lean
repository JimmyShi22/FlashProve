-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/RequestStringsWithHashAsArgumentFull.lean: THE REQUEST's TWO STRINGS WITH THE SECOND HASH FUNCTION AS AN ARGUMENT, AT THE FULL
SIZE. `PV.RunArgsF.spF` (Johnson/PV/RunArgsFull.lean) makes the statement's item "request" by `OnBytes.Flat.itemOf`, so by
`OnBytes.Proof.requestItem`, which calls the format's second hash function BY NAME (`OnBytes.secondHashFunction`, through `secondHashFunctionTree` and the
call lists' digests). The goals hand every description a function o in that function's place (`VerifierAndGoals.SecondHashFunctionType`, which is
ℕ → ByteArray → ByteArray by unfolding; Ladder.lean is not imported here).
  `spFO o pol KL x`     the same two strings, the item by `Fmt.requestItem o` (Fmt/RequestItem.lean), in which the
                        hash function is the argument.
  `spFO_older`         at o := OnBytes.secondHashFunction it is `spF`: by `requestItem_eq`
                        (OnBytes/Tie/Decl/RequestItemLaw.lean): a theorem, not an unfolding.
  `apartFO`, `hreqFO`   `apartF` and `hreqF` (Johnson/PV/MFullOne.lean) AT EVERY o: the proofs read the pair's second part alone,
                        which no hash function enters.
spF, apartF and hreqF keep their bytes: other files' proofs unfold them.
Limits. Definitions and three small laws. Nothing says that a verifier calls spFO. Nothing on soundness. The item's five groups
that are digests are digests under o: at an o with collisions two requests may share the FIRST string; the second string is the
request file's own bytes, and `apartFO` rests on it alone.

-/
import Johnson.PV.MFullOne
import OnBytes.Tie.Decl.RequestItemLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PV.RunArgsF
open OnBytes OnBytes.Flat VerifiableInference.OnPublicFiles

/-- The request's two strings, at the function o in the second hash function's place. -/
def spFO (o : ℕ → ByteArray → ByteArray) (pol KL : ByteArray) (x : ReqAt Inst.Model.ppref) : ByteArray × ByteArray :=
  ((Fmt.requestItem o pol KL (requestBytesOf x.val)).getD ByteArray.empty, requestBytesOf x.val)

/-- **At the format's own second hash function it is `spF`.** -/
theorem spFO_older (pol KL : ByteArray) : spFO OnBytes.secondHashFunction pol KL = spF pol KL := by
  funext x
  unfold spFO spF itemOf
  rw [OnBytes.Tie.Decl.RequestItemLaw.requestItem_eq]

end PV.RunArgsF

namespace PV.MFull
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker OnBytes.Maker.Page _root_.Run
open TypedOracleCompiler.Run TypedOracleCompiler.Run.SerArm VerifiableInference.OnPublicFiles
open PV.OkOwn (okOwnF)

/-- On its yeses the request's two strings are one to one, at every o. -/
theorem apartFO (o : ℕ → ByteArray → ByteArray) (pol KL : ByteArray) (x y : ReqAt Inst.Model.ppref) (hx : okOwnF x = true)
    (hy : okOwnF y = true) (e : PV.RunArgsF.spFO o pol KL x = PV.RunArgsF.spFO o pol KL y) : x = y := by
  unfold PV.RunArgsF.spFO at e
  exact PV.OkOwn.ownF_apart x y hx hy (Prod.mk.inj e).2

/-- So are the typed instance's two strings, on what passes the written test, at every o. -/
theorem hreqFO (o : ℕ → ByteArray → ByteArray) (pol KL : ByteArray) (r₀ : RecFull)
    (z z' : Option (ReqAt Inst.Model.ppref) × RecFull × RecFull)
    (h : ((match z.1 with
      | some x => okOwnF x
      | none => false) && isAt serRecFull r₀ z.2.1 && isAt serRecFull r₀ z.2.2) = true)
    (h' : ((match z'.1 with
      | some x => okOwnF x
      | none => false) && isAt serRecFull r₀ z'.2.1 && isAt serRecFull r₀ z'.2.2) = true)
    (e : (z.1.map (PV.RunArgsF.spFO o pol KL)).getD default =
      (z'.1.map (PV.RunArgsF.spFO o pol KL)).getD default) : z = z' := by
  obtain ⟨a, r1, r2⟩ := z
  obtain ⟨a', r1', r2'⟩ := z'
  cases a with
  | none => simp at h
  | some x =>
    cases a' with
    | none => simp at h'
    | some x' =>
      simp only [Bool.and_eq_true] at h h'
      obtain rfl := apartFO o pol KL x x' h.1.1 h'.1.1 e
      rw [(isAt_iff serRecFull r₀ r1).1 h.1.2, (isAt_iff serRecFull r₀ r2).1 h.2,
        (isAt_iff serRecFull r₀ r1').1 h'.1.2, (isAt_iff serRecFull r₀ r2').1 h'.2]

end PV.MFull

#print axioms PV.RunArgsF.spFO_older
#print axioms PV.MFull.apartFO
#print axioms PV.MFull.hreqFO
