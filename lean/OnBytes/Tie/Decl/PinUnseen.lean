-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Decl/PinUnseen.lean: when a pin by a property is not seen: if every string with the
property that an algorithm asks is one at which the table holds the oracle's own value, the pinned
algorithm has under that oracle the value of the algorithm itself. With it: what the law on the
reading's calls with the number 169 buys.

OnBytes/Tie/Decl/ProofPre.lean answers every query of the proof file's reading at a public string by
a table. Its Limits name what is not shown there: that the public strings which the reading asks are
the three strings of the chains' parameter bytes. Here that law is a NAMED PROPERTY
(`ProofOnly169`), and what follows from it is proved. Definitions, statements and proofs.

Main names:
  `det_pinP_of_asks`: general: see above.
  `ProofOnly169 asm c table copy request words block file`: every string of a call with the number
    169 that the asking half (`typedPR`, OnBytes/Tie/ProofAsked.lean) asks is the string of the call
    on the parameter bytes of one of the three chains.
  `pin_unseen`: under `ProofOnly169`, with the property "a call with the number 169": under EVERY
    family g at whose three strings the table holds g's own values, the pinned asking half has the
    value of the asking half itself.
Limits: `ProofOnly169` is shown of no reading in this file. The law is owed to whoever shows a yes
under a drawn function; no bound rests on it. No probability.

-/
import OnBytes.Tie.Decl.ProofPre
import OnBytes.Slice.WalkOff
import Rom.AsksIn

set_option autoImplicit false

namespace OnBytes.Tie

open Rom
open _root_.Iop (Dig)
open OnBytes.Params (TableName ProofChains)
open OnBytes.Proof (FirstEnd ProofRead)

/-- If every string with P that c asks is one at which T holds g's own value, the pin is not seen
under g. -/
theorem det_pinP_of_asks {lam : ℕ} {α : Type} (P : List Bool → Prop) [DecidablePred P]
    (T : List Bool → Dig lam) (g : Fam (rom lam)) (c : OComp (rom lam) α)
    (h : c.AsksIn fun _ (s : List Bool) => P s → T s = g () s) :
    (pinP P T c).det g = c.det g := by
  induction c with
  | pure a => rfl
  | query o s k ih =>
    cases o
    by_cases hs : P s
    · simp only [pinP, if_pos hs, OComp.det]
      rw [h.1 hs]
      exact ih _ (h.2 _)
    · simp only [pinP, if_neg hs, OComp.det]
      exact ih _ (h.2 _)
  | sample n k ih =>
    simp only [pinP, OComp.det]
    exact ih _ (h _)

/-- THE LAW, AS A NAMED PROPERTY. -/
def ProofOnly169 {Out : Type} (asm : ProofRead → Option Out) (c : ProofChains) (table : TableName)
    (copy : Nat) (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) : Prop :=
  (typedPR asm c table copy request words block file).AsksIn fun _ (s : List Bool) =>
    OnBytes.Slice.IsCall169 s →
      s = strPar c.first.given.bytes ∨ s = strPar c.shared.given.bytes ∨
        s = strPar c.second.given.bytes

/-- **What the law buys.** -/
theorem pin_unseen {Out : Type} [DecidablePred OnBytes.Slice.IsCall169]
    (asm : ProofRead → Option Out) (c : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray)
    (h : ProofOnly169 asm c table copy request words block file)
    (T : List Bool → Dig 256) (g : Fam (rom 256))
    (h1 : T (strPar c.first.given.bytes) = g () (strPar c.first.given.bytes))
    (h2 : T (strPar c.shared.given.bytes) = g () (strPar c.shared.given.bytes))
    (h3 : T (strPar c.second.given.bytes) = g () (strPar c.second.given.bytes)) :
    (pinP OnBytes.Slice.IsCall169 T (typedPR asm c table copy request words block file)).det g =
      (typedPR asm c table copy request words block file).det g := by
  refine det_pinP_of_asks _ T g _ (OComp.AsksIn.mono (fun _ s hs h9 => ?_) h)
  rcases hs h9 with e | e | e
  · rw [e]; exact h1
  · rw [e]; exact h2
  · rw [e]; exact h3

end OnBytes.Tie

#print axioms OnBytes.Tie.det_pinP_of_asks
#print axioms OnBytes.Tie.pin_unseen
