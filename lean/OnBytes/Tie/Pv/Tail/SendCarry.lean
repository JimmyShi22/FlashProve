-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/SendCarry.lean: the two written rounds of a sending of oracle messages, carried
to the two typed rounds of the library's sending of a family.

The library's sending (ldSendFam, Cb/Ld/LdSendFam.lean; Cb/Pv/Send.lean) has two rounds: the prover
sends all words as one oracle and the verifier draws a joint seed; the prover sends the answers of
all members and the verifier says nothing. It puts out the statement with a sample for each member:
the member's seed and its answers; the words go to the implicit instance. In the protocol that a
file holds, the first round's verifier message is hash blocks, out of which the format's sampler
makes field elements, and the second round's prover's message holds the answers as items. This file
has the maps from the written rounds (roundT, OnBytes/Maker/Trees.lean) to the typed ones in the
form that OnBytes/Slice/Carry.lean asks for, and ties the typed output on the image to what the Lean
verifier's sending block has taken off the view (OnBytes/Tie/Pv/Tail/SendRan.lean). Definitions,
statements and proofs.

Main names:
  `ansT d m`: the answers among the items of a written prover's message, read in the library's
    field. `ans_read`, `ansT_of_took`: they are the readings of the answers that the block took.
  `SendRead d₁ d₂ s`: three readings, as letters: the words behind the first written prover's
    message; the joint seed that a list of field elements stands for; the members' answers that a
    list of field elements stands for.
  `carrySend`: the maps. A verifier message goes to nothing if its round's test of work fails.
  `carrySend_fib`: at most w₁ written verifier messages of the first round go to one joint seed,
    and at most w₂ of the second to the one typed value, where w₁, w₂ are the sampler's own bounds;
    if the joint seed determines the typed values, and the second round draws nothing.
  `carrySend_tr`: a written transcript whose two tests of work pass has an image.
  `send_out`: on the image the typed sending puts out the statement with, for each member, its seed
    out of the joint seed and its answers; and the words.
  `send_typed`: where the sending block has run on the view of the written transcript: the joint
    seed is read off the very elements out of which the block has cut its seeds, and the answers
    off the very answers that it has taken.

Limits: the three readings are letters. That the words are what stands behind the roots that the
channel has counted is not said: between a written round and the words stands the step from trees to
words. That sdOf gives each member the seed that the block's own cutting gives it, and that anOf
lays the answers in the block's order, is not said. Nothing on soundness: the errors are carried by
OnBytes/Slice/Carry.lean's rule from `carrySend_fib`.
-/
import OnBytes.Tie.Pv.Tail.SendRan
import Cb.Pv.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Iop Prob OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker

/-- The answer that an item holds, read in the library's field, if it is one. -/
def gotAns : Fmt.ItemValue → Option GE
  | .answer t => some (toE t)
  | _ => none

/-- The answers among the items of a written prover's message. -/
def ansT (d : RDT) (m : (roundT (Run.ckP .two) d).up.Msg) : List GE :=
  (Run.PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2)).filterMap gotAns

theorem ans_read : ∀ l : List E,
    (l.map fun x => Fmt.ItemValue.answer x.triple).filterMap gotAns = l.map Reading.gl.val
  | [] => rfl
  | a :: l => by
    have h : gotAns (Fmt.ItemValue.answer a.triple) = some (toE a.triple) := rfl
    rw [List.map_cons, List.filterMap_cons_some h, ans_read l]
    rfl

/-- Three readings, as letters. -/
structure SendRead (d₁ : RDT) (s : Cb.Pv.Send.Size GE) where
  /-- the words behind the first written prover's message -/
  words : (roundT (Run.ckP .two) d₁).up.Msg → s.N.ext.Str
  /-- the joint seed that a list of elements stands for -/
  sdOf  : List GE → s.Sd.D
  /-- the members' answers that a list of elements stands for -/
  anOf  : List GE → s.N.Answ

section
variable {d₁ : RDT} (d₂ : RDT) {s : Cb.Pv.Send.Size GE} (Q : SendRead d₁ s)

/-- The joint seed of the typed values of the first written verifier message. -/
def SendRead.seed (v : Run.Vals .two (Fmt.dsOf d₁.entry d₁.kind)) : s.Sd.D := Q.sdOf (elemsV _ v)

/-- The maps from the two written rounds to the two typed rounds. -/
def carrySend : Slice.Carry [(roundT (Run.ckP .two) d₁).up, (roundT (Run.ckP .two) d₂).up]
    (s.N.sh s.Sd) :=
  (fun m => (Q.words m, ()), fun _ c => chalTo (rdOf d₁) Q.seed c, fun _ _ =>
    (fun m₂ => ((), Q.anOf (ansT d₂ m₂)), fun _ c₂ => chalTo (rdOf d₂) (fun _ => ()) c₂,
      fun _ _ => ()))

/-- How many written verifier messages go to one typed one. -/
theorem carrySend_fib (hinj : Function.Injective Q.seed) (h₂ : OnlyTrits (rdOf d₂) 0)
    (hl₁ : d₁.entry.logN ≤ 64) (hl₂ : d₂.entry.logN ≤ 64) :
    (carrySend d₂ Q).Fib (((Run.bsRound .two d₁.entry d₁.kind).w,
      (Run.bsRound .two d₂.entry d₂.kind).w, ()) : ℕ × ℕ × Unit) :=
  ⟨fun _ c' => chalTo_fib (rdOf d₁) Q.seed hinj hl₁ c', fun _ _ =>
    ⟨fun _ c' => chalTo_fib (rdOf d₂) (fun _ => ())
      (fun _ _ _ => bitsL_inj h₂ (funext fun i => i.elim0)) hl₂ c', fun _ _ => trivial⟩⟩

/-- The image of a written transcript whose two tests of work pass. -/
theorem carrySend_tr (m₁ : (roundT (Run.ckP .two) d₁).up.Msg)
    (w₁ : (roundT (Run.ckP .two) d₁).up.Chal) (m₂ : (roundT (Run.ckP .two) d₂).up.Msg)
    (w₂ : (roundT (Run.ckP .two) d₂).up.Chal) (p₁ : GChal.pass (b := d₁.entry.work) w₁ = true)
    (p₂ : GChal.pass (b := d₂.entry.work) w₂ = true) :
    (carrySend d₂ Q).tr ((m₁, w₁, m₂, w₂, ()) :
        Tr [(roundT (Run.ckP .two) d₁).up, (roundT (Run.ckP .two) d₂).up]) =
      some (((Q.words m₁, ()), Q.seed (valsOf (rdOf d₁) w₁), ((), Q.anOf (ansT d₂ m₂)), (), ()) :
        Tr (s.N.sh s.Sd)) := by
  have e₁ : chalTo (rdOf d₁) Q.seed w₁ = some (Q.seed (valsOf (rdOf d₁) w₁)) := if_pos p₁
  have e₂ : chalTo (rdOf d₂) (fun _ => ()) w₂ = some () := if_pos p₂
  show (chalTo (rdOf d₁) Q.seed w₁).bind (fun c' =>
    ((chalTo (rdOf d₂) (fun _ => ()) w₂).bind fun c'' => (some ()).map fun τ' =>
      (((), Q.anOf (ansT d₂ m₂)), c'', τ')).map fun τ' => ((Q.words m₁, ()), c', τ')) = _
  rw [e₁, e₂]
  rfl

/-- What the typed sending puts out on the image. -/
theorem send_out (X : Type) (E₀ : ExtSpec) (x : X) (y : E₀.Str)
    (m₁ : (roundT (Run.ckP .two) d₁).up.Msg) (w₁ : (roundT (Run.ckP .two) d₁).up.Chal)
    (m₂ : (roundT (Run.ckP .two) d₂).up.Msg) :
    (Cb.Pv.Send.R s X E₀).red.out (x, y)
        (((Q.words m₁, ()), Q.seed (valsOf (rdOf d₁) w₁), ((), Q.anOf (ansT d₂ m₂)), (), ()) :
          Tr (s.N.sh s.Sd)) =
      some ((x, fun a => (s.Sd.sd a (Q.seed (valsOf (rdOf d₁) w₁)), Q.anOf (ansT d₂ m₂) a)),
        (y, Q.words m₁)) := rfl

end

/-- The answers among the second written message's items are the readings of the answers that the
sending block took. -/
theorem ansT_of_took {x x' : Ctx} {notices : Array OracleNotice} {ids : Array Nat} {r₁ : Fmt.RoundView}
    {d₂ : RDT} {m₂ : (roundT (Run.ckP .two) d₂).up.Msg} {dr₂ : Fmt.Drawn}
    {shapes : List OracleShape} {seeds : List SampleSeed} {ans : List E}
    (T : SendTook x notices ids x' r₁
      ⟨Run.PQ.PlainOf.gots d₂.items (GPlain.old (b := d₂.entry.work) m₂.2), dr₂⟩ shapes seeds
      ans) :
    ansT d₂ m₂ = ans.map Reading.gl.val := by
  have e : Run.PQ.PlainOf.gots d₂.items (GPlain.old (b := d₂.entry.work) m₂.2) =
      ans.map fun x => Fmt.ItemValue.answer x.triple := T.vals₂
  unfold ansT
  rw [e]
  exact ans_read ans

/-- Where the sending block has run on the view of the written transcript: the typed sample is read
off the elements out of which the block has cut its seeds and off the answers that it has taken.
The first half holds of every written verifier message; the run enters the second half alone. -/
theorem send_typed {d₁ d₂ : RDT} {s : Cb.Pv.Send.Size GE} (Q : SendRead d₁ s) {x x' : Ctx}
    {notices : Array OracleNotice} {ids : Array Nat} {m₁ : (roundT (Run.ckP .two) d₁).up.Msg}
    {w₁ : (roundT (Run.ckP .two) d₁).up.Chal} {m₂ : (roundT (Run.ckP .two) d₂).up.Msg}
    {dr₂ : Fmt.Drawn} {shapes : List OracleShape} {seeds : List SampleSeed} {ans : List E}
    (T : SendTook x notices ids x'
      ⟨Run.PQ.PlainOf.gots d₁.items (GPlain.old (b := d₁.entry.work) m₁.2),
        (Run.ckP .two).dr d₁.entry d₁.kind (GChal.old (b := d₁.entry.work) w₁)⟩
      ⟨Run.PQ.PlainOf.gots d₂.items (GPlain.old (b := d₂.entry.work) m₂.2), dr₂⟩ shapes seeds
      ans) :
    Q.seed (valsOf (rdOf d₁) w₁) =
        Q.sdOf ((((Run.ckP .two).dr d₁.entry d₁.kind
          (GChal.old (b := d₁.entry.work) w₁)).elems.map E.ofTriple).map Reading.gl.val) ∧
      Q.anOf (ansT d₂ m₂) = Q.anOf (ans.map Reading.gl.val) :=
  ⟨congrArg Q.sdOf (seed_elems d₁ w₁).symm, congrArg Q.anOf (ansT_of_took T)⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.carrySend_fib
#print axioms OnBytes.Tie.Pv.Tail.carrySend_tr
#print axioms OnBytes.Tie.Pv.Tail.send_out
#print axioms OnBytes.Tie.Pv.Tail.ansT_of_took
#print axioms OnBytes.Tie.Pv.Tail.send_typed
