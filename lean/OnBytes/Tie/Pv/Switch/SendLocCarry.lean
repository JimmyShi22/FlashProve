-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Switch/SendLocCarry.lean: the two rounds "SEND seed" and "LOC" of the code switch
between two groups of a request's chain, carried from the written rounds to the typed rounds.
Definitions, statements and proofs.

What it is for. The typed block (`Cb.Pv.SendLocRide.R`, Cb/Pv/Switch/SendLocRide.lean) has as its
first round ((the rider's word, the members' words) . a joint seed) and as its second ((the members'
answers, nothing) . t long positions). The written rounds of a file's chain have other prover's
messages (roots, words, a nonce) and other verifier's messages (what the chain's hash gives).
Soundness is carried from typed rounds to written rounds along maps of messages, round by round
(`Carry`, OnBytes/Slice/Carry.lean). This file has these maps for the two rounds, general in the
written rounds r₁, r₂ and in five readings.

Main names:
  `Readings s r₁ r₂`: the five readings: the rider's word and the members' words off the first
    written prover's message; the joint seed off the first written verifier's message (none where it
    has no reading); the answers off the second written prover's message; the positions off the
    second written verifier's message (none where it has no reading). The later ones may look at all
    that was sent before.
  `carry s ρ`: the maps. `carry_fib`: if at most w₁ written verifier's messages are read as one
    joint seed, and at most w₂ as one tuple of positions, the maps have `Carry.Fib` at (w₁, w₂).
  `carry_tr`: a written transcript has an image exactly where both verifier's messages have a
    reading, and which.
  `carry_out`: on the image the typed reduction rejects nothing, and what it puts out: the readings
    of the positions, of the seed and of the answers, and the long symbols of the open word at the
    positions read.
  `carry_err`: the carried errors: the sending's times w₁, the locations' times w₂.
Limits: r₁, r₂ and the readings are letters: nothing says that r₁, r₂ are the rounds that a
description of the programs' protocol has at the plan's entries, nor that the readings read what the
program's routine receives there (what a run of that routine has done, call by call:
OnBytes/Tie/Pv/Switch/LocRun.lean). The size s is a letter too.
-/
import OnBytes.Slice.Carry
import Cb.Pv.Switch.SendLocRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Switch
open Iop Prob OnBytes.Slice Cb Cb.Pv

variable {E : Type} [Field E] [Fintype E] (s : SendLocRide.Size E) (r₁ r₂ : Round)

/-- The five readings. -/
structure Readings where
  /-- the rider's word -/
  mask  : r₁.Msg → s.Cw.Word
  /-- the members' words -/
  words : r₁.Msg → s.sw.d.N.ext.Str
  /-- the joint seed -/
  seed  : r₁.Msg → r₁.Chal → Option s.sw.d.Sd.D
  /-- the members' answers -/
  answ  : r₁.Msg → r₁.Chal → r₂.Msg → s.sw.d.N.Answ
  /-- the positions -/
  pos   : r₁.Msg → r₁.Chal → r₂.Msg → r₂.Chal → Option (Fin s.sw.t → s.sw.P)

variable {s r₁ r₂} (ρ : Readings s r₁ r₂)

/-- The maps of the two rounds. -/
def carry : Slice.Carry [r₁, r₂] (SendLocRide.R s).shape :=
  (fun m => ((ρ.mask m, ρ.words m), ((), ())), ρ.seed, fun m c =>
    (fun m₂ => (((), ()), (ρ.answ m c m₂, ())), ρ.pos m c, fun _ _ => ()))

theorem carry_fib (w₁ w₂ : ℕ) (h₁ : ∀ m c', cnt (fun c => ρ.seed m c = some c') ≤ w₁)
    (h₂ : ∀ m c m₂ c', cnt (fun c₂ => ρ.pos m c m₂ c₂ = some c') ≤ w₂) :
    (carry ρ).Fib (w₁, w₂, ()) :=
  ⟨h₁, fun m c => ⟨h₂ m c, fun _ _ => trivial⟩⟩

/-- The image of a written transcript. -/
theorem carry_tr (τ : Tr [r₁, r₂]) :
    (carry ρ).tr τ =
      (ρ.seed τ.1 τ.2.1).bind fun sd => (ρ.pos τ.1 τ.2.1 τ.2.2.1 τ.2.2.2.1).map fun Qs =>
        (((ρ.mask τ.1, ρ.words τ.1), ((), ())), sd,
          (((), ()), (ρ.answ τ.1 τ.2.1 τ.2.2.1, ())), Qs, ()) := by
  obtain ⟨m, c, m₂, c₂, u⟩ := τ
  show (ρ.seed m c).bind (fun sd => ((ρ.pos m c m₂ c₂).bind fun Qs =>
    (some ()).map fun τ' => (_, Qs, τ')).map fun τ' => (_, sd, τ')) = _
  cases ρ.seed m c with
  | none => rfl
  | some sd =>
    cases ρ.pos m c m₂ c₂ with
    | none => rfl
    | some Qs => rfl

/-- On the image the typed reduction puts out the readings. -/
theorem carry_out (x : (SendLoc.stage s.sw).X) (y : (SendLoc.stage s.sw).Ex.Str) (τ : Tr [r₁, r₂])
    (sd : s.sw.d.Sd.D) (Qs : Fin s.sw.t → s.sw.P) (h₁ : ρ.seed τ.1 τ.2.1 = some sd)
    (h₂ : ρ.pos τ.1 τ.2.1 τ.2.2.1 τ.2.2.2.1 = some Qs) :
    ∃ τ', (carry ρ).tr τ = some τ' ∧
      (SendLocRide.R s).red.out (x, y) τ' =
        some ((((x.1.1, (Qs, fun i => s.sw.C.T y.1.1 (Qs i))), x.1.2),
            s.sw.S₀.join s.sw.d.N (T := OMsg.Smp) x.2
              fun a => (s.sw.d.Sd.sd a sd, ρ.answ τ.1 τ.2.1 τ.2.2.1 a)),
          ((y.1.2, s.sw.S₀.join s.sw.d.N (T := OMsg.Str) y.2 (ρ.words τ.1)), ρ.mask τ.1)) := by
  refine ⟨(((ρ.mask τ.1, ρ.words τ.1), ((), ())), sd,
    (((), ()), (ρ.answ τ.1 τ.2.1 τ.2.2.1, ())), Qs, ()), ?_, rfl⟩
  rw [carry_tr, h₁, h₂]
  rfl

/-- The carried errors. -/
theorem carry_err (w₁ w₂ : ℕ) :
    Err.toList (Slice.mulErr [r₁, r₂] (SendLocRide.R s).shape (w₁, w₂, ()) (SendLocRide.eps s)) =
      [ldSendFamErr s.sw.d.N s.sw.d.Sd s.sw.d.L * w₁,
        (Fintype.card s.sw.P - s.sw.e - 1) ^ s.sw.t * w₂] := by
  have h := SendLocRide.errs s
  show [(SendLocRide.eps s).1 * w₁, (SendLocRide.eps s).2.1 * w₂] = _
  have h' : [(SendLocRide.eps s).1, (SendLocRide.eps s).2.1] =
      [ldSendFamErr s.sw.d.N s.sw.d.Sd s.sw.d.L, (Fintype.card s.sw.P - s.sw.e - 1) ^ s.sw.t] := h
  injection h' with a b
  injection b with b _
  rw [a, b]

end OnBytes.Tie.Pv.Switch

#print axioms OnBytes.Tie.Pv.Switch.carry_fib
#print axioms OnBytes.Tie.Pv.Switch.carry_out
#print axioms OnBytes.Tie.Pv.Switch.carry_err
