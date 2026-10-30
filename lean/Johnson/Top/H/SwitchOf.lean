-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/SwitchOf.lean: a maker of callers of the code switch, at which the locations' half of
the kind's condition holds by construction; and what every block of the kind hands on and reads.

Definitions, statements and proofs.

A caller of the kind "SEND seed, LOC with a rider" is a size `Cb.Pv.SendLocRide.Size`
(Cb/Pv/Switch/SendLocRide.lean). Its condition has two halves: four clauses on the family that is
sent (`LdSendD.HypK`, Cb/Thin/Kinds/Send.lean), and that the base joint behind the sending is,
clause by clause, "an open test whose witness is read off the messages" (`LdLocD.HypK`,
Cb/Thin/Kinds/Loc.lean). Here the base joint before the sending is the library's joint with an open
test (`heldB`, Cb/Req1/LdSegKit.lean) over a joint B that is carried, and the open word's witness is
read off the new messages alone. Then the second half is true by unfolding.
Main names:
  `KObj.SwI`: the data: the open messages, the open word's code with radius and number of positions,
    the held messages, the claim on the open word, the carried joint B, the family that is sent, how
    the open word's message and randomness are read off it, the rider's code.
  `KObj.SwI.size`: the caller. `KObj.SwI.loc_hypK`: the locations' half, if the held messages have
    their laws. `KObj.SwI.ok_iff`: the kind's condition is the four clauses on the family and these
    laws.
  `KObj.swRdIn`, `KObj.swRdOut`, `KObj.sw_hands`: for every size: the block hands on the rest of the
    explicit part with the open messages' samples, and the further oracles with the open messages'
    words.
  `KObj.sw_reads`: for every size: the symbols in the statement that the block leaves are the open
    word's long symbols at the positions that the verifier drew.
Limits: the honest sender in `SwI.size` is made up: nothing is said on an honest prover. That a
switch of the programs' protocol is a value of `SwI` is not said. Nothing is said of any value.
-/
import Johnson.Top.H.SendLocRide
import Johnson.E.KObj.PFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop IOR Cb VerifiableInference.OnPublicFiles

/-- the data of a caller of the code switch -/
structure SwI (E : Type) [Field E] [Fintype E] : Type 1 where
  Kc  : Type
  /-- the oracle messages that are open before the sending -/
  S₀  : Sig E
  /-- the open word's code, the radius, the number of positions -/
  P   : Type
  [finP : Fintype P]
  [neP : Nonempty P]
  C   : LdCode E P
  e   : ℕ
  t   : ℕ
  /-- the messages held in the open word -/
  hd  : LdHeld E C
  Xc  : Type
  St₀ : Type
  E₀  : ExtSpec
  /-- the claim on the open word's message -/
  Φ   : Xc → (C.J → E) → Prop
  /-- what is carried: a joint on messages M, which are read off the open and the held messages -/
  M   : Type
  Wq  : Type
  rd  : S₀.Msg → (∀ k, (hd.o k).Msg) → M
  B   : IOR.Rels Kc St₀ E₀ (M × Wq)
  /-- the family that is sent, its seeds, bounds for its lists -/
  N   : Sig E
  Sd  : N.Seeds
  L   : N.O → ℕ
  /-- (message, randomness) of the open word, as the new messages have them -/
  cutN : N.Msg → C.N.Wit
  /-- the extractor's value where nothing is extracted -/
  w₀  : S₀.Wit × (C.N.Wit × Wq)
  /-- the rider's long positions and its code -/
  Pw  : Type
  Cw  : LdCode E Pw

attribute [instance] SwI.finP SwI.neP

namespace SwI
variable {E : Type} [Field E] [Fintype E] (c : SwI E)

/-- the base joint before the sending: an open test over what is carried -/
@[reducible] def A₀ : IOR.Rels c.Kc ((c.Xc × c.hd.Smp) × c.St₀) (c.C.ext.prod c.E₀)
    (c.S₀.Msg × (c.C.N.Wit × c.Wq)) :=
  heldB c.C c.e c.hd c.Φ c.rd c.B

/-- the stage before the sending -/
@[reducible] def stage : LdStage E c.Kc :=
  ⟨c.S₀, (c.Xc × c.hd.Smp) × c.St₀, c.C.ext.prod c.E₀, c.C.N.Wit × c.Wq, c.A₀⟩

/-- a sender of which nothing is asked -/
@[reducible] def sender : c.N.Sender (c.S₀.Wit × (c.C.N.Wit × c.Wq)) (c.S₀.Wit × c.Wq) where
  Nn := ⟨Unit, Unit, fun _ _ a => (c.N.om a).sy0, fun _ => none⟩
  upM := fun _ _ _ => 0
  upR := fun _ _ _ => 0
  Mk := Unit
  put := fun _ _ => ()
  rest := fun w => (w.1, w.2.2)
  w0 := c.w₀

/-- the sending -/
@[reducible] def send : LdSendD c.stage where
  N := c.N
  Sd := c.Sd
  Wp' := c.Wq
  bk := fun m wq => (c.cutN m, wq)
  D := c.sender
  L := c.L
  t := fun _ => 0

/-- the open word's witness, read off all messages behind the sending -/
@[reducible] def cut : (c.S₀.sum c.N).Msg → c.C.N.Wit := fun m =>
  c.cutN (c.S₀.right c.N (T := OMsg.Msg) m)

/-- what is carried, behind the locations -/
@[reducible] def A₁ : IOR.Rels c.Kc c.St₀ c.E₀ ((c.S₀.sum c.N).Msg × c.Wq) where
  rel  := fun x y w => c.B.rel x y
    (c.rd (c.S₀.left c.N (T := OMsg.Msg) w.1) (c.hd.msg (c.cut w.1).1), w.2)
  relR := fun a w => c.B.relR a
    (c.rd (c.S₀.left c.N (T := OMsg.Msg) w.1) (c.hd.msg (c.cut w.1).1), w.2)
  on   := c.B.on
  core := fun w => c.B.core
    (c.rd (c.S₀.left c.N (T := OMsg.Msg) w.1) (c.hd.msg (c.cut w.1).1), w.2)

/-- the switch without the rider -/
@[reducible] def sw : Cb.Pv.SendLoc.Size E where
  Kc := c.Kc
  S₀ := c.S₀
  P := c.P
  C := c.C
  e := c.e
  t := c.t
  hd := c.hd
  Xc := c.Xc
  St₀ := c.St₀
  Wp₀ := c.C.N.Wit × c.Wq
  E₀ := c.E₀
  Φ := c.Φ
  A₀ := c.A₀
  d := c.send
  cut := c.cut
  A₁ := c.A₁
  w₀ := c.w₀

/-- the caller -/
@[reducible] def size : Cb.Pv.SendLocRide.Size E := ⟨c.sw, c.Pw, c.Cw⟩

/-- The locations' half of the condition holds by construction. -/
theorem loc_hypK (h : c.hd.Laws c.e) : (Cb.Pv.SendLoc.loc c.sw).HypK where
  relR := fun _ _ => Iff.rfl
  on := fun _ => Iff.rfl
  laws := h

/-- The kind's condition at a made caller: four clauses on the family that is sent, and the held
messages' laws. -/
theorem ok_iff : Cb.Pv.SendLocRide.OK c.size ↔
    ((∀ i, (c.N.om i).C.Laws) ∧ c.Sd.Fair ∧ (∀ i, (c.N.om i).ListLE (c.L i)) ∧
      ∀ i, (c.N.om i).Evades) ∧ c.hd.Laws c.e :=
  ⟨fun h => ⟨⟨h.1.laws, h.1.fair, h.1.list, h.1.evades⟩, h.2.laws⟩,
    fun h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2⟩, c.loc_hypK h.2⟩⟩

end SwI

/-! ### what every block of the kind hands on and reads -/

section
variable {E : Type} [Field E] [Fintype E] (s : Cb.Pv.SendLocRide.Size E)

/-- before the block: the rest of the explicit part with the open messages' samples; the further
oracles with the open messages' words -/
@[reducible] def swRdIn : Rd (s.sw.St₀ × s.sw.S₀.Smp) (s.sw.E₀.Str × s.sw.S₀.ext.Str)
    (jOf (Cb.Pv.SendLocRide.inJ s)) :=
  ⟨fun x => (x.1.2, x.2), fun y => (y.1.2, y.2)⟩

/-- behind the block: the same, among what has come -/
@[reducible] def swRdOut : Rd (s.sw.St₀ × s.sw.S₀.Smp) (s.sw.E₀.Str × s.sw.S₀.ext.Str)
    (jOf (Cb.Pv.SendLocRide.outJ s)) :=
  ⟨fun x => (x.1.2, s.sw.S₀.left s.sw.d.N (T := OMsg.Smp) x.2),
    fun y => (y.1.1, s.sw.S₀.left s.sw.d.N (T := OMsg.Str) y.1.2)⟩

/-- Every block of the kind hands these on. -/
theorem sw_hands : ((kSendLocRide [s]).block s).Hands (swRdIn s) (swRdOut s) where
  passes := fun x y τ x' h => by
    have e := Option.some.inj (h : some _ = some x')
    rw [← e]
    rfl
  copy := fun _ _ => rfl

/-- The symbols in the statement that the block leaves are the open word's long symbols at the
positions drawn. -/
theorem sw_reads (x : (Cb.Pv.SendLoc.stage s.sw).X) (y : (Cb.Pv.SendLoc.stage s.sw).Ex.Str)
    (τ : Tr (Cb.Pv.SendLocRide.R s).shape) (x' : (Cb.Pv.SendLoc.loc s.sw).tgt.X)
    (h : (Cb.Pv.SendLocRide.R s).out x y τ = some x') :
    x'.1.1.2.2 = fun i => s.sw.C.T y.1.1 (x'.1.1.2.1 i) := by
  have e := Option.some.inj (h : some _ = some x')
  rw [← e]
  rfl

end

#print axioms KObj.SwI.ok_iff
#print axioms KObj.sw_hands
#print axioms KObj.sw_reads

end KObj
