-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Switch/SendLoc.lean: the code switch between two groups of a request's chain, as one kind of
block of two rounds: the sending of a family of oracle messages whose round of answers is closed by
the positions of the open word of the group before.

In the programs' plan of a request's chain a group behind the first begins with a round "SEND seed"
and a round "LOC". In the first the prover sends, as one oracle, the word into which the folded word
of the group before is encoded anew, the kept messages anew, and further oracle messages; the
verifier answers with one joint seed. In the second the prover sends each message's answers in the
plain part of its message, and the verifier answers with t long positions of the OLD open word,
which it reads. The claims that come of it are not batched: they are left as claims on the messages
of the new group.

The library has this switch as two moves of a request's preamble (Cb/Req1/LdSegKit.lean): one
sending (`LdSendD`: two rounds, the second with a verifier's message of one value) and the locations
(`LdLocD`: one round in which nothing is sent). In a row they have three rounds. This file merges
the second and the third by the library's rule for such rounds (case (J1) of Iop/Join.lean), applied
to a reduction (Cb/Pv/Switch/Recut.lean). Nothing of the two moves is stated anew. Definitions and
proofs.

Main names:
  `Size`: what the block is made of: the stage before (the open oracle messages S₀; the open word's
    code C, the radius e, the number t of positions, the messages held in the open word; the base
    joint A₀), the library's record d of the sending from that stage, and what the locations need
    beside: how the open word's message and randomness are read off the messages behind the sending
    (cut), and what else is claimed (A₁).
  `stage s`, `loc s`: the stage before; the library's record of the locations. The stage behind the
    sending IS the stage before the locations, by definition (`seam`).
  `long s`: the two moves in a row: three rounds. `plan s`: the plan that merges the last two.
  `R`, `eps`, `ext`, `inJ`, `outJ`: the reduction, TWO rounds; its errors; the extractor; the two
    joints: that of the stage before, and that of the stage behind the locations.
  `HAt s`: the statement at the size s: the reduction is round-by-round knowledge sound on the
    statements of `inJ`, between the two relaxed relations, at `eps s`.
  `OK s`: the condition: `LdSendD.HypK` and `LdLocD.HypK` (Cb/Thin/Kinds/Send.lean, Loc.lean).
  `hAt`: the statement holds under `OK s`.
  `point`, `isLocal`, `onOut`: beside it, under `OK s`. `rounds`, `errs`, `vals`: two rounds; the
    errors: the sending's, a count of joint seeds, and the locations', a count of tuples of
    positions; the numbers of values of the verifier's messages.
Limits: IN THE PROGRAMS EVERY "SEND seed, LOC" OF A PROOF's FIRST CHAIN BEARS A RIDER, the fresh
mask of the new group's fold, an oracle without a sample (OnBytes/Iop/Req.lean, `ReqFrame.first`,
`ReqFrame.finish`; OnBytes/Iop/Fold.lean, `foldMaskNotice`): so `Size` has a value at no place of
such a chain. The kind with the rider is Cb/Pv/Switch/SendLocRide.lean, which is built on this file.
Nothing says that a pair of rounds of a chain of the programs is a value of `Size`, that
`OK` holds there, or that the errors are small. Every oracle message of the first round is a member
of the family d.N, with a sample: an oracle without a sample in that message (a rider) is not
treated. The second round's prover message is the pair of the two old messages (`Round.joinMsg`,
Iop/Join.lean). Nothing on an honest prover. The errors are bare counts for one instance: nothing on
proof of work, nothing on several instances.
-/
import Cb.Pv.Switch.Recut
import Cb.Thin.Kinds.Send
import Cb.Thin.Kinds.Loc
import Ior.KnowCollRulesChainErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.SendLoc
open Iop Prob IOR Cb

/-- What the block is made of. -/
structure Size (E : Type) [Field E] [Fintype E] : Type 1 where
  /-- the type of cores -/
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
  Wp₀ : Type
  E₀  : ExtSpec
  /-- the claim on the open word's message -/
  Φ   : Xc → (C.J → E) → Prop
  /-- the base joint before the sending -/
  A₀  : IOR.Rels Kc ((Xc × hd.Smp) × St₀) (C.ext.prod E₀) (S₀.Msg × Wp₀)
  /-- the sending -/
  d   : LdSendD (⟨S₀, (Xc × hd.Smp) × St₀, C.ext.prod E₀, Wp₀, A₀⟩ : LdStage E Kc)
  /-- (message, randomness) of the open word, as the messages behind the sending have them -/
  cut : (S₀.sum d.N).Msg → C.N.Wit
  /-- what else is claimed behind the locations -/
  A₁  : IOR.Rels Kc St₀ E₀ ((S₀.sum d.N).Msg × d.Wp')
  /-- the extractor's value where the sending's verifier rejects -/
  w₀  : S₀.Wit × Wp₀

attribute [instance] Size.finP Size.neP

variable {E : Type} [Field E] [Fintype E] (s : Size E)

/-- The stage before the sending. -/
@[reducible] def stage : LdStage E s.Kc :=
  ⟨s.S₀, (s.Xc × s.hd.Smp) × s.St₀, s.C.ext.prod s.E₀, s.Wp₀, s.A₀⟩

/-- The library's record of the locations: its base joint is what the sending makes of A₀. -/
@[reducible] def loc : LdLocD E s.Kc where
  S := s.S₀.sum s.d.N
  P := s.P
  C := s.C
  e := s.e
  t := s.t
  hd := s.hd
  Xc := s.Xc
  St₀ := s.St₀
  Wp := s.d.Wp'
  E₀ := s.E₀
  Φ := s.Φ
  cut := s.cut
  A₁ := s.A₁
  A := s.S₀.grow s.d.N s.A₀ s.d.bk

/-- The stage behind the sending is the stage before the locations. -/
theorem seam : s.d.tgt = (loc s).src := rfl

/-- The two moves in a row: three rounds. -/
noncomputable def long : IOR.Link s.Kc (stage s).J (loc s).tgt.J := s.d.link.seq (loc s).link s.w₀

/-- The plan: the first round stays; the round of the answers, whose verifier's message has one
value, is merged with the round of the positions, in which nothing is sent. -/
noncomputable def plan : XPlan (long s).R.shape := .keep _ (.msg _ _ () (.keep _ .nil))

/-- The reduction: two rounds. -/
noncomputable def R : IOR (stage s).X (stage s).Ex (loc s).tgt.X (loc s).tgt.Ex :=
  (long s).R.recut (plan s)

/-- The errors. -/
noncomputable def eps : Err (R s).shape := Err.recut (plan s) (long s).P.err

/-- The extractor: that of the two moves in a row, on the transcript read back. -/
noncomputable def ext : (stage s).X × (stage s).Ex.Str → Tr (R s).shape → (loc s).tgt.W → (stage
  s).W :=
  fun a τ w => (long s).ext a (Tr.old (plan s) τ) w

/-- The joint before the block. -/
def inJ : Rels s.Kc (stage s).X (stage s).Ex (stage s).W := (stage s).J.rels

/-- The joint behind the block: the symbols read are claimed of the messages. -/
def outJ : Rels s.Kc (loc s).tgt.X (loc s).tgt.Ex (loc s).tgt.W := (loc s).tgt.J.rels

/-- The statement that the block at the size s is knowledge sound. -/
def HAt : Prop := (R s).red.Know (inJ s).on (inJ s).relR (outJ s).relR (ext s) (eps s)

/-- The condition. -/
def OK : Prop := s.d.HypK ∧ (loc s).HypK

theorem long_goodK (h : OK s) : (long s).GoodK :=
  goodK_seq _ _ _ (s.d.goodK h.1) ((loc s).goodK h.2)

theorem plan_ok : (plan s).OK := ⟨fun _ => rfl, trivial⟩

/-- The statement holds under the condition. -/
theorem hAt (h : OK s) : HAt s :=
  recut_know (long s).R (plan s) _ _ _ _ _ (long_goodK s h).know

/-! ### beside the statement -/

theorem point (h : OK s) : Nonempty (R s).shape.IsPoint :=
  recut_point (long s).R (plan s) () (long_goodK s h).point

theorem isLocal (h : OK s) : (R s).IsLocal :=
  recut_isLocal (long s).R (plan s) (long_goodK s h).isLocal (plan_ok s)

theorem onOut (h : OK s) : ∀ a τ b, (inJ s).on a → (R s).red.out a τ = some b → (outJ s).on b :=
  fun a τ b ha hb => (long_goodK s h).onOut a (Tr.old (plan s) τ) b ha hb

/-- The verifier never rejects. -/
theorem never_rejects (x : (stage s).X) (y : (stage s).Ex.Str) (τ : Tr (R s).shape) :
    ((R s).out x y τ).isSome := rfl

theorem rounds : (R s).shape.length = 2 := rfl

/-- The errors: the sending's first; the locations'. The answers' round adds nothing: its error in
the library is 0, and its verifier's message has one value. -/
theorem errs :
    Err.toList (eps s) = [ldSendFamErr s.d.N s.d.Sd s.d.L, (Fintype.card s.P - s.e - 1) ^ s.t] := by
  show [ldSendFamErr s.d.N s.d.Sd s.d.L, 0 * Fintype.card (Fin s.t → s.P) +
    Fintype.card Unit * (Fintype.card s.P - s.e - 1) ^ s.t] = _
  simp

theorem vals :
    Shape.chalList (R s).shape = [Fintype.card s.d.Sd.D, Fintype.card (Fin s.t → s.P)] := rfl

end Cb.Pv.SendLoc

#print axioms Cb.Pv.SendLoc.hAt
#print axioms Cb.Pv.SendLoc.point
#print axioms Cb.Pv.SendLoc.isLocal
#print axioms Cb.Pv.SendLoc.onOut
#print axioms Cb.Pv.SendLoc.errs
