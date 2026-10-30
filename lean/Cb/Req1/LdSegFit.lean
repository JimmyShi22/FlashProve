-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFit.lean: bridge-to-fold, the one sending, the locations: the three moves of a closing
fit together with nothing in between (one group).

Definitions, statements (Cb.Spec.ldSegFit_*) and proofs.
In standard terms: book-keeping for the end of a proximity test inside the preamble of a request, a
chain of interactive oracle reductions (`LdReq`, Cb/Req1/LdReq.lean). An open test is a claim of
proximity in its relaxed relation (`relR`): the folded word, still an oracle, is within e long
positions of the encoding of the witness's pair (message, randomness) (`heldB`,
Cb/Req1/LdSegKit.lean). The locations are its spot check: afterwards the explicit part has t
positions with the symbols read there, and the claim is that the encoding of the pair, now read off
the messages sent, has these symbols at these positions (`LdLocD.After`).
The data of the three moves are independent records (Cb/Req1/LdSegKit.lean: `LdFoldD`, `LdSendD`,
`LdLocD`). Here they are made from one record, and it is shown that the stages agree by definition.

Main names:
  `LdCloseD D`: for a bridge-to-fold D: the family N that is sent (what the closing carries on, kept
    messages encoded anew, and whatever rides along: the next segment's first messages); how the
    seeds are drawn; the further witness afterwards; cutN: (message, randomness) of the folded
    complex, as the messages of N hold them; bk₀: what else of the further witness the messages of N
    give back; the honest sender; bounds; t: the number of locations; the folded code has at least
    one long position (`neP`).
  `Q.snd : LdSendD D.tgt`: the one sending: the open test's witness moves into the new messages.
  `Q.loc : LdLocD`: the locations, with Q.loc.src = Q.snd.tgt by definition.
  `Q.foldP l`, `Q.locP`: the two lists of one move each.
  `Spec.ldSegFit_src`: Q.loc.src = Q.snd.tgt.
  `Spec.ldSegFit_near`: the stage after the sending is "an open test whose witness is read off the
    messages" (`LdLocD.Near`), clause by clause, by definition.
  `Spec.ldSegFit_hyp`: the hypotheses of the three moves from: `D.Hyp l` (`IOR.GoodT` of `l`, the
    fold returns the held messages, the laws of the slots) and the sending's seven (`Q.snd.Hyp`).
    The locations ask nothing more, beside whatever the arguments hold as proofs (for them:
    `Q.neP`, the folded code has at least one long position).
  `Spec.ldSegFit_after`: what is claimed at the end, in the relaxed relation (`relR`), written out:
    the folded form holds of the cut; the old samples' rows hold of the slots of the cut; the
    encoding of the cut has the symbols read; A₀ of (the messages that were not held, the slots of
    the cut).

Limits: this file says nothing on several groups (the open tests are nested; between two locations a
step re-brackets the explicit part). Nothing on layouts: cutN is any function.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

/-- The second half of the closing of one group: the data. -/
structure LdCloseD {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc) : Type 1 where
  N    : Sig E
  Sd   : N.Seeds
  Wp'  : Type
  /-- (message, randomness) of the folded complex, as the new messages hold them -/
  cutN : N.Msg → D.Cf.N.Wit
  /-- what else the new messages give back -/
  bk₀  : N.Msg → Wp' → D.Wp
  Sn   : N.Sender (D.tgt.S.Wit × D.tgt.Wp) (D.tgt.S.Wit × Wp')
  L    : N.O → ℕ
  tN   : N.O → ℕ
  /-- the number of locations -/
  t    : ℕ
  [neP : Nonempty D.Pf]

attribute [instance] LdCloseD.neP

namespace LdCloseD
variable {E Kc : Type} [Field E] [Fintype E] {D : LdFoldD E Kc} (Q : LdCloseD D)

/-- The one sending. -/
@[reducible] def snd : LdSendD D.tgt :=
  ⟨Q.N, Q.Sd, Q.Wp', fun n w' => (Q.cutN n, Q.bk₀ n w'), Q.Sn, Q.L, Q.tN⟩

/-- what else is claimed after the sending: A₀ of the messages that were not held and the slots of
the cut -/
def A₁ : Rels Kc D.St₀ D.E₀ ((D.S₂.sum Q.N).Msg × Q.Wp') where
  rel  := fun st y w =>
    D.A₀.rel st y
      (D.rd (D.S₂.left Q.N (T := OMsg.Msg) w.1)
          (D.held.msg (Q.cutN (D.S₂.right Q.N (T := OMsg.Msg) w.1)).1),
        Q.bk₀ (D.S₂.right Q.N (T := OMsg.Msg) w.1) w.2)
  relR := fun a w =>
    D.A₀.relR a
      (D.rd (D.S₂.left Q.N (T := OMsg.Msg) w.1)
          (D.held.msg (Q.cutN (D.S₂.right Q.N (T := OMsg.Msg) w.1)).1),
        Q.bk₀ (D.S₂.right Q.N (T := OMsg.Msg) w.1) w.2)
  on   := D.A₀.on
  core := fun w =>
    D.A₀.core (D.rd (D.S₂.left Q.N (T := OMsg.Msg) w.1)
          (D.held.msg (Q.cutN (D.S₂.right Q.N (T := OMsg.Msg) w.1)).1),
        Q.bk₀ (D.S₂.right Q.N (T := OMsg.Msg) w.1) w.2)

/-- The locations. -/
@[reducible] def loc : LdLocD E Kc where
  S := D.S₂.sum Q.N
  P := D.Pf
  neP := Q.neP
  C := D.Cf
  e := D.e
  t := Q.t
  hd := D.held
  Xc := E × D.Stf
  St₀ := D.St₀
  Wp := Q.Wp'
  E₀ := D.E₀
  Φ := D.slf.Holds
  cut := fun m => Q.cutN (D.S₂.right Q.N (T := OMsg.Msg) m)
  A₁ := Q.A₁
  A := Q.snd.tgt.A

/-- the lists of one move -/
def foldP (_ : LdCloseD D) (l : Link Kc D.src.J D.mid) : LdProg D.src D.tgt :=
  .snoc (.nil _) (.fold D l)
def locP : LdProg Q.snd.tgt Q.loc.tgt := .snoc (.nil _) (.loc Q.loc)

end LdCloseD

namespace Spec

def ldSegFit_src : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdFoldD E Kc) (Q : LdCloseD D), Q.loc.src = Q.snd.tgt

def ldSegFit_near : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdFoldD E Kc) (Q : LdCloseD D), Q.loc.Near

/-- The hypotheses of the three moves. -/
def ldSegFit_hyp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdFoldD E Kc)
      (Q : LdCloseD D) (l : Link Kc D.src.J D.mid),
    D.Hyp l → Q.snd.Hyp → (Q.foldP l).Hyp ∧ Q.snd.Hyp ∧ Q.locP.Hyp

/-- What is claimed at the end, in the relaxed relation. -/
def ldSegFit_after : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdFoldD E Kc) (Q : LdCloseD D) (x : Q.loc.tgt.St)
      (y : D.E₀.Str) (w : (D.S₂.sum Q.N).Msg × Q.Wp'),
    Q.loc.tgt.A.relR (x, y) w ↔
    (D.slf.Holds x.1.1.1 (Q.cutN (D.S₂.right Q.N (T := OMsg.Msg) w.1)).1 ∧
      (∀ k, (D.held.o k).Z.val (x.1.1.2 k).1
          (D.held.msg (Q.cutN (D.S₂.right Q.N (T := OMsg.Msg) w.1)).1 k) = (x.1.1.2 k).2) ∧
      (fun i =>
          D.Cf.T (D.Cf.enc (Q.cutN (D.S₂.right Q.N (T := OMsg.Msg) w.1)).1
              (Q.cutN (D.S₂.right Q.N (T := OMsg.Msg) w.1)).2) (x.1.2.1 i)) = x.1.2.2) ∧
    D.A₀.relR (x.2, y)
      (D.rd (D.S₂.left Q.N (T := OMsg.Msg) w.1)
          (D.held.msg (Q.cutN (D.S₂.right Q.N (T := OMsg.Msg) w.1)).1),
        Q.bk₀ (D.S₂.right Q.N (T := OMsg.Msg) w.1) w.2)

end Spec

theorem ldSegFit_src : Spec.ldSegFit_src := fun _ _ _ _ _ _ => rfl

theorem ldSegFit_near : Spec.ldSegFit_near := fun _ _ _ _ _ _ =>
  ⟨fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl, fun _ => rfl⟩

theorem LdProg.hyp_nil {E Kc : Type} [Field E] [Fintype E] (a : LdStage E Kc) :
    (LdProg.nil a).Hyp := by
  rw [LdProg.Hyp]; trivial

theorem ldSegFit_hyp : Spec.ldSegFit_hyp := fun E Kc _ _ D Q l h hs =>
  ⟨(LdProg.hyp_snoc (LdProg.nil D.src) (LdMv.fold D l)).2 ⟨LdProg.hyp_nil _, h⟩,
    hs,
    (LdProg.hyp_snoc (LdProg.nil Q.snd.tgt) (LdMv.loc Q.loc)).2
      ⟨LdProg.hyp_nil _, (⟨ldSegFit_near E Kc D Q, h.laws⟩ : Q.loc.Hyp)⟩⟩

theorem ldSegFit_after : Spec.ldSegFit_after := fun _ _ _ _ _ _ _ _ _ => Iff.rfl

end Cb
