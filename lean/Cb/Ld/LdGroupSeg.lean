-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupSeg.lean: this file puts kept messages in the kept slots of a group, and gives the
first half of a closing in the parameters of a preamble's moves.

In the words of lean/GLOSSARY.md: closing: the last part of a test, of the link or of a segment.
group: In `Cb/` and often in `Cm/`, some whole oracle messages of a signature, its members, read at
common long positions and tested together at one radius (`Grp`, Cb/Ld/LdBatSig.lean). shape: In
`Cb/Ld/` and `Cb/Part/`, the shape of a group is how its members' rows are arranged for the fold
(`GShape`, Cb/Ld/LdGroupFold.lean). bridge: the bridge is the one-round step at the head of a run on
a group, be it a whole test or a segment's closing. fold: a step, of several rounds, that combines
the rows of a table of words into one word, under coefficients that the verifier's point gives, and
carries the claim along (the map on vectors: `foldV`, Cb/Ld/LdRel.lean).

A held message (`Hd.cl`) is a member of the group that is read after the bridge (`kp`); `Hd.slot`
names a kept slot (Cb/Ld/LdGroupFold.lean) for each of its main rows, and `Hd.Laws` (its field kept)
says that this slot keeps that row. Under `Hd.Laws` and hc its word is read off the kept slots of
the folded word (`Hd.sW`), and the honest prover's (message, randomness) for it off those of its
folded pair (`Hd.sJ`, `Hd.sQ`).
In all four statements the group's set of common long positions, `G.P`, is nonempty, and E and B are
finite (`[Fintype E] [Fintype B]`).

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdGroupSegProofs.lean.

Why: Cb/Req1/LdSegKit.lean defines the move "first half of the closing of a group" over any folded
complex with slots that are words of oracle messages, and asks four things (`LdFoldD.Hyp`): the
bundle of "bridge, arrangement, fold"; the slots of the folded word are the words of the held
messages; the honest prover ends with their pairs in the slots; the laws of the slots. Here the four
are met, for the shape of Cb/Ld/LdGroupFold.lean, under the hypotheses of `Spec.ldGroup_seg`.

`GHeld Sh kp`: a choice of kept messages. In a shape any main row may be in a kept slot. A kept
message is a whole oracle message, member of the group and read after the bridge, all of whose main
rows are in kept slots.
`Hd.Laws`: slot k r keeps the row r of that member; unW undoes the shape's view on the member's
word; cJ, cQ name the member's entries as the view does; unW of the rows' encodings is the message's
own encoding; where two tuples of rows are read alike at a long position of the group, the two words
are read alike there (the message under its own reading, at the place that the group reads for that
position). (For a message that is declared as "rows under the base code" all are identities.)
With "the joint radius implies each member's own" (`G.Fits` of Cb/Ld/LdBatSig.lean, which the bridge
asks anyway) the last law gives: rows jointly within the group's radius of each other are words
within the message's own radius under its own reading.
  `Hd.link ..` takes hc: every oracle message is a member of the group or is read after the bridge
    (`kp`).

Main names:
  `Spec.ldGroup_seg_word`, `Spec.ldGroup_seg_wit`, `Spec.ldGroup_seg_laws`: three of the four
    hypotheses, one by one: see their doc comments.
  `Spec.ldGroup_seg`: all four hypotheses of the move: `(Hd.foldD ..).Hyp (Hd.link ..)`, from: the
    laws of the shape and of the choice; the fold's own hypotheses; the evader evades; a bound on
    the list of the complex; the joint radius implies each member's own; hc.

Notation: `Sb : B → Type`, `sl : ∀ b, Slf E (Sb b) G.C.J`: in `LdFoldD` (Cb/Req1/LdSegKit.lean), the
rows on the group; `Slf` (Cb/Ld/LdRel.lean): a linear form with a state; `Z`: an `Evader`
(Cb/Gen/BatEvader.lean): a zero-evader: the data; `A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)`: in
`LdFoldD` (Cb/Req1/LdSegKit.lean), what else is claimed, of the messages with kp; `St₀`, `E₀`, `Wp`:
arguments of its type; `Kc`: a type, the first argument of `IOR.Rels` (Ior/Chain.lean); `dw`: of
type `S.Wit × Wp`; `d`, `t`: natural numbers, `Lst`, `mC`, `mS`, `mW`: functions ℕ → ℕ: the
arguments of the fold's own hypotheses `Sh.par.Hyp` (Cb/Ld/LdTowerSumMain.lean); `L`: a natural
number, the number in `G.C.ListAt G.e L`.

Limits: "A kept message has no mask rows" is not asked by name. What the laws say: every entry of
its message and of its randomness has a place in a main row, and its whole native word is rebuilt
from its main rows; so mask rows of a kept message, if a shape lists any, carry nothing of it. (No
statement here says that there are none.) It has to be so: the held message goes on decoding with
its sample from the slots, and a sample reads every entry. Messages with different last readers are
different kept messages: a matter of cl at the next closing.
This file says nothing on the second half of a closing. It does not say that laws and hypotheses can
be met together: a toy is another file's.
Kept messages as oracle messages of their own, in kept slots, follow this protocol's technical
report; fold and main relation follow the paper that this protocol builds on (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupOut
import Cb.Req1.LdSegKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

/-- A choice of kept messages: the data. -/
structure GHeld {E : Type} [Field E] {S : Sig E} {G : Grp S} (Sh : GShape G) (kp : S.O → Prop) where
  /-- which of the oracle messages that are read after the bridge are held in the folded word from
  the fold on -/
  cl   : {o // kp o} → Prop
  [decCl : DecidablePred cl]
  /-- a held message is a member of the group -/
  mem  : ∀ k : {a // cl a}, G.mem k.1.1
  /-- the kept slot of each of its rows -/
  slot : ∀ k : {a // cl a}, Sh.Rm ⟨k.1.1, mem k⟩ → Sh.Kp
  /-- its native word, from its rows -/
  unW  : ∀ k : {a // cl a}, (Sh.Cb.il (Sh.Rm ⟨k.1.1, mem k⟩)).Word → (S.om k.1.1).C.Word
  /-- where an entry of its message, of its randomness, is: (row, place) -/
  cJ   : ∀ k : {a // cl a}, (S.om k.1.1).C.J → Sh.Rm ⟨k.1.1, mem k⟩ × Sh.Cb.J
  cQ   : ∀ k : {a // cl a}, (S.om k.1.1).C.Q → Sh.Rm ⟨k.1.1, mem k⟩ × Sh.Cb.Q

attribute [instance] GHeld.decCl

namespace GHeld
variable {E : Type} [Field E] {S : Sig E} {G : Grp S} {Sh : GShape G}
  {kp : S.O → Prop} (Hd : GHeld Sh kp)

/-- a held message as a member of the group -/
abbrev at' (k : {a // Hd.cl a}) : G.A := ⟨k.1.1, Hd.mem k⟩

/-- The laws of a choice of kept messages. -/
structure Laws : Prop where
  kept : ∀ k r, Sh.kept (Hd.slot k r) = ⟨Hd.at' k, r⟩
  word : ∀ k (f : G.C.Word),
    Hd.unW k (fun p s =>
        LdCode.fstW (C₁ := Sh.Cb.il (Σ a, Sh.Rm a)) (C₂ := Sh.Zb.il (Σ a, Sh.Rz a)) (Sh.flat.wd f)
          p (⟨Hd.at' k, s.1⟩, s.2)) =
      fun p => f ⟨Hd.at' k, p⟩
  upJ  : ∀ k (w : (G.C.J → E) × (G.C.Q → E)) j,
    (Sh.flat.up w).1 (.inl (⟨Hd.at' k, (Hd.cJ k j).1⟩, (Hd.cJ k j).2)) = w.1 ⟨Hd.at' k, j⟩
  upQ  : ∀ k (w : (G.C.J → E) × (G.C.Q → E)) q,
    (Sh.flat.up w).2 (.inl (⟨Hd.at' k, (Hd.cQ k q).1⟩, (Hd.cQ k q).2)) = w.2 ⟨Hd.at' k, q⟩
  enc  : ∀ k m r, Hd.unW k ((Sh.Cb.il (Sh.Rm (Hd.at' k))).enc m r) =
    (S.om k.1.1).C.enc (fun j => m (Hd.cJ k j)) (fun q => r (Hd.cQ k q))
  loc  : ∀ k f g x, (Sh.Cb.il (Sh.Rm (Hd.at' k))).T f x = (Sh.Cb.il (Sh.Rm (Hd.at' k))).T g x →
    (S.om k.1.1).C.T (Hd.unW k f) (G.pos (Hd.at' k) x) =
      (S.om k.1.1).C.T (Hd.unW k g) (G.pos (Hd.at' k) x)

/-- The slots of the folded complex that hold the message. -/
def sW (k : {a // Hd.cl a}) (F : Sh.Cf.Word) : (S.om k.1.1).C.Word :=
  Hd.unW k fun p s =>
    LdCode.fstW (C₁ := Sh.Cs) (C₂ := Sh.Zb.pair Sh.par.Zw) F p (some (Hd.slot k s.1), s.2)
def sJ (k : {a // Hd.cl a}) (j : (S.om k.1.1).C.J) : Sh.Cf.J :=
  .inl (some (Hd.slot k (Hd.cJ k j).1), (Hd.cJ k j).2)
def sQ (k : {a // Hd.cl a}) (q : (S.om k.1.1).C.Q) : Sh.Cf.Q :=
  .inl (some (Hd.slot k (Hd.cQ k q).1), (Hd.cQ k q).2)

end GHeld

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] (Hd : GHeld Sh kp) (Sb : B → Type)
  (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) {St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))

/-- The data of the move. -/
@[reducible] def GHeld.foldD : LdFoldD E Kc where
  S := S
  G := G
  kp := kp
  B := B
  Sb := Sb
  sl := sl
  St₀ := St₀
  Wp := Wp
  E₀ := E₀
  A₀ := A₀
  Pf := G.P
  Cf := Sh.Cf
  Stf := ((Sh.fold Sb sl Z).jOut G.e).St
  slf := (Sh.fold Sb sl Z).slOut
  e := G.e
  cl := Hd.cl
  sW := Hd.sW
  sJ := Hd.sJ
  sQ := Hd.sQ

/-- Its link: bridge, arrangement, fold, beside the carried part. -/
def GHeld.link
    (hc : ∀ o, G.mem o ∨ kp o) (dw : S.Wit × Wp) (d t : ℕ) (Lst mC mS mW : ℕ → ℕ) (L : ℕ) :
    IOR.Link Kc (Hd.foldD Sb sl Z A₀).src.J (Hd.foldD Sb sl Z A₀).mid where
  R := ldRunG G kp Sb sl Z St₀ E₀ (Sh.block Sb sl Z d t Lst mC mS mW)
  H := ldRunGH G kp Sb sl Z St₀ Wp E₀ (Sh.block Sb sl Z d t Lst mC mS mW)
  ext := ldRunGX G kp Sb sl Z St₀ Wp E₀ (Sh.block Sb sl Z d t Lst mC mS mW) hc dw
  P := ldRunGN G kp Sb sl Z St₀ E₀ (Sh.block Sb sl Z d t Lst mC mS mW) Kc (L * Z.err)

end

namespace Spec

/-- States: for `G.P` nonempty and under hc, if `Hd.Laws`, the slots of the folded word are the
words of the held messages as they were sent, for every transcript at which the link puts out a
statement. -/
def ldGroup_seg_word : Prop :=
  ∀ (E B Kc St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (Sh : GShape G) (kp : S.O → Prop) [DecidablePred kp] (Hd : GHeld Sh kp) (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (E₀ : ExtSpec)
      (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (hc : ∀ o, G.mem o ∨ kp o) (dw : S.Wit × Wp)
      (d t : ℕ) (Lst mC mS mW : ℕ → ℕ) (L : ℕ),
    Hd.Laws →
    ∀ a τ b, (Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).R.red.out a τ = some b →
      (Hd.foldD Sb sl Z A₀).Tw b

/-- States: for `G.P` nonempty and under hc, if `Hd.Laws`, the honest prover ends with the held
messages' pairs in the slots. -/
def ldGroup_seg_wit : Prop :=
  ∀ (E B Kc St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (Sh : GShape G) (kp : S.O → Prop) [DecidablePred kp] (Hd : GHeld Sh kp) (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (E₀ : ExtSpec)
      (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (hc : ∀ o, G.mem o ∨ kp o) (dw : S.Wit × Wp)
      (d t : ℕ) (Lst mC mS mW : ℕ → ℕ) (L : ℕ),
    Hd.Laws →
    ∀ w x c ρ (k : {a // Hd.cl a}),
      ((Hd.foldD Sb sl Z A₀).held.msg
            (((Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).H.strat w x c).run ρ).2.2.1.1 k,
          (Hd.foldD Sb sl Z A₀).held.rnd
            (((Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).H.strat w x c).run ρ).2.2.1.2 k) =
        (((Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).H.strat w x c).run ρ).2.2.2.1 k.1

/-- States: for `G.P` nonempty, if `Hd.Laws` and `G.Fits`, the slots have their laws at the joint
radius (`(Hd.foldD ..).held.Laws G.e`). -/
def ldGroup_seg_laws : Prop :=
  ∀ (E B Kc St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (Sh : GShape G) (kp : S.O → Prop) [DecidablePred kp] (Hd : GHeld Sh kp) (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (E₀ : ExtSpec)
      (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)),
    Hd.Laws → G.Fits → (Hd.foldD Sb sl Z A₀).held.Laws G.e

/-- States: under the hypotheses below, the link `Hd.link ..` meets all four hypotheses of the move
(`(Hd.foldD ..).Hyp`). -/
def ldGroup_seg : Prop :=
  ∀ (E B Kc St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (Sh : GShape G) (kp : S.O → Prop) [DecidablePred kp] (Hd : GHeld Sh kp) (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (E₀ : ExtSpec)
      (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (hc : ∀ o, G.mem o ∨ kp o) (dw : S.Wit × Wp)
      (d t : ℕ) (Lst mC mS mW : ℕ → ℕ) (L : ℕ),
    Sh.OK → Hd.Laws → Sh.par.Hyp d G.e t Lst mC mS mW → Z.OK → G.C.ListAt G.e L → G.Fits →
    (Hd.foldD Sb sl Z A₀).Hyp (Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L)

end Spec
end Cb
