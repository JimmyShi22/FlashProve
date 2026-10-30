-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegCarry.lean: which facts (`IOR.MaskFact`, Cb/Req1/LdSegFresh.lean) on fresh masks a move
of a preamble carries.

Definitions, statements (Cb.Spec.segCarry_*, segWide_*) and proofs.
Names and paths: "masked" links: `Link.GoodM` (Ior/KnowCollRulesChain.lean); "does not look":
`Honest.Blind` (Ior/KnowCollRulesMask.lean); moves and stages are in Cb/Req1/LdSeg.lean and
Cb/Req1/LdSegKit.lean.
`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. (`Honest.Fresh`, `Honest.seen`,
Ior/KnowCollRulesMask.lean.) In `Spec.segCarry_send_new` it is a premise (on `d.link.H`).

Why: Cb/Req1/LdReq.lean asks, for zero knowledge of a request, that at every masked link the
fact which the link needs (its reading of the witness, its own masks) is among the facts that are
fresh at its place (`m.After base`: `IOR.Chain.FreshGiven` of the move's chain). Here that condition
is shown to be reachable move by move, under each rule's conditions; for sub-protocols see Limits.

Part 1: for any fact. A move carries a fact if its honest prover does not look: for two witnesses
whose readings differ by an overwriting of the masks it sends the same and ends with the same
explicit part, and the readings of the witnesses handed on differ by the overwriting.
  `Spec.segCarry_bat`: many rows into one: every fact is carried (nothing is sent, the witness is
    handed on).
  `Spec.segCarry_split`: a row into two: if the scalar that is said does not look.
  `Spec.segCarry_loc`: the locations: if "the open word's message and randomness, as the messages
    hold them" (`D.cut`) does not look.
  `Spec.segCarry_step`: a step without rounds: if its honest map does not look.
  `Spec.segCarry_fold`: bridge to fold, then the re-bracketing: from "`l` does not look".
  `Spec.segCarry_send_old`: a sending, for masks sent earlier: if the new messages do not look, and
    what is handed on is read as overwritten.
  `Spec.segCarry_send_new`: a sending, for masks that it sends itself: from Fresh of its honest
    side.

Part 2: the standard facts of a stage.
  `a.wideFact Rd Rr own Mk val`: the fact that is carried. Read: the entries in Rd of all messages
    (all others set to 0); the encoding randomness of the oracle messages with Rr; the whole further
    witness. Masks: Mk, any finite non-empty type; M stands at the entries with "own", with the
    values val M.
    Meant: Rd = all entries but the pads of the oracle messages that rode with the masks; Rr = all
    names but theirs (see Limits).
  `a.entFact Rd own Mk val`: the fact at a masked link: the entries in Rd, and nothing else.
  `Spec.segWide_ent`: the second follows from the first: a smaller set of entries (which holds the
    own ones), no randomness, no further witness.
  `Spec.segWide_splitFact`: the fact that a split needs (`D.mask.fact`) is
    D.src.entFact D.Rd {κ} E (the scalar itself).
  `Spec.segWide_alike`: what follows from "the wide readings differ by an overwriting": the messages
    agree at all entries in Rd that are not own; the randomness at Rr agrees; the further witnesses
    are equal.
  `Spec.segWide_bat`, `Spec.segWide_split`, `Spec.segWide_loc`, `Spec.segWide_send_old`,
    `Spec.segWide_fold` (the split also under `D.Hyp`, the sending also under
    `d.D.Laws (a.S.backN d.N d.bk)`): the wide fact through these moves, with plain conditions:
    split: what the split reads lies in Rd, its first row does not read an own entry, κ is not own;
    loc: D.cut reads entries in Rd that are not own;
    send: new messages and the further witness handed on are made from entries in Rd that are not
    own, randomness at Rr, the further witness and coins. After a sending the sets are extended to
    the new names by any RdN, RrN;
    fold: every member of the group has its randomness read (Rr), all its entries in Rd, none of
    them own (masks, their pads and that message's randomness stand outside the group); of `l` two
    facts are asked: transcript, explicit part and the test's part of the last witness are functions
    of the members' pairs; the carried part is handed on unchanged.
  `Spec.segWide_send_rd`: the wide reading after a sending, if the new family's randomness is not
    read, in the form "rd (new messages) (old pairs, further witness)", in which
    Cb/Ld/LdSendFreshMany.lean (proof: Cb/Ld/LdSendFreshManyProofs.lean) proves Fresh, under the
    hypotheses of its statement (`Spec.ldSendSig_fresh_wide`), for masks that the sending sends.

Why the carried fact must be wide: "does not look" speaks of all pairs of witnesses whose readings
differ by the overwriting; what a reading forgets may differ arbitrarily. A sending makes its
messages from the further witness; a bridge-to-fold reads encoding randomness; a sub-protocol reads
what it likes of the further witness. So a reading that forgets the further witness, or all
randomness (`a.entFact`), is not carried by these moves. It is carried by bat, and by split and loc
under the conditions of `segCarry_split`, `segCarry_loc`.

Limits: a limit stands, and it is not in this file. The rules here hold for every Rd, Rr. What
Rr can be is decided at the sender: Fresh has to be shown for the wide reading.
Cb/Ld/LdSendFresh.lean, Cb/Ld/LdSendFreshMany.lean (proofs: Cb/Ld/LdSendFreshProofs.lean,
Cb/Ld/LdSendFreshManyProofs.lean) show it, under the hypotheses of their statements, for readings
that forget the encoding randomness of every member of the family that is sent in the one prover
message (`Spec.segWide_send_rd` is that form).
With such an Rr a bridge-to-fold on a group that holds any member of that family, before the masked
link, does not carry the fact (`segWide_fold` asks Rr of every member). A write-up of ours
(lean/CREDITS.md)
forbids only groups that hold the mask message itself, and it needs the difference: a mask message
that rides in a request's first prover message serves blocks of every later segment, while its
companions are folded at the first closing.
What is needed at the sender, therefore: Fresh for a reading that forgets only the pad and the
encoding randomness of the message that holds the masks. That stands, under the hypotheses of their
statements: Cb/Ld/LdSendFreshVis.lean (`ldSendFam_freshV`, `ldSendSig_freshV`; for a sender whose
members have independent coins: `ofMem_hid`, `ofMem_pad`). With it Rr leaves out that one name, Rd
that one message's pad, and all rules here apply as they stand.
This file does not say that the two facts on the link `l` (bridge-to-fold) hold: they are hypotheses
of `segWide_fold`. Nothing on sub-protocols (their chains' FreshGiven is m.After by
definition). Nothing on batches.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Req1.LdReq
import Cb.Req1.LdSegCarryKit
import Cb.Ld.LdSendBlind
import Ior.KnowCollRulesMaskFrame
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain

/-! ## The standard facts -/

section
variable {E : Type} [Field E]

open Classical in
/-- the messages, overwritten by v at the entries with "own" -/
def Sig.ow (S : Sig E) (own : S.Ent → Prop) (v : S.Ent → E) (m : S.Msg) : S.Msg :=
  fun a j => if own ⟨a, j⟩ then v ⟨a, j⟩ else m a j

open Classical in
/-- The wide reading. -/
def Sig.wide (S : Sig E) (Wp : Type) (Rd : S.Ent → Prop)
    (Rr : S.O → Prop) (w : S.Wit × Wp) :
    S.Msg × (∀ o, Option (S.om o).Rnd) × Wp :=
  (S.cut Rd (S.msgs w.1), fun o => if Rr o then some (w.1 o).2 else none, w.2)

/-- the messages agree at all entries in Rd that are not own -/
def Sig.Alike (S : Sig E) (Rd own : S.Ent → Prop) (m m' : S.Msg) : Prop :=
  ∀ n : S.Ent, Rd n → ¬ own n → m' n.1 n.2 = m n.1 n.2

/-- sets of entries, sets of names and values over two signatures -/
def Sig.sumP (S N : Sig E) (p : S.Ent → Prop) (q : N.Ent → Prop) : (S.sum N).Ent → Prop
  | ⟨.inl a, j⟩ => p ⟨a, j⟩
  | ⟨.inr a, j⟩ => q ⟨a, j⟩
def Sig.sumO (S N : Sig E) (p : S.O → Prop) (q : N.O → Prop) : (S.sum N).O → Prop := Sum.elim p q
def Sig.sumV (S N : Sig E) (u : S.Ent → E) (v : N.Ent → E) : (S.sum N).Ent → E
  | ⟨.inl a, j⟩ => u ⟨a, j⟩
  | ⟨.inr a, j⟩ => v ⟨a, j⟩

/-- a function of entries, on the entries of some of the oracle messages -/
def Sig.subF {β : Type} (S : Sig E) (kp : S.O → Prop) [DecidablePred kp] (p : S.Ent → β) :
    (S.sub kp).Ent → β :=
  fun n => p ⟨n.1.1, n.2⟩
def Sig.subQ (S : Sig E) (kp : S.O → Prop) [DecidablePred kp] (p : S.Ent → Prop) :
    (S.sub kp).Ent → Prop :=
  fun n => p ⟨n.1.1, n.2⟩

variable {Kc : Type}

/-- The fact that is carried. -/
def LdStage.wideFact (a : LdStage E Kc) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop)
    (own : a.S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → a.S.Ent → E) :
    MaskFact a.J.W :=
  ⟨a.S.Msg × (∀ o, Option (a.S.om o).Rnd) × a.Wp, a.S.wide a.Wp Rd Rr, Mk,
    fun M k => (a.S.ow own (val M) k.1, k.2)⟩

open Classical in
/-- The fact at a masked link. -/
def LdStage.entFact (a : LdStage E Kc) (Rd : a.S.Ent → Prop) (own : a.S.Ent → Prop)
    (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → a.S.Ent → E) : MaskFact a.J.W :=
  ⟨a.S.Msg, fun w => a.S.cut Rd (a.S.msgs w.1), Mk, fun M k => a.S.ow own (val M) k⟩

end

namespace Spec
section
variable (E Kc : Type) [Field E] [Fintype E]

/-! ### Part 1: for any fact -/

def segCarry_bat : Prop :=
  ∀ (D : LdBatD E Kc) (base : MaskFact D.src.J.W → Prop) (f : MaskFact D.src.J.W),
    base f → (LdMv.bat D).After base f

def segCarry_split : Prop :=
  ∀ (D : LdSplD E Kc) (base : MaskFact D.src.J.W → Prop) (f : MaskFact D.src.J.W), base f →
    (∀ (w w' : D.src.J.W) M st, f.kc w' = f.put M (f.kc w) →
      splitVal D.k D.sl₁ (D.S.msgs w'.1) st = splitVal D.k D.sl₁ (D.S.msgs w.1) st) →
    (LdMv.split D).After base f

def segCarry_loc : Prop :=
  ∀ (D : LdLocD E Kc) (base : MaskFact D.src.J.W → Prop) (f : MaskFact D.src.J.W), base f →
    (∀ (w w' : D.src.J.W) M,
      f.kc w' = f.put M (f.kc w) → D.cut (D.S.msgs w'.1) = D.cut (D.S.msgs w.1)) →
    (LdMv.loc D).After base f

def segCarry_step : Prop :=
  ∀ (a b : LdStage E Kc) (f : a.X → Option b.X) (g : ExtMap a.Ex b.Ex) (m : a.X × a.W → b.X × b.W)
      (back : a.X × a.Ex.Str → b.W → a.W) (base : MaskFact a.J.W → Prop) (fa : MaskFact a.J.W)
      (Kc' : Type) (kc' : b.J.W → Kc') (put' : fa.Mk → Kc' → Kc'),
    base fa →
    (∀ x (w w' : a.W) M, fa.kc w' = fa.put M (fa.kc w) →
      (m (x, w')).1 = (m (x, w)).1 ∧ kc' (m (x, w')).2 = put' M (kc' (m (x, w)).2)) →
    (LdMv.step a b f g m back).After base ⟨Kc', kc', fa.Mk, put'⟩

def segCarry_fold : Prop :=
  ∀ (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid) (base : MaskFact D.src.J.W → Prop)
      (fa : MaskFact D.src.J.W) (Kc' : Type) (kc' : D.tgt.J.W → Kc') (put' : fa.Mk → Kc' → Kc'),
    base fa → l.H.Blind fa.kc (fun w => kc' (D.pW w)) fa.Mk fa.put put' →
    (LdMv.fold D l).After base ⟨Kc', kc', fa.Mk, put'⟩

def segCarry_send_old : Prop :=
  ∀ (a : LdStage E Kc) (d : LdSendD a) (base : MaskFact a.J.W → Prop) (fa : MaskFact a.J.W)
      (Kc' : Type) (kc' : d.tgt.J.W → Kc') (put' : fa.Mk → Kc' → Kc'),
    base fa → (∀ (w w' : a.W) M, fa.kc w' = fa.put M (fa.kc w) → ∀ k, d.D.put w' k = d.D.put w k) →
    (∀ (w w' : a.W) M (nw : d.N.Wit), fa.kc w' = fa.put M (fa.kc w) →
      kc' (a.S.join d.N (T := OMsg.Wit) (d.D.rest w').1 nw, (d.D.rest w').2) =
        put' M (kc' (a.S.join d.N (T := OMsg.Wit) (d.D.rest w).1 nw, (d.D.rest w).2))) →
    (LdMv.send a d).After base ⟨Kc', kc', fa.Mk, put'⟩

def segCarry_send_new : Prop :=
  ∀ (a : LdStage E Kc) (d : LdSendD a) (base : MaskFact a.J.W → Prop) (f : MaskFact d.tgt.J.W),
    d.link.H.Fresh a.J.rels.rel d.link.P.bud f.kc f.Mk f.put → (LdMv.send a d).After base f

/-! ### Part 2: the standard facts -/

/-- What follows from "the wide readings differ by an overwriting". -/
def segWide_alike : Prop :=
  ∀ (a : LdStage E Kc) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop) (own : a.S.Ent → Prop) (Mk : Type)
      [Fintype Mk] [Nonempty Mk] (val : Mk → a.S.Ent → E) (w w' : a.W) (M : Mk),
    (a.wideFact Rd Rr own Mk val).kc w' =
      (a.wideFact Rd Rr own Mk val).put M ((a.wideFact Rd Rr own Mk val).kc w) →
    a.S.Alike Rd own (a.S.msgs w.1) (a.S.msgs w'.1) ∧
    (∀ o, Rr o → (w'.1 o).2 = (w.1 o).2) ∧
    w'.2 = w.2

/-- Under the hypotheses below, the fact at a masked link follows from the wide fact, after any
chain. -/
def segWide_ent : Prop :=
  ∀ (A : Joint Kc) (a : LdStage E Kc) (c : Chain Kc A a.J) (base : MaskFact A.W → Prop)
      (Rd Rd' : a.S.Ent → Prop) (Rr : a.S.O → Prop) (own : a.S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → a.S.Ent → E),
    (∀ n, Rd' n → Rd n) → (∀ n, own n → Rd' n) → c.FreshGiven base (a.wideFact Rd Rr own Mk val) →
    c.FreshGiven base (a.entFact Rd' own Mk val)

/-- The fact that a split needs. -/
def segWide_splitFact : Prop :=
  ∀ (D : LdSplD E Kc),
    D.mask.fact = D.src.entFact D.Rd (fun n => n = ⟨D.k.o, D.k.j⟩) E (fun u _ => u)

def segWide_bat : Prop :=
  ∀ (D : LdBatD E Kc) (base : MaskFact D.src.J.W → Prop) (Rd : D.S.Ent → Prop) (Rr : D.S.O → Prop)
      (own : D.S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → D.S.Ent → E),
    base (D.src.wideFact Rd Rr own Mk val) →
    (LdMv.bat D).After base (D.tgt.wideFact Rd Rr own Mk val)

def segWide_split : Prop :=
  ∀ (D : LdSplD E Kc) (base : MaskFact D.src.J.W → Prop) (Rd : D.S.Ent → Prop) (Rr : D.S.O → Prop)
      (own : D.S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → D.S.Ent → E),
    D.Hyp → (∀ n, D.Rd n → Rd n) → (∀ st n, own (D.G₁.ent n) → D.sl₁ st n = 0) →
    ¬ own ⟨D.k.o, D.k.j⟩ → base (D.src.wideFact Rd Rr own Mk val) →
    (LdMv.split D).After base (D.tgt.wideFact Rd Rr own Mk val)

def segWide_loc : Prop :=
  ∀ (D : LdLocD E Kc) (base : MaskFact D.src.J.W → Prop) (Rd : D.S.Ent → Prop) (Rr : D.S.O → Prop)
      (own : D.S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → D.S.Ent → E),
    (∀ m m', D.S.Alike Rd own m m' → D.cut m' = D.cut m) → base (D.src.wideFact Rd Rr own Mk val) →
    (LdMv.loc D).After base (D.tgt.wideFact Rd Rr own Mk val)

/-- A sending, for masks sent earlier. -/
def segWide_send_old : Prop :=
  ∀ (a : LdStage E Kc) (d : LdSendD a) (base : MaskFact a.J.W → Prop) (Rd : a.S.Ent → Prop)
      (Rr : a.S.O → Prop) (own : a.S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk]
      (val : Mk → a.S.Ent → E) (RdN : d.N.Ent → Prop) (RrN : d.N.O → Prop),
    d.D.Laws (a.S.backN d.N d.bk) →
    (∀ w w' : a.W, a.S.Alike Rd own (a.S.msgs w.1) (a.S.msgs w'.1) →
      (∀ o, Rr o → (w'.1 o).2 = (w.1 o).2) → w'.2 = w.2 →
      (∀ k, d.D.put w' k = d.D.put w k) ∧ (d.D.rest w').2 = (d.D.rest w).2) →
    base (a.wideFact Rd Rr own Mk val) →
    (LdMv.send a d).After base
      (d.tgt.wideFact (a.S.sumP d.N Rd RdN) (a.S.sumO d.N Rr RrN) (a.S.sumP d.N own fun _ => False)
        Mk fun M => a.S.sumV d.N (val M) fun _ => 0)

/-- Bridge to fold, for masks that stand outside the group. (not all hypotheses are named here: see
the statement below) -/
def segWide_fold : Prop :=
  ∀ (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid) (base : MaskFact D.src.J.W → Prop)
      (Rd : D.S.Ent → Prop) (Rr : D.S.O → Prop) (own : D.S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → D.S.Ent → E),
    (∀ (w w' : D.src.J.W) x c ρ, D.G.wit w'.1 = D.G.wit w.1 →
      ((l.H.strat w' x c).run ρ).1 = ((l.H.strat w x c).run ρ).1 ∧
      ((l.H.strat w' x c).run ρ).2.1 = ((l.H.strat w x c).run ρ).2.1 ∧
      ((l.H.strat w' x c).run ρ).2.2.1 = ((l.H.strat w x c).run ρ).2.2.1) →
    (∀ (w : D.src.J.W) x c ρ,
      ((l.H.strat w x c).run ρ).2.2.2 = (D.S.res (T := OMsg.Wit) D.kp w.1, w.2)) →
    (∀ o, D.G.mem o → Rr o ∧ ∀ j, Rd ⟨o, j⟩ ∧ ¬ own ⟨o, j⟩) →
    base (D.src.wideFact Rd Rr own Mk val) →
    (LdMv.fold D l).After base
      (D.tgt.wideFact (D.S₁.subQ _ (D.S.subQ D.kp Rd)) (fun a => Rr a.1.1)
        (D.S₁.subQ _ (D.S.subQ D.kp own)) Mk fun M => D.S₁.subF _ (D.S.subF D.kp (val M)))

open Classical in
/-- The wide reading after a sending, as a function of (new messages; old pairs, further witness),
if the new family's randomness is not read. -/
def segWide_send_rd : Prop :=
  ∀ (a : LdStage E Kc) (d : LdSendD a) (Rd : (a.S.sum d.N).Ent → Prop)
      (Rr : a.S.O → Prop) (v : d.tgt.J.W),
    (a.S.sum d.N).wide d.Wp' Rd (a.S.sumO d.N Rr fun _ => False) v =
      ((a.S.sum d.N).cut Rd
          (a.S.join d.N (T := OMsg.Msg) (a.S.msgs (a.S.left d.N (T := OMsg.Wit) v.1))
            (d.N.msgs (a.S.right d.N (T := OMsg.Wit) v.1))),
        a.S.join d.N (T := fun o => Option o.Rnd)
          (fun o => if Rr o then some (a.S.left d.N (T := OMsg.Wit) v.1 o).2 else none)
          (fun _ => none),
        v.2)

end
end Spec

/-! ## Proofs -/

section
variable {E Kc : Type} [Field E] [Fintype E]

theorem segCarry_bat : Spec.segCarry_bat E Kc := fun D base f hb =>
  (freshGiven_one D.link base f).2
    (Or.inr ⟨f.Kc, f.kc, f.put, hb, fun _ _ _ _ _ _ h => ⟨rfl, rfl, h⟩⟩)

theorem segCarry_split : Spec.segCarry_split E Kc := fun D base f hb hv =>
  (freshGiven_one D.link base f).2 (Or.inr ⟨f.Kc, f.kc, f.put, hb, fun w w' M x _ ρ h => by
    have e := hv w w' M x.1.1.2.1 h
    refine ⟨?_, ?_, h⟩
    · show ((((), splitVal D.k D.sl₁ (D.S.msgs w'.1) x.1.1.2.1), ρ.1, ()) : Tr [sayRound E 0]) =
        (((), splitVal D.k D.sl₁ (D.S.msgs w.1) x.1.1.2.1), ρ.1, ())
      rw [e]
      rfl
    · show splitNx D.S D.St₁ D.St₂ D.St₀ x (splitVal D.k D.sl₁ (D.S.msgs w'.1) x.1.1.2.1) =
        splitNx D.S D.St₁ D.St₂ D.St₀ x (splitVal D.k D.sl₁ (D.S.msgs w.1) x.1.1.2.1)
      rw [e]⟩)

theorem segCarry_loc : Spec.segCarry_loc E Kc := fun D base f hb hc =>
  (freshGiven_one D.link base f).2 (Or.inr ⟨f.Kc, f.kc, f.put, hb, by
    refine blind_post _ _ _ _ _ _ _ _ _ _ _ (fun x => some x) D.outE (fun p => p)
      _ _ _ f.kc f.kc f.kc f.Mk f.put f.put f.put (fun _ _ _ _ h => ⟨rfl, h⟩) ?_
    refine blind_pre _ _ _ _ _ _ _ _ _ _ _ (fun x => some x) D.inE (fun x => x) (fun _ w => w)
      _ _ _ f.kc f.kc f.kc f.Mk f.put f.put f.put (fun _ _ _ _ h => h) ?_
    intro w w' M x _ ρ h
    have e := hc w w' M h
    refine ⟨rfl, ?_, h⟩
    show D.V.out x ρ.1 (D.V.at (D.C.enc (D.cut (D.S.msgs w'.1)).1 (D.cut (D.S.msgs w'.1)).2) ρ.1) =
      D.V.out x ρ.1 (D.V.at (D.C.enc (D.cut (D.S.msgs w.1)).1 (D.cut (D.S.msgs w.1)).2) ρ.1)
    rw [e]⟩)

theorem segCarry_step : Spec.segCarry_step E Kc := fun _ _ f g m _ base fa _ kc' put' hb hm =>
  (freshGiven_one _ base _).2
    (Or.inr ⟨fa.Kc, fa.kc, fa.put, hb,
        blind_stepPure _ _ _ _ _ _ f g m _ _ fa.kc kc' fa.Mk fa.put put' hm⟩)

theorem segCarry_fold : Spec.segCarry_fold E Kc := fun D l base fa _ kc' put' hb hl =>
  (freshGiven_one (D.link l) base _).2
    (Or.inr ⟨fa.Kc, fa.kc, fa.put, hb,
        blind_post _ _ _ _ _ _ _ _ _ _ l.H (fun x => some (D.pX x)) D.pE
          (fun p => (D.pX p.1, D.pW p.2)) _ _ _ fa.kc (fun w => kc' (D.pW w))
          kc' fa.Mk fa.put put' put' (fun _ _ _ _ h => ⟨rfl, h⟩) hl⟩)

theorem segCarry_send_old : Spec.segCarry_send_old E Kc := fun a d base fa _ kc' put' hb h1 h2 =>
  (freshGiven_one d.link base _).2
    (Or.inr ⟨fa.Kc, fa.kc, fa.put, hb,
        ldSendSig_blind E a.S d.N d.Sd a.St a.Wp d.Wp' a.E₀ d.D _ _ fa.Mk
          fa.kc kc' fa.put put' h1 h2⟩)

theorem segCarry_send_new : Spec.segCarry_send_new E Kc := fun _ d base f h =>
  (freshGiven_one d.link base f).2 (Or.inl h)

omit [Fintype E] in
theorem segWide_alike : Spec.segWide_alike E Kc := by
  classical
  intro a Rd Rr own Mk _ _ val w w' M h
  have h1 : a.S.cut Rd (a.S.msgs w'.1) = a.S.ow own (val M) (a.S.cut Rd (a.S.msgs w.1)) :=
    (Prod.mk.inj h).1
  have h2 : (fun o => if Rr o then some (w'.1 o).2 else none) =
    fun o => if Rr o then some (w.1 o).2 else none := (Prod.mk.inj (Prod.mk.inj h).2).1
  refine ⟨fun n hR ho => ?_, fun o ho => ?_, (Prod.mk.inj (Prod.mk.inj h).2).2⟩
  · obtain ⟨o, j⟩ := n
    have e : (if Rd ⟨o, j⟩ then a.S.msgs w'.1 o j else 0) =
      if own ⟨o, j⟩ then val M ⟨o, j⟩
      else (if Rd ⟨o, j⟩ then a.S.msgs w.1 o j else 0) := congrFun (congrFun h1 o) j
    rw [if_pos hR, if_neg ho, if_pos hR] at e
    exact e
  · have e := congrFun h2 o
    simp only [if_pos ho] at e
    exact Option.some.inj e

omit [Fintype E] in
theorem segWide_ent : Spec.segWide_ent E Kc := by
  classical
  intro A a c base Rd Rd' Rr own Mk _ _ val hR ho h
  have key := freshGiven_conseq Kc A a.J c base (a.wideFact Rd Rr own Mk val) a.S.Msg (fun k => a.S.cut Rd' k.1) (fun M k => a.S.ow own (val M) k) (fun M k => by
    funext o j
    show (if Rd' ⟨o, j⟩ then (if own ⟨o, j⟩ then val M ⟨o, j⟩ else k.1 o j) else 0) =
      if own ⟨o, j⟩ then val M ⟨o, j⟩ else (if Rd' ⟨o, j⟩ then k.1 o j else 0)
    by_cases h1 : own ⟨o, j⟩
    · rw [if_pos (ho _ h1), if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]) h
  have e : (fun w : a.J.W => a.S.cut Rd' ((a.wideFact Rd Rr own Mk val).kc w).1) =
      fun w => a.S.cut Rd' (a.S.msgs w.1) := by
    funext w o j
    show (if Rd' ⟨o, j⟩ then (if Rd ⟨o, j⟩ then a.S.msgs w.1 o j else 0) else 0) =
      if Rd' ⟨o, j⟩ then a.S.msgs w.1 o j else 0
    by_cases h1 : Rd' ⟨o, j⟩
    · rw [if_pos h1, if_pos h1, if_pos (hR _ h1)]
    · rw [if_neg h1, if_neg h1]
  unfold LdStage.entFact
  rw [← e]
  exact key

theorem segWide_splitFact : Spec.segWide_splitFact E Kc := by
  classical
  intro D
  have e1 : (fun w : D.src.J.W => @Sig.cut E _ D.S D.Rd D.decRd (D.S.msgs w.1)) =
      fun w => @Sig.cut E _ D.S D.Rd (fun n => Classical.propDecidable _) (D.S.msgs w.1) := by
    funext w
    congr
  have e2 : D.k.put = fun u k => D.S.ow (fun n => n = ⟨D.k.o, D.k.j⟩) (fun _ => u) k := by
    funext u m a j
    unfold SplitAt.put Sig.ow
    by_cases h : a = D.k.o
    · subst h
      rw [Function.update_self]
      by_cases hj : j = D.k.j
      · subst hj
        rw [Function.update_self, if_pos rfl]
      · rw [Function.update_of_ne hj]
        refine (if_neg ?_).symm
        intro e
        have e' : (⟨D.k.o, j⟩ : D.S.Ent) = ⟨D.k.o, D.k.j⟩ := e
        exact hj (eq_of_heq (Sigma.mk.inj e').2)
    · rw [Function.update_of_ne h, if_neg fun e => h (congrArg Sigma.fst e)]
  show (⟨D.S.Msg,
      fun w : D.src.J.W => @Sig.cut E _ D.S D.Rd D.decRd (D.S.msgs w.1),
      E,
      D.k.put⟩ : MaskFact D.src.J.W) =
    ⟨D.S.Msg,
      fun w => @Sig.cut E _ D.S D.Rd (fun n => Classical.propDecidable _) (D.S.msgs w.1), E, _⟩
  rw [e1, e2]

theorem segWide_bat : Spec.segWide_bat E Kc := fun D base _ _ _ _ _ _ _ hb =>
  segCarry_bat D base _ hb

theorem segWide_split : Spec.segWide_split E Kc := by
  intro D base Rd Rr own Mk _ _ val hD hsub hrow hκ hb
  refine segCarry_split D base _ hb fun w w' M st h => ?_
  have al := (segWide_alike D.src Rd Rr own Mk val w w' M h).1
  unfold splitVal
  have s1 : D.sl₁.val st (D.G₁.msg (D.S.msgs w'.1)) = D.sl₁.val st (D.G₁.msg (D.S.msgs w.1)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hz : D.sl₁ st n = 0
    · rw [hz, zero_mul, zero_mul]
    · have hRd : D.Rd (D.G₁.ent n) := by
        by_contra hn
        exact hz (hD.rd₁ st n hn)
      have e : D.G₁.msg (D.S.msgs w'.1) n = D.G₁.msg (D.S.msgs w.1) n :=
        al (D.G₁.ent n) (hsub _ hRd) fun ho => hz (hrow st n ho)
      rw [e]
  have s2 : D.k.val (D.S.msgs w'.1) = D.k.val (D.S.msgs w.1) := al ⟨D.k.o, D.k.j⟩ (hsub _ hD.rdK) hκ
  rw [s1, s2]

theorem segWide_loc : Spec.segWide_loc E Kc := fun D base Rd Rr own Mk _ _ val hc hb =>
  segCarry_loc D base _ hb fun w w' M h => hc _ _ (segWide_alike D.src Rd Rr own Mk val w w' M h).1

theorem segWide_send_old : Spec.segWide_send_old E Kc := by
  classical
  intro a d base Rd Rr own Mk _ _ val RdN RrN hL hp hb
  have r1 : ∀ w : a.W, (d.D.rest w).1 = w.1 := fun w =>
    congrArg Prod.fst (hL.back w (Classical.arbitrary _))
  refine segCarry_send_old a d base _ _ _ _ hb (fun w w' M h => ?_) fun w w' M nw h => ?_
  · obtain ⟨al, rn, e⟩ := segWide_alike a Rd Rr own Mk val w w' M h
    exact (hp w w' al rn e).1
  · obtain ⟨al, rn, e⟩ := segWide_alike a Rd Rr own Mk val w w' M h
    have h1 : a.S.cut Rd (a.S.msgs w'.1) = a.S.ow own (val M) (a.S.cut Rd (a.S.msgs w.1)) :=
      (Prod.mk.inj h).1
    have h2 : (fun o => if Rr o then some (w'.1 o).2 else none) =
      fun o => if Rr o then some (w.1 o).2 else none := (Prod.mk.inj (Prod.mk.inj h).2).1
    rw [r1, r1, (hp w w' al rn e).2]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · funext o j
      cases o with
      | inl o => exact congrFun (congrFun h1 o) j
      | inr o =>
          show _ = d.tgt.S.ow (a.S.sumP d.N own fun _ => False) (a.S.sumV d.N (val M) fun _ => 0)
              (d.tgt.S.cut (a.S.sumP d.N Rd RdN)
                (d.tgt.S.msgs (a.S.join d.N (T := OMsg.Wit) w.1 nw)))
              (Sum.inr o) j
          unfold Sig.ow
          exact (if_neg (fun h : False => h)).symm
    · funext o
      cases o with
      | inl o => exact congrFun h2 o
      | inr o => rfl

theorem segWide_fold : Spec.segWide_fold E Kc := by
  classical
  intro D l base Rd Rr own Mk _ _ val F1 F2 hm hb
  refine segCarry_fold D l base _ _ _ _ hb fun w w' M x c ρ h => ?_
  obtain ⟨al, rn, e⟩ := segWide_alike D.src Rd Rr own Mk val w w' M h
  have h1 : D.S.cut Rd (D.S.msgs w'.1) = D.S.ow own (val M) (D.S.cut Rd (D.S.msgs w.1)) :=
    (Prod.mk.inj h).1
  have h2 : (fun o => if Rr o then some (w'.1 o).2 else none) =
    fun o => if Rr o then some (w.1 o).2 else none := (Prod.mk.inj (Prod.mk.inj h).2).1
  have hG : D.G.wit w'.1 = D.G.wit w.1 :=
    Prod.ext (funext fun n => al ⟨n.1.1, n.2⟩ ((hm n.1.1 n.1.2).2 n.2).1 ((hm n.1.1 n.1.2).2 n.2).2)
      (funext fun n => congrFun (rn n.1.1 (hm n.1.1 n.1.2).1) n.2)
  obtain ⟨t1, t2, t3⟩ := F1 w w' x c ρ hG
  refine ⟨t1, t2, ?_⟩
  have p : ∀ v : D.src.J.W, D.pW ((l.H.strat v x c).run ρ).2.2 =
      ((fun a => v.1 a.1.1, (((l.H.strat v x c).run ρ).2.2.1, v.2)) : D.tgt.W) := fun v => by
    unfold LdFoldD.pW
    rw [F2 v x c ρ]
    rfl
  beta_reduce
  rw [p w', p w, t3, e]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext a j
    exact congrFun (congrFun h1 a.1.1) j
  · funext a
    exact congrFun h2 a.1.1

omit [Fintype E] in
theorem segWide_send_rd : Spec.segWide_send_rd E Kc := by
  classical
  intro a d Rd Rr v
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · refine congrArg ((a.S.sum d.N).cut Rd) (funext fun o => ?_)
    cases o <;> rfl
  · funext o
    cases o with
    | inl o => rfl
    | inr o => exact if_neg fun h => h

end
end Cb
