-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegKit.lean: the stages of a preamble and the data of its moves: one sending of a family;
the first half of the closing of a group, with kept messages; the locations.

Definitions only; the statements are in Cb/Req1/LdSeg.lean.
Data types for a request's preamble, the reduction from a request to claims on the encoded index and
on the oracles that it leaves. They fix the interface between two steps (a stage) and the data of
the steps by which a group of oracle messages is tested for proximity and replaced by new ones: a
fold, a sending of new oracle messages, and a query phase (the locations).

A preamble is a chain of blocks all of whose joints have one form: a signature S of the oracle
messages that are open, and a base joint A that says what is claimed of their messages; relaxed by
decoding with a sample; "collision-free" is a condition that may fail with a bad event.
A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and of
witness: the honest relation; a second relation, called relaxed, of which round-by-round knowledge
soundness speaks; the set of statements of which that soundness speaks; and a map from a witness to
its core.
The relaxed relation of `S.over A` says that the decoder with the sample (`OMsg.dec`,
Cb/Ld/LdSig.lean: the nearest codeword, first in a fixed order (given by `rank`; it is a total order
if `rank` is injective, which nothing here asks), among the pairs whose message has the answers;
none beyond the radius) returns the witness's messages, and A's relaxed relation of them.
  `LdStage E Kc`: the data of such a joint (see its fields' docstrings; E₀: an encoded index, the
    word of a test that is open). `a.X`, `a.Ex`, `a.W`: the types. `a.J` = (S.over A).cf, as a joint
    of a chain.
  `a.idLink`: the step that does nothing (no round): the head of a chain that may be empty.

The moves whose form is fixed:
 1. One sending of a family N (`LdSendD a`: see its fields' docstrings, also for bk).
    `d.tgt`: the stage over `S.sum N` with the base joint `S.grow N A bk`. `d.link`: the block of
    Cb/Ld/LdSigSum.lean: one prover message with all words, one verifier message with the seeds, one
    prover message with all answers.
    `d.Hyp`: that block's seven hypotheses, word for word.
 2. Kept messages held in an open word (`LdHeld E C`). After a fold the folded word has slots that
    are words of oracle messages which later parts of the protocol still read. From the fold to the
    locations such an oracle message is read there: sW k f is its word, cut out of the open word f;
    sJ, sQ name its message and randomness among those of a codeword of C.
    `h.Laws e`: the slot of an encoding is the encoding of the slots; words of C within e long
    positions of each other have slots within the member's own radius.
    `o.decW`, `o.ClashW`: the decoder with a sample and "collision" of Cb/Ld/LdSig.lean, for a
    native word (o.dec f = o.decW (o.upW f), by definition).
    `heldB C e h Φ rd A₀`: the base joint with an open test. Further oracles: (the open word f,
    those of A₀). Explicit part: ((claim on f, the samples of the held messages), that of A₀).
    Further witness: ((message, randomness) of C, that of A₀).
      Exact: f is the encoding, Φ of its message, the held slots have the answers of their samples,
      A₀ of "rd messages slots".
      Relaxed: f is within e long positions of the encoding (existential: no decoder of f) and Φ;
      each held message decodes with its sample, to the slot of the witness; A₀'s relaxation of "rd
      messages slots". Condition: no held message has a collision, and A₀'s.
    So the carried predicates go on reading the decoding of a kept message until the locations.
 3. The first half of the closing of a group (`LdFoldD`: see its fields' docstrings).
    `D.src`: the stage "rows on G, beside A₀ of the kept messages": the input joint of the bridge
      (Cb/Ld/LdBatSig.lean), letter for letter.
    `D.mid`: the joint at which l ends (l: "bridge, arrangement, fold", a parameter of `D.link`):
      the main relation of Cf, relaxed existentially, beside (S.sub kp).over A₀.
    `D.tgt`: the stage over the kp that are not held, with the base joint heldB Cf e .. slf.Holds ..
      A₀.
    `D.link l`: the link l from D.src to D.mid, then a step without rounds: re-bracketing; the words
      of the held messages are dropped (they are in the folded word), their samples move into the
      explicit part.
    `D.Tw`: "the slots of the folded word are the words of the held messages": a property of the
      statements that l puts out.
    `D.Hyp l`: see its docstring.
 4. The locations (`LdLocD`: see its fields' docstrings). The new messages are among the members of
    its signature S.
    `D.src`: any stage whose base joint A is, clause by clause (`D.Near`), "heldB with the witness
      of the open word read off the messages": what one sending makes of `LdFoldD.tgt`.
    `D.tgt`: the open word is gone, and with it the held messages. Explicit part: the old one, the
      locations, the long symbols read. Claimed of the messages of S, in the exact and in the
      relaxed form alike: Φ of the cut; the old samples' rows hold of the slots of the cut; the
      encoding of the cut has the symbols read at the locations; A₁.
    `D.link`: the block of Cb/Ld/LdSwitchLoc.lean between two re-bracketings: one round, nothing
      sent, t locations.
 5. The two moves before the folds: `LdBatD` (many rows, on whatever groups, into one:
    Cb/Ld/LdBatSig.lean) and `LdSplD` (a row on two groups into a row on each, by one mask entry
    that both groups hold: Cb/Ld/LdSplit.lean): source and target stage, link, hypotheses; `D.mask`:
    the parameters of the split's item "masked messages".

Limits: this file states nothing. It says nothing on which groups a protocol forms, on layouts. This
file gives no value of any parameter of the protocol.
Stages, moves and the treatment of kept messages follow this protocol's technical report; main
relation, fold and locations follow the paper that this protocol builds on (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSigSum
import Cb.Ld.LdBatSig
import Cb.Ld.LdSplit
import Cb.Ld.LdSwitchLoc
import Ior.KnowCollRulesChain
import Ior.KnowCollRulesFrame
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood

/-! ## 0. The decoder with a sample, for a native word -/

namespace OMsg
variable {E : Type} [Field E] (o : OMsg E)

/-- the decoder of Cb/Ld/LdSig.lean, for a native word -/
def decW (f : o.C.Word) (σ : o.Smp) : Option o.Msg :=
  decMin (fun w : o.Wit => cnt fun x : o.P => o.C.T f x ≠ o.C.T (o.C.enc w.1 w.2) x)
    o.rank Prod.fst o.Z.val o.e σ.1 σ.2

/-- a collision at a seed, for a native word -/
def ClashW (f : o.C.Word) (ρ : o.Z.D) : Prop := Ood.Clash (o.C.Msgs o.e f) o.Z.val ρ

end OMsg

/-! ## 1. Stages -/

/-- A stage of a preamble: the data of a joint over oracle messages with samples. -/
structure LdStage (E Kc : Type) : Type 1 where
  /-- the oracle messages that are open -/
  S  : Sig E
  /-- the explicit part without the samples -/
  St : Type
  /-- further oracles, never sampled -/
  E₀ : ExtSpec
  /-- a further witness -/
  Wp : Type
  /-- what is claimed of the messages -/
  A  : IOR.Rels Kc St E₀ (S.Msg × Wp)

namespace LdStage
variable {E Kc : Type}

abbrev X (a : LdStage E Kc) : Type := a.St × a.S.Smp
abbrev Ex (a : LdStage E Kc) : ExtSpec := a.E₀.prod a.S.ext
abbrev W (a : LdStage E Kc) : Type := a.S.Wit × a.Wp

variable [Field E]

/-- The joint of a chain: relaxed by decoding with a sample; "collision-free" may fail. -/
@[reducible] def J (a : LdStage E Kc) : IOR.Joint Kc := ⟨a.X, a.Ex, a.W, (a.S.over a.A).cf⟩

/-- the step that does nothing -/
def idLink (a : LdStage E Kc) : IOR.Link Kc a.J a.J :=
  ⟨IOR.pure (fun x => some x) (ExtMap.id a.Ex),
    IOR.Honest.pure _ _ (fun p => p),
    fun _ _ w => w,
    IOR.Nums.pure Kc _ _⟩

end LdStage

/-! ## 2. One sending -/

/-- One sending of a family: the data. -/
structure LdSendD {E Kc : Type} (a : LdStage E Kc) : Type 1 where
  /-- the family -/
  N   : Sig E
  /-- how the seeds are drawn -/
  Sd  : N.Seeds
  /-- the further witness afterwards, and what the new messages give back of the old one -/
  Wp' : Type
  bk  : N.Msg → Wp' → a.Wp
  /-- the honest sender -/
  D   : N.Sender (a.S.Wit × a.Wp) (a.S.Wit × Wp')
  /-- bounds for the lists; long positions that the encodings bear (by type any maps `N.O → ℕ`; they
  enter `ldSendSigNums`; that they are such bounds is asked: `LdSendD.Hyp.list`, `.hides`) -/
  L   : N.O → ℕ
  t   : N.O → ℕ

namespace LdSendD
variable {E Kc : Type} {a : LdStage E Kc} (d : LdSendD a)

/-- the stage after the sending -/
@[reducible] def tgt : LdStage E Kc := ⟨a.S.sum d.N, a.St, a.E₀, d.Wp', a.S.grow d.N a.A d.bk⟩

variable [Field E]

/-- The link. -/
def link : IOR.Link Kc a.J d.tgt.J where
  R := ldSendSig a.S d.N d.Sd a.St a.E₀
  H := ldSendSigHon d.Sd a.St a.E₀ d.D
  ext := fun _ _ w =>
    (a.S.left d.N (T := OMsg.Wit) w.1, d.bk (d.N.msgs (a.S.right d.N (T := OMsg.Wit) w.1)) w.2)
  P := ldSendSigNums a.S d.N d.Sd a.St a.E₀ Kc d.L d.t

/-- What is asked: the hypotheses of the block. -/
structure Hyp : Prop where
  laws   : ∀ i, (d.N.om i).C.Laws
  fair   : d.Sd.Fair
  list   : ∀ i, (d.N.om i).ListLE (d.L i)
  evades : ∀ i, (d.N.om i).Evades
  sender : d.D.Laws (a.S.backN d.N d.bk)
  blind  : d.D.Blind d.Sd
  hides  : d.D.Nn.Hides (d.N.budT d.t)

end LdSendD

/-! ## 3. Kept messages held in an open word -/

/-- Oracle messages whose words are slots of a word of C: the data. -/
structure LdHeld (E : Type) {P : Type} (C : LdCode E P) : Type 1 where
  K  : Type
  o  : K → OMsg E
  /-- the word of a held message, cut out of a word of C -/
  sW : ∀ k, C.Word → (o k).C.Word
  /-- where its message and its randomness are among those of C -/
  sJ : ∀ k, (o k).C.J → C.J
  sQ : ∀ k, (o k).C.Q → C.Q

namespace LdHeld
variable {E P : Type} {C : LdCode E P} (h : LdHeld E C)

abbrev Smp : Type := ∀ k, (h.o k).Smp
/-- the slots of a message and of encoding randomness -/
def msg (u : C.J → E) : ∀ k, (h.o k).Msg := fun k j => u (h.sJ k j)
def rnd (r : C.Q → E) : ∀ k, (h.o k).Rnd := fun k q => r (h.sQ k q)

/-- nothing is held -/
@[reducible] def none (E : Type) {P : Type} (C : LdCode E P) : LdHeld E C :=
  ⟨Empty, fun k => k.elim, fun k => k.elim, fun k => k.elim, fun k => k.elim⟩

/-- The laws. -/
structure Laws [Field E] [Finite P] (e : ℕ) : Prop where
  slot : ∀ k m r, h.sW k (C.enc m r) = (h.o k).C.enc (h.msg m k) (h.rnd r k)
  fits : ∀ k f g, C.Near e f g → (h.o k).C.Near (h.o k).e (h.sW k f) (h.sW k g)

end LdHeld

section
variable {E P Kc Xc M M' St₀ Wp : Type} [Field E] [Fintype E] [Fintype P] {E₀ : ExtSpec}

/-- The base joint with an open test. -/
def heldB (C : LdCode E P) (e : ℕ) (h : LdHeld E C) (Φ : Xc → (C.J → E) → Prop)
    (rd : M' → (∀ k, (h.o k).Msg) → M) (A₀ : IOR.Rels Kc St₀ E₀ (M × Wp)) :
    IOR.Rels Kc ((Xc × h.Smp) × St₀) (C.ext.prod E₀) (M' × (C.N.Wit × Wp)) where
  rel  := fun x y w =>
    Con C.N Φ x.1.1 y.1 w.2.1 ∧
    (∀ k, (h.o k).Z.val (x.1.2 k).1 (h.msg w.2.1.1 k) = (x.1.2 k).2) ∧
    A₀.rel x.2 y.2 (rd w.1 (h.msg w.2.1.1), w.2.2)
  relR := fun a w =>
    ConL C.N e Φ (a.1.1.1, a.2.1) w.2.1 ∧
    (∀ k, (h.o k).decW (h.sW k a.2.1) (a.1.1.2 k) = some (h.msg w.2.1.1 k)) ∧
    A₀.relR (a.1.2, a.2.2) (rd w.1 (h.msg w.2.1.1), w.2.2)
  on   := fun a => (∀ k, ¬ (h.o k).ClashW (h.sW k a.2.1) (a.1.1.2 k).1) ∧ A₀.on (a.1.2, a.2.2)
  core := fun w => A₀.core (rd w.1 (h.msg w.2.1.1), w.2.2)

end

/-! ## 4. The first half of the closing of a group -/

/-- Bridge, arrangement, fold on one group, with kept messages: the data. -/
structure LdFoldD (E Kc : Type) [Field E] [Fintype E] : Type 1 where
  S   : Sig E
  G   : Grp S
  /-- the oracle messages that something after the bridge still reads -/
  kp  : S.O → Prop
  [decKp : DecidablePred kp]
  /-- the rows on the group -/
  B   : Type
  Sb  : B → Type
  sl  : ∀ b, Slf E (Sb b) G.C.J
  /-- what else is claimed, of the messages with kp -/
  St₀ : Type
  Wp  : Type
  E₀  : ExtSpec
  A₀  : IOR.Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)
  /-- the folded complex, its one form, the joint radius -/
  Pf  : Type
  [finPf : Fintype Pf]
  Cf  : LdCode E Pf
  Stf : Type
  slf : Slf E Stf Cf.J
  e   : ℕ
  /-- which of the oracle messages with kp are held in the folded word from here on -/
  cl  : {o // kp o} → Prop
  [decCl : DecidablePred cl]
  sW  : ∀ k : {a // cl a}, Cf.Word → (S.om k.1.1).C.Word
  sJ  : ∀ k : {a // cl a}, (S.om k.1.1).C.J → Cf.J
  sQ  : ∀ k : {a // cl a}, (S.om k.1.1).C.Q → Cf.Q

attribute [instance] LdFoldD.decKp LdFoldD.finPf LdFoldD.decCl

namespace LdFoldD
variable {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc)

/-- the oracle messages after the bridge; those that are not held -/
abbrev S₁ : Sig E := D.S.sub D.kp
abbrev S₂ : Sig E := D.S₁.sub fun a => ¬ D.cl a

/-- the held messages -/
@[reducible] def held : LdHeld E D.Cf := ⟨{a // D.cl a}, fun k => D.S.om k.1.1, D.sW, D.sJ, D.sQ⟩

/-- the messages after the bridge, from those that are not held and the slots -/
def rd (m : D.S₂.Msg) (u : ∀ k, (D.held.o k).Msg) : D.S₁.Msg := fun a =>
  if h : D.cl a then u ⟨a, h⟩ else m ⟨a, h⟩

/-- Rows on the group, beside A₀ of the kept messages. -/
@[reducible] def src : LdStage E Kc :=
  ⟨D.S, ((D.B → E) × (∀ b, D.Sb b)) × D.St₀,
    D.E₀, D.Wp,
    claimRels (fun x m => Slf.All D.sl x (D.G.msg m))
      (onMsgRels (D.S.res (T := OMsg.Msg) D.kp) D.A₀)⟩

/-- The main relation of the folded complex, relaxed existentially, beside the carried part. -/
@[reducible] def mid : IOR.Joint Kc :=
  ⟨(E × D.Stf) × (D.St₀ × D.S₁.Smp),
    D.Cf.ext.prod (D.E₀.prod D.S₁.ext),
    D.Cf.N.Wit × (D.S₁.Wit × D.Wp),
    IOR.Rels.beside (D.Cf.rels D.slf D.e fun _ => ()) (D.S₁.over D.A₀)⟩

/-- The stage with the open test. -/
@[reducible] def tgt : LdStage E Kc :=
  ⟨D.S₂, ((E × D.Stf) × D.held.Smp) × D.St₀, D.Cf.ext.prod D.E₀, D.Cf.N.Wit × D.Wp,
    heldB D.Cf D.e D.held D.slf.Holds D.rd D.A₀⟩

/-- The slots of the folded word are the words of the held messages. -/
def Tw (b : D.mid.X × D.mid.E.Str) : Prop :=
  ∀ k : {a // D.cl a}, D.sW k b.2.1 = (D.S.om k.1.1).upW (b.2.2.2 k.1)

/-- the step without rounds: explicit part, oracles, the honest prover, the extractor -/
def pX (x : D.mid.X) : D.tgt.X := (((x.1, fun k => x.2.2 k.1), x.2.1), fun a => x.2.2 a.1)

def pE : ExtMap D.mid.E D.tgt.Ex :=
  ((ExtMap.fst D.Cf.ext (D.E₀.prod D.S₁.ext)).pair
      ((ExtMap.fst D.E₀ D.S₁.ext).comp (ExtMap.snd D.Cf.ext (D.E₀.prod D.S₁.ext)))).pair
    ((D.S₁.subExt fun a => ¬ D.cl a).comp
      ((ExtMap.snd D.E₀ D.S₁.ext).comp (ExtMap.snd D.Cf.ext (D.E₀.prod D.S₁.ext))))

def pW (w : D.mid.W) : D.tgt.W := (fun a => w.2.1 a.1, (w.1, w.2.2))

def pB (w : D.tgt.W) : D.mid.W :=
  (w.2.1, (fun a =>
        if h : D.cl a then (D.held.msg w.2.1.1 ⟨a, h⟩, D.held.rnd w.2.1.2 ⟨a, h⟩) else w.1 ⟨a, h⟩,
      w.2.2))

/-- The link: l, then the step. -/
def link (l : IOR.Link Kc D.src.J D.mid) : IOR.Link Kc D.src.J D.tgt.J where
  R := l.R.post (fun x => some (D.pX x)) D.pE
  H := l.H.post (fun x => some (D.pX x)) D.pE fun p => (D.pX p.1, D.pW p.2)
  ext := fun a τ w => l.ext a τ (D.pB w)
  P := l.P.post (fun x => some (D.pX x)) D.pE

/-- What is asked: `IOR.GoodT` of l; the fold returns the held messages: words (of every statement
that l puts out) and the honest prover's pairs; the laws of the slots. -/
structure Hyp (l : IOR.Link Kc D.src.J D.mid) : Prop where
  good : IOR.GoodT l.R l.H (D.S.over D.src.A) D.mid.rels l.ext l.P
  word : ∀ a τ b, l.R.red.out a τ = some b → D.Tw b
  wit  : ∀ w x c ρ (k : {a // D.cl a}),
    (D.held.msg ((l.H.strat w x c).run ρ).2.2.1.1 k,
        D.held.rnd ((l.H.strat w x c).run ρ).2.2.1.2 k) =
      ((l.H.strat w x c).run ρ).2.2.2.1 k.1
  laws : D.held.Laws D.e

end LdFoldD

/-! ## 5. The locations -/

/-- The locations: the data. -/
structure LdLocD (E Kc : Type) [Field E] [Fintype E] : Type 1 where
  S   : Sig E
  /-- the open word's code, the radius, the number of locations -/
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
  Wp  : Type
  E₀  : ExtSpec
  /-- the claim on the open word's message -/
  Φ   : Xc → (C.J → E) → Prop
  /-- (message, randomness) of the open word, as the messages of S have them -/
  cut : S.Msg → C.N.Wit
  /-- what else is claimed -/
  A₁  : IOR.Rels Kc St₀ E₀ (S.Msg × Wp)
  /-- the base joint before the locations -/
  A   : IOR.Rels Kc ((Xc × hd.Smp) × St₀) (C.ext.prod E₀) (S.Msg × Wp)

attribute [instance] LdLocD.finP LdLocD.neP

namespace LdLocD
variable {E Kc : Type} [Field E] [Fintype E] (D : LdLocD E Kc)

@[reducible] def src : LdStage E Kc :=
  ⟨D.S, (D.Xc × D.hd.Smp) × D.St₀, D.C.ext.prod D.E₀, D.Wp, D.A⟩

/-- The base joint before the locations is "an open test whose witness is read off the messages",
clause by clause. -/
structure Near : Prop where
  rel  : ∀ x y w,
    D.A.rel x y w ↔
    Con D.C.N D.Φ x.1.1 y.1 (D.cut w.1) ∧
    (∀ k, (D.hd.o k).Z.val (x.1.2 k).1 (D.hd.msg (D.cut w.1).1 k) = (x.1.2 k).2) ∧
    D.A₁.rel x.2 y.2 w
  relR : ∀ a w,
    D.A.relR a w ↔
    ConL D.C.N D.e D.Φ (a.1.1.1, a.2.1) (D.cut w.1) ∧
    (∀ k, (D.hd.o k).decW (D.hd.sW k a.2.1) (a.1.1.2 k) = some (D.hd.msg (D.cut w.1).1 k)) ∧
    D.A₁.relR (a.1.2, a.2.2) w
  on   : ∀ a,
    D.A.on a ↔ (∀ k, ¬ (D.hd.o k).ClashW (D.hd.sW k a.2.1) (a.1.1.2 k).1) ∧ D.A₁.on (a.1.2, a.2.2)
  core : ∀ w, D.A.core w = D.A₁.core w

/-- the locations and the long symbols read -/
abbrev Lc : Type := (Fin D.t → D.P) × (Fin D.t → D.C.Aa → E)

/-- What is claimed after the locations, of the messages: the claim; the old samples' rows on the
slots; the symbols read. -/
def After (x : (D.Xc × D.hd.Smp) × D.Lc) (m : D.S.Msg) : Prop :=
  D.Φ x.1.1 (D.cut m).1 ∧
  (∀ k, (D.hd.o k).Z.val (x.1.2 k).1 (D.hd.msg (D.cut m).1 k) = (x.1.2 k).2) ∧
  (fun i => D.C.T (D.C.enc (D.cut m).1 (D.cut m).2) (x.2.1 i)) = x.2.2

@[reducible] def tgt : LdStage E Kc :=
  ⟨D.S, ((D.Xc × D.hd.Smp) × D.Lc) × D.St₀, D.E₀, D.Wp, claimRels D.After D.A₁⟩

/-- the verifier of the block -/
@[reducible] def V : LdLocV E D.P D.src.X D.tgt.X :=
  ⟨D.C, D.t, fun x Qs v => (((x.1.1, (Qs, v)), x.1.2), x.2)⟩

/-- the two re-bracketings -/
def inE : ExtMap D.src.Ex (D.C.ext.prod (D.E₀.prod D.S.ext)) :=
  ((ExtMap.fst D.C.ext D.E₀).comp (ExtMap.fst (D.C.ext.prod D.E₀) D.S.ext)).pair
    (((ExtMap.snd D.C.ext D.E₀).comp (ExtMap.fst (D.C.ext.prod D.E₀) D.S.ext)).pair
      (ExtMap.snd (D.C.ext.prod D.E₀) D.S.ext))

def outE : ExtMap (extNone.prod (D.E₀.prod D.S.ext)) D.tgt.Ex :=
  ExtMap.snd extNone (D.E₀.prod D.S.ext)

/-- The link. -/
def link : IOR.Link Kc D.src.J D.tgt.J where
  R := ((ldLocOf D.V (D.E₀.prod D.S.ext)).pre (fun x => some x) D.inE).post (fun x => some x) D.outE
  H := ((ldLocHon D.V (D.E₀.prod D.S.ext) fun w : D.src.W => D.cut (D.S.msgs w.1)).pre
      (fun x => some x) D.inE fun p => p).post
    (fun x => some x) D.outE fun p => p
  ext := fun _ _ w => w
  P := ((ldLocNums D.V Kc (D.E₀.prod D.S.ext) D.e).pre (fun x => some x) D.inE).post
    (fun x => some x) D.outE

/-- What is asked. -/
structure Hyp : Prop where
  near : D.Near
  laws : D.hd.Laws D.e

end LdLocD

/-! ## 6. Many rows into one; a row on two groups into a row on each -/

/-- Many rows into one, on statements with samples: the data. -/
structure LdBatD (E Kc : Type) [Field E] : Type 1 where
  S   : Sig E
  B   : Type
  [finB : Fintype B]
  Sb  : B → Type
  /-- the rows: linear forms on all entries of all messages -/
  sl  : ∀ b, Slf E (Sb b) S.Ent
  Z   : Evader E B
  St₀ : Type
  Wp  : Type
  E₀  : ExtSpec
  A₀  : IOR.Rels Kc St₀ E₀ (S.Msg × Wp)

attribute [instance] LdBatD.finB

namespace LdBatD
variable {E Kc : Type} [Field E] (D : LdBatD E Kc)

@[reducible] def src : LdStage E Kc :=
  ⟨D.S, ((D.B → E) × (∀ b, D.Sb b)) × D.St₀, D.E₀, D.Wp,
    claimRels (fun x m => Slf.All D.sl x (D.S.ents m)) D.A₀⟩
@[reducible] def tgt : LdStage E Kc :=
  ⟨D.S, (E × ((∀ b, D.Sb b) × D.Z.D)) × D.St₀, D.E₀, D.Wp,
    claimRels (fun x m => (Slf.bat D.Z.ze D.sl).Holds x (D.S.ents m)) D.A₀⟩

def link : IOR.Link Kc D.src.J D.tgt.J :=
  ⟨ldBatSig D.S D.Sb D.Z D.St₀ D.E₀,
    ldBatSigH D.S D.Sb D.Z D.St₀ D.Wp D.E₀,
    fun _ _ w => w,
    ldBatSigN D.S D.Sb D.Z D.St₀ D.E₀ Kc⟩

def Hyp : Prop := D.Z.OK

end LdBatD

/-- A row on two groups into a row on each: the data. -/
structure LdSplD (E Kc : Type) [Field E] [Fintype E] : Type 1 where
  S   : Sig E
  G₁  : Grp S
  G₂  : Grp S
  /-- where the mask entry is -/
  k   : SplitAt G₁ G₂
  St₁ : Type
  St₂ : Type
  sl₁ : Slf E St₁ G₁.C.J
  sl₂ : Slf E St₂ G₂.C.J
  St₀ : Type
  Wp  : Type
  E₀  : ExtSpec
  A₀  : IOR.Rels Kc St₀ E₀ (S.Msg × Wp)
  /-- the entries that the block reads -/
  Rd  : S.Ent → Prop
  [decRd : DecidablePred Rd]

attribute [instance] LdSplD.decRd

namespace LdSplD
variable {E Kc : Type} [Field E] [Fintype E] (D : LdSplD E Kc)

@[reducible] def src : LdStage E Kc :=
  ⟨D.S, (E × (D.St₁ × D.St₂)) × D.St₀, D.E₀, D.Wp, claimRels (splitIn D.sl₁ D.sl₂) D.A₀⟩
@[reducible] def tgt : LdStage E Kc :=
  ⟨D.S, ((E × D.St₁) × (E × D.St₂)) × D.St₀, D.E₀, D.Wp, claimRels (splitOut D.k D.sl₁ D.sl₂) D.A₀⟩

def link : IOR.Link Kc D.src.J D.tgt.J :=
  ⟨ldSplitR D.S D.St₁ D.St₂ D.St₀ D.E₀,
    ldSplitH D.k D.sl₁ D.St₂ D.St₀ D.Wp D.E₀,
    fun _ _ w => w,
    ldSplitN D.S D.St₁ D.St₂ D.St₀ D.E₀ Kc⟩

/-- the parameters of its item "masked messages" -/
def mask : IOR.MaskData D.link.R D.src.J.W :=
  ldSplitD D.k D.sl₁ D.sl₂ D.Rd D.St₀ D.Wp D.E₀

structure Hyp : Prop where
  own₁ : ∀ st, D.sl₁ st D.k.e₁ = 0
  own₂ : ∀ st, D.sl₂ st D.k.e₂ = 0
  rd₁  : ∀ st n, ¬ D.Rd (D.G₁.ent n) → D.sl₁ st n = 0
  rd₂  : ∀ st n, ¬ D.Rd (D.G₂.ent n) → D.sl₂ st n = 0
  rdK  : D.Rd ⟨D.k.o, D.k.j⟩

end LdSplD

end Cb
