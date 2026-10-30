-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdMia.lean: masks sent in advance: one theorem on a composition of blocks of three kinds.

This file is about the sequential composition of interactive oracle reductions: it defines which
lists of steps its composition theorem covers, and states and proves that theorem.
Definitions, statements and proofs.
This protocol's technical report (lean/CREDITS.md) has one lemma of its own for all its preambles
(it is not of the paper that this protocol builds on: the reduction of the paper that this protocol
builds on sends its masks itself): oracle messages that hold masks go out early; later blocks use
entries of them; in between nobody looks. In this library the
same idea is spread over several definitions and rules (`Fresh`, `Blind`, `FreshGiven`, the wide
fact, the senders' rules, the joining rule). Here it is one statement on a program of moves
(`LdProg`, `LdMv`: Cb/Req1/LdSeg.lean) over stages (`LdStage`: Cb/Req1/LdSegKit.lean), by induction
along the composition, where a write-up of ours (lean/CREDITS.md) writes indices.

Main names:
  `LdPend`: what is tracked: at each stage a set of pending blocks β. In a pending block, `own` is a
    set of entries of open oracle messages: the masks of one later block, or of a part of one. `Mk`
    is the masks' type, and `val` gives the values laid at own. `Rd` and `Rr` tell what may be seen
    meanwhile: the entries Rd, and the names Rr whose encoding randomness may be seen. `β.fact` is
    the wide fact (Cb/Req1/LdSegCarry.lean), a `MaskFact` (Cb/Req1/LdSegFresh.lean). A `MaskFact W`
    is a reading `kc` of witnesses of type W into a type `Kc`, a finite, non-empty type `Mk`, and a
    map `put : Mk → Kc → Kc`.
  `c.FreshS kc Mk put` (Cb/Req1/LdSegFreshS.lean) is
    `∀ d : A.W, (c.link d).H.Fresh A.rels.rel (c.link d).P.bud kc Mk put`.
    `H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and
    every T with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its
    third part is overwritten by `put M` at an independent uniform M. In `Spec.ldMia` `FreshS`
    stands as a conclusion; in `Spec.ldProgC` as a premise (of the chain before) and as a
    conclusion.
  `LdMia F p Pd`: "p is a composition of blocks of the three kinds, and Pd are blocks whose masks
    are out and unused behind it":
    (i) send: p ; the standard sending of a layout Y (Cb/Obj/LdObjectSenders.lean: data off the
        witness, free entries uniform, pads), with `Y.OK t` and "what is read back off the data,
        with what is handed on, is the further witness". Pending behind it:
      newMany: a block whose masks are at any injective family of free entries in whichever new
        members. Seen are all new entries that are no pads, and no new encoding randomness.
      newOne: a block whose masks are at any injective family of free entries of one new member o.
        Seen are all new entries but o's pads, and the encoding randomness of all new members but o
        (the form that can cross a closing).
      In both, of the old messages anything is seen.
      old: a block that was pending, if the data that are sent do not look at it (`DatBlind`). Of
        the new messages it may see anything.
    (ii) masked: p ; one link with masked messages (`l.GoodM D`), whose fact follows from pending
         facts by join at one reading, coarser readings, another type for the same masks
         (`MaskFact.JCl`: Cb/Req1/LdSegFreshS.lean): so its masks may come from several sendings.
         Pending behind it: what the link hands on.
    (iii) other: p ; any move of which zero knowledge asks nothing beside its own bundle:
          `∀ X, m.Zk X` (steps, batchings, folds, locations, sendings, chains of links with zero
          knowledge of their own). Pending behind it: what the move hands on.
  `m.Hands β β'`: the move m hands the pending block β on as β'. That is: for every set Y of facts
    with β's, the fact of β' is fresh after m, given Y. Unfolded (`FreshGiven`), link by link:
    `Fresh`; or the honest prover's messages and the rest of its output are the same when β's own
    entries are overwritten, and these entries are copied (`Blind`) (exactly: `Chain.FreshGiven`,
    Cb/Req1/LdSegFresh.lean).
  `LdProg.AfterC`, `LdProg.ZkC`, `Spec.ldProgC`: the calculus of Cb/Req1/LdReq.lean with the set of
    fresh facts closed after every move. Under the hypotheses of its statement, behind any chain
    whose facts are fresh, every link is of one of the two kinds (`Chain.OkS`,
    Cb/Req1/LdSegFreshS.lean), and every fact of the closed set is fresh (Cb/Req1/LdReqS.lean's
    rules, one move at a time).
  `Spec.ldMia_zk`: `LdMia F p Pd` → what zero knowledge asks of p, beside its hypotheses (`p.Hyp`),
    is met in this sense: `p.ZkC (fun _ => False)` (`LdProg.ZkC`: `LdMv.Zk` of every move, a
    condition move by move; a premise of `Spec.ldProgC`), and the facts of all blocks in Pd are
    fresh behind p in this sense: they are in `p.AfterC (fun _ => False)` (that every fact of this
    set is fresh: `Spec.ldProgC`, under its hypotheses).
  `Spec.ldMia`: `LdMia F p Pd` → `p.Hyp` → the composition as one link has the whole bundle
    (completeness, knowledge soundness round by round, exact honest-verifier zero knowledge with the
    composed simulator (in this sense: `GoodT.exact`: `Honest.Exact`, Ior/Honest.lean:
    `∃ S : Sim R, …`, which speaks only of ρ outside `H.Hid w x` and of T with `P.bud ρ T`: the
    statement names no simulator)), and it is Fresh for the fact of every block in Pd.

Correspondences with the write-up's lemma (in our words):
  its first kind (a sending of messages with masks; others may ride): clause (i). That the sending
    is fresh is derived here, from `Y.OK t`; the write-up's proof has it as its key step.
  its second kind (masked messages on the block's set of entries): clause (ii).
  its third kind (zero knowledge by itself; blocks without prover message; sendings without masks):
    clause (iii).
  "no step is of the first two kinds at once": by the form of the clauses.
  a message is pending from its sending to the last block that uses it: as long as some pending
    block has an own entry in it.
  the unused part of a pending message: what the facts of the blocks still pending forget.
  a block's set may hold entries of several messages: newMany (one sending); the join in clause (ii)
    (several sendings).
  its hypothesis on the steps in between, third item (the prover's messages and the rest of its
    output depend on the unused part only through the step's own set), and the copying of the first
    item: `Hands` / `DatBlind`.
  its conclusion (the whole is zero knowledge; nothing is pending at the end): `Spec.ldMia` at any
    Pd; the write-up's case is Pd empty. That pending facts are fresh behind p is more, and
    what a composition of programs needs.

Notation: `F`, `E`: finite fields, E an algebra over F; `Kc` in `LdStage E Kc`: the type into which
a joint's `core` maps witnesses; in the sentence on `MaskFact` it is that structure's own field;
`a`, `b`: stages (`LdStage E Kc`); `c` in the row of `FreshS`: a chain (`Chain Kc A B`) from the
joint `A`; `d`: a witness at `A`; `p`: a program (`LdProg a b`); `m`: a move (`LdMv`); `l`: a link
(`Link`); `D` in (ii): a `MaskData` of l; `Pd`: a set of pending blocks at the last stage
(`LdPend b → Prop`); `β`, `β'`: pending blocks; `X`, and `Y` in the row of `Hands`: sets of facts;
`Y` in (i): a layout (`N.StdL F`) over the signature `N` of the new members; `t`: a number for each
new member (`N.O → ℕ`); `w₀`: a witness at the first stage (`a.W`). (`IOR.Rels`: Ior/Chain.lean;
`MaskFact`: Cb/Req1/LdSegFresh.lean; `Chain.FreshS`: Cb/Req1/LdSegFreshS.lean.)

Limits:
Where this is not the write-up's lemma:
  (1) Exact hiding only: no error terms of the encodings. The write-up's error has three
      sums: of the third kind's errors, of the encodings' errors, of the completeness errors of all
      steps but the last; here: the links' own numbers, composed; to the third sum correspond the
      probabilities of the hidden withheld sets.
  (2) No vectors of numbers of queries (the write-up's two further hypotheses): the budget
      is the
      links' own, nested. That it holds the sets "at most t positions of each message" is the matter
      of formats (Cb/*/LdReq*Fmt*.lean), not of this theorem.
  (3) In clause (ii) the write-up also asks that the verifier make no query. Not asked here:
      `l.GoodM D` says that the block sends no oracle; it sets no bound on what its verifier reads
      of the implicit instance (`R.extReads`).
  (4) Not asked here, so this statement is wider: that no verifier in between query a pending
      message's mask word (a pending word may be read within what its encoding hides); that the
      relations in between constrain the unused part by encoding and sample alone.
  (5) The write-up protects the mask part of a pending message (its mask word, that word's
      encoding randomness, the unused mask entries with the pad) and wants the pad there. Here a
      message is one word: the holder's whole encoding randomness and its pads are forgotten until
      the block runs; other blocks' unused entries may be seen by a block's reading.
  (6) That the blocks' sets of entries are disjoint is not asked as such; at a sending two pending
      blocks may even name one entry. Harmless: disjointness is what makes `Hands` true in
      instances: the first block that uses an entry breaks `Hands` for every other block that names
      it (in this sense: `Spec.ldMia` is proved, `ldMia`, without a premise on disjointness;
      no theorem of this library states that a use breaks `Hands`; the controls
      `Iop.MaskCtl.used_not_blind`, `Iop.MaskCtl.used_not_fresh`, Ior/MaskControls.lean, are on
      `Honest.Blind` and `Honest.Fresh` at one small case on bits, `Hb`, `H₁.seq Hb`, not on
      `Hands`).
  (7) One statement is proved at a time: no batch of several statements (the write-up's last
      sentence): no form for sets of instances. The write-up uses that form: in the test for
      linear constraints, and for the request followed by that test.
  (8) No clause for a move "split" (by a proof that Lean accepted and that is no part of this
      library: `LdMia F p Pd` → no move of p has the tag "split"): clause (ii) takes "sub (one l)"
      alone, and clause (iii) asks `m.Zk X` for all X, which is false for a split at the empty set.
      In the write-up's test for linear constraints the block of the second kind is the
      splitting. So "one lemma for all its preambles" is not what this theorem covers: of the four
      places at which the write-up uses its lemma (weights-formedness, the test for linear
      constraints, segments and request, the range check) the second is outside, unless the
      splitting is written as "sub (one D.link)".

No instance of `LdMia` is shown in this file but the empty program (`LdMia.nil`).
No theorem of this library states that the hypotheses of `ldMia` can be met together. In LdMia's own
calculus the join of clause (ii) has no instance.
At the toy parameters (`RefToy.p`: Cb/Req1/LdSegRefToy.lean) the one event at which
the honest prover can give up is the request's one hidden withheld set, the range check's window
event (that it is the only such set: by reading, not by a theorem). It is empty, in this sense:
`rngEv RefToy.p Y = ∅` for every `Y : RefToy.p.Cells` (`ldRng_toyNoEv`,
Cb/Req1/LdSegRefToyNoEv.lean). So none of the guards at these parameters has a mask
pending across a link that can withhold (by reading). Of other parameters that theorem says nothing.


This theorem (`ldMia`) stands alone: no other file names it. This file says
nothing on segments and requests (Cb/Req1/LdReqS.lean, Cb/Req1/LdReqRefLayJ.lean have their own
forms).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Req1.LdReqSProofs
import Cb.Req1.LdReqRefLayJ
import Cb.Req1.LdReqStdFresh
import Cb.Ld.LdSendStdVis
import Cb.Req1.LdSegProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR IOR.Chain Cb.Ood

/-- the closure is closed -/
theorem MaskFact.jcl_idem {W : Type} {X : MaskFact W → Prop} :
    ∀ f, MaskFact.JCl (MaskFact.JCl X) f → MaskFact.JCl X f := by
  intro f hf
  induction hf with
  | base f hx => exact hx
  | join Kc kc M₁ M₂ put₁ put₂ _ _ i1 i2 => exact .join Kc kc M₁ M₂ put₁ put₂ i1 i2
  | conseq f Kc' g put' hg _ ih => exact .conseq f Kc' g put' hg ih
  | equiv f Mk' e _ ih => exact .equiv f Mk' e ih

section
variable {E Kc : Type} [Field E] [Fintype E]

namespace LdProg

/-- Facts that are fresh after a program under the hypotheses of `Spec.ldProgC`: the set closed
after every move under join at
one reading, a coarser reading, another type for the same masks. -/
def AfterC : {a b : LdStage E Kc} → LdProg a b → (MaskFact a.J.W → Prop) → MaskFact b.J.W → Prop
  | _, _, .nil _, base => MaskFact.JCl base
  | _, _, .snoc p m, base => MaskFact.JCl (m.After (AfterC p base))

/-- What zero knowledge asks of a program, beside its hypotheses, a masked block taking its fact
from the closed set (a condition: `LdMv.Zk` of every move; a premise of `Spec.ldProgC`). -/
def ZkC : {a b : LdStage E Kc} → LdProg a b → (MaskFact a.J.W → Prop) → Prop
  | _, _, .nil _, _ => True
  | _, _, .snoc p m, base => ZkC p base ∧ m.Zk (AfterC p base)

theorem afterC_closed {a b : LdStage E Kc} (p : LdProg a b) (base : MaskFact a.J.W → Prop)
    (f : MaskFact b.J.W) (h : MaskFact.JCl (p.AfterC base) f) : p.AfterC base f := by
  cases p with
  | nil => rw [AfterC] at h ⊢; exact MaskFact.jcl_idem f h
  | snoc p m => rw [AfterC] at h ⊢; exact MaskFact.jcl_idem f h

end LdProg

/-- The program after a chain, under the hypotheses below: every link is of one of the two kinds,
and every fact of the closed set is fresh. -/
def Spec.ldProgC : Prop :=
  ∀ (A : Joint Kc) (a b : LdStage E Kc) (c₀ : Chain Kc A a.J)
      (p : LdProg a b) (base : MaskFact a.J.W → Prop),
    c₀.OkS → (∀ g, base g → c₀.FreshS g.kc g.Mk g.put) → p.Hyp → p.ZkC base →
    (p.onto c₀).OkS ∧ ∀ f, p.AfterC base f → (p.onto c₀).FreshS f.kc f.Mk f.put

theorem ldProgC : Spec.ldProgC (E := E) (Kc := Kc) := by
  intro A a b c₀ p base h0 hb
  induction p with
  | nil => 
      intro _ _
      rw [LdProg.onto_nil]
      exact ⟨h0, fun f hf => by rw [LdProg.AfterC] at hf; exact freshS_jcl Kc _ _ c₀ base hb f hf⟩
  | snoc p m ih =>
      intro hH hZ
      rw [LdProg.Hyp] at hH
      rw [LdProg.ZkC] at hZ
      obtain ⟨i1, i2⟩ := ih hH.1 hZ.1
      have e : ((LdProg.nil _).snoc m).onto (p.onto c₀) = (p.snoc m).onto c₀ := by
        rw [LdProg.onto_snoc, LdProg.onto_nil, LdProg.onto_snoc]
      have hq : ((LdProg.nil _).snoc m).Hyp := by rw [LdProg.Hyp, LdProg.Hyp]; exact ⟨trivial, hH.2⟩
      have hz : ((LdProg.nil _).snoc m).Zk (p.AfterC base) := by
        rw [LdProg.zk_snoc, LdProg.after_nil]; exact ⟨by rw [LdProg.Zk]; trivial, hZ.2⟩
      refine ⟨e ▸
          ldReqS_prog_ok E Kc A _ _ (p.onto c₀) ((LdProg.nil _).snoc m) (p.AfterC base) i1 i2 hq hz,
        fun f hf => ?_⟩
      rw [LdProg.AfterC] at hf
      rw [← e]
      refine freshS_jcl Kc _ _ _ (m.After (p.AfterC base)) (fun g hg => ?_) f hf
      exact ldReqS_prog_fresh E Kc A _ _ (p.onto c₀) ((LdProg.nil _).snoc m) (p.AfterC base)
        (allB_of_okS Kc _ _ _ i1) hq i2 g (by rw [LdProg.after_snoc, LdProg.after_nil]; exact hg)

end

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- A pending block: the masks of one later block (or of a part of one) that are out and unused: the
set of their entries, their type, the values laid at the entries; and what may be seen meanwhile:
entries Rd, names Rr whose encoding randomness may be seen. -/
structure LdPend (a : LdStage E Kc) : Type 1 where
  Rd  : a.S.Ent → Prop
  Rr  : a.S.O → Prop
  own : a.S.Ent → Prop
  Mk  : Type
  [fin : Fintype Mk]
  [ne  : Nonempty Mk]
  val : Mk → a.S.Ent → E

attribute [instance] LdPend.fin LdPend.ne

/-- its fact -/
def LdPend.fact {a : LdStage E Kc} (β : LdPend a) : MaskFact a.J.W :=
  a.wideFact β.Rd β.Rr β.own β.Mk β.val

/-- the move hands the pending block β on as β' -/
def LdMv.Hands {a b : LdStage E Kc} (m : LdMv a b) (β : LdPend a) (β' : LdPend b) : Prop :=
  ∀ Y : MaskFact a.J.W → Prop, Y β.fact → m.After Y β'.fact

section Send
variable (a : LdStage E Kc) (N : Sig E) (Sd : N.Seeds) (Wp' : Type) (L t : N.O → ℕ) (Y : N.StdL F)
  (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → Wp')
  (bk₀ : (∀ i, Y.Dt i → E) → Wp' → a.Wp) (w0 : a.S.Wit × a.Wp)

/-- new pending block, masks at free entries in whichever members: seen: all new entries that are no
pads, no new encoding randomness; of the old messages anything -/
def LdPend.newMany {I : Type} [Fintype (I → E)] [Nonempty (I → E)]
    (pl : I → Σ o, Y.Fr o) (RdOld : a.S.Ent → Prop) (RrOld : a.S.O → Prop) :
    LdPend (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).tgt :=
  ⟨a.S.sumP N RdOld Y.NoPad,
    a.S.sumO N RrOld fun _ => False,
    a.S.sumP N (fun _ => False) (Y.ownP pl),
    I → E,
    fun M => a.S.sumV N (fun _ => 0) (Y.valP pl M)⟩

/-- new pending block, masks at free entries of one member o: seen: all new entries but o's pads,
the encoding randomness of all new members but o; of the old messages anything -/
def LdPend.newOne (o : N.O) {I : Type} [Fintype (I → E)] [Nonempty (I → E)]
    (pl : I → Y.Fr o) (RdOld : a.S.Ent → Prop) (RrOld : a.S.O → Prop) :
    LdPend (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).tgt :=
  ⟨a.S.sumP N RdOld (Y.rdBut o),
    a.S.sumO N RrOld (Y.rrBut o),
    a.S.sumP N (fun _ => False) (Y.ownO o pl),
    I → E,
    fun M => a.S.sumV N (fun _ => 0) (Y.valO o pl M)⟩

/-- an old pending block behind a sending: of the new messages it may see anything -/
def LdPend.old (β : LdPend a) (RdN : N.Ent → Prop) (RrN : N.O → Prop) :
    LdPend (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).tgt :=
  ⟨a.S.sumP N β.Rd RdN, a.S.sumO N β.Rr RrN, a.S.sumP N β.own fun _ => False, β.Mk,
    fun M => a.S.sumV N (β.val M) fun _ => 0⟩

end Send

variable (F) in
/-- A composition of blocks of the three kinds, with the blocks whose masks are out and unused
behind it. -/
inductive LdMia : {a b : LdStage E Kc} → LdProg a b → (LdPend b → Prop) → Prop
  /-- nothing has happened; nothing is pending -/
  | nil (a : LdStage E Kc) : LdMia (.nil a) fun _ => False
  /-- fewer pending blocks may be tracked -/
  | sub {a b : LdStage E Kc} (p : LdProg a b) (Pd Pd' : LdPend b → Prop) :
      LdMia p Pd → (∀ β, Pd' β → Pd β) → LdMia p Pd'
  /-- (i) A sending, standard -/
  | send {a b : LdStage E Kc} (p : LdProg a b) (Pd : LdPend b → Prop) (N : Sig E)
      (Sd : N.Seeds) (Wp' : Type) (L t : N.O → ℕ) (Y : N.StdL F)
      (dat : b.S.Wit × b.Wp → ∀ i, Y.Dt i → E) (rst : b.Wp → Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → Wp' → b.Wp) (w0 : b.S.Wit × b.Wp) :
      LdMia p Pd → Y.OK t → (∀ w, bk₀ (dat w) (rst w.2) = w.2) →
      LdMia (p.snoc (.send b (LdSendD.std b N Sd Wp' L t Y dat rst bk₀ w0))) fun β' =>
        (∃ (I : Type) (_ : Fintype I) (_ : Fintype (I → E)) (_ : Nonempty (I → E))
              (pl : I → Σ o, Y.Fr o) (RdOld : b.S.Ent → Prop) (RrOld : b.S.O → Prop),
            Function.Injective pl ∧
            β' = LdPend.newMany b N Sd Wp' L t Y dat rst bk₀ w0 pl RdOld RrOld) ∨
        (∃ (o : N.O) (I : Type) (_ : Fintype (I → E)) (_ : Nonempty (I → E)) (pl : I → Y.Fr o)
              (RdOld : b.S.Ent → Prop) (RrOld : b.S.O → Prop),
            Function.Injective pl ∧
            β' = LdPend.newOne b N Sd Wp' L t Y dat rst bk₀ w0 o pl RdOld RrOld) ∨
        ∃ (β : LdPend b) (RdN : N.Ent → Prop) (RrN : N.O → Prop),
          Pd β ∧ DatBlind b dat β.Rd β.Rr β.own ∧
          β' = LdPend.old b N Sd Wp' L t Y dat rst bk₀ w0 β RdN RrN
  /-- (ii) A block with masked messages, whose fact follows from pending facts by join at one
  reading, coarser readings, another type for the same masks -/
  | masked {a b : LdStage E Kc} (p : LdProg a b) (Pd : LdPend b → Prop) (c : LdStage E Kc)
      (l : Link Kc b.J c.J) (D : MaskData l.R _) : LdMia p Pd → l.GoodM D →
      MaskFact.JCl (fun f => ∃ β, Pd β ∧ f = β.fact) D.fact →
      LdMia (p.snoc (.sub b c (.one l))) fun β' => ∃ β, Pd β ∧ (LdMv.sub b c (.one l)).Hands β β'
  /-- (iii) Any other move: one of which zero knowledge asks nothing beside its own bundle -/
  | other {a b : LdStage E Kc}
      (p : LdProg a b) (Pd : LdPend b → Prop) (c : LdStage E Kc) (m : LdMv b c) :
      LdMia p Pd → (∀ X, m.Zk X) →
      LdMia (p.snoc m) fun β' => ∃ β, Pd β ∧ m.Hands β β'

/-- For `LdMia F p Pd`: what zero knowledge asks of the program, beside its hypotheses, is met in
this sense: `p.ZkC (fun _ => False)` (a condition move by move; a premise of `Spec.ldProgC`), and
the pending blocks' facts are fresh behind it in this sense: they are in `p.AfterC (fun _ =>
False)` (that every fact of this set is fresh: `Spec.ldProgC`, under its hypotheses).
-/
def Spec.ldMia_zk : Prop :=
  ∀ (a b : LdStage E Kc) (p : LdProg a b) (Pd : LdPend b → Prop),
    LdMia F p Pd → p.ZkC (fun _ => False) ∧ ∀ β, Pd β → p.AfterC (fun _ => False) β.fact

theorem ldMia_zk : Spec.ldMia_zk (F := F) (E := E) (Kc := Kc) := by
  intro a b p Pd h
  induction h with
  | nil => exact ⟨by rw [LdProg.ZkC]; trivial, fun _ hβ => hβ.elim⟩
  | sub p Pd Pd' _ hs ih => exact ⟨ih.1, fun β hβ => ih.2 β (hs β hβ)⟩
  | send p Pd N Sd Wp' L t Y dat rst bk₀ w0 _ hY hbk ih =>
      refine ⟨by rw [LdProg.ZkC]; exact ⟨ih.1, trivial⟩, fun β' hβ' => ?_⟩
      rw [LdProg.AfterC]
      refine .base _ ?_
      rcases hβ' with ⟨I, _, _, _, pl, RdOld, RrOld, hpl, rfl⟩ | ⟨o, I, _, _, pl, RdOld, RrOld, hpl,
        rfl⟩ | ⟨β, RdN, RrN, hβ, hD, rfl⟩
      · exact stdSend_manyAfter F E Kc _ N Sd Wp' L t Y dat rst bk₀ w0 I pl RdOld RrOld _ hpl hY
      · exact stdL_visAfter _ N Sd Wp' L t Y dat rst bk₀ w0 o I pl RdOld RrOld _ hpl hY
      · obtain ⟨s1, s2⟩ :=
          stdSend_one F E Kc _ N Sd Wp' L t Y dat rst bk₀ w0 β.Rd β.Rr β.own hY hbk hD
        exact segWide_send_old _ (LdSendD.std _ N Sd Wp' L t Y dat rst bk₀ w0)
          _ β.Rd β.Rr β.own β.Mk β.val RdN RrN s1 s2 (ih.2 β hβ)
  | masked p Pd c l D _ hD hf ih =>
      have hz : (LdMv.sub _ c (.one l)).Zk (p.AfterC fun _ => False) := by
        show (Chain.one l).OkGiven _
        rw [Chain.OkGiven]
        exact Or.inr
          ⟨D, hD,
            LdProg.afterC_closed p _ _ (MaskFact.jcl_mono (fun f ⟨β, hβ, e⟩ => e ▸ ih.2 β hβ) _ hf)⟩
      refine ⟨by rw [LdProg.ZkC]; exact ⟨ih.1, hz⟩, fun β' ⟨β, hβ, hc⟩ => ?_⟩
      rw [LdProg.AfterC]
      exact .base _ (hc _ (ih.2 β hβ))
  | other p Pd c m _ hm ih =>
      refine ⟨by rw [LdProg.ZkC]; exact ⟨ih.1, hm _⟩, fun β' ⟨β, hβ, hc⟩ => ?_⟩
      rw [LdProg.AfterC]
      exact .base _ (hc _ (ih.2 β hβ))

/-- Masks sent in advance. States, for all stages a and b, every program p from a to b, every set Pd
of pending blocks at b and every witness w₀ at a: `LdMia F p Pd` → `p.Hyp` (of every move of p what
is asked of a move: `LdMv.Hyp`, Cb/Req1/LdSeg.lean) → the composition as one link (`Chain.link`, at
w₀, of the links of p after the step that does nothing, `a.idLink`) has the whole bundle `GoodT`,
and `Chain.FreshS` (Cb/Req1/LdSegFreshS.lean) for the fact of every block in Pd (what these say: the
row of `Spec.ldMia` in the head). -/
def Spec.ldMia : Prop :=
  ∀ (a b : LdStage E Kc) (p : LdProg a b) (Pd : LdPend b → Prop) (w₀ : a.W), LdMia F p Pd → p.Hyp →
    ((p.onto (.one a.idLink)).link w₀).GoodT ∧
    ∀ β, Pd β → (p.onto (.one a.idLink)).FreshS β.fact.kc β.fact.Mk β.fact.put

theorem ldMia : Spec.ldMia (F := F) (E := E) (Kc := Kc) := by
  intro a b p Pd w₀ h hH
  obtain ⟨z1, z2⟩ := ldMia_zk a b p Pd h
  obtain ⟨o1, o2⟩ := ldProgC _ a b (.one a.idLink) p (fun _ => False)
    (by rw [Chain.OkS]; exact LdStage.idLink_goodT a) (fun _ hg => hg.elim) hH z1
  exact ⟨chainS_ok Kc _ _ _ w₀ o1, fun β hβ => o2 _ (z2 β hβ)⟩

end
end Cb
