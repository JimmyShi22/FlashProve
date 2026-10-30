-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayDKit.lean: masks sent in advance, on data: pending blocks; what a step, a standard
sending and a closed body are asked so that a pending block passes them: conditions on places,
layouts, data maps and a step's honest map and, inside the front's places, some clauses on relations
(`LdRefF.OK`, Cb/Req1/LdSegRefCross.lean; `LdPreD.OK`, Cb/Req1/LdSegRefLkpPre.lean); not the whole
list: see the row of `OutD`.

In standard terms: book-keeping for the honest prover's side of a request's sub-protocol, a chain of
interactive oracle reductions: which entries of earlier oracle messages a later step uses, who reads
which entries in between, and how each message is laid out.

Definitions only, but for the theorem `LdLayQ.ok_sound`; the rules that tie them to the calculus of
fresh facts are in Cb/Ld/LdLayDKitProofs.lean; for `OutD`: Cb/Ld/LdLayDListProofs.lean,
Cb/Ld/LdLayDTailProofs.lean.

Why: zero knowledge of a reference request stands, in the records above (Cb/Req1/LdReqRefStd.lean:
`lay`, `layT`, `layB`), as a hypothesis block for block: "its masks are still uniform given all that
has been shown, and no step before the block reads them" (exactly: `Honest.Fresh`, `Honest.Blind`,
Ior/KnowCollRulesMask.lean). These clauses unfold to properties of honest provers. The rules that
derive them from data are in this library, each in a file of its own. This file gives the conditions
of these rules one form, in which they can be strung along the list of a request's segments
(Cb/Ld/LdLayDList.lean).

A pending block β (`LdPend`, Cb/Ld/LdMia.lean) is what is tracked: a set "own" of entries of open
oracle messages: masks of one later block, or of a part of one, that are out and unused; their type
Mk, the values val M laid at the own entries; and what may be seen meanwhile: entries Rd, names Rr
whose encoding randomness may be seen. `β.fact` is its wide fact (Cb/Req1/LdSegCarry.lean), of type
`MaskFact` (Cb/Req1/LdSegFresh.lean). A `MaskFact W` is a reading `kc` of witnesses of type W into a
type `Kc`, a finite, non-empty type `Mk`, and a map `put : Mk → Kc → Kc`. (W and `Kc` are that
record's own letters: not the `W : LdRefW A` of `OutD`, nor this file's variable `Kc`.)
A stage (`LdStage`, Cb/Req1/LdSegKit.lean) is the data of a relation over the oracle messages that
are open, each with a sample; a sending (`LdSendD`, same file) is the data of the reduction
(`LdSendD.link`) in which the prover sends a further family of oracle messages in one message, the
verifier draws their seeds, and the prover answers the samples. A segment: a piece of a request's
part of the protocol. A body: the first part of a segment, before its closing: a list of sendings,
sub-protocols and steps without rounds (`LdSeg`, Cb/Req1/LdSeg.lean).
A closing: the last part of a test, of the link or of a segment. The
data of a closed body are an `LdRefD` (Cb/Req1/LdSegRefAll.lean: closed: no list of moves is left
free); the parameters of its front's conditions are an `LdRefF`, a wide reading W over it is an
`LdRefW` (both Cb/Req1/LdSegRefCross.lean); its two late blocks are the digits' lookup and the
batching of the tensor rows.

Main names:
  `β.Over M w w'`: the witness w' is w with β's own entries overwritten by M, as far as β's reading
    shows: the entries in Rd agree off "own", at own entries in Rd w' has val M (at an own entry
    outside Rd it asks val M = 0); the encoding randomness at Rr agrees; the further witnesses are
    equal.
  `LdPend.StepD m β β'`: the own condition of a step without rounds with the honest map m:
    overwriting β's masks changes nothing in the new explicit part, and in the new witness it
    overwrites the masks of β', as far as β' shows. The two types of masks are tied by a bijection.
    For the entry and exit steps of a segment, which are free moves, this is a condition on the
    model's map; a write-up of ours (lean/CREDITS.md) has no such steps, so the clause has
    no counterpart there.
  `LdPend.JD X`: the closure of a set X of pending blocks, on data: pair (two blocks, from
    whichever sendings, as one block, at every reading within both that holds all own entries); a
    smaller reading that holds the own entries; another type for the same masks; the same set "own"
    and the same values at it, written otherwise. So each own entry of a later block may have a
    holder of its own: nothing wires a kind of block to a message.
  `LdLayQ E`, `Q.Sound`: what is asked of a layout is a parameter: Q N t F Y, for a family N,
    numbers t, a pads' field F and a layout Y of N. `Q.Sound`: it gives `Y.OK t`
    (Cb/Ld/LdSendStdL.lean: the words as sent are the code's encodings; data, free entries and pads
    lie at their places; every member's sample is private under its pad; the encoders hide t
    positions). Why a parameter: for families of given codes the two last clauses are theorems from
    conditions on the layout; whoever has such a form puts it in.
  `d.StdBl Q Rd Rr own`: the sending d is the standard one for some pads' field, layout Y and data
    map dat (one equation), Q of the layout, what is read back off the data with what is handed on
    is the further witness, and the data map does not look (`DatBlind`,
    Cb/Req1/LdReqStdFresh.lean). Slimmer than `d.IsStdB` (Cb/Req1/LdReqStdLay.lean): no clause on
    codes, lists or samples but what Q holds (without `IsStdB`'s `C.Laws`, `Sd.Fair`, `ListLE`,
    `Evades`).
  `d.pendMany Y pl RdOld RrOld`, `d.pendOne Y o pl RdOld RrOld`: the two forms of a block that a
    standard sending lays: masks at an injective family pl of free entries in whichever new members
    (seen: all new entries that are no pads, no new encoding randomness), or of one new member o
    (seen: all new entries but o's pads, the encoding randomness of all new members but o: the form
    that can cross a closing: see "Limits", Cb/Ld/LdLayD.lean); of the old messages anything may be
    seen.
  `d.LaysD Q β`: β is of one of these two forms, with pl injective, for a pads' field and a layout Y
    with the equation and Q.
  `A.OutD Q pp W own Mk val`: what a closed body is asked, beside `A.OK pp` (`LdRefD.OK`,
    Cb/Req1/LdSegRefAll.lean), `[CharP E pp]` and `[Nonempty I.C.E0.Str]` among others, so that the
    wide fact passes it:
    `front`: there are parameters of the front with: the core is the ghost (`LdRefD.Ghost`,
      Cb/Req1/LdSegRefAll.lean), the front's conditions (`LdRefF.OK`, Cb/Req1/LdSegRefCross.lean:
      places, and clauses on relations), overwriting changes no entry that the front reads
      (`LdRefF.Quiet`, Cb/Req1/LdSegRefCross.lean);
    `send1`, `send3`: the body's two sendings are standard and their data do not look;
    `maskL`, `ownT`: the places of the two late blocks;
    `apartL`, `apartT`: each late block reads only entries of the wide reading that are not own.

The pads' field and the layout are existentially quantified in each clause, with the equation
repeated: the field is chosen sending by sending. Each clause is used alone; that two clauses on
one sender name one layout is neither asked nor needed. A layout has one pads' field for the whole
family of a sending: a sending whose family mixes messages over the large field and over the base
field must be taken all over the large field; the write-up's first sending and each
closing's sending are such.

Limits: this file states nothing, but for `LdLayQ.ok_sound`. It says nothing on a splitting. A
body's own sendings lay no masks here: the pending blocks at a body's entry are all that its blocks
can use (so does the write-up's request: all masks of a segment's blocks lie in messages
sent before it; only its corollary on the range check, stated by itself, is wider). This file speaks
of one statement at a time: it has no form for sets of instances.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdMia
import Cb.Req1.LdReqStdLayVis
import Cb.Req1.LdReqRefLayStd
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- w' is w with β's own entries overwritten by M, as far as β's reading shows. -/
def LdPend.Over {a : LdStage E Kc} (β : LdPend a) (M : β.Mk) (w w' : a.W) : Prop :=
  β.fact.kc w' = β.fact.put M (β.fact.kc w)

/-- The own condition of a step without rounds, between two pending blocks. -/
def LdPend.StepD {a b : LdStage E Kc} (m : a.X × a.W → b.X × b.W) (β : LdPend a) (β' : LdPend b) :
    Prop :=
  ∃ e : β.Mk ≃ β'.Mk, ∀ (x : a.X) (w w' : a.W) (M : β.Mk),
    β.Over M w w' → (m (x, w')).1 = (m (x, w)).1 ∧ β'.Over (e M) (m (x, w)).2 (m (x, w')).2

open Classical in
/-- The closure of a set of pending blocks, on data. -/
inductive LdPend.JD {a : LdStage E Kc} (X : LdPend a → Prop) : LdPend a → Prop
  | base (β : LdPend a) : X β → LdPend.JD X β
  /-- two blocks as one, at every reading within both that holds all own entries -/
  | pair (β₁ β₂ : LdPend a) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop) :
      (∀ n, Rd n → β₁.Rd n ∧ β₂.Rd n) → (∀ o, Rr o → β₁.Rr o ∧ β₂.Rr o) →
      (∀ n, β₁.own n ∨ β₂.own n → Rd n) → LdPend.JD X β₁ → LdPend.JD X β₂ →
      LdPend.JD X
        ⟨Rd, Rr, fun n => β₁.own n ∨ β₂.own n, β₁.Mk × β₂.Mk,
          fun M n => if β₁.own n then β₁.val M.1 n else β₂.val M.2 n⟩
  /-- a smaller reading that holds the own entries -/
  | less (β : LdPend a) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop) :
      (∀ n, Rd n → β.Rd n) → (∀ o, Rr o → β.Rr o) → (∀ n, β.own n → Rd n) →
      LdPend.JD X β → LdPend.JD X ⟨Rd, Rr, β.own, β.Mk, β.val⟩
  /-- another type for the same masks -/
  | reMk (β : LdPend a) (Mk' : Type) [Fintype Mk'] [Nonempty Mk'] (e : β.Mk ≃ Mk') :
      LdPend.JD X β → LdPend.JD X ⟨β.Rd, β.Rr, β.own, Mk', fun M => β.val (e.symm M)⟩
  /-- the same own entries and the same values at them, written otherwise -/
  | same (β : LdPend a) (own : a.S.Ent → Prop) (val : β.Mk → a.S.Ent → E) :
      (∀ n, β.own n ↔ own n) → (∀ M n, β.own n → β.val M n = val M n) →
      LdPend.JD X β → LdPend.JD X ⟨β.Rd, β.Rr, own, β.Mk, val⟩

end

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- What is asked of a layout: a parameter. -/
abbrev LdLayQ (E : Type) [Field E] [Fintype E] : Type 1 :=
  ∀ (N : Sig E) (_ : N.O → ℕ) (F : Type) [Field F] [Fintype F] [Algebra F E], N.StdL F → Prop

/-- the layout's own conditions, as they stand -/
def LdLayQ.ok : LdLayQ E := fun _ t _ _ _ _ Y => Y.OK t

/-- it gives the layout's own conditions -/
def LdLayQ.Sound (Q : LdLayQ E) : Prop :=
  ∀ (N : Sig E) (t : N.O → ℕ) (F : Type) [Field F] [Fintype F] [Algebra F E] (Y : N.StdL F),
    Q N t F Y → Y.OK t

theorem LdLayQ.ok_sound : (LdLayQ.ok : LdLayQ E).Sound := fun _ _ _ _ _ _ _ h => h

/-- The sending is the standard one for some pads' field and layout, and its data map does not
look (whole: the head's row). -/
def LdSendD.StdBl {a : LdStage E Kc} (d : LdSendD a) (Q : LdLayQ E) (Rd : a.S.Ent → Prop)
    (Rr : a.S.O → Prop) (own : a.S.Ent → Prop) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : Algebra F E) (Y : d.N.StdL F)
      (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → d.Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp),
    d.StdAt F Y dat rst bk₀ w0 ∧ Q d.N d.t F Y ∧
    (∀ w, bk₀ (dat w) (rst w.2) = w.2) ∧ DatBlind a dat Rd Rr own

/-- a block that the sending lays: masks at free entries in whichever new members -/
def LdSendD.pendMany {F : Type} [Field F] [Fintype F] [Algebra F E] {a : LdStage E Kc}
    (d : LdSendD a) (Y : d.N.StdL F) {I : Type} [Fintype (I → E)] [Nonempty (I → E)]
    (pl : I → Σ o, Y.Fr o) (RdOld : a.S.Ent → Prop) (RrOld : a.S.O → Prop) : LdPend d.tgt :=
  ⟨a.S.sumP d.N RdOld Y.NoPad,
    a.S.sumO d.N RrOld fun _ => False,
    a.S.sumP d.N (fun _ => False) (Y.ownP pl),
    I → E,
    fun M => a.S.sumV d.N (fun _ => 0) (Y.valP pl M)⟩

/-- a block that the sending lays: masks at free entries of one new member o -/
def LdSendD.pendOne {F : Type} [Field F] [Fintype F] [Algebra F E] {a : LdStage E Kc}
    (d : LdSendD a) (Y : d.N.StdL F) (o : d.N.O) {I : Type} [Fintype (I → E)] [Nonempty (I → E)]
    (pl : I → Y.Fr o) (RdOld : a.S.Ent → Prop) (RrOld : a.S.O → Prop) : LdPend d.tgt :=
  ⟨a.S.sumP d.N RdOld (Y.rdBut o),
    a.S.sumO d.N RrOld (Y.rrBut o),
    a.S.sumP d.N (fun _ => False) (Y.ownO o pl),
    I → E,
    fun M => a.S.sumV d.N (fun _ => 0) (Y.valO o pl M)⟩

/-- The sending lays the block β. -/
def LdSendD.LaysD {a : LdStage E Kc} (d : LdSendD a) (Q : LdLayQ E) (β : LdPend d.tgt) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : Algebra F E) (Y : d.N.StdL F)
      (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → d.Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp),
    d.StdAt F Y dat rst bk₀ w0 ∧
    Q d.N d.t F Y ∧
    ((∃ (I : Type) (_ : Fintype I) (_ : Fintype (I → E)) (_ : Nonempty (I → E))
            (pl : I → Σ o, Y.Fr o) (RdOld : a.S.Ent → Prop) (RrOld : a.S.O → Prop),
          Function.Injective pl ∧ β = d.pendMany Y pl RdOld RrOld) ∨
      ∃ (o : d.N.O) (I : Type) (_ : Fintype (I → E)) (_ : Nonempty (I → E)) (pl : I → Y.Fr o)
          (RdOld : a.S.Ent → Prop) (RrOld : a.S.O → Prop),
        Function.Injective pl ∧ β = d.pendOne Y o pl RdOld RrOld)

/-- What a closed body is asked, beside `A.OK pp` among others, so that the wide fact passes it. -/
structure LdRefD.OutD {I : LdRefIx E} (A : LdRefD E Kc I) (Q : LdLayQ E) (pp : ℕ)
    (W : LdRefW A) (own : A.Xa.Q.D.S.Ent → Prop) (Mk : Type) [Fintype Mk]
    [Nonempty Mk] (val : Mk → A.Xa.Q.D.S.Ent → E) : Prop where
  /-- the front: the core is the ghost; its conditions (`LdRefF.OK`: places, and clauses on
  relations); overwriting changes no entry that it reads (`LdRefF.Quiet`) -/
  front  : ∃ (Fr : LdRefF A) (κ : A.Gh → Kc), A.Ghost κ ∧ Fr.OK pp ∧ Fr.Quiet (W.fact own Mk val)
  /-- the body's two sendings -/
  send1  : A.Xa.Q.D.d1.StdBl Q W.Rd W.Rr own
  send3  : A.Xa.Q.D.d3.StdBl Q (A.Xa.Q.D.S.sumP A.Xa.Q.D.N W.Rd W.RdN)
    (A.Xa.Q.D.S.sumO A.Xa.Q.D.N W.Rr W.RrN) (A.Xa.Q.D.S.sumP A.Xa.Q.D.N own fun _ => False)
  /-- the digits' lookup -/
  maskL  : A.Xa.A.MaskOK A.Xa.Dt
  apartL : ∀ n, A.Xa.A.srAll A.Xa.Dt n → W.Rd2 n ∧ ¬ A.own2 own n
  /-- the batching of the tensor rows -/
  ownT   : A.X.Own
  apartT : ∀ n, A.Rdt n → W.Rd2 n ∧ ¬ A.own2 own n

end
end Cb
