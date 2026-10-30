-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBatSig.lean: the random linear combination of claims (Cb/Ld/LdBat.lean) for statements whose
encoded messages are fixed by samples: many claims into one; and the one-round step that hands such
a statement to a proximity test.

Definitions and statements; the proofs are in Cb/Ld/LdBatSigProofs.lean.

In standard terms: `S.over A` is the relation "each word is the encoding of its pair (message,
randomness), each message has the answers of its sample, and A holds of the messages". Relaxed by
decoding with a sample, the first two clauses become: each message is what the fixed decoder
`OMsg.dec` returns on word and sample, namely the message of the nearest codeword (ties by
`OMsg.rank`) among those whose message has the answers, if it is within the radius. The third clause
becomes A's own relaxed form (`A.relR`). A statement is collision-free if at no oracle message two
different messages of the word's list have the same answers at the sample's seed (`Sig.CF`). The
condition of `S.over A` is this together with A's own (`A.on`); that is meant wherever this file
says "on collision-free statements". `Sig.over`, `OMsg.dec` and `Sig.CF` are in Cb/Ld/LdSig.lean.
`LdCode.rels` (the main relation and its existential relaxation) is in Cb/Ld/LdRel.lean.
A zero-evader: data: a set of seeds, a vector of coefficients for each seed, and a number (`Evader`,
Cb/Gen/BatEvader.lean). The property of a zero-evader (`Z.OK`, a hypothesis here): a vector other
than 0 is annihilated by at most err seeds; err is the evader's number.
`PieceTr`, a piece of a chain, asks of a reduction between two joints the bundle `IOR.GoodT` and
three further clauses, `noHid`, `noTie` and `bears`, which Cb/Ld/LdTowerKit.lean states (`bears`
through `IOR.Bears`, Ior/Bears.lean); `IOR.Piece` (Ior/Tail.lean) asks the same over `IOR.Good`.
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge. `Spec.ldBat_sig`, `Spec.ldBat_sig_lin`, `Spec.ldBat_ex_beside` and
`Spec.ldBat_bridge` conclude `PieceTr`.

Use 1: many claims into one (`ldBatSig`, `Spec.ldBat_sig`, `Spec.ldBat_sig_lin`). Claims named by B
on the messages of the statement's oracle messages, on whatever groups: values with a state (`Vf`),
or rows (linear forms on all entries, `S.Ent`). The prover sends nothing, the verifier sends the
seed of a zero-evader, the new claim is the combination. If `Z.OK`, the error is the evader's
number, without a list size: the messages are a function of words and samples, which are fixed
before the seed.
The count in the proof does not use the condition on statements; "collision-free" is only handed on.
The coefficients (1 - ρ, ρ) (`Evader.line` of Cb/Ld/LdBat.lean) give the reduction of two claims to
one.

Use 2: the bridge (`ldBridge`, `Spec.ldBat_bridge`).
  A group (`Grp S`): some whole oracle messages of the signature (mem), read at common long
    positions (P, pos), with one joint radius e. `G.C` is its code complex: the members' codes side
    by side.
  `G.Fits`: a hypothesis; `Spec.ldBat_fits` gives it under its two premises (a repetition; in
    fractions: joint distance at most the member's).
  The rows that a test takes in (`G.Row B`, `G.rows sl`, `G.claims x σ`): the rows of the claim and
    all sample rows of all members, the seed as state and the answer as target. By construction no
    test on a group can leave a member's sample out: this is what makes several tests on one oracle
    message speak of one message.
  Kept oracle messages (kp, `S.sub kp`): meant for those that something after the test still reads.
    Every oracle message is a member of the group or kept (hc); it may be both. The members that
    nothing reads later (not kept) are dropped here, not after the test: a carried relation that
    still listed them would still say that they decode, and the test would have closed nothing. A
    member that carried predicates still read is both a member and kept; where it leaves later is
    not the matter of this block.
  `Spec.ldBat_bridge`: under the hypotheses of its statement, `ldBridge` is a piece of a chain
    (`IOR.PieceTr`, Cb/Ld/LdTowerKit.lean), on collision-free statements. One round: the prover
    sends nothing, the verifier sends the seed of a zero-evader with one coefficient for each row.
    No query. Perfectly complete, nothing to simulate.
  The extractor (`ldBrBack`): the pair of a member is cut out of the test's witness, the pair of any
    other oracle message is the carried one. It reads nothing else (the further witness, `w.2.2`, is
    handed back as it is). Where an oracle message is both a member and kept, the two candidates
    hold the same message: both are in its list and have its answers, and the statement is
    collision-free.
  How it is made: a step without rounds and without error (`Spec.ldBat_step`: decoding with a sample
    → existential, all rows; here collision-freeness and `G.Fits` are used), then the batching
    inside the existential relaxation beside a carried joint (stated by itself as
    `Spec.ldBat_ex_beside`; the bridge's proof repeats that statement's proof; here the error takes
    the factor L).

Notation: `q`, `qi`, `qo`: predicates on finite sets of positions of the oracles (`PieceTr`'s last
two arguments: of the input, of the output).

Limits: this file does not say that any list is bounded: `C.ListAt e L` and `G.C.ListAt G.e L` are
hypotheses. L · err (the error `L * Z.err` of `Spec.ldBat_ex_beside` and of `Spec.ldBat_bridge`) at
or above the number of seeds says nothing. This file says nothing on which groups a protocol forms,
and does not say that every oracle message is closed by some test. That the combination of claims of
some kind is a claim of that kind is said for rows only. It says nothing on running times or
succinctness of the batched form.
Declared differences to a write-up of ours (lean/CREDITS.md). (by a reading) (a) A group
here is any family of whole oracle messages under any common reading: nothing on one base code, one
mask code, numbers of rows that are powers of two, rows that are not sent and count as zero.
Bringing `G.C` into the shape that a fold wants is a step of its own.
(b) The write-up lists the sample rows among the rows of the claim; here the verifier adds
them in the step without rounds (in the relaxed relation they follow from the decoding, in the exact
one they are a clause).
(c) The write-up states the bridge without a carried part and has the carried part in a rule
for conjunctions and in the notion of a run; here the carried part and the dropping are in the
statement. With kp = nobody and a trivial A₀ it is the write-up's.
(d) Radii and errors are counts. (e) Witnesses of relaxed relations have the type of the exact ones
(Cb/Ld/LdSig.lean (c)): the extractor hands back encoding randomness, which no relaxed relation by
decoding reads.
Two things here go back to advice: groups of whole oracle messages, and the rule on sample rows. The
batched form and the union over the list follow the paper that this protocol builds on. For the
bridge as a block the file follows this protocol's technical report, where it is made out of one
proof step of the same paper (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdBat
import Cb.Ld.LdSig
import Ior.KnowCollRulesFrame
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood

/-! ## 0. Joints -/

/-- A base joint with a claim on the messages beside it. The claim has its own part of the explicit
part; it reads the messages alone. -/
def claimRels {K X St₀ M Wp : Type} {E₀ : ExtSpec}
    (Φ : X → M → Prop) (A₀ : IOR.Rels K St₀ E₀ (M × Wp)) :
    IOR.Rels K (X × St₀) E₀ (M × Wp) where
  rel  := fun x y w => Φ x.1 w.1 ∧ A₀.rel x.2 y w
  relR := fun a w => Φ a.1.1 w.1 ∧ A₀.relR (a.1.2, a.2) w
  on   := fun a => A₀.on (a.1.2, a.2)
  core := A₀.core

/-- A base joint on some of the messages, read on all of them. -/
def onMsgRels {K St₀ M M' Wp : Type} {E₀ : ExtSpec}
    (r : M → M') (A₀ : IOR.Rels K St₀ E₀ (M' × Wp)) : IOR.Rels K St₀ E₀ (M × Wp) where
  rel  := fun x y w => A₀.rel x y (r w.1, w.2)
  relR := fun a w => A₀.relR a (r w.1, w.2)
  on   := A₀.on
  core := fun w => A₀.core (r w.1, w.2)

/-- A form on the entries of one member of a family, as a form on all entries of the family: zeros
elsewhere. -/
def Slf.atMem {E St A : Type} [Zero E] [DecidableEq A] {Jf : A → Type}
    (a : A) (sl : Slf E St (Jf a)) : Slf E St (Σ a, Jf a) :=
  fun st n => if h : n.1 = a then sl st (h ▸ n.2) else 0

/-! ## 1. Many claims into one, on statements with samples -/

namespace Sig
variable {E : Type} (S : Sig E)

/-- all entries of all messages, and a tuple of messages as one vector -/
abbrev Ent : Type := Σ a, (S.om a).C.J
def ents (m : S.Msg) : S.Ent → E := fun n => m n.1 n.2

/-- Some of the oracle messages: the signature on the names with kp. -/
@[reducible] def sub (kp : S.O → Prop) [DecidablePred kp] : Sig E :=
  { O := {o // kp o}, om := fun a => S.om a.1 }

/-- a family over the oracle messages, cut down to those with kp -/
def res {T : OMsg E → Type} (kp : S.O → Prop) [DecidablePred kp] (t : ∀ a, T (S.om a)) :
    ∀ a, T ((S.sub kp).om a) := fun a => t a.1

/-- the words with kp: a copy -/
def subExt (kp : S.O → Prop) [DecidablePred kp] : ExtMap S.ext (S.sub kp).ext :=
  ⟨fun y a => y a.1, fun q => {⟨q.1.1, q.2⟩}⟩

end Sig

section
variable {E B : Type} [Field E] [Fintype B] (S : Sig E) (Sb : B → Type) (Z : Evader E B)
  (St₀ Wp : Type) (E₀ : ExtSpec)

/-- the new explicit part: the claims become one; the rest and the samples stay -/
def ldBatSigNx :
    (((B → E) × (∀ b, Sb b)) × St₀) × S.Smp → Z.D → ((E × ((∀ b, Sb b) × Z.D)) × St₀) × S.Smp :=
  fun x ρ => ((batNx Z.ze x.1.1 ρ, x.1.2), x.2)

/-- The batching on statements with samples: the verifier draws the seed. -/
abbrev ldBatSig :
    IOR ((((B → E) × (∀ b, Sb b)) × St₀) × S.Smp) (E₀.prod S.ext)
      (((E × ((∀ b, Sb b) × Z.D)) × St₀) × S.Smp) (E₀.prod S.ext) :=
  IOR.draw Z.D (ldBatSigNx S Sb Z St₀) (E₀.prod S.ext)

abbrev ldBatSigH : (ldBatSig S Sb Z St₀ E₀).Honest (S.Wit × Wp) (S.Wit × Wp) :=
  IOR.Honest.draw Z.D (ldBatSigNx S Sb Z St₀) (E₀.prod S.ext) (S.Wit × Wp)

abbrev ldBatSigN (Kc : Type) : IOR.Nums Kc (ldBatSig S Sb Z St₀ E₀) :=
  IOR.Nums.draw Kc Z.D (ldBatSigNx S Sb Z St₀) (E₀.prod S.ext) Z.err

end

/-! ## 2. Groups -/

/-- A group: the data. Some whole oracle messages of a signature, read at common long positions,
with one joint radius. -/
structure Grp {E : Type} (S : Sig E) where
  /-- the common long positions -/
  P : Type
  [finP : Fintype P]
  /-- the members -/
  mem : S.O → Prop
  [decMem : DecidablePred mem]
  /-- where a member is read for a common long position -/
  pos : ∀ a : {o // mem o}, P → (S.om a.1).P
  /-- the joint radius: a count of common long positions -/
  e : ℕ

attribute [instance] Grp.finP Grp.decMem

namespace Grp
variable {E : Type} {S : Sig E} (G : Grp S)

abbrev A : Type := {o // G.mem o}

/-- The code complex of the group: the members' codes side by side, read at the common long
positions. -/
@[reducible] def C : LdCode E G.P := LdCode.fam fun a : G.A => (S.om a.1).C.atPos (G.pos a)

/-- the members' words as one native word of the complex; the members' messages as one message; the
members' pairs as one pair -/
def word (y : S.ext.Str) : G.C.Word := fun p => (S.om p.1.1).upW (y p.1.1) p.2
def msg (m : S.Msg) : G.C.J → E := fun n => m n.1.1 n.2
def wit (w : S.Wit) : (G.C.J → E) × (G.C.Q → E) :=
  (fun n => (w n.1.1).1 n.2, fun n => (w n.1.1).2 n.2)

open Classical in
/-- From the words of the statement to the implicit instance of a test on the group: a common long
position is read in each member where pos says. -/
def toExt : ExtMap S.ext G.C.ext :=
  ⟨G.word, fun x => Finset.univ.image fun a : G.A => (⟨a.1, G.pos a x⟩ : Σ a, (S.om a).P)⟩

/-- The joint radius implies each member's own: two native words of a member that differ at no more
than G.e common long positions differ at no more than the member's radius of its own long positions.
-/
def Fits [Field E] : Prop :=
  ∀ (a : G.A) (f g : (S.om a.1).C.Word),
    ((S.om a.1).C.atPos (G.pos a)).Near G.e f g → (S.om a.1).C.Near (S.om a.1).e f g

/-- The names of the rows that a test on the group takes in: the rows of the claim, and all sample
rows of all members. -/
abbrev Row (B : Type) : Type := B ⊕ Σ a : G.A, (S.om a.1).Z.S

/-- the states of the rows: a sample row has the seed as its state -/
def RowSt {B : Type} (Sb : B → Type) : G.Row B → Type
  | .inl b => Sb b
  | .inr as => (S.om as.1.1).Z.D

/-- The rows, as forms on the message of the complex. -/
def rows [Zero E] {B : Type} {Sb : B → Type} (sl : ∀ b, Slf E (Sb b) G.C.J) :
    ∀ ν, Slf E (G.RowSt Sb ν) G.C.J
  | .inl b => sl b
  | .inr as => Slf.atMem (Jf := fun a : G.A => (S.om a.1).C.J) as.1 ((S.om as.1.1).row as.2)

/-- The claims: targets and states of all rows; a sample row has the answer as its target. -/
def claims {B : Type} {Sb : B → Type} (x : (B → E) × (∀ b, Sb b)) (σ : S.Smp) :
    (G.Row B → E) × (∀ ν, G.RowSt Sb ν) :=
  (Sum.elim x.1 fun as => (σ as.1.1).2 as.2, fun ν => match ν with
    | .inl b => x.2 b
    | .inr as => (σ as.1.1).1)

end Grp

/-! ## 3. The bridge -/

section
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} (G : Grp S) (kp : S.O → Prop)
  [DecidablePred kp] (Sb : B → Type) (Z : Evader E (G.Row B)) (St₀ Wp : Type) (E₀ : ExtSpec)

/-- the explicit part, the oracles and the witnesses between the step without rounds and the seed,
and after the seed: on the left what the test on the group gets, on the right what is carried -/
abbrev LdBrXm : Type := ((G.Row B → E) × (∀ ν, G.RowSt Sb ν)) × (St₀ × (S.sub kp).Smp)
abbrev LdBrXo : Type := (E × ((∀ ν, G.RowSt Sb ν) × Z.D)) × (St₀ × (S.sub kp).Smp)
abbrev LdBrE : ExtSpec := G.C.ext.prod (E₀.prod (S.sub kp).ext)
abbrev LdBrW : Type := G.C.N.Wit × ((S.sub kp).Wit × Wp)

/-- The step without rounds, explicit part: the sample rows of all members join the rows of the
claim; the samples of the kept oracle messages are carried. -/
def ldBrF (x : (((B → E) × (∀ b, Sb b)) × St₀) × S.Smp) : LdBrXm G kp Sb St₀ :=
  (G.claims x.1.1 x.2, (x.1.2, S.res (T := OMsg.Smp) kp x.2))

/-- The step without rounds, oracles: the members' words as the implicit instance of the test; the
further oracles and the kept words are carried. -/
def ldBrG : ExtMap (E₀.prod S.ext) (LdBrE G kp E₀) :=
  (G.toExt.comp (ExtMap.snd E₀ S.ext)).pair
    ((ExtMap.fst E₀ S.ext).pair ((S.subExt kp).comp (ExtMap.snd E₀ S.ext)))

/-- what the honest prover does at that step -/
def ldBrM (a : ((((B → E) × (∀ b, Sb b)) × St₀) × S.Smp) × (S.Wit × Wp)) :
    LdBrXm G kp Sb St₀ × LdBrW G kp Wp :=
  (ldBrF G kp Sb St₀ a.1, (G.wit a.2.1, (S.res (T := OMsg.Wit) kp a.2.1, a.2.2)))

/-- The extractor: the pair of a member of the group is cut out of the test's witness; the pair of
any other oracle message is the carried one. It reads no oracle, no transcript. -/
def ldBrBack (hc : ∀ o, G.mem o ∨ kp o) (w : LdBrW G kp Wp) : S.Wit × Wp :=
  (fun o =>
      if h : G.mem o then (fun j => w.1.1 ⟨⟨o, h⟩, j⟩, fun q => w.1.2 ⟨⟨o, h⟩, q⟩)
      else w.2.1 ⟨o, (hc o).resolve_left h⟩,
    w.2.2)

/-- the seed: the rows on the left become one -/
def ldBrNx : LdBrXm G kp Sb St₀ → Z.D → LdBrXo G kp Sb Z St₀ := fun x ρ => (batNx Z.ze x.1 ρ, x.2)

/-- The bridge: the step without rounds, then the verifier draws the seed. -/
abbrev ldBridge :
    IOR ((((B → E) × (∀ b, Sb b)) × St₀) × S.Smp) (E₀.prod S.ext)
      (LdBrXo G kp Sb Z St₀) (LdBrE G kp E₀) :=
  (IOR.draw Z.D (ldBrNx G kp Sb Z St₀) (LdBrE G kp E₀)).pre
    (fun x => some (ldBrF G kp Sb St₀ x)) (ldBrG G kp E₀)

abbrev ldBridgeH : (ldBridge G kp Sb Z St₀ E₀).Honest (S.Wit × Wp) (LdBrW G kp Wp) :=
  (IOR.Honest.draw Z.D (ldBrNx G kp Sb Z St₀) (LdBrE G kp E₀) (LdBrW G kp Wp)).pre
    (fun x => some (ldBrF G kp Sb St₀ x)) (ldBrG G kp E₀) (ldBrM G kp Sb St₀ Wp)

abbrev ldBridgeN (Kc : Type) (err : ℕ) : IOR.Nums Kc (ldBridge G kp Sb Z St₀ E₀) :=
  (IOR.Nums.draw Kc Z.D (ldBrNx G kp Sb Z St₀) (LdBrE G kp E₀) err).pre
    (fun x => some (ldBrF G kp Sb St₀ x)) (ldBrG G kp E₀)

end

/-! ## The statements -/

namespace Spec
open IOR

/-- Many claims into one, on statements with samples. States: if `Z.OK`, `ldBatSig` is a piece of a
chain (`IOR.PieceTr`) from all claims to the combined claim, each beside any base joint A₀ (what
else the statement says) and relaxed by decoding with a sample, on collision-free statements that
meet `A₀.on`; the identity extracts; the error is the evader's number: no list size. -/
def ldBat_sig : Prop :=
  ∀ (E B Kc St₀ Wp : Type) [Field E] [Fintype B] (S : Sig E) (Sb : B → Type)
      (v : ∀ b, Vf E (Sb b) S.Msg) (Z : Evader E B) (E₀ : ExtSpec)
      (A₀ : Rels Kc St₀ E₀ (S.Msg × Wp)) (q : Finset (E₀.prod S.ext).Pos → Prop),
    Z.OK → PieceTr (ldBatSig S Sb Z St₀ E₀) (ldBatSigH S Sb Z St₀ Wp E₀)
      (S.over (claimRels (Vf.All v) A₀)) (S.over (claimRels (Vf.bat Z.ze v).Holds A₀))
      (fun _ _ w => w) (ldBatSigN S Sb Z St₀ E₀ Kc) q q

/-- The same for rows: linear forms on all entries of all messages (on whatever groups); the one new
claim is the row of the combined form. -/
def ldBat_sig_lin : Prop :=
  ∀ (E B Kc St₀ Wp : Type) [Field E] [Fintype B] (S : Sig E) (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) S.Ent) (Z : Evader E B) (E₀ : ExtSpec)
      (A₀ : Rels Kc St₀ E₀ (S.Msg × Wp)) (q : Finset (E₀.prod S.ext).Pos → Prop),
    Z.OK → PieceTr (ldBatSig S Sb Z St₀ E₀) (ldBatSigH S Sb Z St₀ Wp E₀)
      (S.over (claimRels (fun x m => Slf.All sl x (S.ents m)) A₀))
      (S.over (claimRels (fun x m => (Slf.bat Z.ze sl).Holds x (S.ents m)) A₀)) (fun _ _ w => w)
      (ldBatSigN S Sb Z St₀ E₀ Kc) q q

/-- The batching inside the existential relaxation, beside any carried joint. States, if `Z.OK` and
`C.ListAt e L`: a piece of a chain (`IOR.PieceTr`): several rows into one, at the same radius,
beside the carried joint Bc; the identity extracts; the error is L, a bound for the list of C at e,
times the evader's number (`L * Z.err`). -/
def ldBat_ex_beside : Prop :=
  ∀ (E P B Kc Xc Wc : Type) [Field E] [Fintype E] [Fintype P] [Fintype B] (C : LdCode E P)
      (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) C.J) (Z : Evader E B) (e L : ℕ) (Ec : ExtSpec)
      (Bc : Rels Kc Xc Ec Wc) (q : Finset (C.ext.prod Ec).Pos → Prop),
    Z.OK → C.ListAt e L →
    PieceTr (IOR.draw Z.D
        (fun (x : ((B → E) × (∀ b, Sb b)) × Xc) ρ => (batNx Z.ze x.1 ρ, x.2)) (C.ext.prod Ec))
      (Honest.draw Z.D _ (C.ext.prod Ec) (C.N.Wit × Wc))
      (IOR.Rels.beside (C.relsAll sl e fun _ => ()) Bc)
      (IOR.Rels.beside (C.rels (Slf.bat Z.ze sl) e fun _ => ()) Bc) (fun _ _ w => w)
      (Nums.draw Kc Z.D _ (C.ext.prod Ec) (L * Z.err)) q q

/-- The value of a form that lives on one member. -/
def ldBat_atMem : Prop :=
  ∀ (E St A : Type) [Field E] [Fintype A] [DecidableEq A] (Jf : A → Type) [∀ a, Fintype (Jf a)]
      (a : A) (sl : Slf E St (Jf a)) (st : St) (m : (Σ a, Jf a) → E),
    ∑ n, Slf.atMem a sl st n * m n = ∑ j, sl st j * m ⟨a, j⟩

/-- What the rows of a group say: the rows of the claim hold, and every member's message has the
answers of its sample. -/
def ldBat_rows_iff : Prop :=
  ∀ (E B : Type) [Field E] (S : Sig E) (G : Grp S) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (x : (B → E) × (∀ b, Sb b)) (σ : S.Smp) (u : G.C.J → E),
    Slf.All (G.rows sl) (G.claims x σ) u ↔
    Slf.All sl x u ∧ ∀ a : G.A, (S.om a.1).Z.val (σ a.1).1 (fun j => u ⟨a, j⟩) = (σ a.1).2

/-- Where "the joint radius implies each member's own" comes from: every long position of the member
is read for at least μ common long positions, and G.e < μ (e + 1). -/
def ldBat_fits : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (G : Grp S) (μ : G.A → ℕ),
    (∀ (a : G.A) (p : (S.om a.1).P), μ a ≤ cnt fun x : G.P => G.pos a x = p) →
    (∀ a : G.A, G.e < μ a * ((S.om a.1).e + 1)) → G.Fits

/-- The step without rounds, without error. States: if `G.Fits` and every oracle message is a member
of the group or kept (`hc`), then `ldBrF`, `ldBrG`, `ldBrM` and `ldBrBack` are a step (`IOR.Step`)
from the relaxation by decoding with a sample to the existential relaxation with all rows, beside
the carried part. On collision-free statements that meet `A₀.on`. -/
def ldBat_step : Prop :=
  ∀ (E B Kc St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (E₀ : ExtSpec) (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (hc : ∀ o, G.mem o ∨ kp o),
    G.Fits →
    Step (fun x => some (ldBrF G kp Sb St₀ x)) (ldBrG G kp E₀)
      (ldBrM G kp Sb St₀ Wp) (fun _ w => ldBrBack G kp Wp hc w)
      (S.over
        (claimRels (fun x m => Slf.All sl x (G.msg m)) (onMsgRels (S.res (T := OMsg.Msg) kp) A₀)))
      (IOR.Rels.beside (G.C.relsAll (G.rows sl) G.e fun _ => ()) ((S.sub kp).over A₀))

open Classical in
/-- The bridge. States: if every oracle message is a member or kept (`hc`), `Z.OK`,
`G.C.ListAt G.e L`, `G.Fits`, and for every set U within qo the positions that `ldBrG` reads for U
are within qi, then `ldBridge` is a piece of a chain (`IOR.PieceTr`, Cb/Ld/LdTowerKit.lean) from
`S.over` ("the rows sl hold of the group's message" beside A₀ of the kept messages): relaxed by
decoding with a sample, on collision-free statements that meet `A₀.on`, to [ `G.C.rels` (the one
batched form) `G.e`: the main relation of the complex, relaxed existentially at the joint radius ]
beside [ `(S.sub kp).over A₀`: relaxed by decoding with a sample ] (`IOR.Rels.beside` of
Ior/KnowCollRulesFrame.lean). One round; the error is L, a bound for the list of the complex, times
the evader's number. -/
def ldBat_bridge : Prop :=
  ∀ (E B Kc St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (L : ℕ) (E₀ : ExtSpec) (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
      (hc : ∀ o, G.mem o ∨ kp o) (qi : Finset (E₀.prod S.ext).Pos → Prop)
      (qo : Finset (LdBrE G kp E₀).Pos → Prop),
    Z.OK → G.C.ListAt G.e L → G.Fits → (∀ U, qo U → qi (U.biUnion (ldBrG G kp E₀).src)) →
    PieceTr (ldBridge G kp Sb Z St₀ E₀) (ldBridgeH G kp Sb Z St₀ Wp E₀)
      (S.over
        (claimRels (fun x m => Slf.All sl x (G.msg m)) (onMsgRels (S.res (T := OMsg.Msg) kp) A₀)))
      (IOR.Rels.beside (G.C.rels (Slf.bat Z.ze (G.rows sl)) G.e fun _ => ()) ((S.sub kp).over A₀))
      (fun _ _ w => ldBrBack G kp Wp hc w) (ldBridgeN G kp Sb Z St₀ E₀ Kc (L * Z.err)) qi qo

end Spec
end Cb
