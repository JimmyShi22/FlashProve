-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSig.lean: which message a sent word stands for at a radius beyond unique decoding: list
decoding with a sample.

A sample is a seed drawn by the verifier and the prover's answers, a few linear functionals of the
message; the decoder returns a message of the list that has these answers, or none.
Definitions, and the statements of their first laws (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdSigProofs.lean, that of `Spec.sig_two` in Cb/Ld/LdSigTest.lean.

Why: beyond half the distance a word is close to several codewords. Cb/Ld/LdRel.lean relaxes a
relation existentially (`ConL`: the witness names a codeword within the radius): that is the form
inside a proximity test. Outside the tests a protocol refers to "the message of this oracle" in many
places (several tests read one oracle; predicates on messages are reduced to one another over many
rounds), and "some codeword" in each place need not be the same one.
So right after a word is sent the verifier draws a seed and the prover answers with a few linear
functionals of the message (a sample, Cb/Gen/OodDec.lean). From then on the statement carries seed
and answers, and "the message of the oracle" is a total function of the statement: nearest-codeword
decoding, first in a fixed order, with one condition under the minimum: the message has the answers
(`decMin`, Cb/Gen/OodDecMin.lean).

Main names, by the file's sections (the docstrings tell more):
 0. `LdCode.atPos`: a code of Cb/Ld/LdRel.lean read at other long positions, so that one word can be
    read at the common long positions of several groups (Cb/Ld/LdBatSig.lean).
 1. `OMsg E`, an oracle message. Data only.
      `C`: main rows and mask rows, if any, are one record (a pair or a family); `C.J` names all
        entries of its message: entries proper, masks, pad, unused places.
      `Sy`, `up`, `sy0`, the format: what may be sent, by type. Words with symbols in a subfield are
        the case for which it is there.
      `o.dec f σ`, the decoder.
      `o.Clash f ρ`, a collision at the seed ρ. No answer of the prover occurs in it.
      `o.ListLE L`, `o.Evades`: the two hypotheses of the lemma on collisions.
 2. `Sig E`, a signature.
 3. The constraint relations, over any base joint `A : IOR.Rels Kc St E₀ (S.Msg × Wp)`
    (Ior/Chain.lean): what is claimed of the messages. St: the rest of the explicit part. E₀:
    further oracles of the statement that are no oracle messages (never sampled: an input of a test
    that is only copied, a fresh mask of a test); A may read them. Wp: a further witness (Unit if
    there is none). A treats the messages as a witness and cannot read encoding randomness, by type.
    A statement is x = (st, samples), y = (further oracles, the words). A witness is ((message,
    randomness) for each oracle message, further witness).
      `S.CF`: samples and words are collision-free. A condition on statements; it is not a part of
        any relation defined here.
      `S.over A`, the joint of a chain: rel (exact) = Enc ∧ Ans ∧ A.rel; relR (relaxed by decoding
        with a sample) = for every oracle message the decoder returns the witness's message, ∧
        A.relR; on = CF ∧ A.on. The encoding randomness of the witness is not read by relR (two
        members of a list may hold one message).
      `o.sent A back`, one more oracle message, for any joint `A : IOR.Rels Kc X E₀ W` (no signature
        in it): statement ((x, sample), (y, word)), witness ((message, randomness), w'); A is
        claimed of back message w': a part of A's witness now stands in the message. rel = the word
        is the encoding ∧ the answers ∧ A.rel; relR = the decoder returns the message ∧ A.relR; on =
        A.on ∧ no collision. This is the output joint of the sending (Cb/Ld/LdSend.lean).
 Statements (`Cb.Spec`):
      `sig_dec_good`, `sig_cnt_clash` (the lemma on collisions), `sig_over_cf`: the main ones; see
        their docstrings.
      `sig_list_of_code`, `sig_evades_of_ok`, `sig_evades_of_okOn`: where the two hypotheses come
        from.
      `sig_sent_sub`: under `o.C.Laws` and `o.C.Dist 1`, the exact relation of `o.sent A back` is
        contained in the relaxed one, if that holds of A.

Why `Evades` and not `Sample.OK`: for a message over a subfield the pad stands under a row that is a
zero-evader only on vectors whose pad part lies in the subfield: `Sample.OK`, which speaks of all
vectors over E, is false for it (an argument in words, no theorem; it hangs on the parameters of the
row). What holds, and what the lemma needs, is the property on differences of members of one list
(`Spec.sig_evades_of_okOn`).
How the condition travels (Ior/KnowColl.lean, Ior/KnowCollGood.lean): a block between a sending and
a test is proved "on collision-free statements" (its joints are S.over ..); a block that copies
words and samples carries the condition (`Spec.sig_copies`); the sending is proved into
collision-free statements, and pays for it; chains are made at the joints (S.over ..).cf.
The types are those of `keep` in Ior/Frame.lean: a reduction R between base joints that keeps the
messages becomes R.keep S.Smp S.ext between the joints over them.

Limits:
Declared differences to a write-up of ours (lean/CREDITS.md) and to the texts behind it.
 (a) One field E for witnesses, as in Cb/Ld/LdRel.lean; a subfield enters through the format alone:
     the minimum runs over all pairs over E. Below the distance a member of the list of a word over
     the subfield is itself over the subfield, so within the radius the two minima have the same
     members. This is not proved here (its first clause is proved under hypotheses:
     `Spec.ld_subfield_member`, Cb/Req1/LdReqJohnSub.lean).
 (b) Radii are counts of long positions.
 (c) The witness of the relaxed relation has the type of the exact one, and its randomness is not
     read, where the write-up drops it.
 (d) The order is given by a function into ℕ; no statement here needs it injective. Where it is not,
     it is no total order: among the nearest pairs whose message has the answers, of least `rank`
     among these, `decMin` returns one by choice; it is so at the standard oracle messages
     (`StdM.om`, Cb/Obj/LdObjectToyKit.lean), whose `rank` is the constant 0.
 (e) The distance of an oracle message is taken under its own reading (o.P); what a common reading
     of several oracle messages gives for each is the matter of the batching.
 (f) An encoded index is not an oracle message: it is never closed, has one answer for each row, its
     sample is taken outside the protocols, and no extractor hands its message back. Its place here
     is in the base joint: the index is a further oracle (E₀), its record stands in St, A.relR reads
     the decoding and is false where there is none, A.on holds "no collision" for it (or "it
     decodes": Cb/Ld/LdLin.lean).
This file says nothing on a protocol. No bound on a list is proved, but for unique decoding
(`Spec.sig_dec_unique`, under its hypotheses: at most one message). (L choose 2) · Z.err at or above
the number of seeds says nothing. At a collision nothing is claimed about which candidate the
decoder returns. This file says nothing on hiding (Cb/Ld/LdSend.lean), on groups, on running times:
the decoder is a choice.

The decoder (nearest codeword, first in a fixed order) follows the worked example named in
lean/CREDITS.md.  The unit "oracle message" goes back to advice and follows the paper that this
protocol builds on.  For the condition under the minimum, and for "collision-free" as a condition on
statements, the file follows this protocol's technical report, which for the second follows that
worked example and that paper.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdRelJohnson
import Cb.Gen.OodDecMin
import Cb.Gen.OodDecPad
import Ior.KnowCollGood
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood

/-! ## 0. A code read at other long positions -/

/-- The same code, read at other long positions: the long position x is read where pos x was. -/
@[reducible] def LdCode.atPos {E P P' : Type} (C : LdCode E P) (pos : P' → P) : LdCode E P' where
  NP := C.NP
  NS := C.NS
  J := C.J
  Q := C.Q
  enc := C.enc
  Aa := C.Aa
  T := fun f x => C.T f (pos x)
  src := fun x => C.src (pos x)

/-! ## 1. An oracle message -/

/-- An oracle message: the data. The unit that is sent in one prover message, sampled once, tested
and closed only as a whole. -/
structure OMsg (E : Type) where
  /-- its long positions -/
  P : Type
  [finP : Fintype P]
  /-- its code, read under a transformation; C.J names all entries of the message -/
  C : LdCode E P
  /-- the sample map, on all entries of the message -/
  Z : Sample E C.J
  /-- the radius: a count of long positions -/
  e : ℕ
  /-- the fixed total order of the pairs (message, randomness) (given by `rank`; it is a total order
  if `rank` is injective, which no statement here asks) -/
  rank : (C.J → E) × (C.Q → E) → ℕ
  /-- the format: the symbols as sent, how they are read as native symbols of C, a fixed symbol -/
  Sy : C.NP → Type
  up : ∀ p, Sy p → C.NS p → E
  sy0 : ∀ p, Sy p

attribute [instance] OMsg.finP

namespace OMsg
variable {E : Type}

/-- The plain format: what is sent is a native word of the code. -/
@[reducible] def plain [Zero E] {P : Type} [Fintype P] (C : LdCode E P) (Z : Sample E C.J)
    (e : ℕ) (rank : (C.J → E) × (C.Q → E) → ℕ) : OMsg E :=
  { P := P, C := C, Z := Z, e := e, rank := rank, Sy := fun p => C.NS p → E,
    up := fun _ s => s, sy0 := fun _ _ => 0 }

variable (o : OMsg E)

/-- the words as sent -/
abbrev Str : Type := ∀ p, o.Sy p
/-- a word as sent, read as a native word of the code -/
def upW (f : o.Str) : o.C.Word := fun p => o.up p (f p)
/-- The kind of the implicit instance: the string is the word as sent; positions and symbols are the
long ones. -/
abbrev ext : ExtSpec := ⟨o.Str, o.P, o.C.Aa → E, fun f => o.C.T (o.upW f)⟩
/-- messages, encoding randomness, witnesses: those of the code -/
abbrev Msg : Type := o.C.J → E
abbrev Rnd : Type := o.C.Q → E
abbrev Wit : Type := o.Msg × o.Rnd
/-- A sample: seed and answers. -/
abbrev Smp : Type := o.Z.D × (o.Z.S → E)

/-- At how many long positions the word differs from the encoding of w. -/
def dist (f : o.Str) (w : o.Wit) : ℕ :=
  cnt fun x : o.P => o.C.T (o.upW f) x ≠ o.C.T (o.C.enc w.1 w.2) x

/-- The sample's rows as linear forms with a state (`Slf`); the state is the seed. This is what a
test takes in. -/
def row (s : o.Z.S) : Slf E o.Z.D o.C.J := fun ρ => o.Z.mat ρ s

variable [Field E]

/-- The list of a word: the messages some encoding of which is within the radius. -/
def InList (f : o.Str) : o.Msg → Prop := o.C.Msgs o.e (o.upW f)

/-- A candidate: in the list, with the answers. -/
def Cand (f : o.Str) (σ : o.Smp) : o.Msg → Prop := Ood.Cand (o.InList f) o.Z.val σ.1 σ.2

/-- The decoder with a sample: nearest codeword, first in the fixed order, among the pairs whose
message has the answers; none if that one is beyond the radius. -/
def dec (f : o.Str) (σ : o.Smp) : Option o.Msg :=
  decMin (o.dist f) o.rank Prod.fst o.Z.val o.e σ.1 σ.2

/-- A collision at a seed: two different messages of the list have the same answers. -/
def Clash (f : o.Str) (ρ : o.Z.D) : Prop := Ood.Clash (o.InList f) o.Z.val ρ

/-- Every list has at most L messages. -/
def ListLE (L : ℕ) : Prop := ∀ f : o.Str, Ood.ListLE (o.InList f) L

/-- Two different messages of one list have the same answers at no more than Z.err seeds. -/
def Evades : Prop :=
  ∀ (f : o.Str) (m m' : o.Msg), o.InList f m → o.InList f m' → m ≠ m' →
    cnt (fun ρ : o.Z.D => o.Z.val ρ m = o.Z.val ρ m') ≤ o.Z.err

end OMsg

/-! ## 2. A signature -/

/-- A signature: the oracle messages of a statement. -/
structure Sig (E : Type) where
  O : Type
  [finO : Fintype O]
  [decO : DecidableEq O]
  om : O → OMsg E

attribute [instance] Sig.finO Sig.decO

namespace Sig
variable {E : Type}

/-- no oracle message; one; one more -/
@[reducible] def nil (E : Type) : Sig E := { O := Empty, om := fun a => a.elim }
@[reducible] def one (o : OMsg E) : Sig E := { O := Unit, om := fun _ => o }
@[reducible] def add (S : Sig E) (o : OMsg E) : Sig E :=
  { O := Option S.O, om := fun a => a.elim o S.om }

variable (S : Sig E)

/-- The kind of the implicit instance: all words side by side; a position is (name, long position).
-/
abbrev ext : ExtSpec :=
  ⟨∀ a, (S.om a).Str, Σ a, (S.om a).P,
    Σ a, ((S.om a).C.Aa → E),
    fun y q => ⟨q.1, (S.om q.1).C.T ((S.om q.1).upW (y q.1)) q.2⟩⟩
abbrev Smp : Type := ∀ a, (S.om a).Smp
abbrev Msg : Type := ∀ a, (S.om a).Msg
abbrev Wit : Type := ∀ a, (S.om a).Wit

/-- the messages of a witness -/
def msgs (w : S.Wit) : S.Msg := fun a => (w a).1

/-- A family over the oracle messages of S.add o: from the new member and the old ones; and back. -/
def cons {T : OMsg E → Type} (o : OMsg E) (t : T o) (ts : ∀ a, T (S.om a)) : ∀ a, T ((S.add o).om a)
  | none => t
  | some a => ts a
def new {T : OMsg E → Type} (o : OMsg E) (ts : ∀ a, T ((S.add o).om a)) : T o := ts none
def old {T : OMsg E → Type} (o : OMsg E) (ts : ∀ a, T ((S.add o).om a)) : ∀ a, T (S.om a) :=
  fun a => ts (some a)

/-! ## 3. The constraint relations -/

variable [Field E]

/-- every word is the encoding of its pair -/
def Enc (y : S.ext.Str) (w : S.Wit) : Prop :=
  ∀ a, (S.om a).upW (y a) = (S.om a).C.enc (w a).1 (w a).2
/-- every message has the answers of its sample -/
def Ans (σ : S.Smp) (m : S.Msg) : Prop := ∀ a, (S.om a).Z.val (σ a).1 (m a) = (σ a).2

/-- the decoded messages: a function of samples and words -/
def decs (σ : S.Smp) (y : S.ext.Str) : ∀ a, Option (S.om a).Msg := fun a =>
  (S.om a).dec (y a) (σ a)

/-- Samples and words are collision-free: no oracle message has a collision at the seed of its
sample. -/
def CF (σ : S.Smp) (y : S.ext.Str) : Prop := ∀ a, ¬ (S.om a).Clash (y a) (σ a).1

variable {St St' Wp Kc : Type} {E₀ E₀' : ExtSpec}

/-- The joint of a chain: the base joint A, claimed of the messages of the oracle messages of S.
Exact: encodings and answers. Relaxed: by decoding with a sample. -/
def over (A : IOR.Rels Kc St E₀ (S.Msg × Wp)) :
    IOR.Rels Kc (St × S.Smp) (E₀.prod S.ext) (S.Wit × Wp) where
  rel  := fun x y w => S.Enc y.2 w.1 ∧ S.Ans x.2 (S.msgs w.1) ∧ A.rel x.1 y.1 (S.msgs w.1, w.2)
  relR := fun a w =>
    (∀ i, S.decs a.1.2 a.2.2 i = some (w.1 i).1) ∧ A.relR (a.1.1, a.2.1) (S.msgs w.1, w.2)
  on   := fun a => S.CF a.1.2 a.2.2 ∧ A.on (a.1.1, a.2.1)
  core := fun w => A.core (S.msgs w.1, w.2)

/-- The base joint of a predicate (exact form, relaxed form) on the rest of the explicit part, the
messages and the further witness, with no further oracle. -/
def pred (Pred PredR : St → S.Msg → Wp → Prop) : IOR.Rels Unit St extNone (S.Msg × Wp) where
  rel  := fun st _ w => Pred st w.1 w.2
  relR := fun a w => PredR a.1 w.1 w.2
  on   := fun _ => True
  core := fun _ => ()

/-- The joint over a predicate. -/
@[reducible] def rels (Pred : St → S.Msg → Wp → Prop) :
    IOR.Rels Unit (St × S.Smp) (extNone.prod S.ext) (S.Wit × Wp) :=
  S.over (S.pred Pred Pred)

/-- A reduction copies words and samples. -/
def Copies (R : IOR (St × S.Smp) (E₀.prod S.ext) (St' × S.Smp) (E₀'.prod S.ext)) : Prop :=
  (∀ x y τ xo, R.out x y τ = some xo → xo.2 = x.2) ∧ ∀ y τ, (R.imp y τ).2 = y.2

end Sig

/-- One more oracle message: the joint A, a part of whose witness is in the message of o. -/
def OMsg.sent {E : Type} [Field E] (o : OMsg E) {Kc X W W' : Type} {E₀ : ExtSpec}
    (A : IOR.Rels Kc X E₀ W) (back : o.Msg → W' → W) :
    IOR.Rels Kc (X × o.Smp) (E₀.prod o.ext) (o.Wit × W') where
  rel  := fun x y w =>
    o.upW y.2 = o.C.enc w.1.1 w.1.2 ∧ o.Z.val x.2.1 w.1.1 = x.2.2 ∧ A.rel x.1 y.1 (back w.1.1 w.2)
  relR := fun a w => o.dec a.2.2 a.1.2 = some w.1.1 ∧ A.relR (a.1.1, a.2.1) (back w.1.1 w.2)
  on   := fun a => A.on (a.1.1, a.2.1) ∧ ¬ o.Clash a.2.2 a.1.2.1
  core := fun w => A.core (back w.1.1 w.2)

/-! ## The statements -/

namespace Spec
section
variable (E : Type) [Field E]

def sig_inList_iff : Prop :=
  ∀ (o : OMsg E) (f : o.Str) (m : o.Msg), Within (o.dist f) Prod.fst o.e m ↔ o.InList f m

def sig_dist_near : Prop :=
  ∀ (o : OMsg E) (f : o.Str) (w : o.Wit) (k : ℕ),
    o.dist f w ≤ k ↔ o.C.Near k (o.upW f) (o.C.enc w.1 w.2)

/-- Always: what the decoder returns is a candidate. -/
def sig_dec_cand : Prop :=
  ∀ (o : OMsg E) (f : o.Str) (σ : o.Smp) (m : o.Msg), o.dec f σ = some m → o.Cand f σ m

/-- Always: none if and only if there is no candidate. -/
def sig_dec_none : Prop :=
  ∀ (o : OMsg E) (f : o.Str) (σ : o.Smp), o.dec f σ = none ↔ ∀ m, ¬ o.Cand f σ m

/-- At a seed without collision, for every answer: the decoder returns m if and only if m is a
candidate; whatever the order. -/
def sig_dec_good : Prop :=
  ∀ (o : OMsg E) (f : o.Str) (ρ : o.Z.D),
    ¬ o.Clash f ρ → ∀ (v : o.Z.S → E) (m : o.Msg), o.dec f (ρ, v) = some m ↔ o.Cand f (ρ, v) m

/-- Under `o.C.Laws` and `o.C.Dist 1` (different pairs have different transforms): decoding undoes
encoding, at every seed, with the message's answers there, and every radius. -/
def sig_dec_enc : Prop :=
  ∀ (o : OMsg E), o.C.Laws → o.C.Dist 1 →
    ∀ (f : o.Str) (w : o.Wit) (ρ : o.Z.D),
      o.upW f = o.C.enc w.1 w.2 → o.dec f (ρ, o.Z.val ρ w.1) = some w.1

/-- Under `o.C.Laws` and `o.C.Dist d`, at every seed: within e' ≤ e of an encoding of m, with e + e'
< d and the answers of m, the decoder returns m. -/
def sig_dec_close : Prop :=
  ∀ (o : OMsg E) (d e' : ℕ), o.C.Laws → o.C.Dist d → e' ≤ o.e → o.e + e' < d →
    ∀ (f : o.Str) (m : o.Msg),
      o.C.Msgs e' (o.upW f) m → ∀ ρ : o.Z.D, o.dec f (ρ, o.Z.val ρ m) = some m

/-- A message has the answers if and only if the sample's rows hold of it. -/
def sig_rows : Prop :=
  ∀ (o : OMsg E) (σ : o.Smp) (m : o.Msg), o.Z.val σ.1 m = σ.2 ↔ ∀ s, (o.row s).Holds (σ.2 s, σ.1) m

/-- The list of the code bounds the lists of messages. -/
def sig_list_of_code [Finite E] : Prop := ∀ (o : OMsg E) (L : ℕ), o.C.ListAt o.e L → o.ListLE L

def sig_evades_of_ok : Prop := ∀ o : OMsg E, o.Z.OK → o.Evades

def sig_evades_of_okOn : Prop :=
  ∀ (o : OMsg E) (V : o.Msg → Prop), o.Z.OKOn V →
    (∀ (f : o.Str) (m m' : o.Msg), o.InList f m → o.InList f m' → V (m - m')) → o.Evades

/-- The lemma on collisions. Under `o.ListLE L` and `o.Evades`, for every word as sent: at most (L
choose 2) · Z.err seeds have a collision; twice their number is at most L² · Z.err. The word is
fixed before the seed is drawn. -/
def sig_cnt_clash : Prop :=
  ∀ (o : OMsg E) (L : ℕ), o.ListLE L → o.Evades →
    ∀ f : o.Str, cnt (o.Clash f) ≤ L.choose 2 * o.Z.err ∧ 2 * cnt (o.Clash f) ≤ L ^ 2 * o.Z.err

/-- The guard: under `o.C.Laws` and `o.C.Dist d`, within unique decoding (2 e < d): no seed has a
collision, whatever the sample map. -/
def sig_no_clash_unique : Prop :=
  ∀ (o : OMsg E) (d : ℕ),
    o.C.Laws → o.C.Dist d → 2 * o.e < d → ∀ (f : o.Str) (ρ : o.Z.D), ¬ o.Clash f ρ

/-- The guard: under `o.C.Laws` and `o.C.Dist d`, within unique decoding (2 e < d): the decoder
returns m if and only if m is in the list and has the answers; and the list has at most one message.
-/
def sig_dec_unique : Prop :=
  ∀ (o : OMsg E) (d : ℕ), o.C.Laws → o.C.Dist d → 2 * o.e < d →
    ∀ (f : o.Str) (σ : o.Smp) (m : o.Msg),
      (o.dec f σ = some m ↔ o.InList f m ∧ o.Z.val σ.1 m = σ.2) ∧
      ∀ m', o.InList f m → o.InList f m' → m' = m

/-- Under `C.Laws` and `C.Dist 1` of every oracle message: the exact relation is contained in the
relaxed one, if that holds of the base joint. -/
def sig_over_sub : Prop :=
  ∀ (S : Sig E) (Kc St Wp : Type) (E₀ : ExtSpec) (A : IOR.Rels Kc St E₀ (S.Msg × Wp)),
    (∀ a, (S.om a).C.Laws) → (∀ a, (S.om a).C.Dist 1) → (∀ x y w, A.rel x y w → A.relR (x, y) w) →
    ∀ x y w, (S.over A).rel x y w → (S.over A).relR (x, y) w

def sig_sent_sub : Prop :=
  ∀ (o : OMsg E) (Kc X W W' : Type) (E₀ : ExtSpec) (A : IOR.Rels Kc X E₀ W) (back : o.Msg → W' → W),
    o.C.Laws → o.C.Dist 1 → (∀ x y w, A.rel x y w → A.relR (x, y) w) →
    ∀ x y w, (o.sent A back).rel x y w → (o.sent A back).relR (x, y) w

/-- The relaxed relation determines the messages of its witnesses, on all statements, whatever the
base joints: they are `S.decs` of the statement. -/
def sig_over_det : Prop :=
  ∀ (S : Sig E) (Kc St Wp : Type) (E₀ : ExtSpec) (A A' : IOR.Rels Kc St E₀ (S.Msg × Wp)) a w w',
    (S.over A).relR a w → (S.over A').relR a w' → S.msgs w.1 = S.msgs w'.1

/-- On collision-free statements: the relaxed relation holds if and only if every message is in the
list of its word and has its answers, and `A.relR` holds. -/
def sig_over_cf : Prop :=
  ∀ (S : Sig E) (Kc St Wp : Type) (E₀ : ExtSpec) (A : IOR.Rels Kc St E₀ (S.Msg × Wp)) a w,
    S.CF a.1.2 a.2.2 →
    ((S.over A).relR a w ↔
      (∀ i, (S.om i).Cand (a.2.2 i) (a.1.2 i) (w.1 i).1) ∧ A.relR (a.1.1, a.2.1) (S.msgs w.1, w.2))

/-- Collision-free, with one more oracle message. -/
def sig_cf_add : Prop :=
  ∀ (S : Sig E) (o : OMsg E) (σs : S.Smp) (σ : o.Smp) (y : S.ext.Str) (f : o.Str),
    (S.add o).CF (S.cons (T := OMsg.Smp) o σ σs) (S.cons (T := OMsg.Str) o f y) ↔
    S.CF σs y ∧ ¬ o.Clash f σ.1

/-- "One more oracle message" is the joint over the signature of that message alone, up to the
names: in relation, relaxed relation and condition. -/
def sig_sent_one : Prop :=
  ∀ (o : OMsg E) (Kc X W' : Type) (E₀ : ExtSpec) (A : IOR.Rels Kc X E₀ ((Sig.one o).Msg × W'))
      (x : X) (σ : o.Smp) (y : E₀.Str) (f : o.Str) (w : o.Wit) (w' : W'),
    (((Sig.one o).over A).rel (x, fun _ => σ) (y, fun _ => f) (fun _ => w, w') ↔
      (o.sent A fun m v => (fun _ => m, v)).rel (x, σ) (y, f) (w, w')) ∧
    (((Sig.one o).over A).relR ((x, fun _ => σ), (y, fun _ => f)) (fun _ => w, w') ↔
      (o.sent A fun m v => (fun _ => m, v)).relR ((x, σ), (y, f)) (w, w')) ∧
    (((Sig.one o).over A).on ((x, fun _ => σ), (y, fun _ => f)) ↔
      (o.sent A fun m v => (fun _ => m, v)).on ((x, σ), (y, f)))

/-- A reduction that copies words and samples carries "collision-free". -/
def sig_copies : Prop :=
  ∀ (S : Sig E) (St St' : Type) (E₀ E₀' : ExtSpec)
      (R : IOR (St × S.Smp) (E₀.prod S.ext) (St' × S.Smp) (E₀'.prod S.ext)),
    S.Copies R → ∀ a τ b, S.CF a.1.2 a.2.2 → R.red.out a τ = some b → S.CF b.1.2 b.2.2

end

/-- The relaxation is not vacuous: there are an oracle message with `C.Laws` and `Z.OK`, a radius
below its distance, a word with two messages in its list, a seed without collision, and two answers
at which the decoder returns the one and the other. -/
def sig_two : Prop :=
  ∃ (E : Type) (_ : Field E) (o : OMsg E) (d : ℕ) (f : o.Str) (ρ : o.Z.D) (m m' : o.Msg), o.C.Laws ∧
    o.C.Dist d ∧ o.e < d ∧ o.Z.OK ∧ m ≠ m' ∧ o.InList f m ∧ o.InList f m' ∧ ¬ o.Clash f ρ ∧
    o.dec f (ρ, o.Z.val ρ m) = some m ∧ o.dec f (ρ, o.Z.val ρ m') = some m'

end Spec
end Cb
