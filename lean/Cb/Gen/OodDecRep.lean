-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecRep.lean: list decoding with an out-of-domain sample, for words that may differ in
length and are queried at common positions. The decoder with samples for a code complex whose words
are read at common positions (`Cb.Reading` of Cb/Gen/CodeRep.lean: say a long main word and a short
mask word, repeated).

Definitions and statements; proofs in Cb/Gen/OodDecRepProofs.lean. A reading is even if each
position of the component a is read exactly mult a > 0 times.

How it differs from Cb/Gen/OodDecCx.lean: there every component has a radius of its own. Here there
is one distance and one radius for all words that are sent together: the number of long positions
(the members of the reading's common set P of positions) at which some component differs from the
encoding. The sample is joint in both. Which of the two a protocol takes is open; the distance is a
parameter of the abstract decoder (`Cb.Ood.decMin`, `Cb.Ood.Within`), of which this file is an
instance; this file and Cb/Gen/OodDecCx.lean (`Cx.decS`: `Cb.Ood.pick` on the list `Cx.Near`) rest
on the same notions `Cand`, `Coll` and the same counting lemma.
`ood_cxU_near_comp` compares them.

Main names, the definitions:
  `Cx.distU`, `Cx.NearU`, `Cx.pickU`: see their docstrings.
  `Cx.CollU`: collision: two different messages of the list (`Cx.NearU`) have the answers v at the
    seed ρ.
  `Cx.decMinU`: the decoder by a constrained minimum (two kinds of value): among all pairs (message,
    randomness) whose message has the answers, the first, in a fixed total order of the pairs (given
    by `rank`; it is a total order if `rank` is injective, which no statement here asks), of those
    at the least distance; its message, if that distance is at most e.

Main names, the statements. `ood_cxU_list`, `ood_cxU_cnt`, `ood_cxU_johnson`, `ood_cxU_close` and
`ood_cxU_enc` assume "place": msg + r ≤ k for every component.
  `ood_cxU_dist`: the same quantity as in Cb/Gen/CodeRep.lean: `Cx.distU` is the number of long
    positions that are off (`Reading.Off`) between the tables of the words, read in E, and the full
    messages that the encoder forms; so "distU ≤ e" is `Reading.DecodesTo`.
  `ood_cxU_list`: a bound on the list of families of full messages under the reading bounds the list
    of messages.
  `ood_cxU_cnt`: the counting lemma (`ood_cnt_clash`, Cb/Gen/OodDec.lean), under such a bound L: the
    seeds at which some answers have a collision number at most (L choose 2) err (`Sample.err`);
    twice their number is at most L² err. For a sample map with the property on a set V of vectors
    that holds all differences of messages (`Sample.OKOn`; V = everything gives `Sample.OK`).
  `ood_cxU_johnson`: the first of these bounds, for the same sample maps, with L = `listMax` from
    the distance alone: an even reading, a lower bound d a on the distance of each generator
    (`HasDist`), D ≤ mult a · d a for all components, the radius below the Johnson radius for
    (number of long positions, D). It does not multiply over the components.
  `ood_cxU_good`: without a collision: `Cx.decMinU` returns m if and only if m is in the list and
    has the answers; and `Cx.decMinU` is `Cx.pickU` (with none for "none").
  `ood_cxU_close`, `ood_cxU_enc` (e' = 0): at every seed, for T, d a and D as in `ood_cxU_johnson`:
    words within e' ≤ e long positions of an encoding of m, with e + e' < D, and the answers of m:
    `Cx.decMinU` returns m.
  `ood_cxU_one`: the guard: for one component, read as it stands, the list is `Comp.Near`.

Limits: no relaxed relation, no protocol, nothing on hiding (Cb/Gen/OodDecPad.lean has privacy of
the sample's map). At a collision nothing is claimed about the value of `Cx.decMinU` beyond
`Cb.Spec.ood_decMin_iff` (for an injective `rank`), `ood_decMin_cand` and `ood_decMin_none_iff`
(Cb/Gen/OodDecMin.lean).
That the words sent together are decoded together, under one sample, follows advice; the joint
distance under a repetition, and the lists at that distance, follow this protocol's technical
report, which follows the paper that this protocol builds on (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.OodDecCx
import Cb.Gen.OodDecMin
import Cb.Gen.OodDecPad
import Cb.Gen.CodeRep
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Blocks Hiop

section
variable {F : Type} [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

/-- the codes of the components -/
abbrev Cx.cods (K : Cx F) : K.A → Code.Enc F := fun a => (K.comp a).code

/-- The distance under a reading: the number of long positions at which some component differs from
the encoding. -/
def Cx.distU (K : Cx F) (T : Reading K.cods)
    (y : (K.ext E).Str) (w : K.Msg E × K.Rnd E) : ℕ :=
  cnt (fun x : T.P => ∃ a, y a (T.pos a x) ≠ ((K.comp a).enc E).enc (w.1 a) (w.2 a) (T.pos a x))

/-- The list: the messages some encoding of which is within e long positions. -/
def Cx.NearU (K : Cx F) (T : Reading K.cods) (e : ℕ) (y : (K.ext E).Str) : K.Msg E → Prop :=
  Ood.Within (K.distU E T y) Prod.fst e

/-- Collision. -/
def Cx.CollU (K : Cx F) (T : Reading K.cods) (e : ℕ) (Z : Ood.Sample E K.Ent) (y : (K.ext E).Str)
    (ρ : Z.D) (v : Z.S → E) : Prop :=
  Ood.Coll (K.NearU E T e y) (K.ans Z) ρ v

/-- The decoder by a constrained minimum. -/
def Cx.decMinU (K : Cx F) (T : Reading K.cods) (rank : K.Msg E × K.Rnd E → ℕ) (e : ℕ)
    (Z : Ood.Sample E K.Ent) (y : (K.ext E).Str) (ρ : Z.D) (v : Z.S → E) : Option (K.Msg E) :=
  Ood.decMin (K.distU E T y) rank Prod.fst (K.ans Z) e ρ v

/-- The decoder with three kinds of value. -/
def Cx.pickU (K : Cx F) (T : Reading K.cods) (e : ℕ) (Z : Ood.Sample E K.Ent)
    (y : (K.ext E).Str) (ρ : Z.D) (v : Z.S → E) : Ood.Val (K.Msg E) :=
  Ood.pick (K.NearU E T e y) (K.ans Z) ρ v

end

namespace Spec
open Cb.Ood

section
variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

/-- The same quantity as in Cb/Gen/CodeRep.lean: `Cx.distU` is the number of long positions that are
off (`Reading.Off`). -/
def ood_cxU_dist : Prop :=
  ∀ (K : Cx F) (T : Reading K.cods) (y : (K.ext E).Str) (w : K.Msg E × K.Rnd E), K.distU E T y w =
    cnt (T.Off E (R := fun a => (K.comp a).R) (fun a => (K.comp a).tab (y a)) fun a =>
        (K.comp a).fullOf (w.1 a) (w.2 a))

def ood_cxU_list : Prop :=
  ∀ (K : Cx F) (T : Reading K.cods) (e : ℕ) (y : (K.ext E).Str) (L : ℕ),
    (∀ a, (K.comp a).code.msg + (K.comp a).code.r ≤ (K.comp a).code.k) →
    ListLE (fun M : ∀ a, (K.comp a).R → Fin (K.comp a).code.k →
        E => T.DecodesTo E e (fun a => (K.comp a).tab (y a)) M) L →
    ListLE (K.NearU E T e y) L

/-- The counting lemma, under a reading. -/
def ood_cxU_cnt : Prop :=
  ∀ (K : Cx F) (T : Reading K.cods) (e : ℕ) (Z : Sample E K.Ent) (V : (K.Ent → E) → Prop)
      (y : (K.ext E).Str) (L : ℕ),
    (∀ a, (K.comp a).code.msg + (K.comp a).code.r ≤ (K.comp a).code.k) →
    ListLE (fun M : ∀ a, (K.comp a).R → Fin (K.comp a).code.k →
        E => T.DecodesTo E e (fun a => (K.comp a).tab (y a)) M) L →
    Z.OKOn V → (∀ m m' : K.Msg E, V (K.ents m - K.ents m')) →
    cnt (fun ρ : Z.D => ∃ v, K.CollU E T e Z y ρ v) ≤ L.choose 2 * Z.err ∧
    2 * cnt (fun ρ : Z.D => ∃ v, K.CollU E T e Z y ρ v) ≤ L ^ 2 * Z.err

/-- The counting lemma below the Johnson radius of the group (the components read together). -/
def ood_cxU_johnson : Prop :=
  ∀ (K : Cx F) (T : Reading K.cods) (D e : ℕ) (Z : Sample E K.Ent)
      (V : (K.Ent → E) → Prop) (y : (K.ext E).Str),
    (∀ a, (K.comp a).code.msg + (K.comp a).code.r ≤ (K.comp a).code.k) → T.Even →
    (∀ a, HasDist (K.comp a).code.G (K.comp a).code.d) → (∀ a, D ≤ T.mult a * (K.comp a).code.d) →
    InJohnson (Fintype.card T.P) D e → Z.OKOn V → (∀ m m' : K.Msg E, V (K.ents m - K.ents m')) →
    cnt (fun ρ : Z.D => ∃ v, K.CollU E T e Z y ρ v) ≤
      (listMax (Fintype.card T.P) D e).choose 2 * Z.err

/-- Without a collision the decoder returns the only candidate, and the two forms agree. -/
def ood_cxU_good : Prop :=
  ∀ (K : Cx F) (T : Reading K.cods) (rank : K.Msg E × K.Rnd E → ℕ) (e : ℕ) (Z : Sample E K.Ent)
      (y : (K.ext E).Str) (ρ : Z.D) (v : Z.S → E),
    ¬ K.CollU E T e Z y ρ v →
    (∀ m, K.decMinU E T rank e Z y ρ v = some m ↔ K.NearU E T e y m ∧ K.ans Z ρ m = v) ∧
    K.decMinU E T rank e Z y ρ v = (K.pickU E T e Z y ρ v).opt

/-- Close to an encoding, at every seed. -/
def ood_cxU_close : Prop :=
  ∀ (K : Cx F) (T : Reading K.cods) (rank : K.Msg E × K.Rnd E → ℕ) (D e e' : ℕ) (Z : Sample E K.Ent)
      (y : (K.ext E).Str) (m : K.Msg E),
    (∀ a, (K.comp a).code.msg + (K.comp a).code.r ≤ (K.comp a).code.k) → T.Even →
    (∀ a, HasDist (K.comp a).code.G (K.comp a).code.d) → (∀ a, D ≤ T.mult a * (K.comp a).code.d) →
    e' ≤ e → e + e' < D → K.NearU E T e' y m →
    ∀ ρ : Z.D, K.decMinU E T rank e Z y ρ (K.ans Z ρ m) = some m

/-- Under the hypotheses below, decoding undoes encoding, at every seed, for every e < D, with the
answers of m. -/
def ood_cxU_enc : Prop :=
  ∀ (K : Cx F) (T : Reading K.cods) (rank : K.Msg E × K.Rnd E → ℕ) (D e : ℕ) (Z : Sample E K.Ent)
      (m : K.Msg E) (r : K.Rnd E),
    (∀ a, (K.comp a).code.msg + (K.comp a).code.r ≤ (K.comp a).code.k) → T.Even →
    (∀ a, HasDist (K.comp a).code.G (K.comp a).code.d) → (∀ a, D ≤ T.mult a * (K.comp a).code.d) →
    e < D → ∀ ρ : Z.D, K.decMinU E T rank e Z ((K.enc E).enc m r) ρ (K.ans Z ρ m) = some m

/-- Within e under an even reading: within e / mult a in each component. -/
def ood_cxU_near_comp : Prop :=
  ∀ (K : Cx F) (T : Reading K.cods) (e : ℕ) (y : (K.ext E).Str) (m : K.Msg E),
    T.Even → K.NearU E T e y m → K.Near E (fun a => e / T.mult a) y m

/-- The guard: one component, read as it stands. -/
def ood_cxU_one : Prop :=
  ∀ (c : Comp F) (e : ℕ) (y : ((Cx.one c).ext E).Str) (m : (Cx.one c).Msg E),
    (Cx.one c).NearU E (Reading.one c.code) e y m ↔ c.Near E e (y ()) (m ())

end
end Spec
end Cb
