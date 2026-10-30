-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSwitchLoc.lean: the one-round block "locations": the second half of a code switch whose rows
are kept apart.

In standard terms: a spot check of proximity. The verifier reads the old word at t long positions
that it draws and computes the new explicit part from the old one, the positions and the symbols
read (`V.out`); hk1 below asks that the new claim imply that they are the long symbols, at these
positions, of the encoding of the (message, randomness) that the witness holds.

This file is the frame: the verifier and the claims are parameters. Definitions and statements (each
a `Prop` in `Cb.Spec`); the proofs are in Cb/Ld/LdSwitchLocProofs.lean. P is not empty
(`[Nonempty P]`) in all statements: the round's definition needs it.

Why: the code switch of Cb/Ld/LdSwitch.lean does three things: it sends and samples a new word; it
draws long positions of the old word; it batches all rows into one. Here the
three stand apart: the new word is sent and sampled by the general block for that (`ldSend`,
Cb/Ld/LdSend.lean); this block draws the positions; the rows stay apart until some later batching.
So a collision of the sample is charged in one block only, and the new word may be sent together
with others, the positions still coming after its answers.

The block. A statement has, beside an explicit part `x : Xi`, the old word f (a native word of the
code Cin, read under its transformation) and carried oracles of any kind E₀ (among them the new
word). A witness `w : W` belongs to the carried part, and `old w` is the (message, randomness) of
Cin that it holds.
  The verifier never rejects. The old word is dropped: the new implicit instance is a pair: no
  oracle in the old word's place and, beside it, the carried oracles (`extNone.prod E₀`). The pair
  has the brackets of Cb/Ld/LdSig.lean's joints: further oracles on the left, sampled words on the
  right.
  The claims are arbitrary predicates on (explicit part, carried oracles, witness): ΦiH, ΦoH for the
  honest relations, ΦiR, ΦoR for the relaxations.
  Input joint (`ldLocIn`): exact: f is the encoding of old w, and ΦiH; relaxed: f is within e long
  positions of the encoding of old w (existential: no decoder of f), and ΦiR; a condition "on" on
  statements.
  Output joint (`ldLocOut`): ΦoH; ΦoR; a condition on'.

Main names:
  `Spec.ldLoc_good`: `IOR.Good` (Ior/Chain.lean) from four hypotheses on the predicates, named here
    as its proof names them:
    hk1 (what the new claim says): ΦoR of the output gives ΦiR of the input, and: the encoding of
    old w, under the transformation, has at the drawn positions the long symbols that the output
    names (the rows of the generator at the drawn positions, with what was read as targets).
    hk2 (the carried claim fixes the old part): on the statements with "on": two witnesses with ΦiR
    have the same old part. True on all statements if ΦiR says "the new message is what the decoder
    with a sample returns"; true on collision-free statements if it says "a member of the list with
    the answers".
    hc (completeness): ΦiH gives ΦoH of the output at the true long symbols.
    hon: the condition is carried.
  `Spec.ldLoc_data`: one round; at most t reads of the old word, none of the carried oracles; a
    carried symbol is copied.
  `Spec.ldLoc_exactWith`: see its statement.

The error, a count of lists of positions: (|P| - e - 1)^t; as a probability ((|P| - e - 1)/|P|)^t.
No list size, and the number of old rows plays no part: the word that is compared with f is fixed
before the positions are drawn.
Honest-verifier zero knowledge is trivial: nothing is sent. The simulator is given the long symbols
of the old word at the verifier's t positions (the positions are uniform) and does not use them
(they enter the new explicit part). Nothing is withheld; under hc, completeness is perfect.

Notation: `P`: the long positions; `Cin.T`: the transformation of Cin; `Cin.Aa`: the coordinates of
a long symbol; `Cin.J`, `Cin.Q`: the coordinates of the message and of the encoding randomness;
`Cin.Near e`: two native words are within e long positions of each other (all: `LdCode`,
Cb/Ld/LdRel.lean); `core : W → Kc`: a field of a joint (`IOR.Rels`, Ior/Chain.lean); `imp`, `srcE`,
`srcO`, `tie`, `blinded`: fields of `IOR` (Ior/Ior.lean).

Limits: which predicates a protocol puts in (rows as linear forms with states, the relaxation by
decoding with a sample) is not in this file.
For t = 0 the error is everything.
This file says nothing on running times.
That the step which draws the positions never uses that there is one row is an observation on an
argument of the paper that this protocol builds on.  The block as a statement follows this
protocol's technical report, which in part follows that paper (lean/CREDITS.md).
ADDED LATER (a comparison by reading with a later text on the locations). This is the case without
re-encoded oracle messages. The later text also allows a set of oracle messages that the switch
encodes anew: their rows are rows of the old word, they are dropped from the output, the carried
claim reads their messages off the new message, the extractor is not the identity, and "no
collision" is used after nearness. The frame's hypothesis hk1 (Cb/Ld/LdSwitchLoc.lean: the output's
relaxed claim gives the input's carried claim, outright) cannot be met with such messages. Not
mended here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRelKit
import Ior.KnowCollGood
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks

/-- The verifier of "locations": the data. -/
structure LdLocV (E P Xi Xo : Type) where
  /-- the code of the old word -/
  Cin : LdCode E P
  /-- the number of long positions drawn -/
  t   : ℕ
  /-- the new explicit part, from the old one, the positions, and the long symbols read -/
  out : Xi → (Fin t → P) → (Fin t → Cin.Aa → E) → Xo

section
variable {E P Xi Xo : Type} [Fintype P] [Nonempty P] (V : LdLocV E P Xi Xo)

/-- the one round: no prover message -/
abbrev LdLocV.sh : Shape := [plainRound Unit (Fin V.t → P) ()]

def LdLocV.pt : V.sh.IsPoint := (plainPoint _ _ _, ())

/-- The long symbols of a native word at a list of positions. -/
def LdLocV.at (f : V.Cin.Word) (Qs : Fin V.t → P) : Fin V.t → V.Cin.Aa → E := fun i =>
  V.Cin.T f (Qs i)

open Classical in
/-- The block "locations". -/
def ldLocOf (E₀ : ExtSpec) : IOR Xi (V.Cin.ext.prod E₀) Xo (extNone.prod E₀) where
  shape := V.sh
  blinded _ := true
  extReads ρ := Finset.univ.image fun i => Sum.inl (ρ.1 i)
  reads _ := ∅
  out x y τ := some (V.out x τ.2.1 (V.at y.1 τ.2.1))
  imp y _ := ((), y.2)
  srcE _ q := Sum.elim (fun x => x.elim) (fun p => {Sum.inr p}) q
  srcO _ _ := ∅
  tie _ _ := ∅

variable {E₀ : ExtSpec} {W Kc : Type}

/-- The honest side: nothing is sent, no coins, nothing is withheld; the witness is handed on. -/
def ldLocHon (E₀ : ExtSpec) (old : W → (V.Cin.J → E) × (V.Cin.Q → E)) :
    (ldLocOf V E₀).Honest W W where
  Coin := Unit
  strat w x _ := (((), ()), fun Qs => (V.out x Qs (V.at (V.Cin.enc (old w).1 (old w).2) Qs), w))
  Bad := ∅
  Hid _ _ := ∅

/-- The simulator: the empty view. -/
def ldLocSim (E₀ : ExtSpec) : IOR.Honest.Sim (ldLocOf V E₀) :=
  fun _ ρ T _ => (unif Unit).map fun _ => some ((ldLocOf V E₀).view T (((), ()), ρ.1, ()))

/-- The input joint. -/
def ldLocIn (old : W → (V.Cin.J → E) × (V.Cin.Q → E)) (e : ℕ) (ΦH ΦR : Xi → E₀.Str → W → Prop)
    (on : Xi × (V.Cin.ext.prod E₀).Str → Prop) (core : W → Kc) :
    IOR.Rels Kc Xi (V.Cin.ext.prod E₀) W where
  rel  := fun x y w => y.1 = V.Cin.enc (old w).1 (old w).2 ∧ ΦH x y.2 w
  relR := fun a w => V.Cin.Near e a.2.1 (V.Cin.enc (old w).1 (old w).2) ∧ ΦR a.1 a.2.2 w
  on   := on
  core := core

omit [Fintype P] [Nonempty P] in
/-- The output joint. -/
def ldLocOut (_ : LdLocV E P Xi Xo) (ΦH ΦR : Xo → E₀.Str → W → Prop)
    (on' : Xo × (extNone.prod E₀).Str → Prop) (core : W → Kc) :
    IOR.Rels Kc Xo (extNone.prod E₀) W where
  rel  := fun x y w => ΦH x y.2 w
  relR := fun a w => ΦR a.1 a.2.2 w
  on   := on'
  core := core

/-- The bad lists of positions for the statement a: some witness has the new claim, though the old
word is farther than e from the encoding of its old part. -/
def ldLocBad (old : W → (V.Cin.J → E) × (V.Cin.Q → E)) (e : ℕ)
    (ΦoR : Xo → E₀.Str → W → Prop) (a : Xi × (V.Cin.ext.prod E₀).Str) : BadFam V.sh :=
  (fun _ =>
      {Qs | ∃ w,
        ΦoR (V.out a.1 Qs (V.at a.2.1 Qs)) a.2.2 w ∧
        ¬ V.Cin.Near e a.2.1 (V.Cin.enc (old w).1 (old w).2)},
    fun _ _ => ())

/-- The numbers: one error; nothing is withheld; no oracle is sent, so every set of further
positions is empty. -/
def ldLocNums (Kc : Type) (E₀ : ExtSpec) (e : ℕ) : IOR.Nums Kc (ldLocOf V E₀) :=
  ⟨((Fintype.card P - e - 1) ^ V.t, ()), 0, 0, fun _ _ => True, fun _ => ∅⟩

end

namespace Spec
open IOR

open Classical in
/-- The data. -/
def ldLoc_data : Prop :=
  ∀ (E P Xi Xo : Type) [Fintype P] [Nonempty P] (V : LdLocV E P Xi Xo) (E₀ : ExtSpec),
    (ldLocOf V E₀).shape.length = 1 ∧
    (ldLocOf V E₀).ImpBy (fun y _ => ((), y.2)) ∧
    (∀ ρ p, (ldLocOf V E₀).tie ρ p = ∅) ∧
    (∀ ρ, (ldLocOf V E₀).reads ρ = ∅) ∧
    (∀ ρ, ((ldLocOf V E₀).extReads ρ).card ≤ V.t) ∧
    (∀ ρ q, Sum.inr q ∉ (ldLocOf V E₀).extReads ρ) ∧
    (∀ ρ q, (ldLocOf V E₀).srcE ρ (Sum.inr q) = {Sum.inr q}) ∧
    (∀ ρ q, (ldLocOf V E₀).srcO ρ q = ∅) ∧
    IsEmpty (OPos (ldLocOf V E₀).shape)

/-- The bad set is within the error, under hk1 of the head at a, P not empty, on a statement whose
carried claim fixes the old part. -/
def ldLoc_within : Prop :=
  ∀ (E P Xi Xo : Type) [Fintype P] [Nonempty P] (V : LdLocV E P Xi Xo) (E₀ : ExtSpec) (W : Type)
      (old : W → (V.Cin.J → E) × (V.Cin.Q → E)) (e : ℕ) (ΦiR : Xi → E₀.Str → W → Prop)
      (ΦoR : Xo → E₀.Str → W → Prop) (a : Xi × (V.Cin.ext.prod E₀).Str),
    (∀ Qs v w, ΦoR (V.out a.1 Qs v) a.2.2 w →
      ΦiR a.1 a.2.2 w ∧ V.at (V.Cin.enc (old w).1 (old w).2) Qs = v) →
    (∀ w w', ΦiR a.1 a.2.2 w → ΦiR a.1 a.2.2 w' → old w = old w') →
    (ldLocBad V old e ΦoR a).Within ((Fintype.card P - e - 1) ^ V.t, ())

/-- The backward step, under hk1 of the head at a, P not empty: no bad list; then a witness of the
output statement in the relaxation is one of the input statement. -/
def ldLoc_clean : Prop :=
  ∀ (E P Xi Xo : Type) [Fintype P] [Nonempty P] (V : LdLocV E P Xi Xo) (E₀ : ExtSpec) (W : Type)
      (old : W → (V.Cin.J → E) × (V.Cin.Q → E)) (e : ℕ) (ΦiR : Xi → E₀.Str → W → Prop)
      (ΦoR : Xo → E₀.Str → W → Prop) (a : Xi × (V.Cin.ext.prod E₀).Str),
    (∀ Qs v w, ΦoR (V.out a.1 Qs v) a.2.2 w →
      ΦiR a.1 a.2.2 w ∧ V.at (V.Cin.enc (old w).1 (old w).2) Qs = v) →
    ∀ (τ : Tr V.sh) b w, (ldLocBad V old e ΦoR a).Clean τ → (ldLocOf V E₀).red.out a τ = some b →
      ΦoR b.1 b.2.2 w → V.Cin.Near e a.2.1 (V.Cin.enc (old w).1 (old w).2) ∧ ΦiR a.1 a.2.2 w

/-- Round-by-round knowledge soundness, under hk1 and hk2 of the head, P not empty: the extractor is
the identity. -/
def ldLoc_know : Prop :=
  ∀ (E P Xi Xo : Type) [Fintype P] [Nonempty P] (V : LdLocV E P Xi Xo) (E₀ : ExtSpec) (W : Type)
      (old : W → (V.Cin.J → E) × (V.Cin.Q → E)) (e : ℕ) (ΦiR : Xi → E₀.Str → W → Prop)
      (ΦoR : Xo → E₀.Str → W → Prop) (on : Xi × (V.Cin.ext.prod E₀).Str → Prop),
    (∀ x Qs v y₀ w,
      ΦoR (V.out x Qs v) y₀ w → ΦiR x y₀ w ∧ V.at (V.Cin.enc (old w).1 (old w).2) Qs = v) →
    (∀ a, on a → ∀ w w', ΦiR a.1 a.2.2 w → ΦiR a.1 a.2.2 w' → old w = old w') →
    (ldLocOf V E₀).red.Know on
      (fun a w => V.Cin.Near e a.2.1 (V.Cin.enc (old w).1 (old w).2) ∧ ΦiR a.1 a.2.2 w)
      (fun b w => ΦoR b.1 b.2.2 w) (fun _ _ w => w) ((Fintype.card P - e - 1) ^ V.t, ())

/-- Completeness, under hc of the head, P not empty: perfect. -/
def ldLoc_acc : Prop :=
  ∀ (E P Xi Xo : Type) [Fintype P] [Nonempty P] (V : LdLocV E P Xi Xo) (E₀ : ExtSpec)
      (W : Type) (old : W → (V.Cin.J → E) × (V.Cin.Q → E))
      (ΦiH : Xi → E₀.Str → W → Prop) (ΦoH : Xo → E₀.Str → W → Prop),
    (∀ x y₀ w Qs, ΦiH x y₀ w → ΦoH (V.out x Qs (V.at (V.Cin.enc (old w).1 (old w).2) Qs)) y₀ w) →
    (ldLocHon V E₀ old).Acc (fun x y w => y.1 = V.Cin.enc (old w).1 (old w).2 ∧ ΦiH x y.2 w)
      fun x y w => ΦoH x y.2 w

/-- For P not empty: honest-verifier exact zero knowledge, with the simulator named, for every input
relation and every set of further positions (`IOR.Honest.ExactWith`, Ior/Honest.lean). -/
def ldLoc_exactWith : Prop :=
  ∀ (E P Xi Xo : Type) [Fintype P] [Nonempty P] (V : LdLocV E P Xi Xo) (E₀ : ExtSpec) (W : Type)
      (old : W → (V.Cin.J → E) × (V.Cin.Q → E)) (Ri : Xi → (V.Cin.ext.prod E₀).Str → W → Prop),
    (ldLocHon V E₀ old).ExactWith Ri (fun _ _ => True) (ldLocSim V E₀)

/-- For P not empty, under the four hypotheses below (hk1, hk2, hc, hon of the head), "locations"
leads from a claim on the old word and the carried oracles to a claim on the carried oracles
alone. -/
def ldLoc_good : Prop :=
  ∀ (E P Xi Xo : Type) [Fintype P] [Nonempty P] (V : LdLocV E P Xi Xo) (E₀ : ExtSpec) (W Kc : Type)
      (old : W → (V.Cin.J → E) × (V.Cin.Q → E)) (core : W → Kc) (e : ℕ)
      (ΦiH ΦiR : Xi → E₀.Str → W → Prop) (ΦoH ΦoR : Xo → E₀.Str → W → Prop)
      (on : Xi × (V.Cin.ext.prod E₀).Str → Prop) (on' : Xo × (extNone.prod E₀).Str → Prop),
    (∀ x Qs v y₀ w,
      ΦoR (V.out x Qs v) y₀ w → ΦiR x y₀ w ∧ V.at (V.Cin.enc (old w).1 (old w).2) Qs = v) →
    (∀ a, on a → ∀ w w', ΦiR a.1 a.2.2 w → ΦiR a.1 a.2.2 w' → old w = old w') →
    (∀ x y₀ w Qs, ΦiH x y₀ w → ΦoH (V.out x Qs (V.at (V.Cin.enc (old w).1 (old w).2) Qs)) y₀ w) →
    (∀ a Qs, on a → on' (V.out a.1 Qs (V.at a.2.1 Qs), ((), a.2.2))) →
    Good (ldLocOf V E₀) (ldLocHon V E₀ old) (ldLocIn V old e ΦiH ΦiR on core)
      (ldLocOut V ΦoH ΦoR on' core) (fun _ _ w => w) (ldLocNums V Kc E₀ e)

end Spec
end Cb
