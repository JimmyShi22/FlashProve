-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/Code.lean: codes as encodings with randomness and decoding (`Hiop.Enc`, Hiop/Enc.lean).

Definitions, and the statements of their laws (in `Cb.Spec`); the proofs are in
Cb/Gen/CodeProofs.lean (generic part) and Cb/Gen/CodeProofsComp.lean (components, complexes).
In standard terms: encodings with randomness by linear codes, interleaved codes, and finite
families of these, each as a kind of oracle with an encoder and a decoder.
An encoding N : `Hiop.Enc X`, for a kind of oracle X, is a pair of maps: `enc` takes a message and
randomness to an oracle string, `dec` takes any string to a pair (message, randomness) or to no
result.

Main names:
 1. Generic, no code in it: the laws of an encoding (`Hiop.Enc.Laws`: decoding undoes encoding) and
    what it hides (`Hiop.Enc.Hides bud`: on every set of positions within the budget the law of the
    symbols, over the encoding randomness, does not depend on the message); two encodings side by
    side (`Enc.prod`) and a finite family (`Enc.fam`), encoded and decoded component by component
    (no result if a component has none); "a part of an encoding" (`Enc.Part`: renaming, restriction
    to a sub-family, re-bracketing), with its laws.
 2. One component c (`Cb.Comp`), in standard terms an interleaved code: a code with encoder
    (`Code.Enc`, Code/Iface.lean), a finite set of names of interleaved rows, and a flag "entries
    in F" (else in E). A row over E is encoded by the same generator matrix over E.
    `Comp.full`: the same words, with the full messages (any vectors of length k) as message and no
    randomness. `c.code.Props E` below is `Code.Enc.Props` (Code/Iface.lean): the properties of a
    code with encoder.
 3. A code complex (`Cb.Cx`): a finite family of components, indexed by a type of names (so there
    is no order of components); the entries of its message, read in E (`Cx.ents`).
 4. `Con N Φ`: the constraint relation of the predicate Φ. `trivRels`: the joint (`Iop.IOR.Rels`)
    at the trivial statement.
Under `c.code.Props E`, hiding is exact: any b positions of an encoding are uniform (error 0), for
one row, for interleaved rows (the error does not grow: it is 0) and over E.

Limits:
Decoding (declared difference to a print of this protocol's technical report
(lean/CREDITS.md)). The paper's code of an encoding is the
IMAGE of the encoder, and its decoder gives no result if the closest codeword is outside that image.
Here: unique decoding, at the radius e of the code with 2 e < d, in the whole code of dimension k
(`Blocks.dec`, Blocks/Decode.lean); then message and randomness are read off the full message and
whatever is at the other coordinates is dropped. So, at a distance within this radius, more words
decode here than there, and every relaxation by decoding is larger here.
Where the randomness is placed (declared difference). The encoder of Code/Iface.lean puts the
randomness right behind the message. The paper's encoder for circle codes leaves a gap of zeros
between them, so that the randomness starts at an aligned coordinate. In Lean the gap counts as
message: "msg" is the aligned offset, an honest message is 0 in the gap, and a decoded message need
not be. A predicate that renders one of the paper's must not read the gap; nothing in this file
enforces that (Cx.ents gives all entries).
The full code (declared difference). In the paper the full message of a word has msg + r
coordinates (message, randomness), and it says that a linear relation over a code and over its full
code have the same statements and the same witnesses. Here that sentence fails: `fullCode` has
msg := k, all coordinates of the generator's input (also those behind the randomness, and for the
index the gap before it), so the full code's relations have more witnesses. What holds, and is all
that is used: an encoding is an encoding under the full code (forward), and `Spec.comp_full`
(backward, under `c.code.Props E`): a word decodes under the one if and only if it does under the
other, and message and randomness are the parts of the full message.
This file says nothing on running times. Decoding is a choice among the full messages within the
radius, which is unique under `c.code.Props E`. On proximity gaps (Code/, Blocks/Decode.lean part 6
have them) no statement of this file concludes anything, but that `Spec.full_props` hands the field
`mca` of `Code.Enc.Props` (Code/Iface.lean) on from its premise `C.Props E` to `fullCode C`.
The notions follow definitions of the preliminaries of this protocol's technical report, which
follow the paper that this protocol builds on (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Hiop.Enc
import Ior.Chain
import Blocks.BlockFront
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop

/-- A family of kinds of oracles side by side. -/
abbrev ExtSpec.fam {A : Type} (E : A → ExtSpec) : ExtSpec :=
  ⟨∀ a, (E a).Str, Σ a, (E a).Pos, Σ a, (E a).Sym, fun y p => ⟨p.1, (E p.1).rd (y p.1) p.2⟩⟩

end Iop

namespace Hiop
open Iop Prob

namespace Enc
variable {E E' E₁ E₂ : ExtSpec}

/-- A witness of a statement about encoded oracles: message and encoding randomness. -/
abbrev Wit (N : Enc E) : Type := N.Msg × N.Rnd

/-- The law of an encoding: decoding undoes encoding. (That a word has at most one decoding holds by
the type of `dec`.) -/
structure Laws (N : Enc E) : Prop where
  dec_enc : ∀ m r, N.dec (N.enc m r) = some (m, r)

/-- What an encoding shows on a set of positions. -/
def shows (N : Enc E) (S : Finset E.Pos) (m : N.Msg) (r : N.Rnd) : S → E.Sym := fun p =>
  E.rd (N.enc m r) p

/-- Hiding: on every set of positions within the budget, the law of the symbols does not depend on
the message. Error 0. -/
def Hides (N : Enc E) (bud : Finset E.Pos → Prop) : Prop :=
  ∀ S, bud S → ∀ m m', (unif N.Rnd).map (N.shows S m) = (unif N.Rnd).map (N.shows S m')

/-- Two encodings side by side. -/
@[reducible] def prod (N₁ : Enc E₁) (N₂ : Enc E₂) : Enc (E₁.prod E₂) where
  Msg := N₁.Msg × N₂.Msg
  Rnd := N₁.Rnd × N₂.Rnd
  enc m r := (N₁.enc m.1 r.1, N₂.enc m.2 r.2)
  dec y := (N₁.dec y.1).bind fun a => (N₂.dec y.2).map fun b => ((a.1, b.1), (a.2, b.2))

/-- Each side bears its own budget. -/
def budProd (b₁ : Finset E₁.Pos → Prop) (b₂ : Finset E₂.Pos → Prop) :
    Finset (E₁.prod E₂).Pos → Prop :=
  fun S => b₁ S.toLeft ∧ b₂ S.toRight

open Classical in
/-- A finite family of encodings side by side: no result if a component has none. -/
@[reducible] def fam
    {A : Type} [Fintype A] [DecidableEq A] {E : A → ExtSpec} (N : ∀ a, Enc (E a)) :
    Enc (ExtSpec.fam E) where
  Msg := ∀ a, (N a).Msg
  Rnd := ∀ a, (N a).Rnd
  enc m r := fun a => (N a).enc (m a) (r a)
  dec y := if h : ∀ a, ((N a).dec (y a)).isSome then
      some (fun a => (((N a).dec (y a)).get (h a)).1, fun a => (((N a).dec (y a)).get (h a)).2)
    else none

/-- The positions of a set that lie in the component a. -/
def fibre {A : Type} {E : A → ExtSpec} (S : Finset (ExtSpec.fam E).Pos) (a : A) :
    Finset (E a).Pos :=
  S.preimage (fun p : (E a).Pos => (⟨a, p⟩ : (ExtSpec.fam E).Pos))
    (fun _ _ _ _ h => eq_of_heq (Sigma.mk.inj h).2)

/-- Each component bears its own budget. -/
def budFam {A : Type} {E : A → ExtSpec} (b : ∀ a, Finset (E a).Pos → Prop) :
    Finset (ExtSpec.fam E).Pos → Prop :=
  fun S => ∀ a, b a (fibre S a)

/-- A part of an encoding: the data. N' has some of the components of N, perhaps under other names
or in other brackets. `Part.Laws` asks that every symbol of the part is determined by one symbol of
the whole, at the position `src`. -/
structure Part (N : Enc E) (N' : Enc E') where
  str : E.Str → E'.Str
  src : E'.Pos → E.Pos
  msg : N.Msg → N'.Msg
  rnd : N.Rnd → N'.Rnd

/-- The laws of a part. -/
structure Part.Laws {N : Enc E} {N' : Enc E'} (π : Part N N') : Prop where
  loc : ∀ y y' q, E.rd y (π.src q) = E.rd y' (π.src q) → E'.rd (π.str y) q = E'.rd (π.str y') q
  enc : ∀ m r, π.str (N.enc m r) = N'.enc (π.msg m) (π.rnd r)
  dec : ∀ y w, N.dec y = some w → N'.dec (π.str y) = some (π.msg w.1, π.rnd w.2)

/-- The part is the whole (renaming, re-bracketing): nothing is lost. -/
structure Part.Whole {N : Enc E} {N' : Enc E'} (π : Part N N') : Prop extends π.Laws where
  back : ∀ y w', N'.dec (π.str y) = some w' → ∃ w, N.dec y = some w
  inj  : ∀ w w' : N.Wit, π.msg w.1 = π.msg w'.1 → π.rnd w.2 = π.rnd w'.2 → w = w'

/-- the two sides of a pair, as parts -/
def partFst (N₁ : Enc E₁) (N₂ : Enc E₂) : Part (N₁.prod N₂) N₁ :=
  ⟨Prod.fst, Sum.inl, Prod.fst, Prod.fst⟩
def partSnd (N₁ : Enc E₁) (N₂ : Enc E₂) : Part (N₁.prod N₂) N₂ :=
  ⟨Prod.snd, Sum.inr, Prod.snd, Prod.snd⟩

/-- the family re-indexed along any map σ, as a part: a sub-family (σ injective), a renaming (σ
bijective) -/
def partSub {A A' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    {E : A → ExtSpec} (N : ∀ a, Enc (E a)) (σ : A' → A) :
    Part (fam N) (fam fun a' => N (σ a')) :=
  ⟨fun y a' => y (σ a'), fun q => ⟨σ q.1, q.2⟩, fun m a' => m (σ a'), fun r a' => r (σ a')⟩

/-- a family over a sum of two sets of names is the pair of the two families -/
def partSum {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {E : A ⊕ B → ExtSpec} (N : ∀ c, Enc (E c)) :
    Part (fam N) ((fam fun a => N (.inl a)).prod (fam fun b => N (.inr b))) :=
  ⟨fun y => (fun a => y (.inl a), fun b => y (.inr b)),
   fun q => match q with
     | .inl p => ⟨.inl p.1, p.2⟩
     | .inr p => ⟨.inr p.1, p.2⟩,
   fun m =>
     (fun a => m (.inl a), fun b => m (.inr b)),
       fun r => (fun a => r (.inl a), fun b => r (.inr b))⟩

end Enc
end Hiop

namespace Cb
open Iop Prob Blocks Hiop

/-- The randomness part of a full message: the r coordinates behind the message. -/
def rndPart {F : Type} (C : Code.Enc F) {K : Type} [Zero K] (v : Fin C.k → K) : Fin C.r → K :=
  fun t => nat v (C.msg + t.val)

/-- A component of a code complex: the data. Interleaved rows, named by i : R, under one code with
encoder; entries, randomness and symbols in F if the flag is set, else in E. -/
structure Comp (F : Type) where
  code  : Code.Enc F
  R     : Type
  [finR : Fintype R]
  [decR : DecidableEq R]
  overF : Bool

attribute [instance] Comp.finR Comp.decR

/-- rows numbered 0, .., rows - 1 -/
@[reducible] def Comp.fin {F : Type} (code : Code.Enc F) (rows : ℕ) (overF : Bool) : Comp F :=
  ⟨code, Fin rows, overF⟩

/-- The code with the full message as its message: no randomness, nothing hidden. -/
@[reducible] def fullCode {F : Type} (C : Code.Enc F) : Code.Enc F :=
  { C with msg := C.k, r := 0, b := 0 }

/-- The component with the full messages of its rows as its message. -/
@[reducible] def Comp.full {F : Type} (c : Comp F) : Comp F := { c with code := fullCode c.code }

/-- A code complex: the data. The components have names a : A; there is no order. -/
structure Cx (F : Type) where
  A : Type
  [finA : Fintype A]
  [decA : DecidableEq A]
  comp : A → Comp F

attribute [instance] Cx.finA Cx.decA

section
variable {F : Type} [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

namespace Comp
variable (c : Comp F)

/-- the oracle: one word of n symbols, a symbol is a column -/
abbrev ext : ExtSpec := oneExternalString c.code.n (c.R → Kf F E c.overF)
abbrev Msg : Type := c.R → Fin c.code.msg → Kf F E c.overF
abbrev Rnd : Type := c.R → Fin c.code.r → Kf F E c.overF

variable {E} in
/-- the word as a table of rows, read in E -/
def tab (y : (c.ext E).Str) : c.R → Fin c.code.n → E := fun i p => (y p i).toE

open Classical in
/-- The encoding of a component, with unique decoding in the whole code. -/
@[reducible] def enc : Enc (c.ext E) where
  Msg := c.Msg E
  Rnd := c.Rnd E
  enc m r := fun p i => encK c.code (m i) (r i) p
  dec y := if Decodes (c.code.GE E) c.code.e (c.tab y) then
      some (fun i j => Kf.ofE (msgPart c.code (dec (c.code.GE E) c.code.e (c.tab y) i) j),
            fun i t => Kf.ofE (rndPart c.code (dec (c.code.GE E) c.code.e (c.tab y) i) t))
    else none

/-- the budget of a component: the b positions of its code -/
def bud : Finset (c.ext E).Pos → Prop := fun S => S.card ≤ c.code.b

end Comp

namespace Cx
variable (K K' : Cx F)

abbrev ext : ExtSpec := ExtSpec.fam fun a => (K.comp a).ext E
abbrev Msg : Type := ∀ a, (K.comp a).Msg E
abbrev Rnd : Type := ∀ a, (K.comp a).Rnd E

/-- The encoding of a complex: component by component. -/
@[reducible] def enc : Enc (K.ext E) := Enc.fam fun a => (K.comp a).enc E

/-- all codes have the properties of a code with encoder -/
def Props : Prop := ∀ a, (K.comp a).code.Props E

/-- the budget: each component bears the b positions of its code -/
def bud : Finset (K.ext E).Pos → Prop := Enc.budFam fun a => (K.comp a).bud E

/-- The entries of the message: (name, row, place). -/
abbrev Ent : Type := Σ a, (K.comp a).R × Fin (K.comp a).code.msg

variable {E} in
/-- The message, read in E, entry by entry. -/
def ents (m : K.Msg E) : K.Ent → E := fun n => (m n.1 n.2.1 n.2.2).toE

/-- two complexes side by side: names are the sum -/
def sum : Cx F := ⟨K.A ⊕ K'.A, Sum.elim K.comp K'.comp⟩
/-- one more component, named none -/
def add (c : Comp F) : Cx F := ⟨Option K.A, fun o => o.elim c K.comp⟩
/-- the components named by σ -/
def sub {A' : Type} [Fintype A'] [DecidableEq A'] (σ : A' → K.A) : Cx F :=
  ⟨A', fun a' => K.comp (σ a')⟩
/-- one component -/
def one (c : Comp F) : Cx F := ⟨Unit, fun _ => c⟩

end Cx
end

/-! ## The statements -/

namespace Spec

/-- Laws and hiding of a pair and of a family, from those of the components. -/
def laws_prod : Prop :=
  ∀ (E₁ E₂ : ExtSpec) (N₁ : Enc E₁) (N₂ : Enc E₂), N₁.Laws → N₂.Laws → (N₁.prod N₂).Laws

def laws_fam : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (E : A → ExtSpec) (N : ∀ a, Enc (E a)),
    (∀ a, (N a).Laws) → (Enc.fam N).Laws

/-- A family decodes to (m, r) if and only if every component does. -/
def dec_fam_iff : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (E : A → ExtSpec) (N : ∀ a, Enc (E a))
      (y : (ExtSpec.fam E).Str) (w : (Enc.fam N).Wit),
    (Enc.fam N).dec y = some w ↔ ∀ a, (N a).dec (y a) = some (w.1 a, w.2 a)

def hides_prod : Prop :=
  ∀ (E₁ E₂ : ExtSpec) (N₁ : Enc E₁) (N₂ : Enc E₂)
      (b₁ : Finset E₁.Pos → Prop) (b₂ : Finset E₂.Pos → Prop),
    N₁.Hides b₁ → N₂.Hides b₂ → (N₁.prod N₂).Hides (Enc.budProd b₁ b₂)

def hides_fam : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (E : A → ExtSpec)
      (N : ∀ a, Enc (E a)) (b : ∀ a, Finset (E a).Pos → Prop),
    (∀ a, (N a).Hides (b a)) → (Enc.fam N).Hides (Enc.budFam b)

/-- Hiding, as a change of the randomness: the form in which simulators use it. -/
def hides_iff_equiv : Prop :=
  ∀ (E : ExtSpec) (N : Enc E) (bud : Finset E.Pos → Prop),
    N.Hides bud ↔
    ∀ S, bud S →
      ∀ m m', ∃ e : N.Rnd ≃ N.Rnd, ∀ r, ∀ p ∈ S, E.rd (N.enc m r) p = E.rd (N.enc m' (e r)) p

/-- The parts. -/
def part_fst : Prop := ∀ (E₁ E₂ : ExtSpec) (N₁ : Enc E₁) (N₂ : Enc E₂), (Enc.partFst N₁ N₂).Laws
def part_snd : Prop := ∀ (E₁ E₂ : ExtSpec) (N₁ : Enc E₁) (N₂ : Enc E₂), (Enc.partSnd N₁ N₂).Laws
def part_sub : Prop :=
  ∀ (A A' : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] (E : A → ExtSpec)
      (N : ∀ a, Enc (E a)) (σ : A' → A),
    (Enc.partSub N σ).Laws
def part_sub_whole : Prop :=
  ∀ (A A' : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] (E : A → ExtSpec)
      (N : ∀ a, Enc (E a)) (σ : A' → A),
    Function.Surjective σ → (Enc.partSub N σ).Whole
def part_sum : Prop :=
  ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
      (E : A ⊕ B → ExtSpec) (N : ∀ c, Enc (E c)),
    (Enc.partSum N).Whole

section
variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

/-- What decoding of a component means, under `c.code.Props E`: the word, as a table of rows over E,
is within e columns of the table of the codewords of full messages M (any vectors of length k), and
m, r are the parts of M at the places of message and randomness.
In particular a word over F has message and randomness over F. -/
def comp_dec_iff : Prop :=
  ∀ c : Comp F, c.code.Props E →
    ∀ (y : (c.ext E).Str) (m : c.Msg E) (r : c.Rnd E),
      (c.enc E).dec y = some (m, r) ↔
      ∃ M : c.R → Fin c.code.k → E,
        DecodesTo (c.code.GE E) c.code.e (c.tab y) M ∧
        (∀ i j, (m i j).toE = msgPart c.code (M i) j) ∧
        ∀ i t, (r i t).toE = rndPart c.code (M i) t

def comp_laws : Prop := ∀ c : Comp F, c.code.Props E → (c.enc E).Laws

/-- Unique decoding, under `c.code.Props E`: a word that differs from an encoding in at most e
symbols (columns) decodes to its message and randomness. -/
def comp_close : Prop :=
  ∀ c : Comp F, c.code.Props E → ∀ (y : (c.ext E).Str) (m : c.Msg E) (r : c.Rnd E),
    cnt (fun p => y p ≠ (c.enc E).enc m r p) ≤ c.code.e → (c.enc E).dec y = some (m, r)

/-- Under `c.code.Props E`: any b positions of an encoding are uniform, for every message: one row
or many, over F or over E. -/
def comp_uniform : Prop :=
  ∀ c : Comp F, c.code.Props E → ∀ (S : Finset (Fin c.code.n)), S.card ≤ c.code.b → ∀ m : c.Msg E,
    (unif (c.Rnd E)).map ((c.enc E).shows S m) = unif (S → c.R → Kf F E c.overF)

def comp_hides : Prop := ∀ c : Comp F, c.code.Props E → (c.enc E).Hides (c.bud E)

/-- The full code. `full_props`: it has the properties of a code with encoder if the code has;
`comp_full`: then a word decodes under the one if and only if it does under the other, and message
and randomness are the parts of the full message. -/
def full_props : Prop := ∀ C : Code.Enc F, C.Props E → (fullCode C).Props E
def comp_full : Prop :=
  ∀ c : Comp F, c.code.Props E →
    ∀ y : (c.ext E).Str, (c.enc E).dec y =
      ((c.full.enc E).dec y).map fun w =>
        (fun i j => msgPart c.code (w.1 i) j, fun i t => rndPart c.code (w.1 i) t)

/-- The law of an encoding (`Enc.Laws`) for a complex, under `K.Props E`. -/
def cx_laws : Prop := ∀ K : Cx F, K.Props E → (K.enc E).Laws
def cx_hides : Prop := ∀ K : Cx F, K.Props E → (K.enc E).Hides (K.bud E)

end
end Spec

section
variable {E : ExtSpec} (N : Enc E) {X : Type}

/-- The constraint relation of the predicate Φ. -/
def Con (Φ : X → N.Msg → Prop) : X → E.Str → N.Wit → Prop := fun x y w =>
  y = N.enc w.1 w.2 ∧ Φ x w.1

end

/-- The joint at the trivial statement. -/
def trivRels : IOR.Rels Unit Unit extNone Unit :=
  ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩
end Cb
