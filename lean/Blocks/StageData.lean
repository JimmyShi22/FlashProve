-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/StageData.lean: the data that layer 1 needs beside a protocol that is built from blocks
(`Block`, Blocks/Block.lean): numberings, decision procedures, serialisers, widths.

Book-keeping for the compilation of an interactive oracle protocol: definitions, and a few lemmas on
sizes. Layer 1 (the compiler) turns blocks of bits into verifier messages and coins, positions into
leaves of a tree, and symbols and plain parts into strings (Iop/Num.lean, Iop/SerS.lean,
Blocks/Numbering.lean, Blocks/SerS.lean, Blocks/Sizes.lean). For the encoded shape of such a
protocol this file gives `SerS` and `BitsS` (serialisers and their widths, Iop/SerS.lean), with
the proof that the serialisers keep these widths. Here they are given once, by recursion on the
shape.
A shape is the list of a protocol's rounds (`Round`, `Shape`, Iop/Shape.lean). Encoding data
(`REnc` for one round, `EncData` for a shape, Blocks/BlockFront.lean) say of which vectors the
oracle part of each prover message consists and under which code each is sent; `encShape s d` is the
shape with the words in place of the vectors.

Main names:
  `RNum e`: for one round with its encoding data e. It has a numbering of its verifier messages,
    enumerations of its vectors and of its plain parts, and three small numbers with their laws: how
    many scalars the plain part holds, and that the verifier message has at most |E|^chalE · 2^chalB
    values (class `ChalK`, Blocks/ChalK.lean). Sums of them over the rounds of a protocol are
    found by evaluation. It also has, under the names of the same fields of that class: how the
    verifier message is drawn from blocks of bits coordinate by coordinate (`draw`, which may be
    `none`), the number of its blocks (`nb`), and three laws (bias, number of blocks, "put together
    by the rules and by nothing else": Iop/DrawRule.lean).
  `Hon.Dec H`: decision procedures for the public bad set and for the rest of the withheld set of an
    honest side.
  `serSE`, `bitsE`, `withinE`: from these, and enumerations of F and E.
  `Core.Data C t`: numberings and decision procedures of a protocol with its track.
    `CChain.Track.Data`: for chains. `SC.Prover.data`, `PL.Prover.data`: the masked sum-check and
    the product layer.

Nothing is taken by choice: every enumeration and numbering is given, or built by Mathlib's
`FinEnum` from the enumerations that are given. (Some definitions are marked noncomputable: the
mark comes from arguments such as what the verifier of a sum-check computes (`SC.pb`,
Blocks/SumCheckBlock.lean), which Lean's compiler does not take; it is no sign of choice.)

Why: in the sections that have `[Fintype E] [DecidableEq E]` beside `[FinEnum E]`, these two stand
before it: else Lean takes equality on E from the enumeration, and the data speak of another object
than the caller's. Enumerations of index types of a caller are arguments.

Terms: lean/GLOSSARY.md: layer, block, core, shape, plain part, word, honest side, sampler,
track, pad, mask, withheld.
-/
import Blocks.BlockFront
import Blocks.Numbering
import Blocks.SerS
import Blocks.Sizes
import Blocks.ChalK
import Blocks.StageLib
import Blocks.SumCheckStage
import Blocks.ProductStage
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks
open Iop

variable {F E : Type}

/-- The entries of a vector over F or over E can be enumerated. -/
instance Kf.instFinEnum [FinEnum F] [FinEnum E] : ∀ b : Bool, FinEnum (Kf F E b)
  | true => inferInstanceAs (FinEnum F)
  | false => inferInstanceAs (FinEnum E)

/-! ## 1. One round, all rounds -/

/-- The numberings of one round, beside its encoding data; and three small numbers, which the kernel
can evaluate where it cannot evaluate the number of elements of a large type: the plain part holds
at most `plainK` scalars (it has at most |E|^plainK values); the verifier message has at most
|E|^chalE · 2^chalB values (Blocks/ChalK.lean). The numbers are data and name no choice; their laws
are propositions and speak of `Nat.card`, so that they depend on no instance. And the block sampler
of the verifier message (`BS`, Iop/Draw.lean), with the number of its blocks. (`draw` may be
`none`: Blocks/ChalK.lean.) -/
structure RNum {r : Round} (e : REnc F E r) where
  chal : Num r.Chal
  enumA : FinEnum e.A
  enumPlain : FinEnum r.Plain
  plainK : ℕ
  plainK_le : Nat.card r.Plain ≤ Nat.card E ^ plainK
  chalE : ℕ
  chalB : ℕ
  chal_le : Nat.card r.Chal ≤ Nat.card E ^ chalE * 2 ^ chalB
  /-- How the verifier message is drawn from blocks of lam bits, coordinate by coordinate (or
  `none`), and (`nb`) the number of its blocks (Blocks/ChalK.lean: the fields of the same names). -/
  draw : (lam : ℕ) → BS lam E → ℕ → Option (BS lam r.Chal)
  nb : ℕ → ℕ → ℕ → ℕ
  draw_good : ∀ (lam : ℕ) (bE : BS lam E) (sl : ℕ) [DrawBase bE sl] (s : BS lam r.Chal),
    draw lam bE sl = some s → s.Good (kapSl sl ^ s.b)
  draw_b : ∀ (lam : ℕ) (bE : BS lam E) (sl : ℕ) (s : BS lam r.Chal),
    draw lam bE sl = some s → s.b = nb lam bE.b sl
  draw_rule : ∀ (lam : ℕ) (bE : BS lam E) (sl : ℕ) (s : BS lam r.Chal),
    draw lam bE sl = some s → BS.Rule bE sl s

/-- A plain part of scalars k : K holds `IdxK.n K` scalars: `K → E` has at most |E|^(IdxK.n K)
elements. (Blocks/ChalK.lean: `IdxK.n K` is the number of elements of K, in a form that the kernel
can evaluate.) -/
theorem card_scalars_le' (E K : Type) [FinEnum K] [i : IdxK K] :
    Nat.card (K → E) ≤ Nat.card E ^ IdxK.n K := by
  haveI : Finite K := Finite.of_equiv _ (FinEnum.equiv (α := K)).symm
  rw [Nat.card_fun, i.eq]

/-- A plain part of scalars k : K holds `FinEnum.card K` scalars: `K → E` has at most
|E|^(FinEnum.card K) elements. -/
theorem card_scalars_le (E K : Type) [FinEnum K] :
    Nat.card (K → E) ≤ Nat.card E ^ FinEnum.card K := by
  haveI : Finite K := Finite.of_equiv _ (FinEnum.equiv (α := K)).symm
  rw [Nat.card_fun, finEnum_card_eq]

/-- The numberings of all rounds of a shape. -/
def SNum : (s : Shape) → EncData F E s → Type
  | [], _ => Unit
  | _ :: s, (e, d) => RNum e × SNum s d

section
variable [Field F] [Field E] [Algebra F E]

def SNum.app :
    {s t : Shape} → {d : EncData F E s} → {d' : EncData F E t} →
    SNum s d → SNum t d' → SNum (s ++ t) (d.app d')
  | [], _, _, _, _, b => b
  | _ :: _, _, (_, _), _, (a, as), b => (a, SNum.app as b)

variable [FinEnum F] [FinEnum E]

/-- The serialisers of the encoded shape. -/
def serSE : (s : Shape) → (d : EncData F E s) → SNum s d → SerS (encShape s d)
  | [], _, _ => ()
  | r :: s, (e, d), (a, as) =>
      (letI := a.enumA; letI := a.enumPlain
       wordsSer e.A (fun v => (e.code v).n) (fun v => Fin (e.rows v) → Kf F E (e.overF v))
           r.Plain r.Chal (fun _ _ => 0) r.dPlain,
         serSE s d as)

/-- Their widths, in bits (`BitsS`, Iop/SerS.lean); `withinE` proves that the serialisers keep
them. -/
def bitsE : (s : Shape) → (d : EncData F E s) → SNum s d → BitsS (encShape s d)
  | [], _, _ => ()
  | r :: s, (e, d), (a, as) =>
      (letI := a.enumA; letI := a.enumPlain
       wordsBits e.A (fun v => (e.code v).n) (fun v => Fin (e.rows v) → Kf F E (e.overF v)) r.Plain,
         bitsE s d as)

omit [Algebra F E] in
theorem withinE :
    ∀ (s : Shape) (d : EncData F E s) (n : SNum s d),
      SerS.Within (encShape s d) (serSE s d n) (bitsE s d n)
  | [], _, _ => trivial
  | r :: s, (e, d), (a, as) =>
      within_cons (letI := a.enumA; letI := a.enumPlain
        wordsSer_within e.A (fun v => (e.code v).n) (fun v => Fin (e.rows v) → Kf F E (e.overF v)) r.Plain r.Chal (fun _ _ => 0) r.dPlain) (withinE s d as)

end

/-! ## 2. Decision procedures for the withheld sets -/

section Dec

variable {Xi Yi Xo Yo X₁ Y₁ X₂ Y₂ X₃ Y₃ P Ii Io I₁ I₂ I₃ : Type}

/-- Decision procedures for the public bad set and for the rest of the withheld set of an honest
side. (`Hon.Bad`, `Hon.Win`, Blocks/BlockHon.lean.) -/
structure Hon.Dec {B : Block Xi Yi Xo Yo} (H : Hon B P E Ii Io) where
  bad : ∀ ρ, Decidable (ρ ∈ H.Bad)
  win : ∀ a ρ, Decidable (ρ ∈ H.Win a)

namespace Hon.Dec

def seq {B₁ : Block X₁ Y₁ X₂ Y₂} {B₂ : Block X₂ Y₂ X₃ Y₃} {H₁ : Hon B₁ P E I₁ I₂}
    {H₂ : Hon B₂ P E I₂ I₃} (D₁ : H₁.Dec) (D₂ : H₂.Dec) : (H₁.seq H₂).Dec where
  bad ρ := @instDecidableOr _ _ (D₁.bad (Rho.fst ρ)) (D₂.bad (Rho.snd (s := B₁.shape) ρ))
  win a ρ := @instDecidableOr
    _ _ (D₁.win a (Rho.fst ρ)) (D₂.win (H₁.next a (Rho.fst ρ)) (Rho.snd (s := B₁.shape) ρ))

def pure (f : Xi → Option Xo) (g : Yi → Yo) (nx : Ii → Io) :
    (Hon.pure (P := P) (E := E) f g nx).Dec where
  bad _ := isFalse fun h => h
  win _ _ := isFalse fun h => h

def on {X Y X' Y' J J' : Type} {B : Block Xi Yi Xo Yo} {H : Hon B P E Ii Io}
    (D : H.Dec) (gx : X → Xi) (px : X → Xo → X') (gy : Y → Yi) (py : Y → Yo → Y')
    (ga : J → Ii) (pa : J → Io → J') :
    (H.on gx px gy py ga pa).Dec where
  bad := D.bad
  win a := D.win (ga a)

def one {r : Round} {pb : Xi → r.Chal → r.Plain → Option Xo} {im : Yi → r.Msg → r.Chal → Yo}
    (msg : Ii → (P → E) → r.Msg) (nx : Ii → r.Chal → Io) (Bd : Set r.Chal) (Wn : Ii → Set r.Chal)
    (dB : ∀ c, Decidable (c ∈ Bd)) (dW : ∀ a c, Decidable (c ∈ Wn a)) :
    (Hon.one (pb := pb) (im := im) msg nx Bd Wn).Dec where
  bad ρ := dB ρ.1
  win a ρ := dW a ρ.1

/-- One round of which nothing is withheld. -/
def oneEmpty {r : Round} {pb : Xi → r.Chal → r.Plain → Option Xo} {im : Yi → r.Msg → r.Chal → Yo}
    (msg : Ii → (P → E) → r.Msg) (nx : Ii → r.Chal → Io) :
    (Hon.one (pb := pb) (im := im) msg nx ∅ fun _ => ∅).Dec :=
  one msg nx ∅ (fun _ => ∅) (fun _ => isFalse fun h => h) fun _ _ => isFalse fun h => h

def pads [AddCommGroup E] {n : ℕ} (idx : Fin n → P) :
    (Hon.pads (E := E) (Ii := Ii) Xi Yi idx).Dec :=
  oneEmpty (r := Block.padRound E n) (pb := fun (x : Xi) _ _ => some x)
    (im := fun (y : Yi) m _ => (y, m.1 () 0))
    (fun _ π => (fun _ _ j => π (idx j), fun k => Empty.elim k)) fun a _ => a

def sample [AddCommGroup E] {C : Type} [Fintype C] [Nonempty C] (ok : C → Bool) (nx : Ii → C → Io) :
    (Hon.sample (P := P) (E := E) Xi Yi ok nx).Dec :=
  one (r := Block.chalRound E C) (pb := fun (x : Xi) c _ => if ok c then some (x, c) else none)
    (im := fun (y : Yi) _ _ => y) (fun _ _ => (fun a => Empty.elim a, fun k => Empty.elim k)) nx
    {c | ok c = false} (fun _ => ∅) (fun c => inferInstanceAs (Decidable (ok c = false)))
    fun _ _ => isFalse fun h => h

end Hon.Dec

end Dec

/-! ## 3. What the verifier opens in the words of the vectors, round by round -/

section Opens

variable [Field F] [Field E] [Algebra F E]

/-- For each round the sum of the numbers q a of its vectors a. It is the bound that fits if in a
round at most q a positions of the word of each vector a are opened. -/
def opensE : (s : Shape) → (d : EncData F E s) → OpenList (encShape s d)
  | [], _ => ()
  | _ :: s, (e, d) => (∑ a, e.q a, opensE s d)

end Opens

/-! ## 4. The rounds of the library -/

section Lib

variable [Field F] [Field E] [Algebra F E] [FinEnum E]

/-- A round with vectors a : A, scalars k : K and a verifier message in C (`REnc.ofVKc`,
Blocks/BlockFront.lean). The numbers and the sampler are those of the classes `IdxK K` and
`ChalK E C`; so too in the four definitions that follow. -/
def RNum.ofVKc (A : Type) [Fintype A] [DecidableEq A] [FinEnum A] (overF : A → Bool)
    (code : A → Code.Enc F) (rows mrow : A → ℕ) (role : A → Role) (q : A → ℕ) (len : A → ℕ)
    (hlen : ∀ a, (code a).msg = len a) [∀ a, Nonempty (Fin (code a).n)] (K C : Type) [FinEnum K]
    [IdxK K] [Fintype C] [Nonempty C] [FinEnum C] [ChalK E C] :
    RNum (REnc.ofVKc E A overF code rows mrow role q len hlen K C) where
  chal := Num.ofFinEnum C
  enumA := inferInstanceAs (FinEnum A)
  enumPlain := inferInstanceAs (FinEnum (K → E))
  plainK := IdxK.n K
  plainK_le := card_scalars_le' E K
  chalE := ChalK.kE E C
  chalB := ChalK.kb E C
  chal_le := ChalK.le
  draw := ChalK.draw
  nb := ChalK.nb E C
  draw_good := ChalK.draw_good
  draw_b := ChalK.draw_b
  draw_rule := ChalK.draw_rule

def RNum.ofVK (A : Type) [Fintype A] [DecidableEq A] [FinEnum A] (overF : A → Bool)
    (code : A → Code.Enc F) (rows mrow : A → ℕ) (role : A → Role) (q : A → ℕ)
    [∀ a, Nonempty (Fin (code a).n)] (K C : Type) [FinEnum K] [IdxK K] [Fintype C] [Nonempty C]
    [FinEnum C] [ChalK E C] :
    RNum (REnc.ofVK E A overF code rows mrow role q K C) where
  chal := Num.ofFinEnum C
  enumA := inferInstanceAs (FinEnum A)
  enumPlain := inferInstanceAs (FinEnum (K → E))
  plainK := IdxK.n K
  plainK_le := card_scalars_le' E K
  chalE := ChalK.kE E C
  chalB := ChalK.kb E C
  chal_le := ChalK.le
  draw := ChalK.draw
  nb := ChalK.nb E C
  draw_good := ChalK.draw_good
  draw_b := ChalK.draw_b
  draw_rule := ChalK.draw_rule

def RNum.ofV (A : Type) [Fintype A] [DecidableEq A] [FinEnum A] (code : A → Code.Enc F)
    (rows mrow : A → ℕ) (role : A → Role) (q : A → ℕ) [∀ a, Nonempty (Fin (code a).n)] (K C : Type)
    [FinEnum K] [IdxK K] [Fintype C] [Nonempty C] [FinEnum C] [ChalK E C] :
    RNum (REnc.ofV E A code rows mrow role q K C) where
  chal := Num.ofFinEnum C
  enumA := inferInstanceAs (FinEnum A)
  enumPlain := inferInstanceAs (FinEnum (K → E))
  plainK := IdxK.n K
  plainK_le := card_scalars_le' E K
  chalE := ChalK.kE E C
  chalB := ChalK.kb E C
  chal_le := ChalK.le
  draw := ChalK.draw
  nb := ChalK.nb E C
  draw_good := ChalK.draw_good
  draw_b := ChalK.draw_b
  draw_rule := ChalK.draw_rule

/-- A library round whose vectors are enumerated by an argument (an enumeration of a caller's index
type is no instance). -/
def RNum.ofEnum {A : Type} {overF : A → Bool} {rows len : A → ℕ} {K C : Type} [FinEnum K] [IdxK K]
    [Fintype C] [Nonempty C] [FinEnum C] [ChalK E C]
    (e : REnc F E (vRoundK E F A overF rows len K C)) (eA : FinEnum e.A) : RNum e where
  chal := Num.ofFinEnum C
  enumA := eA
  enumPlain := inferInstanceAs (FinEnum (K → E))
  plainK := IdxK.n K
  plainK_le := card_scalars_le' E K
  chalE := ChalK.kE E C
  chalB := ChalK.kb E C
  chal_le := ChalK.le
  draw := ChalK.draw
  nb := ChalK.nb E C
  draw_good := ChalK.draw_good
  draw_b := ChalK.draw_b
  draw_rule := ChalK.draw_rule

/-- A round without vectors. -/
def RNum.none (F : Type) [Field F] [Algebra F E] (K C : Type) [FinEnum K] [IdxK K] [Fintype C]
    [Nonempty C] [FinEnum C] [ChalK E C] : RNum (REnc.none E F K C) where
  chal := Num.ofFinEnum C
  enumA := inferInstanceAs (FinEnum Empty)
  enumPlain := inferInstanceAs (FinEnum (K → E))
  plainK := IdxK.n K
  plainK_le := card_scalars_le' E K
  chalE := ChalK.kE E C
  chalB := ChalK.kb E C
  chal_le := ChalK.le
  draw := ChalK.draw
  nb := ChalK.nb E C
  draw_good := ChalK.draw_good
  draw_b := ChalK.draw_b
  draw_rule := ChalK.draw_rule

end Lib

/-! ## 5. Protocols of stages (`Core`, `Stage`, Blocks/Stage.lean) -/

section Core

variable {P : Type} [Field F] [Field E] [Algebra F E] {a b c : Sorts}

/-- The data of a protocol with its track: the numberings of its rounds, and the decision procedures
of its honest side. -/
structure Core.Data (C : Core P E a b) {ra : Reads F E a}
    {rb : Reads F E b} (t : C.Track ra rb) where
  num : SNum C.B.shape t.d
  dec : C.H.Dec

namespace Core.Data

/-- Two protocols in a row. -/
def seq {C₁ : Core P E a b} {C₂ : Core P E b c} {ra : Reads F E a}
    {rb : Reads F E b} {rc : Reads F E c} {t₁ : C₁.Track ra rb}
    {t₂ : C₂.Track rb rc} (D₁ : C₁.Data t₁) (D₂ : C₂.Data t₂) :
    (C₁.seq C₂).Data (t₁.seq t₂) where
  num := SNum.app D₁.num D₂.num
  dec := D₁.dec.seq D₂.dec

/-- The protocol without rounds. -/
def id (ra : Reads F E a) : (Core.id (P := P) (E := E) a).Data (Core.Track.id ra) where
  num := ()
  dec := Hon.Dec.pure _ _ _

def pure (f : a.X → Option b.X) (g : a.Y → b.Y) (nx : a.I → b.I) (ra : Reads F E a)
    (rb : Reads F E b) (σ : rb.N → ra.N) :
    (Core.pure (P := P) (E := E) f g nx).Data (Core.trackPure f g nx ra rb σ) where
  num := ()
  dec := Hon.Dec.pure _ _ _

/-- Vectors for a hidden quantity. (`Core.nameVec`, Blocks/StageLib.lean.) -/
def nameVec {r : Round} {e : REnc F E r} (n : RNum e) (p₀ : r.Plain)
    (msg : a.I → r.Orc) (ra : Reads F E a) :
    (Core.nameVec (P := P) (E := E) a r p₀ msg).Data (Core.trackNameVec e p₀ msg ra) where
  num := (n, ())
  dec := Hon.Dec.oneEmpty (pb := fun (x : a.X) _ _ => some x) (im := fun (y : a.Y) m _ => (y, m.1))
    (fun s _ => (msg s, p₀)) fun s _ => s

/-- One prover message of vectors. -/
def send {X' Z : Type} {r : Round} {e : REnc F E r} (n : RNum e) (p₀ : r.Plain)
    (msg : a.I → (P → E) → r.Orc) (φ : r.Orc → Z) (fx : a.X → X') (ra : Reads F E a)
    (rb : Reads F E ⟨X', a.Y × Z, a.I⟩) (src : rb.N → ra.N ⊕ (e.A × ℕ × ℕ)) :
    (Core.send a X' Z r p₀ msg φ fx).Data (Core.trackSend e p₀ msg φ fx ra rb src) where
  num := (n, ())
  dec := Hon.Dec.oneEmpty (pb := fun (x : a.X) _ _ => some (fx x))
    (im := fun (y : a.Y) m _ => (y, φ m.1)) (fun s π => (msg s π, p₀)) fun s _ => s

variable [FinEnum E]

/-- A pad vector. (`Core.pads`, Blocks/StageLib.lean.) -/
def pads (C : Code.Enc F) [Nonempty (Fin C.n)] (q : ℕ) (idx : Fin C.msg → P) (ra : Reads F E a) :
    (Core.pads (E := E) a idx).Data (Core.trackPads C q idx ra) where
  num := (RNum.ofV Unit (fun _ => C) (fun _ => 1) (fun _ => 0) (fun _ => Role.pad)
      (fun _ => q) Empty Unit,
    ())
  dec := Hon.Dec.pads idx

/-- Masked scalars. (`Core.nameScalars`, Blocks/StageLib.lean.) -/
def nameScalars {K : Type} [FinEnum K] [IdxK K] (idx : K → P)
    (val : a.I → K → E) (ra : Reads F E a) :
    (Core.nameScalars (E := E) a idx val).Data (Core.trackNameScalars idx val ra) where
  num := (RNum.none F K Unit, ())
  dec := Hon.Dec.oneEmpty (r := Stage.scRound E K) (pb := fun (x : a.X) _ p => some (x, p))
    (im := fun (y : a.Y) _ _ => y)
    (fun s π => (fun e => Empty.elim e, fun k => val s k + π (idx k))) fun s _ => s

/-- A challenge. -/
def sample {I' C : Type} [Fintype C] [Nonempty C] [FinEnum C] [ChalK E C] (ok : C → Bool)
    (nx : a.I → C → I') (ra : Reads F E a) :
    (Core.sample (P := P) (E := E) a I' C ok nx).Data (Core.trackSample ok nx ra) where
  num := (RNum.none F Empty C, ())
  dec := Hon.Dec.one _ _ _ _ (fun c => inferInstanceAs (Decidable (ok c = false)))
    fun _ _ => isFalse fun h => h

variable {a' b' : Sorts}

/-- A protocol that acts on a part of a larger statement. -/
def on {C : Core P E a b} {ra : Reads F E a} {rb : Reads F E b} {t : C.Track ra rb} (D : C.Data t)
    (gx : a'.X → a.X) (px : a'.X → b.X → b'.X) (gy : a'.Y → a.Y) (py : a'.Y → b.Y → b'.Y)
    (ga : a'.I → a.I) (pa : a'.I → b.I → b'.I) (ra' : Reads F E a') (rb' : Reads F E b')
    (κ : ra.N → ra'.N) (σ : rb'.N → ra'.N ⊕ rb.N) :
    (C.on gx px gy py ga pa).Data (t.on gx px gy py ga pa ra' rb' κ σ) where
  num := D.num
  dec := D.dec.on gx px gy py ga pa

end Core.Data

/-- Any number of protocols in a row: the data. -/
inductive CChain.Track.Data :
    {a b : Sorts} → {t : CChain P E a b} → {ra : Reads F E a} → {rb : Reads F E b} →
    CChain.Track t ra rb → Type 1
  | nil {a : Sorts} (ra : Reads F E a) : CChain.Track.Data (.nil (P := P) ra)
  | cons {a b c : Sorts} {C : Core P E a b} {t : CChain P E b c} {ra : Reads F E a}
      {rb : Reads F E b} {rc : Reads F E c} {hC : C.Track ra rb} {ht : CChain.Track t rb rc}
      (D : C.Data hC) (Ds : CChain.Track.Data ht) : CChain.Track.Data (.cons hC ht)

/-- The data of the chain as one protocol. -/
def CChain.Track.Data.core :
    {a b : Sorts} → {t : CChain P E a b} → {ra : Reads F E a} → {rb : Reads F E b} →
    {k : CChain.Track t ra rb} → CChain.Track.Data k → t.core.Data k.core
  | _, _, _, _, _, _, .nil ra => Core.Data.id ra
  | _, _, _, _, _, _, .cons D Ds => D.seq Ds.core

end Core

/-! ## 6. The masked sum-check -/

namespace SC

variable {Y P Ξ ι A : Type} [Field E] [Fintype E] [DecidableEq E] [DecidableEq ι] {S : SC E Y P Ξ ι}
  [Field F] [Algebra F E] [FinEnum E]

variable (S) in
/-- The numberings of its rounds; the round that binds the variable i has e i + 1 scalars and a
challenge in E. -/
def numSc : (l : List ι) → SNum (S.sc l).shape (encSc S F l)
  | [] => ()
  | i :: l => (RNum.none F (Fin (S.e i + 1)) E, numSc l)

/-- The public bad set "a challenge by which a later block divides is 0" is decided. -/
def Prover.decSc (H : S.Prover A) : (l l' : List ι) → (H.sc l l').Dec
  | [], _ => Hon.Dec.pure _ _ _
  | i :: l, l' =>
      Hon.Dec.seq (H₁ := H.round i (l ++ l')) (H₂ := H.sc l l')
        (Hon.Dec.one (r := S.rd i) (pb := S.pb i) (im := fun (y : Y) _ _ => y) (H.msg i (l ++ l'))
          (fun s r => (s.1, Function.update s.2 i r)) {r | S.nzv i = true ∧ r = 0} (fun _ => ∅)
          (fun r => inferInstanceAs (Decidable (S.nzv i = true ∧ r = 0)))
          fun _ _ => isFalse fun h => h) (decSc H l l')

variable [Fintype P] [DecidableEq P]

/-- The data of the masked sum-check. -/
def Prover.data (H : S.Prover A) (l : List ι) (ra : Reads F E ⟨S.X, Y, A × (ι → E)⟩) :
    (H.core l).Data (H.track l ra) where
  num := numSc (F := F) S l
  dec := H.decSc l []

end SC

/-! ## 6b. The product layer -/

namespace PL.Prover

variable {Y P N Ξ A : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] {L : PL E Y P N Ξ} (H : L.Prover A) [Field F] [Algebra F E] [FinEnum E]
  [Fintype P] [DecidableEq P]

variable (L F) in
/-- The numberings of the rounds of a product layer: no round; the rounds of its sum-check; the
round (v0, v1; ζ). -/
def numPl :
    SNum L.pl.shape
      (EncData.app (s := L.init.shape) PUnit.unit
        (EncData.app (s := (L.sc.sc L.ord).shape) (t := L.fin.shape)
          (SC.encSc L.sc F L.ord) (REnc.none E F Bool E, PUnit.unit))) :=
  SNum.app (s := L.init.shape) (d := PUnit.unit) ()
    (SNum.app (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) (d := SC.encSc L.sc F L.ord)
      (d' := (REnc.none E F Bool E, PUnit.unit)) (SC.numSc L.sc L.ord) (RNum.none F Bool E, ()))

/-- Of the round (v0, v1; ζ) the values of ζ that fail the public test are withheld. (The test:
`PL.okE`, Blocks/ProductBlock.lean.) -/
def decPl : H.pl.Dec :=
  Hon.Dec.seq (H₁ := Hon.pure (fun x : PLX N E Ξ => some (x.C, fun _ => 0, (x.pt, x.led, x.pub)))
        id fun a => (a, fun _ => 0))
    (H₂ := (H.scP.sc L.ord []).seq H.fin) (Hon.Dec.pure _ _ _)
    (Hon.Dec.seq (H₁ := H.scP.sc L.ord []) (H₂ := H.fin) (H.scP.decSc L.ord [])
      (Hon.Dec.one (r := rV E)
        (pb := fun x ζ s => if L.okE ζ && x.2.2.2.1.wf then some (L.out x ζ s) else none)
        (im := fun (y : Y) _ _ => y)
        (fun s π => (fun e => Empty.elim e, fun b => H.vval s b + π (L.pv b)))
        (fun s ζ => H.set s.1 (consPt ζ s.2) (H.vval s false) (H.vval s true))
        {ζ | L.okE ζ = false} (fun _ => ∅)
        (fun ζ => inferInstanceAs (Decidable (L.okE ζ = false))) fun _ _ => isFalse fun h => h))

/-- The data of the product layer. -/
def data (e : ℕ) (ra : Reads F E ⟨PLX N E Ξ, Y, A⟩) : H.core.Data (H.track e ra) where
  num := numPl F L
  dec := H.decPl

end PL.Prover

end Blocks
