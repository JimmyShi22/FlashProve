-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/BlockHon.lean: the honest side of a block (Blocks/Block.lean). Pointwise completeness
(`Hon.AccOn`) and the form of honest-verifier zero knowledge, for what the verifier reads in full,
that composes (`Hon.Masked`), each with its composition theorem.

Masked form: every scalar is a value plus a pad of its own, and the value reads only pads that come
earlier in one fixed order.

The pads. All blocks of one protocol share one family of pads π : P → E, which is the honest
prover's randomness on this floor. A pad vector is a slice of the family that the block `pads` sends
(Blocks/BlockLib.lean). For soundness the sent pad vectors are part of the implicit statement;
here they are coins.

The honest state. What the honest prover hands from one block to the next (index, instance, trace,
the points so far) is a function of its input and of the verifier's randomness alone: it does not
hold the coins. So the sets `Win` of later blocks do not depend on coins.

Masked, semantically. A block masks with the pads in U and reads the pads in D if (in both, after
`V a → ρ ∉ H.withheld a →`)
  (reads) its plain parts depend on π only through the entries in D, and
  (law)   for every value of the entries outside U, the plain parts, over uniform entries in U, have
          a law Sim ρ that depends on nothing else.
A scalar value + own pad has this form (Blocks/BlockLib.lean). Two blocks in a row are masked with
U₁ ∪ U₂ if U₁ and U₂ are disjoint and one of the two blocks does not read the pads with which the
other masks (the triangular order of masked form), and if `H₁.Keeps V₁ V₂`. (not all hypotheses are
named here: see `Masked.comp`, `Masked.comp'`)

Notation: `B`: a `Block Xi Yi Xo Yo` (Blocks/Block.lean): Xi, Yi are the explicit and the implicit
part of the input statement, Xo, Yo those of the output statement;
`B.pub : Xi → Rho shape → Plains shape → Option Xo`: the verifier; none = reject;
`B.imp : Yi → Tr shape → Yo`: see the field's docstring at `Block`; `Rho`, `Tr`, `Plains`,
`Strat s β` (Iop/Shape.lean): the verifier's randomness of a whole execution; full transcripts; the
plain parts of all prover messages; deterministic prover strategies that end with a result in β;
`H.Bad : Set (Rho B.shape)`, `H.Win : Ii → Set (Rho B.shape)`: see the fields' docstrings at `Hon`.

Limits: (1) The two rules of composition cover "all pads of the first block come before all pads of
the second" and the reverse, not an order of the pads that interleaves the two blocks; and
`masked_one` (Blocks/BlockLib.lean) does not allow a value that reads the pad of another scalar of
the same message.
(2) The simulator of a block sees the block's own ρ and nothing else, and the simulators of two
    blocks draw independently.
That suffices as long as every plain element is a masked scalar or a constant; a plain element that
is sent unmasked and depends on x or on earlier messages cannot be expressed.

Prob/Linear.lean has the uniformity of additive maps that the splitting of the pads uses.
Terms: lean/GLOSSARY.md.
-/
import Blocks.Block
import Prob.Linear
noncomputable section -- Lean tags what it cannot compile

namespace Blocks
open Iop Prob

/-! ## A strategy that ends with a function of the verifier's randomness -/

/-- The strategy σ, ending with f ρ. -/
def tag : {s : Shape} → {β : Type} → Strat s Unit → (Rho s → β) → Strat s β
  | [], _, _, f => f ()
  | _ :: _, _, (m, k), f => (m, fun c => tag (k c) fun ρ => f (c, ρ))

theorem run_tag : ∀ {s : Shape} {β : Type} (σ : Strat s Unit) (f : Rho s → β) (ρ : Rho s),
    Strat.run (tag σ f) ρ = ((Strat.run σ ρ).1, f ρ)
  | [], _, _, _, () => rfl
  | _ :: _, _, (m, k), f, (c, ρ) => by
      have h := run_tag (k c) (fun ρ => f (c, ρ)) ρ
      show ((m, c, (Strat.run (tag (k c) fun ρ => f (c, ρ)) ρ).1),
          (Strat.run (tag (k c) fun ρ => f (c, ρ)) ρ).2) =
        ((m, c, (Strat.run (k c) ρ).1), f (c, ρ))
      rw [h]

/-! ## The honest side -/

/-- The honest side of a block: the data. P indexes the pads, E is the type of their values; Ii and
Io are the honest prover's states before and after. -/
structure Hon {Xi Yi Xo Yo : Type} (B : Block Xi Yi Xo Yo) (P E Ii Io : Type) where
  /-- the honest prover; where it has no honest message it sends substitutes -/
  strat : Ii → (P → E) → Strat B.shape Unit
  /-- the state for what follows: no coins -/
  next : Ii → Rho B.shape → Io
  /-- the public bad set: no argument but the block's own ρ -/
  Bad : Set (Rho B.shape)
  /-- the rest of the withheld set, which may depend on the state -/
  Win : Ii → Set (Rho B.shape)

namespace Hon

variable {Xi Yi Xo Yo X₁ Y₁ X₂ Y₂ X₃ Y₃ P E Ii Io I₁ I₂ I₃ : Type}

/-- The transcript of the honest prover. -/
def tr {B : Block Xi Yi Xo Yo} (H : Hon B P E Ii Io) (a : Ii) (π : P → E) (ρ : Rho B.shape) :
    Tr B.shape :=
  ((H.strat a π).run ρ).1

theorem rho_tr {B : Block Xi Yi Xo Yo} (H : Hon B P E Ii Io) (a : Ii)
    (π : P → E) (ρ : Rho B.shape) : (H.tr a π ρ).rho = ρ :=
  Strat.rho_run _ _

/-- The withheld set (exactly: `H.Bad ∪ H.Win a`). This file does not bound its probability (among
the conditions on it: `Stage.Props.prBad`, `prWin`, Blocks/Stage.lean). -/
def withheld {B : Block Xi Yi Xo Yo} (H : Hon B P E Ii Io) (a : Ii) : Set (Rho B.shape) :=
  H.Bad ∪ H.Win a

/-- The first honest prover, then the second on the state that the first hands on, with the same
pads. The withheld sets unite. -/
@[reducible] def seq {B₁ : Block X₁ Y₁ X₂ Y₂} {B₂ : Block X₂ Y₂ X₃ Y₃}
    (H₁ : Hon B₁ P E I₁ I₂) (H₂ : Hon B₂ P E I₂ I₃) : Hon (B₁.seq B₂) P E I₁ I₃ where
  strat a π := Strat.bind (tag (H₁.strat a π) (H₁.next a)) fun a' => H₂.strat a' π
  next a ρ := H₂.next (H₁.next a (Rho.fst ρ)) (Rho.snd (s := B₁.shape) ρ)
  Bad := Rho.cylFst B₂.shape H₁.Bad ∪ Rho.cylSnd B₁.shape H₂.Bad
  Win a := {ρ | Rho.fst ρ ∈ H₁.Win a ∨ Rho.snd (s := B₁.shape) ρ ∈ H₂.Win (H₁.next a (Rho.fst ρ))}

theorem tr_seq {B₁ : Block X₁ Y₁ X₂ Y₂} {B₂ : Block X₂ Y₂ X₃ Y₃} (H₁ : Hon B₁ P E I₁ I₂)
    (H₂ : Hon B₂ P E I₂ I₃) (a : I₁) (π : P → E) (ρ : Rho (B₁.shape ++ B₂.shape)) :
    (H₁.seq H₂).tr a π ρ =
      Tr.app (H₁.tr a π (Rho.fst ρ))
        (H₂.tr (H₁.next a (Rho.fst ρ)) π (Rho.snd (s := B₁.shape) ρ)) := by
  show (Strat.run (Strat.bind (tag (H₁.strat a π) (H₁.next a)) fun a' => H₂.strat a' π) ρ).1 = _
  rw [Strat.run_bind, run_tag]
  rfl

theorem not_withheld_seq {B₁ : Block X₁ Y₁ X₂ Y₂} {B₂ : Block X₂ Y₂ X₃ Y₃}
    {H₁ : Hon B₁ P E I₁ I₂} {H₂ : Hon B₂ P E I₂ I₃} {a : I₁}
    {ρ : Rho (B₁.shape ++ B₂.shape)} (h : ρ ∉ (H₁.seq H₂).withheld a) :
    Rho.fst ρ ∉ H₁.withheld a ∧ Rho.snd (s := B₁.shape) ρ ∉ H₂.withheld (H₁.next a (Rho.fst ρ)) :=
  ⟨fun h' => h (h'.elim (fun hb => Or.inl (Or.inl hb)) fun hw => Or.inr (Or.inl hw)),
    fun h' => h (h'.elim (fun hb => Or.inl (Or.inr hb)) fun hw => Or.inr (Or.inr hw))⟩

/-- The honest side of a block without rounds. -/
@[reducible] def pure (f : Xi → Option Xo) (g : Yi → Yo) (nx : Ii → Io) :
    Hon (Block.pure f g) P E Ii Io where
  strat _ _ := ()
  next a _ := nx a
  Bad := ∅
  Win _ := ∅

/-- The honest side of a block that acts on a part of a larger statement: the state has a lens of
its own. -/
@[reducible] def on {X Y X' Y' J J' : Type} {B : Block Xi Yi Xo Yo}
    (H : Hon B P E Ii Io) (gx : X → Xi) (px : X → Xo → X') (gy : Y → Yi)
    (py : Y → Yo → Y') (ga : J → Ii) (pa : J → Io → J') :
    Hon (B.on gx px gy py) P E J J' where
  strat a π := H.strat (ga a) π
  next a ρ := pa a (H.next (ga a) ρ)
  Bad := H.Bad
  Win a := H.Win (ga a)

/-! ## Pointwise completeness -/

/-- Pointwise completeness. Hi a π x y says that (x, y) is the statement that belongs to the honest
state a under the pads π, and that it is true; Ho likewise after the block. At every ρ outside the
withheld set and for all pads the verifier does not reject, and its output with the extended
implicit part belongs to the next honest state. -/
def AccOn {B : Block Xi Yi Xo Yo} (H : Hon B P E Ii Io)
    (Hi : Ii → (P → E) → Xi → Yi → Prop) (Ho : Io → (P → E) → Xo → Yo → Prop) : Prop :=
  ∀ a π x y ρ, Hi a π x y → ρ ∉ H.withheld a →
    ∃ xo, B.pub x ρ (H.tr a π ρ).plains = some xo ∧ Ho (H.next a ρ) π xo (B.imp y (H.tr a π ρ))

/-- Sequential composition of completeness: the withheld sets unite. -/
theorem AccOn.comp {B₁ : Block X₁ Y₁ X₂ Y₂} {B₂ : Block X₂ Y₂ X₃ Y₃} {H₁ : Hon B₁ P E I₁ I₂}
    {H₂ : Hon B₂ P E I₂ I₃} {R₁ : I₁ → (P → E) → X₁ → Y₁ → Prop}
    {R₂ : I₂ → (P → E) → X₂ → Y₂ → Prop} {R₃ : I₃ → (P → E) → X₃ → Y₃ → Prop}
    (h₁ : H₁.AccOn R₁ R₂) (h₂ : H₂.AccOn R₂ R₃) : (H₁.seq H₂).AccOn R₁ R₃ := by
  intro a π x y ρ hi hρ
  obtain ⟨hρ₁, hρ₂⟩ := not_withheld_seq hρ
  obtain ⟨x', hx', hm⟩ := h₁ a π x y _ hi hρ₁
  obtain ⟨xo, hxo, ho⟩ := h₂ _ π x' _ _ hm hρ₂
  refine ⟨xo, ?_, ?_⟩
  · show (B₁.pub x (Rho.fst ρ) (plFst ((H₁.seq H₂).tr a π ρ).plains)).bind
        (fun x' =>
          B₂.pub x' (Rho.snd (s := B₁.shape) ρ)
            (plSnd (s := B₁.shape) ((H₁.seq H₂).tr a π ρ).plains)) = some xo
    rw [tr_seq, plains_app, plFst_app, plSnd_app, hx']
    exact hxo
  · show R₃ _ π xo
      (B₂.imp (B₁.imp y (Tr.fst ((H₁.seq H₂).tr a π ρ)))
        (Tr.snd (s := B₁.shape) ((H₁.seq H₂).tr a π ρ)))
    rw [tr_seq, Tr.fst_app, Tr.snd_app]
    exact ho

/-- Consequence. -/
theorem AccOn.conseq {B : Block Xi Yi Xo Yo} {H : Hon B P E Ii Io}
    {Hi Hi' : Ii → (P → E) → Xi → Yi → Prop} {Ho Ho' : Io → (P → E) → Xo → Yo → Prop}
    (h : H.AccOn Hi Ho) (hi : ∀ a π x y, Hi' a π x y → Hi a π x y)
    (ho : ∀ a π x y, Ho a π x y → Ho' a π x y) :
    H.AccOn Hi' Ho' := fun a π x y ρ h' hρ =>
  let ⟨xo, hxo, hh⟩ := h a π x y ρ (hi a π x y h') hρ
  ⟨xo, hxo, ho _ _ _ _ hh⟩

/-- Completeness of a block without rounds. -/
theorem accOn_pure {f : Xi → Option Xo} {g : Yi → Yo} {nx : Ii → Io}
    {Hi : Ii → (P → E) → Xi → Yi → Prop} {Ho : Io → (P → E) → Xo → Yo → Prop}
    (h : ∀ a π x y, Hi a π x y → ∃ xo, f x = some xo ∧ Ho (nx a) π xo (g y)) :
    (Hon.pure (P := P) (E := E) f g nx).AccOn Hi Ho :=
  fun a π x y _ hi _ => h a π x y hi

/-- Completeness on a part of a larger statement, from one forward step on statements. (not all
hypotheses are named here: see the statement below) -/
theorem AccOn.on {X Y X' Y' J J' : Type} {B : Block Xi Yi Xo Yo} {H : Hon B P E Ii Io}
    {Hi : Ii → (P → E) → Xi → Yi → Prop} {Ho : Io → (P → E) → Xo → Yo → Prop} (h : H.AccOn Hi Ho)
    {gx : X → Xi} {px : X → Xo → X'} {gy : Y → Yi} {py : Y → Yo → Y'} {ga : J → Ii}
    {pa : J → Io → J'} {R : J → (P → E) → X → Y → Prop} {R' : J' → (P → E) → X' → Y' → Prop}
    (hfwd : ∀ a π x y, R a π x y →
      Hi (ga a) π (gx x) (gy y) ∧ ∀ ao xo yo, Ho ao π xo yo → R' (pa a ao) π (px x xo) (py y yo)) :
    (H.on gx px gy py ga pa).AccOn R R' := by
  intro a π x y ρ hR hρ
  obtain ⟨xo, hxo, ho⟩ := h (ga a) π (gx x) (gy y) ρ (hfwd a π x y hR).1 hρ
  refine ⟨px x xo, ?_, (hfwd a π x y hR).2 _ _ _ ho⟩
  show (B.pub (gx x) ρ (H.tr (ga a) π ρ).plains).map (px x) = some (px x xo)
  rw [hxo]
  rfl

/-- The same with the actual output in the forward step. -/
theorem AccOn.on' {X Y X' Y' J J' : Type} {B : Block Xi Yi Xo Yo} {H : Hon B P E Ii Io}
    {Hi : Ii → (P → E) → Xi → Yi → Prop} {Ho : Io → (P → E) → Xo → Yo → Prop} (h : H.AccOn Hi Ho)
    {gx : X → Xi} {px : X → Xo → X'} {gy : Y → Yi} {py : Y → Yo → Y'} {ga : J → Ii}
    {pa : J → Io → J'} {R : J → (P → E) → X → Y → Prop} {R' : J' → (P → E) → X' → Y' → Prop}
    (hfwd : ∀ a π x y, R a π x y →
      Hi (ga a) π (gx x) (gy y) ∧
      ∀ ρ xo, ρ ∉ H.withheld (ga a) → B.pub (gx x) ρ (H.tr (ga a) π ρ).plains = some xo →
        Ho (H.next (ga a) ρ) π xo (B.imp (gy y) (H.tr (ga a) π ρ)) →
        R' (pa a (H.next (ga a) ρ)) π (px x xo) (py y (B.imp (gy y) (H.tr (ga a) π ρ)))) :
    (H.on gx px gy py ga pa).AccOn R R' := by
  intro a π x y ρ hR hρ
  obtain ⟨xo, hxo, ho⟩ := h (ga a) π (gx x) (gy y) ρ (hfwd a π x y hR).1 hρ
  refine ⟨px x xo, ?_, (hfwd a π x y hR).2 ρ xo hρ hxo ho⟩
  show (B.pub (gx x) ρ (H.tr (ga a) π ρ).plains).map (px x) = some (px x xo)
  rw [hxo]
  rfl

/-- One honest side, two pairs of relations (the honest counterpart of `Clean.both`). -/
theorem AccOn.and {B : Block Xi Yi Xo Yo} {H : Hon B P E Ii Io}
    {Hi Hi' : Ii → (P → E) → Xi → Yi → Prop} {Ho Ho' : Io → (P → E) → Xo → Yo → Prop}
    (h : H.AccOn Hi Ho) (h' : H.AccOn Hi' Ho') :
    H.AccOn (fun a π x y => Hi a π x y ∧ Hi' a π x y)
      (fun a π x y => Ho a π x y ∧ Ho' a π x y) := by
  intro a π x y ρ hi hρ
  obtain ⟨xo, hxo, ho⟩ := h a π x y ρ hi.1 hρ
  obtain ⟨xo', hxo', ho'⟩ := h' a π x y ρ hi.2 hρ
  obtain rfl := Option.some.inj (hxo.symm.trans hxo')
  exact ⟨xo, hxo, ho, ho'⟩

/-- Frame rule with transport (the honest counterpart of `Clean.frame`). -/
theorem AccOn.frame {B : Block Xi Yi Xo Yo} {H : Hon B P E Ii Io}
    {Hi S : Ii → (P → E) → Xi → Yi → Prop}
    {Ho S' : Io → (P → E) → Xo → Yo → Prop} (h : H.AccOn Hi Ho)
    (hc : ∀ a π x y ρ xo, ρ ∉ H.withheld a → B.pub x ρ (H.tr a π ρ).plains = some xo → Hi a π x y →
      Ho (H.next a ρ) π xo (B.imp y (H.tr a π ρ)) → S a π x y →
      S' (H.next a ρ) π xo (B.imp y (H.tr a π ρ))) :
    H.AccOn (fun a π x y => Hi a π x y ∧ S a π x y) (fun a π x y => Ho a π x y ∧ S' a π x y) := by
  intro a π x y ρ hi hρ
  obtain ⟨xo, hxo, ho⟩ := h a π x y ρ hi.1 hρ
  exact ⟨xo, hxo, ho, hc a π x y ρ xo hρ hxo hi.1 ho hi.2⟩

/-- Validity of the honest state, a property without coins, is handed on at every ρ outside the
withheld set. -/
def Keeps {B : Block Xi Yi Xo Yo} (H : Hon B P E Ii Io) (V : Ii → Prop) (V' : Io → Prop) : Prop :=
  ∀ a ρ, V a → ρ ∉ H.withheld a → V' (H.next a ρ)

theorem Keeps.comp {B₁ : Block X₁ Y₁ X₂ Y₂} {B₂ : Block X₂ Y₂ X₃ Y₃} {H₁ : Hon B₁ P E I₁ I₂}
    {H₂ : Hon B₂ P E I₂ I₃} {V₁ : I₁ → Prop} {V₂ : I₂ → Prop} {V₃ : I₃ → Prop}
    (h₁ : H₁.Keeps V₁ V₂) (h₂ : H₂.Keeps V₂ V₃) : (H₁.seq H₂).Keeps V₁ V₃ :=
  fun a _ ha hρ => h₂ _ _ (h₁ a _ ha (not_withheld_seq hρ).1) (not_withheld_seq hρ).2

end Hon

/-! ## Splitting the pads -/

theorem map_congr' {α β : Type} (p : PMF α) {f g : α → β} (h : ∀ a, f a = g a) :
    p.map f = p.map g := by rw [funext h]

theorem bind_congr' {α β : Type} (p : PMF α) {f g : α → PMF β} (h : ∀ a, f a = g a) :
    p.bind f = p.bind g := by rw [funext h]

section Mix
variable {P E : Type}

open Classical in
/-- The family that agrees with π on U and with σ outside U. -/
def mix (U : Set P) (π σ : P → E) : P → E := fun p => if p ∈ U then π p else σ p

theorem mix_mem {U : Set P} (π σ : P → E) {p : P} (h : p ∈ U) : mix U π σ p = π p := if_pos h
theorem mix_notMem {U : Set P} (π σ : P → E) {p : P} (h : p ∉ U) : mix U π σ p = σ p := if_neg h
theorem mix_self (U : Set P) (π : P → E) : mix U π π = π :=
  funext fun p => by by_cases h : p ∈ U <;> simp [mix, h]

variable [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E]

/-- Two independent uniform families, mixed, give a uniform family. -/
theorem map_unif_mix (U : Set P) :
    (unif ((P → E) × (P → E))).map (fun q => mix U q.1 q.2) = unif (P → E) := by
  let φ : (P → E) × (P → E) →+ (P → E) :=
    { toFun := fun q => mix U q.1 q.2
      map_zero' := funext fun p => by by_cases h : p ∈ U <;> simp [mix, h]
      map_add' := fun a b => funext fun p => by by_cases h : p ∈ U <;> simp [mix, h] }
  exact map_unif_addMonoidHom φ fun π => ⟨(π, π), mix_self U π⟩

/-- The entries in U and those outside U of a uniform family are independent: draw two families and
take the entries in U from the first. -/
theorem map_unif_split {γ : Type} (U : Set P) (G : (P → E) → γ) :
    (unif (P → E)).map G =
      (unif (P → E)).bind fun π₁ => (unif (P → E)).map fun π₂ => G (mix U π₁ π₂) := by
  calc
    (unif (P → E)).map G = ((unif ((P → E) × (P → E))).map fun q => mix U q.1 q.2).map G := by
      rw [map_unif_mix]
    _ = _ := by
      rw [PMF.map_comp, unif_prod]
      unfold Prob.prod
      rw [PMF.map_bind]
      refine bind_congr' _ fun π₁ => ?_
      rw [PMF.map_comp]
      rfl

end Mix

/-! ## Masked form -/

namespace Hon
variable {Xi Yi Xo Yo X₁ Y₁ X₂ Y₂ X₃ Y₃ P E Ii Io I₁ I₂ I₃ : Type}
  [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E]

/-- Masked form, semantically: honest-verifier zero knowledge of one block, for what the verifier
reads in full, in the form that survives a cut between two blocks. The block masks with the pads in
U and reads the pads in D; V is validity of the honest state.
The law of the plain parts is exactly Sim ρ, at every ρ outside the withheld set, for every valid
state, and for every value of the pads outside U: so it stays Sim ρ given anything that other blocks
reveal about their own pads. A pad is a one-time resource: U says which pads this block spends.
The simulator sees the block's own ρ and nothing else. Nothing is asked of the vectors that the
prover sends: their contents may be anything; whether their encodings hide them is no statement of
this structure. -/
structure Masked {B : Block Xi Yi Xo Yo} (H : Hon B P E Ii Io) (V : Ii → Prop) (U D : Set P)
    (Sim : Rho B.shape → PMF (Plains B.shape)) : Prop where
  reads : ∀ a ρ π π',
    V a → ρ ∉ H.withheld a → (∀ p ∈ D, π p = π' p) → (H.tr a π ρ).plains = (H.tr a π' ρ).plains
  law : ∀ a ρ σ,
    V a → ρ ∉ H.withheld a → (unif (P → E)).map (fun π => (H.tr a (mix U π σ) ρ).plains) = Sim ρ

/-- The simulator of two blocks in a row: independent draws. -/
def simSeq {s t : Shape} (S₁ : Rho s → PMF (Plains s))
    (S₂ : Rho t → PMF (Plains t)) (ρ : Rho (s ++ t)) : PMF (Plains (s ++ t)) :=
  (S₁ (Rho.fst ρ)).bind fun p₁ => (S₂ (Rho.snd (s := s) ρ)).map fun p₂ => plApp p₁ p₂

/-- What masked form gives, under `ha`, `hρ`: over all pads, the plain parts have the law Sim ρ. -/
theorem Masked.law_all {B : Block Xi Yi Xo Yo} {H : Hon B P E Ii Io} {V : Ii → Prop} {U D : Set P}
    {Sim : Rho B.shape → PMF (Plains B.shape)} (h : H.Masked V U D Sim) (a : Ii) (ρ : Rho B.shape)
    (ha : V a) (hρ : ρ ∉ H.withheld a) :
    (unif (P → E)).map (fun π => (H.tr a π ρ).plains) = Sim ρ := by
  rw [map_unif_split Uᶜ]
  have : ∀ π₁ : P → E, ((unif (P → E)).map fun π₂ => (H.tr a (mix Uᶜ π₁ π₂) ρ).plains) = Sim ρ := by
    intro π₁
    rw [← h.law a ρ π₁ ha hρ]
    refine map_congr' _ fun π₂ => ?_
    have : mix Uᶜ π₁ π₂ = mix U π₂ π₁ := funext fun p => by by_cases hp : p ∈ U <;> simp [mix, hp]
    rw [this]
  simp only [this]
  exact PMF.bind_const _ _

/-- More pads may be declared as read. -/
theorem Masked.mono {B : Block Xi Yi Xo Yo} {H : Hon B P E Ii Io} {V : Ii → Prop} {U D D' : Set P}
    {Sim : Rho B.shape → PMF (Plains B.shape)} (h : H.Masked V U D Sim) (hD : D ⊆ D') :
    H.Masked V U D' Sim :=
  ⟨fun a ρ π π' ha hρ hπ => h.reads a ρ π π' ha hρ fun p hp => hπ p (hD hp), h.law⟩

/-- A stronger validity may be assumed. -/
theorem Masked.anti {B : Block Xi Yi Xo Yo} {H : Hon B P E Ii Io} {V V' : Ii → Prop} {U D : Set P}
    {Sim : Rho B.shape → PMF (Plains B.shape)} (h : H.Masked V U D Sim) (hV : ∀ a, V' a → V a) :
    H.Masked V' U D Sim :=
  ⟨fun a ρ π π' ha => h.reads a ρ π π' (hV a ha), fun a ρ σ ha => h.law a ρ σ (hV a ha)⟩

/-- Sequential composition of honest-verifier zero knowledge (masked form), in the order of the
blocks. Hypotheses: no pad is spent twice (U₁ and U₂ are disjoint), and values read earlier pads
only (the first block does not read the pads that the second spends), and `hk : H₁.Keeps V₁ V₂`.
(not all hypotheses are named here: see the statement below)
Conclusion: the two blocks in a row spend U₁ ∪ U₂, and their plain parts are simulated by
independent draws from the two simulators, exactly.
A later block may mask with entries of a pad vector that an earlier block has sent, which a
composition for every fixed input of the second protocol does not allow: for a fixed pad vector a
masked scalar is one fixed number. -/
theorem Masked.comp {B₁ : Block X₁ Y₁ X₂ Y₂} {B₂ : Block X₂ Y₂ X₃ Y₃} {H₁ : Hon B₁ P E I₁ I₂}
    {H₂ : Hon B₂ P E I₂ I₃} {V₁ : I₁ → Prop} {V₂ : I₂ → Prop} {U₁ D₁ U₂ D₂ : Set P}
    {S₁ : Rho B₁.shape → PMF (Plains B₁.shape)} {S₂ : Rho B₂.shape → PMF (Plains B₂.shape)}
    (h₁ : H₁.Masked V₁ U₁ D₁ S₁) (h₂ : H₂.Masked V₂ U₂ D₂ S₂) (hk : H₁.Keeps V₁ V₂)
    (hU : Disjoint U₁ U₂) (hD : Disjoint D₁ U₂) :
    (H₁.seq H₂).Masked V₁ (U₁ ∪ U₂) (D₁ ∪ D₂) (simSeq S₁ S₂) := by
  constructor
  · intro a ρ π π' ha hρ hπ
    obtain ⟨hρ₁, hρ₂⟩ := not_withheld_seq hρ
    rw [tr_seq, tr_seq, plains_app, plains_app,
      h₁.reads a _ π π' ha hρ₁ fun p hp => hπ p (Or.inl hp),
      h₂.reads _ _ π π' (hk a _ ha hρ₁) hρ₂ fun p hp => hπ p (Or.inr hp)]
  · intro a ρ σ ha hρ
    obtain ⟨hρ₁, hρ₂⟩ := not_withheld_seq hρ
    rw [map_unif_split U₁]
    unfold simSeq
    rw [← h₁.law a _ σ ha hρ₁, PMF.bind_map]
    refine bind_congr' _ fun π₁ => ?_
    show _ = (S₂ (Rho.snd (s := B₁.shape) ρ)).map fun p₂ =>
        plApp (H₁.tr a (mix U₁ π₁ σ) (Rho.fst ρ)).plains p₂
    rw [← h₂.law _ _ (mix U₁ π₁ σ) (hk a _ ha hρ₁) hρ₂, PMF.map_comp]
    refine map_congr' _ fun π₂ => ?_
    have hm : mix (U₁ ∪ U₂) (mix U₁ π₁ π₂) σ = mix U₂ π₂ (mix U₁ π₁ σ) := funext fun p => by
      by_cases h2 : p ∈ U₂
      · have h1 : p ∉ U₁ := fun h1 => Set.disjoint_left.1 hU h1 h2
        simp [mix, h1, h2]
      · by_cases h1 : p ∈ U₁ <;> simp [mix, h1, h2]
    show ((H₁.seq H₂).tr a (mix (U₁ ∪ U₂) (mix U₁ π₁ π₂) σ) ρ).plains = _
    rw [hm, tr_seq, plains_app]
    have h1 : (H₁.tr a (mix U₂ π₂ (mix U₁ π₁ σ)) (Rho.fst ρ)).plains =
        (H₁.tr a (mix U₁ π₁ σ) (Rho.fst ρ)).plains :=
      h₁.reads a _ _ _ ha hρ₁ fun p hp => mix_notMem _ _ fun h2 => Set.disjoint_left.1 hD hp h2
    rw [h1]
    rfl

/-- Sequential composition of masked form, against the order of the blocks (the order of the pads
need not be the order in time):
the second block does not read the pads with which the first masks. (not all hypotheses are named
here: see the statement below) -/
theorem Masked.comp' {B₁ : Block X₁ Y₁ X₂ Y₂} {B₂ : Block X₂ Y₂ X₃ Y₃} {H₁ : Hon B₁ P E I₁ I₂}
    {H₂ : Hon B₂ P E I₂ I₃} {V₁ : I₁ → Prop} {V₂ : I₂ → Prop} {U₁ D₁ U₂ D₂ : Set P}
    {S₁ : Rho B₁.shape → PMF (Plains B₁.shape)} {S₂ : Rho B₂.shape → PMF (Plains B₂.shape)}
    (h₁ : H₁.Masked V₁ U₁ D₁ S₁) (h₂ : H₂.Masked V₂ U₂ D₂ S₂) (hk : H₁.Keeps V₁ V₂)
    (hU : Disjoint U₁ U₂) (hD : Disjoint D₂ U₁) :
    (H₁.seq H₂).Masked V₁ (U₁ ∪ U₂) (D₁ ∪ D₂) (simSeq S₁ S₂) := by
  constructor
  · intro a ρ π π' ha hρ hπ
    obtain ⟨hρ₁, hρ₂⟩ := not_withheld_seq hρ
    rw [tr_seq, tr_seq, plains_app, plains_app,
      h₁.reads a _ π π' ha hρ₁ fun p hp => hπ p (Or.inl hp),
      h₂.reads _ _ π π' (hk a _ ha hρ₁) hρ₂ fun p hp => hπ p (Or.inr hp)]
  · intro a ρ σ ha hρ
    obtain ⟨hρ₁, hρ₂⟩ := not_withheld_seq hρ
    have hsim : simSeq S₁ S₂ ρ =
        (S₂ (Rho.snd (s := B₁.shape) ρ)).bind fun p₂ =>
          (S₁ (Rho.fst ρ)).map fun p₁ => plApp p₁ p₂ := by
      unfold simSeq
      simp only [PMF.map]
      exact PMF.bind_comm _ _ _
    rw [map_unif_split U₂, hsim, ← h₂.law _ _ σ (hk a _ ha hρ₁) hρ₂, PMF.bind_map]
    refine bind_congr' _ fun π₂ => ?_
    show _ = (S₁ (Rho.fst ρ)).map fun p₁ =>
        plApp p₁ (H₂.tr (H₁.next a (Rho.fst ρ)) (mix U₂ π₂ σ) (Rho.snd (s := B₁.shape) ρ)).plains
    rw [← h₁.law _ _ (mix U₂ π₂ σ) ha hρ₁, PMF.map_comp]
    refine map_congr' _ fun π₁ => ?_
    have hm : mix (U₁ ∪ U₂) (mix U₂ π₂ π₁) σ = mix U₁ π₁ (mix U₂ π₂ σ) := funext fun p => by
      by_cases h1 : p ∈ U₁
      · have h2 : p ∉ U₂ := fun h2 => Set.disjoint_left.1 hU h1 h2
        simp [mix, h1, h2]
      · by_cases h2 : p ∈ U₂ <;> simp [mix, h1, h2]
    show ((H₁.seq H₂).tr a (mix (U₁ ∪ U₂) (mix U₂ π₂ π₁) σ) ρ).plains = _
    rw [hm, tr_seq, plains_app]
    have h2 : (H₂.tr (H₁.next a (Rho.fst ρ)) (mix U₁ π₁ (mix U₂ π₂ σ))
          (Rho.snd (s := B₁.shape) ρ)).plains =
        (H₂.tr (H₁.next a (Rho.fst ρ)) (mix U₂ π₂ σ) (Rho.snd (s := B₁.shape) ρ)).plains :=
      h₂.reads _ _ _ _ (hk a _ ha hρ₁) hρ₂ fun p hp =>
        mix_notMem _ _ fun h1 => Set.disjoint_left.1 hD hp h1
    rw [h2]
    rfl

/-- A block without rounds is masked: it sends nothing. -/
theorem masked_pure (f : Xi → Option Xo) (g : Yi → Yo) (nx : Ii → Io) (V : Ii → Prop) :
    (Hon.pure (P := P) (E := E) f g nx).Masked V ∅ ∅ (fun _ => PMF.pure ()) :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => PMF.map_const _ _⟩

/-- Masked form on a part of a larger statement. -/
theorem Masked.on {X Y X' Y' J J' : Type} {B : Block Xi Yi Xo Yo} {H : Hon B P E Ii Io}
    {V : Ii → Prop} {U D : Set P} {Sim : Rho B.shape → PMF (Plains B.shape)}
    (h : H.Masked V U D Sim) (gx : X → Xi) (px : X → Xo → X') (gy : Y → Yi) (py : Y → Yo → Y')
    (ga : J → Ii) (pa : J → Io → J') :
    (H.on gx px gy py ga pa).Masked (fun a => V (ga a)) U D Sim :=
  ⟨fun a ρ π π' ha hρ hπ => h.reads (ga a) ρ π π' ha hρ hπ,
    fun a ρ σ ha hρ => h.law (ga a) ρ σ ha hρ⟩

end Hon
end Blocks
