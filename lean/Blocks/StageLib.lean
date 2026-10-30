-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/StageLib.lean: general-purpose blocks as stages, each with one theorem on `Stage.Props`
between two records of relations (`Cut`) and one on its tracking data (`Core.Track.OK`), so that a
row of a segment (a row: one stage of a `Chain`, Blocks/Stage.lean) is one line. (Words of this
library: lean/GLOSSARY.md.)

Main names: `Stage.send`, `pads`, `nameVec` (vectors for a hidden quantity, over E or over F),
`nameScalars`, `sample`, `pure`, `on`; `Stage.Props.of_empty`, `frame`. The blocks are those of
Blocks/BlockLib.lean, `Block.pure` and `Block.on` (Blocks/Block.lean); `nameVec` and `nameScalars`
record only what is new (vectors in the implicit part, scalars in the explicit part).
The withheld set (`Hon.withheld`, Blocks/BlockHon.lean) is the set of verifier randomness outside
which completeness is stated. A backward step: the relation for soundness after a stage implies the
one before it. A forward step: the relation for the honest run before it implies the one after it.
Validity: a valid state of the honest prover stays valid.
Notation: `Sorts`: the types between two stages: the explicit part X and the implicit part Y of a
statement, and the state I of the honest prover; `Cut`: the relations between two stages: `R`: the
relation for soundness; `Hn`: the relation of the honest run; `V`: validity of the honest state
(both: Blocks/Stage.lean); a `Stage` has `ε`: the errors, round by round, as counts (an `Err`,
Iop/Rbr.lean: one number for each round); for `U`, `D`, `Sim`, `pBad`, `pWin` see the record
(Blocks/Stage.lean). `P` indexes the pads (`Hon`, Blocks/BlockHon.lean); π : P → E: the pads. ρ :
`Rho`, the verifier's randomness of a whole execution; τ : `Tr`, full transcripts (Iop/Shape.lean).
-/
import Blocks.StageTrack
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks
open Iop Prob
open scoped ENNReal

private theorem prRho_empty₀ (s : Shape) : prRho (∅ : Set (Rho s)) = 0 := by
  unfold prRho
  exact pr_empty _

variable {F P E : Type} [Field F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E] [Fintype P]
  [DecidableEq P] {a b : Sorts}

namespace Stage

/-- Under clean (`Block.Clean`), acc (`Hon.AccOn`), masked (`Hon.Masked`) and keeps (a valid state
stays valid): a stage whose withheld set (`Hon.withheld`) is empty has `Stage.Props`, whatever the
two bounds `pBad`, `pWin` are. -/
theorem Props.of_empty {S : Stage P E a b} {ca : Cut P E a} {cb : Cut P E b}
    (clean : S.B.Clean ca.R cb.R S.ε) (acc : S.H.AccOn ca.Hn cb.Hn)
    (masked : S.H.Masked ca.V S.U S.D S.Sim) (keeps : ∀ s ρ, ca.V s → cb.V (S.H.next s ρ))
    (hBad : S.H.Bad = ∅) (hWin : ∀ s, S.H.Win s = ∅) : S.Props ca cb where
  clean := clean
  acc := acc
  masked := masked
  keeps := keeps
  prBad := by rw [hBad, prRho_empty₀]; exact zero_le _
  prWin := fun s _ => by rw [hWin s, prRho_empty₀]; exact zero_le _

/-! ### pads -/

/-- A pad vector: the pads idx 0, idx 1, ... of the family of pads join the implicit part. -/
@[reducible] def _root_.Blocks.Core.pads (a : Sorts) {n : ℕ} (idx : Fin n → P) :
    Core P E a ⟨a.X, a.Y × (Fin n → E), a.I⟩ where
  B := Block.pads a.X a.Y E n
  H := Hon.pads a.X a.Y idx

@[inherit_doc Core.pads]
def pads (a : Sorts) {n : ℕ} (idx : Fin n → P) :
    Stage P E a ⟨a.X, a.Y × (Fin n → E), a.I⟩ where
  toCore := Core.pads a idx
  ε := (0, ())
  U := ∅
  D := ∅
  Sim := fun _ => PMF.pure ((fun k => Empty.elim k), ())
  pBad := 0
  pWin := 0

/-- The relations after a pad vector. -/
def cutPads {n : ℕ} (idx : Fin n → P) (ca : Cut P E a) : Cut P E ⟨a.X, a.Y × (Fin n → E), a.I⟩ :=
  ⟨fun x y => ca.R x y.1, fun s π x y => ca.Hn s π x y.1 ∧ ∀ j, y.2 j = π (idx j), ca.V⟩

theorem props_pads {n : ℕ} (idx : Fin n → P) (ca : Cut P E a) :
    (pads (E := E) a idx).Props ca (cutPads idx ca) :=
  Props.of_empty (S := pads (E := E) a idx) (cb := cutPads idx ca) (Block.clean_pads n ca.R)
    (Hon.accOn_pads idx ca.Hn) (Hon.masked_pads idx ca.V) (fun _ _ h => h) rfl fun _ => rfl

/-- what is exposed after a pad vector -/
def readsPads (n : ℕ) (ra : Reads F E a) : Reads F E ⟨a.X, a.Y × (Fin n → E), a.I⟩ :=
  ⟨ra.N ⊕ Fin n, fun y => Sum.elim (ra.rd y.1) y.2, fun y => ra.mat y.1⟩

def _root_.Blocks.Core.trackPads
    (C : Code.Enc F) [Nonempty (Fin C.n)] (q : ℕ) (idx : Fin C.msg → P) (ra : Reads F E a) :
    (Core.pads (E := E) a idx).Track ra (readsPads C.msg ra) :=
  ⟨(REnc.pad E C q, PUnit.unit), srcPads C q ra.N⟩

abbrev trackPads (C : Code.Enc F) [Nonempty (Fin C.n)] (q : ℕ)
    (idx : Fin C.msg → P) (ra : Reads F E a) :
    (pads (E := E) a idx).Track ra (readsPads C.msg ra) :=
  Core.trackPads C q idx ra

theorem trackPads_ok (C : Code.Enc F) [Nonempty (Fin C.n)] (q : ℕ)
    (idx : Fin C.msg → P) (ra : Reads F E a) : (trackPads C q idx ra).OK :=
  ⟨Block.tracks_pads' C q ra.rd, fun _ _ => rfl⟩

/-! ### Vectors for a hidden quantity -/

/-- Vectors for a hidden quantity: the oracle part of the message is added to the implicit part. The
plain part of the round is the fixed value p₀ (for the rounds of the library: the empty tuple); the
honest message depends on no pad. -/
@[reducible] def _root_.Blocks.Core.nameVec
    (a : Sorts) (r : Round) (p₀ : r.Plain) (msg : a.I → r.Orc) :
    Core P E a ⟨a.X, a.Y × r.Orc, a.I⟩ where
  B := Block.one r (fun x _ _ => some x) fun y m _ => (y, m.1)
  H := Hon.one (fun s _ => (msg s, p₀)) (fun s _ => s) ∅ fun _ => ∅

@[inherit_doc Core.nameVec]
def nameVec (a : Sorts) (r : Round) (p₀ : r.Plain) (msg : a.I → r.Orc) :
    Stage P E a ⟨a.X, a.Y × r.Orc, a.I⟩ where
  toCore := Core.nameVec a r p₀ msg
  ε := (0, ())
  U := ∅
  D := ∅
  Sim := fun _ => PMF.pure (p₀, ())
  pBad := 0
  pWin := 0

/-- `Stage.Props`. t is the hidden quantity; `sent` computes it from the vectors sent. For
soundness: before the stage the predicate S at t x y; after it, S at the sent quantity, and that
quantity equals t x y. -/
theorem props_nameVec (r : Round) (p₀ : r.Plain) (msg : a.I → r.Orc) {T : Type} (t : a.X → a.Y → T)
    (sent : a.X → a.Y → r.Orc → T) (S : T → a.X → a.Y → Prop)
    (Hn : a.I → (P → E) → a.X → a.Y → Prop) (V : a.I → Prop) :
    (nameVec (P := P) (E := E) a r p₀ msg).Props ⟨fun x y => S (t x y) x y, Hn, V⟩
      ⟨fun x yo => S (sent x yo.1 yo.2) x yo.1 ∧ sent x yo.1 yo.2 = t x yo.1,
        fun s π x yo => Hn s π x yo.1 ∧ yo.2 = msg s,
        V⟩ :=
  Props.of_empty (S := nameVec (P := P) (E := E) a r p₀ msg)
    (ca := ⟨fun x y => S (t x y) x y, Hn, V⟩)
    (cb := ⟨fun x yo => S (sent x yo.1 yo.2) x yo.1 ∧ sent x yo.1 yo.2 = t x yo.1,
        fun s π x yo => Hn s π x yo.1 ∧ yo.2 = msg s,
        V⟩)
    (Block.clean_one (r := r) (pb := fun (x : a.X) _ _ => some x)
      (im := fun (y : a.Y) m _ => (y, m.1))
      (Ri := fun x y => S (t x y) x y)
      (Ro := fun x yo => S (sent x yo.1 yo.2) x yo.1 ∧ sent x yo.1 yo.2 = t x yo.1)
      (fun _ _ _ => ∅) 0 (fun _ _ _ => le_of_eq (cnt_false fun _ h => h))
      fun x y m c xo _ hxo hRo => by
        obtain rfl := Option.some.inj hxo
        have h1 : S (sent x y m.1) x y := hRo.1
        have h2 : sent x y m.1 = t x y := hRo.2
        rw [← h2]
        exact h1)
    (Hon.accOn_one (r := r) (pb := fun (x : a.X) _ _ => some x)
      (im := fun (y : a.Y) m _ => (y, m.1)) (msg := fun (s : a.I) (_ : P → E) => (msg s, p₀))
      (nx := fun s _ => s) (Bd := ∅) (Wn := fun _ => ∅) (Hi := Hn)
      (Ho := fun s π x yo => Hn s π x yo.1 ∧ yo.2 = msg s)
      fun _ _ x _ _ hi _ _ => ⟨x, rfl, hi, rfl⟩)
    (Hon.masked_one_const (r := r) (pb := fun (x : a.X) _ _ => some x)
      (im := fun (y : a.Y) m _ => (y, m.1)) (msg := fun (s : a.I) (_ : P → E) => (msg s, p₀))
      (nx := fun s _ => s) (Bd := ∅) (Wn := fun _ => ∅) V p₀ fun _ _ _ => rfl)
    (fun _ _ h => h) rfl fun _ => rfl

/-- what is exposed after the vectors of a round -/
def readsName {r : Round} (e : REnc F E r) (ra : Reads F E a) : Reads F E ⟨a.X, a.Y × r.Orc, a.I⟩ :=
  ⟨ra.N ⊕ e.Ent, rdName e ra.rd, fun y => ra.mat y.1⟩

def _root_.Blocks.Core.trackNameVec
    {r : Round} (e : REnc F E r) (p₀ : r.Plain) (msg : a.I → r.Orc) (ra : Reads F E a) :
    (Core.nameVec (P := P) (E := E) a r p₀ msg).Track ra (readsName e ra) :=
  ⟨(e, PUnit.unit), srcName e ra.N⟩

abbrev trackNameVec {r : Round} (e : REnc F E r) (p₀ : r.Plain)
    (msg : a.I → r.Orc) (ra : Reads F E a) :
    (nameVec (P := P) (E := E) a r p₀ msg).Track ra (readsName e ra) :=
  Core.trackNameVec e p₀ msg ra

theorem trackNameVec_ok {r : Round} (e : REnc F E r) (p₀ : r.Plain)
    (msg : a.I → r.Orc) (ra : Reads F E a) :
    (trackNameVec (P := P) e p₀ msg ra).OK :=
  ⟨Block.tracks_nameFin (Xi := a.X) e ra.rd, fun _ _ => rfl⟩

/-! ### One prover message of vectors, in general -/

/-- One prover message of vectors. φ of the oracle part is added to the implicit part (for instance:
the vectors read in E, in the arrangement that the relations use); fx maps the explicit part. The
honest message may depend on pads. The plain part of the round is the fixed value p₀. -/
@[reducible] def _root_.Blocks.Core.send (a : Sorts) (X' Z : Type) (r : Round) (p₀ : r.Plain)
    (msg : a.I → (P → E) → r.Orc) (φ : r.Orc → Z) (fx : a.X → X') :
    Core P E a ⟨X', a.Y × Z, a.I⟩ where
  B := Block.one r (fun x _ _ => some (fx x)) fun y m _ => (y, φ m.1)
  H := Hon.one (fun s π => (msg s π, p₀)) (fun s _ => s) ∅ fun _ => ∅

@[inherit_doc Core.send]
def send (a : Sorts) (X' Z : Type) (r : Round) (p₀ : r.Plain)
    (msg : a.I → (P → E) → r.Orc) (φ : r.Orc → Z) (fx : a.X → X') :
    Stage P E a ⟨X', a.Y × Z, a.I⟩ where
  toCore := Core.send a X' Z r p₀ msg φ fx
  ε := (0, ())
  U := ∅
  D := ∅
  Sim := fun _ => PMF.pure (p₀, ())
  pBad := 0
  pWin := 0

/-- `Stage.Props`, from one backward step, one forward step, and validity. All errors are 0, no pad
is used for masking, the withheld set is empty. -/
theorem props_send {X' Z : Type} (r : Round) (p₀ : r.Plain) (msg : a.I → (P → E) → r.Orc)
    (φ : r.Orc → Z) (fx : a.X → X') {ca : Cut P E a} {cb : Cut P E ⟨X', a.Y × Z, a.I⟩}
    (hback : ∀ x y o, cb.R (fx x) (y, φ o) → ca.R x y)
    (hfwd : ∀ s π x y, ca.Hn s π x y → cb.Hn s π (fx x) (y, φ (msg s π)))
    (hV : ∀ s, ca.V s → cb.V s) :
    (send a X' Z r p₀ msg φ fx).Props ca cb :=
  Props.of_empty (S := send a X' Z r p₀ msg φ fx)
    (Block.clean_one (r := r) (pb := fun (x : a.X) _ _ => some (fx x))
      (im := fun (y : a.Y) m _ => (y, φ m.1)) (Ri := ca.R) (Ro := cb.R)
      (fun _ _ _ => ∅) 0 (fun _ _ _ => le_of_eq (cnt_false fun _ h => h))
      fun x y m c xo _ hxo hRo => by
        obtain rfl := Option.some.inj hxo
        exact hback x y m.1 hRo)
    (Hon.accOn_one (r := r) (pb := fun (x : a.X) _ _ => some (fx x))
      (im := fun (y : a.Y) m _ => (y, φ m.1)) (msg := fun (s : a.I) (π : P → E) => (msg s π, p₀))
      (nx := fun s _ => s) (Bd := ∅) (Wn := fun _ => ∅) (Hi := ca.Hn) (Ho := cb.Hn)
      fun s π x y _ hi _ _ => ⟨fx x, rfl, hfwd s π x y hi⟩)
    (Hon.masked_one_const (r := r) (pb := fun (x : a.X) _ _ => some (fx x))
      (im := fun (y : a.Y) m _ => (y, φ m.1)) (msg := fun (s : a.I) (π : P → E) => (msg s π, p₀))
      (nx := fun s _ => s) (Bd := ∅) (Wn := fun _ => ∅) ca.V p₀ fun _ _ _ => rfl)
    (fun s _ h => hV s h) rfl fun _ => rfl

def _root_.Blocks.Core.trackSend {X' Z : Type} {r : Round} (e : REnc F E r) (p₀ : r.Plain)
    (msg : a.I → (P → E) → r.Orc) (φ : r.Orc → Z) (fx : a.X → X') (ra : Reads F E a)
    (rb : Reads F E ⟨X', a.Y × Z, a.I⟩) (src : rb.N → ra.N ⊕ (e.A × ℕ × ℕ)) :
    (Core.send a X' Z r p₀ msg φ fx).Track ra rb :=
  ⟨(e, PUnit.unit), srcOne e src⟩

abbrev trackSend {X' Z : Type} {r : Round} (e : REnc F E r) (p₀ : r.Plain)
    (msg : a.I → (P → E) → r.Orc) (φ : r.Orc → Z) (fx : a.X → X') (ra : Reads F E a)
    (rb : Reads F E ⟨X', a.Y × Z, a.I⟩) (src : rb.N → ra.N ⊕ (e.A × ℕ × ℕ)) :
    (send a X' Z r p₀ msg φ fx).Track ra rb :=
  Core.trackSend e p₀ msg φ fx ra rb src

theorem trackSend_ok {X' Z : Type} {r : Round} (e : REnc F E r) (p₀ : r.Plain)
    (msg : a.I → (P → E) → r.Orc) (φ : r.Orc → Z) (fx : a.X → X') (ra : Reads F E a)
    (rb : Reads F E ⟨X', a.Y × Z, a.I⟩) (src : rb.N → ra.N ⊕ (e.A × ℕ × ℕ))
    (h : ∀ y o n, rb.rd (y, φ o) n =
      Sum.elim (ra.rd y) (fun q => nat (fun i' => nat (e.vecE o q.1 i') q.2.2) q.2.1) (src n))
    (hm : ∀ y z, rb.mat (y, z) = ra.mat y) :
    (trackSend e p₀ msg φ fx ra rb src).OK :=
  ⟨Block.tracks_one (pb := fun (x : a.X) _ _ => some (fx x)) (im := fun (y : a.Y) m _ => (y, φ m.1))
      e src fun y m _ n => h y m.1 n,
    fun y _ => hm y _⟩

/-! ### Masked scalars for hidden values -/

/-- the round of the scalars k : K, without vectors and without a challenge -/
abbrev scRound (E K : Type) [Zero E] : Round :=
  vRound E Empty (fun e => Empty.elim e) (fun e => Empty.elim e) K Unit

/-- Masked scalars for hidden values: the scalar k is val k plus the pad idx k; the scalars are
added to the explicit part. The values depend on no pad. -/
@[reducible] def _root_.Blocks.Core.nameScalars
    (a : Sorts) {K : Type} (idx : K → P) (val : a.I → K → E) :
    Core P E a ⟨a.X × (K → E), a.Y, a.I⟩ where
  B := Block.one (scRound E K) (fun x _ p => some (x, p)) fun y _ _ => y
  H := Hon.one (fun s π => (fun e => Empty.elim e, fun k => val s k + π (idx k)))
    (fun s _ => s) ∅ fun _ => ∅

@[inherit_doc Core.nameScalars]
def nameScalars
    (a : Sorts) {K : Type} [Fintype K] [DecidableEq K] (idx : K → P) (val : a.I → K → E) :
    Stage P E a ⟨a.X × (K → E), a.Y, a.I⟩ where
  toCore := Core.nameScalars a idx val
  ε := (0, ())
  U := Set.range idx
  D := Set.range idx
  Sim := Hon.simOne (r := scRound E K) E _root_.id
  pBad := 0
  pWin := 0

/-- `Stage.Props`, for injective idx. padOf gives the sent pads from the implicit part; the value of
a scalar is the scalar minus its pad. t holds the hidden values. -/
theorem props_nameScalars {K : Type} [Fintype K] [DecidableEq K] (idx : K → P)
    (hidx : Function.Injective idx) (val : a.I → K → E) (padOf : a.Y → P → E)
    (t : a.X → a.Y → K → E) (S : (K → E) → a.X → a.Y → Prop)
    (Hn : a.I → (P → E) → a.X → a.Y → Prop) (V : a.I → Prop) :
    (nameScalars (E := E) a idx val).Props ⟨fun x y => S (t x y) x y, Hn, V⟩
      ⟨fun xo y =>
          S (fun k => xo.2 k - padOf y (idx k)) xo.1 y ∧
          (fun k => xo.2 k - padOf y (idx k)) = t xo.1 y,
        fun s π xo y => Hn s π xo.1 y ∧ xo.2 = fun k => val s k + π (idx k),
        V⟩ :=
  Props.of_empty (S := nameScalars (E := E) a idx val)
    (ca := ⟨fun x y => S (t x y) x y, Hn, V⟩)
    (cb := ⟨fun xo y =>
          S (fun k => xo.2 k - padOf y (idx k)) xo.1 y ∧
          (fun k => xo.2 k - padOf y (idx k)) = t xo.1 y,
        fun s π xo y => Hn s π xo.1 y ∧ xo.2 = fun k => val s k + π (idx k),
        V⟩)
    (Block.clean_one (r := scRound E K)
      (pb := fun (x : a.X) _ p => some (x, p)) (im := fun (y : a.Y) _ _ => y)
      (Ri := fun x y => S (t x y) x y)
      (Ro := fun xo y =>
          S (fun k => xo.2 k - padOf y (idx k)) xo.1 y ∧
          (fun k => xo.2 k - padOf y (idx k)) = t xo.1 y)
      (fun _ _ _ => ∅) 0 (fun _ _ _ => le_of_eq (cnt_false fun _ h => h))
      fun x y m c xo _ hxo hRo => by
        obtain rfl := Option.some.inj hxo
        have h1 : S (fun k => m.2 k - padOf y (idx k)) x y := hRo.1
        have h2 : (fun k => m.2 k - padOf y (idx k)) = t x y := hRo.2
        rw [← h2]
        exact h1)
    (Hon.accOn_one (r := scRound E K) (pb := fun (x : a.X) _ p => some (x, p))
      (im := fun (y : a.Y) _ _ => y)
      (msg := fun (s : a.I) (π : P → E) => (fun e => Empty.elim e, fun k => val s k + π (idx k)))
      (nx := fun s _ => s) (Bd := ∅) (Wn := fun _ => ∅) (Hi := Hn)
      (Ho := fun s π xo y => Hn s π xo.1 y ∧ xo.2 = fun k => val s k + π (idx k))
      fun s π x _ _ hi _ _ => ⟨(x, fun k => val s k + π (idx k)), rfl, hi, rfl⟩)
    (by
      have h := Hon.masked_one (r := scRound E K) (pb := fun (x : a.X) _ p => some (x, p))
        (im := fun (y : a.Y) _ _ => y)
        (msg := fun (s : a.I) (π : P → E) => (fun e => Empty.elim e, fun k => val s k + π (idx k)))
        (nx := fun s _ => s) (Bd := ∅) (Wn := fun _ => ∅) _root_.id V idx hidx
        (fun s _ k => val s k) ∅ (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (Set.empty_disjoint _)
      rw [Set.empty_union] at h
      exact h)
    (fun _ _ h => h) rfl fun _ => rfl

/-- nothing new is exposed -/
def readsX (X' I' : Type) (ra : Reads F E a) : Reads F E ⟨X', a.Y, I'⟩ := ⟨ra.N, ra.rd, ra.mat⟩

def _root_.Blocks.Core.trackNameScalars
    {K : Type} (idx : K → P) (val : a.I → K → E) (ra : Reads F E a) :
    (Core.nameScalars (E := E) a idx val).Track ra (readsX (a.X × (K → E)) a.I ra) :=
  ⟨(REnc.none E F K Unit, PUnit.unit), srcSame (REnc.none E F K Unit) ra.N⟩

abbrev trackNameScalars {K : Type} [Fintype K] [DecidableEq K] (idx : K → P)
    (val : a.I → K → E) (ra : Reads F E a) :
    (nameScalars (E := E) a idx val).Track ra (readsX (a.X × (K → E)) a.I ra) :=
  Core.trackNameScalars idx val ra

theorem trackNameScalars_ok {K : Type} [Fintype K] [DecidableEq K] (idx : K → P)
    (val : a.I → K → E) (ra : Reads F E a) :
    (trackNameScalars idx val ra).OK :=
  ⟨Block.tracks_one (pb := fun (x : a.X) _ p => some (x, p)) (im := fun (y : a.Y) _ _ => y)
      (REnc.none E F K Unit) (fun n => Sum.inl n) fun _ _ _ _ => rfl,
    fun _ _ => rfl⟩

/-! ### A challenge -/

/-- A challenge in C; the verifier rejects if it fails the public check `ok`, and else records it;
the honest prover's state becomes nx s c. -/
@[reducible] def _root_.Blocks.Core.sample (a : Sorts) (I' : Type) (C : Type) [Fintype C]
    [Nonempty C] (ok : C → Bool) (nx : a.I → C → I') :
    Core P E a ⟨a.X × C, a.Y, I'⟩ where
  B := Block.sample a.X a.Y E C ok
  H := Hon.sample a.X a.Y ok nx

@[inherit_doc Core.sample]
def sample (a : Sorts) (I' : Type) (C : Type) [Fintype C] [Nonempty C] (ok : C → Bool)
    (nx : a.I → C → I') (e : ℕ) (pBad : ℝ≥0∞) :
    Stage P E a ⟨a.X × C, a.Y, I'⟩ where
  toCore := Core.sample a I' C ok nx
  ε := (e, ())
  U := ∅
  D := ∅
  Sim := fun _ => PMF.pure ((fun k => Empty.elim k), ())
  pBad := pBad
  pWin := 0

/-- `Stage.Props`, for a nonempty C, from: a set of at most e bad challenges with a backward step
outside it; a forward step; validity; a bound on the probability that the check fails. -/
theorem props_sample {I' C : Type} [Fintype C] [Nonempty C] (ok : C → Bool) (nx : a.I → C → I')
    (e : ℕ) (pBad : ℝ≥0∞) {ca : Cut P E a} {cb : Cut P E ⟨a.X × C, a.Y, I'⟩}
    (bad : a.X → a.Y → Set C) (hcnt : ∀ x y, cnt (fun c => c ∈ bad x y) ≤ e)
    (hback : ∀ x y c, c ∉ bad x y → ok c = true → cb.R (x, c) y → ca.R x y)
    (hfwd : ∀ s π x y c, ca.Hn s π x y → ok c = true → cb.Hn (nx s c) π (x, c) y)
    (hV : ∀ s c, ca.V s → cb.V (nx s c))
    (hp : prRho {ρ : Rho [Block.chalRound E C] | ok ρ.1 = false} ≤ pBad) :
    (sample (P := P) (E := E) a I' C ok nx e pBad).Props ca cb where
  clean := Block.clean_sample bad e hcnt hback
  acc := Hon.accOn_sample ok nx hfwd
  masked := Hon.masked_sample ok nx ca.V
  keeps := fun s ρ h => hV s ρ.1 h
  prBad := hp
  prWin := fun _ _ => by
    show prRho (∅ : Set (Rho [Block.chalRound E C])) ≤ 0
    rw [prRho_empty₀]

def _root_.Blocks.Core.trackSample
    {I' C : Type} [Fintype C] [Nonempty C] (ok : C → Bool) (nx : a.I → C → I') (ra : Reads F E a) :
    (Core.sample (P := P) (E := E) a I' C ok nx).Track ra (readsX (a.X × C) I' ra) :=
  ⟨(REnc.none E F Empty C, PUnit.unit), srcSame (REnc.none E F Empty C) ra.N⟩

theorem _root_.Blocks.Core.trackSample_ok
    {I' C : Type} [Fintype C] [Nonempty C] (ok : C → Bool) (nx : a.I → C → I') (ra : Reads F E a) :
    (Core.trackSample (P := P) ok nx ra).OK :=
  ⟨Block.tracks_sample' ok ra.rd, fun _ _ => rfl⟩

/-! ### No round -/

/-- A stage without rounds: the verifier computes, or rejects; the implicit part and the honest
prover's state are mapped. -/
@[reducible] def _root_.Blocks.Core.pure (f : a.X → Option b.X) (g : a.Y → b.Y) (nx : a.I → b.I) :
    Core P E a b where
  B := Block.pure f g
  H := Hon.pure f g nx

@[inherit_doc Core.pure]
def pure (f : a.X → Option b.X) (g : a.Y → b.Y) (nx : a.I → b.I) : Stage P E a b where
  toCore := Core.pure f g nx
  ε := ()
  U := ∅
  D := ∅
  Sim := fun _ => PMF.pure ()
  pBad := 0
  pWin := 0

theorem props_pure {f : a.X → Option b.X} {g : a.Y → b.Y} {nx : a.I → b.I} {ca : Cut P E a}
    {cb : Cut P E b} (hback : ∀ x y xo, f x = some xo → cb.R xo (g y) → ca.R x y)
    (hfwd : ∀ s π x y, ca.Hn s π x y → ∃ xo, f x = some xo ∧ cb.Hn (nx s) π xo (g y))
    (hV : ∀ s, ca.V s → cb.V (nx s)) :
    (pure (P := P) (E := E) f g nx).Props ca cb :=
  Props.of_empty (S := pure (P := P) (E := E) f g nx) (Block.clean_pure_iff.2 hback)
    (Hon.accOn_pure hfwd) (Hon.masked_pure f g nx ca.V) (fun s _ h => hV s h) rfl fun _ => rfl

def _root_.Blocks.Core.trackPure (f : a.X → Option b.X) (g : a.Y → b.Y) (nx : a.I → b.I)
    (ra : Reads F E a) (rb : Reads F E b) (σ : rb.N → ra.N) :
    (Core.pure (P := P) (E := E) f g nx).Track ra rb :=
  ⟨PUnit.unit, fun n => .inl (σ n)⟩

abbrev trackPure (f : a.X → Option b.X) (g : a.Y → b.Y) (nx : a.I → b.I) (ra : Reads F E a)
    (rb : Reads F E b) (σ : rb.N → ra.N) :
    (pure (P := P) (E := E) f g nx).Track ra rb :=
  Core.trackPure f g nx ra rb σ

theorem trackPure_ok (f : a.X → Option b.X) (g : a.Y → b.Y) (nx : a.I → b.I)
    (ra : Reads F E a) (rb : Reads F E b) (σ : rb.N → ra.N)
    (h : ∀ y n, rb.rd (g y) n = ra.rd y (σ n)) (hm : ∀ y, rb.mat (g y) = ra.mat y) :
    (trackPure (P := P) f g nx ra rb σ).OK :=
  ⟨Block.tracks_pure σ h, fun y _ => hm y⟩

/-! ### A stage on a part of a larger statement -/

variable {a' b' : Sorts}

/-- A stage that acts on a part of a larger statement: a lens on each of the explicit part, the
implicit part and the honest prover's state. -/
@[reducible] def _root_.Blocks.Core.on (S : Core P E a b) (gx : a'.X → a.X) (px : a'.X → b.X → b'.X)
    (gy : a'.Y → a.Y) (py : a'.Y → b.Y → b'.Y) (ga : a'.I → a.I) (pa : a'.I → b.I → b'.I) :
    Core P E a' b' where
  B := S.B.on gx px gy py
  H := S.H.on gx px gy py ga pa

@[inherit_doc Core.on]
def on (S : Stage P E a b) (gx : a'.X → a.X) (px : a'.X → b.X → b'.X)
    (gy : a'.Y → a.Y) (py : a'.Y → b.Y → b'.Y) (ga : a'.I → a.I) (pa : a'.I → b.I → b'.I) :
    Stage P E a' b' where
  toCore := S.toCore.on gx px gy py ga pa
  ε := S.ε
  U := S.U
  D := S.D
  Sim := S.Sim
  pBad := S.pBad
  pWin := S.pWin

/-- `Stage.Props` of `S.on`, from `Stage.Props` of S, one backward step, one forward step (both may
assume that the outputs are those that the stage computes), and validity. -/
theorem Props.on {S : Stage P E a b} {ca : Cut P E a} {cb : Cut P E b} (h : S.Props ca cb)
    {gx : a'.X → a.X} {px : a'.X → b.X → b'.X} {gy : a'.Y → a.Y} {py : a'.Y → b.Y → b'.Y}
    {ga : a'.I → a.I} {pa : a'.I → b.I → b'.I} {ca' : Cut P E a'} {cb' : Cut P E b'}
    (hback : ∀ x y τ xo, S.B.pub (gx x) τ.rho τ.plains = some xo →
      cb'.R (px x xo) (py y (S.B.imp (gy y) τ)) →
      cb.R xo (S.B.imp (gy y) τ) ∧ (ca.R (gx x) (gy y) → ca'.R x y))
    (hfwd : ∀ s π x y, ca'.Hn s π x y →
      ca.Hn (ga s) π (gx x) (gy y) ∧
      ∀ ρ xo, ρ ∉ S.H.withheld (ga s) → S.B.pub (gx x) ρ (S.H.tr (ga s) π ρ).plains = some xo →
        cb.Hn (S.H.next (ga s) ρ) π xo (S.B.imp (gy y) (S.H.tr (ga s) π ρ)) →
        cb'.Hn (pa s (S.H.next (ga s) ρ)) π (px x xo) (py y (S.B.imp (gy y) (S.H.tr (ga s) π ρ))))
    (hV : ∀ s, ca'.V s → ca.V (ga s)) (hV' : ∀ s so, ca'.V s → cb.V so → cb'.V (pa s so)) :
    (S.on gx px gy py ga pa).Props ca' cb' where
  clean := h.clean.on' hback
  acc := h.acc.on' hfwd
  masked := (h.masked.on gx px gy py ga pa).anti hV
  keeps := fun s ρ hs => hV' s _ hs (h.keeps (ga s) ρ (hV s hs))
  prBad := h.prBad
  prWin := fun s hs => h.prWin (ga s) (hV s hs)

def _root_.Blocks.Core.Track.on {S : Core P E a b} {ra : Reads F E a} {rb : Reads F E b}
    (t : S.Track ra rb) (gx : a'.X → a.X) (px : a'.X → b.X → b'.X) (gy : a'.Y → a.Y)
    (py : a'.Y → b.Y → b'.Y) (ga : a'.I → a.I) (pa : a'.I → b.I → b'.I) (ra' : Reads F E a')
    (rb' : Reads F E b') (κ : ra.N → ra'.N) (σ : rb'.N → ra'.N ⊕ rb.N) :
    (S.on gx px gy py ga pa).Track ra' rb' :=
  ⟨t.d, fun n => Sum.elim Sum.inl (fun m => (t.src m).map κ _root_.id) (σ n)⟩

theorem _root_.Blocks.Core.Track.OK.on {S : Core P E a b} {ra : Reads F E a} {rb : Reads F E b}
    {t : S.Track ra rb} (h : t.OK) (gx : a'.X → a.X) (px : a'.X → b.X → b'.X) {gy : a'.Y → a.Y}
    {py : a'.Y → b.Y → b'.Y} (ga : a'.I → a.I) (pa : a'.I → b.I → b'.I) {ra' : Reads F E a'}
    {rb' : Reads F E b'} (κ : ra.N → ra'.N) (σ : rb'.N → ra'.N ⊕ rb.N)
    (hi : ∀ y k, ra.rd (gy y) k = ra'.rd y (κ k))
    (ho : ∀ y yo n, rb'.rd (py y yo) n = Sum.elim (ra'.rd y) (rb.rd yo) (σ n))
    (hm : ∀ y yo, rb'.mat (py y yo) = ra'.mat y) :
    (t.on gx px gy py ga pa ra' rb' κ σ).OK :=
  ⟨h.1.on gx px κ σ hi ho, fun y _ => hm y _⟩

end Stage

/-! ### Conditions that are carried along -/

/-- The relations c with one more condition for soundness and one more for the honest run. -/
def Cut.and (c : Cut P E a) (K : a.X → a.Y → Prop) (KH : a.I → (P → E) → a.X → a.Y → Prop) :
    Cut P E a :=
  ⟨fun x y => c.R x y ∧ K x y, fun s π x y => c.Hn s π x y ∧ KH s π x y, c.V⟩

/-- Frame rule for stages. Conditions may be added before and after a stage if, for soundness, the
one after it implies the one before it, and, for the honest run, the one before it implies the one
after it. For both implications the stage's own relations may be assumed, and that the outputs are
those that the stage computes. -/
theorem Stage.Props.frame {S : Stage P E a b} {ca : Cut P E a} {cb : Cut P E b} (h : S.Props ca cb)
    {K : a.X → a.Y → Prop} {K' : b.X → b.Y → Prop} {KH : a.I → (P → E) → a.X → a.Y → Prop}
    {KH' : b.I → (P → E) → b.X → b.Y → Prop}
    (hK : ∀ x y τ xo, S.B.pub x τ.rho τ.plains = some xo → ca.R x y → cb.R xo (S.B.imp y τ) →
      K' xo (S.B.imp y τ) → K x y)
    (hKH : ∀ s π x y ρ xo, ρ ∉ S.H.withheld s → S.B.pub x ρ (S.H.tr s π ρ).plains = some xo →
      ca.Hn s π x y → cb.Hn (S.H.next s ρ) π xo (S.B.imp y (S.H.tr s π ρ)) → KH s π x y →
      KH' (S.H.next s ρ) π xo (S.B.imp y (S.H.tr s π ρ))) :
    S.Props (ca.and K KH) (cb.and K' KH') where
  clean := h.clean.frame hK
  acc := h.acc.frame hKH
  masked := h.masked
  keeps := h.keeps
  prBad := h.prBad
  prWin := h.prWin

end Blocks
