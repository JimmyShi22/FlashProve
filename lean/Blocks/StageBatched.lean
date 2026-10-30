-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/StageBatched.lean: the batched sumcheck, as one stage. (Words of this library:
lean/GLOSSARY.md.)

The protocol. The claim is val(f) = ∑_x ∑_b W_b(x) A_b(x) B_b(x) over a hypercube, for nb members b,
with W_b public and A_b, B_b hidden. The verifier keeps a list of deferred claims (`Ledger`,
Blocks/Form.lean: LIN, REL, opened forms).
 1. A masked sumcheck in the plain form (weights 1 and 1: `plainW`, Alg/SumCheck.lean) for Φ = ∑_b
    W_b A_b B_b, with end point ζ and end form f_end.
 2. The prover sends, in one message, the masked scalars A*_b, B*_b, honestly A_b(ζ), B_b(ζ), in the
    order A*_0, B*_0, A*_1, B*_1, ...
 3. The verifier checks that its list is well-formed (every term of a REL refers to an opened form
    on the list), opens the 2 nb forms of these scalars and adds REL(f_end; ∑_b W_b(ζ) A*_b B*_b).
Afterwards the claims are val(A*_b) = A_b(ζ) and val(B*_b) = B_b(ζ), for the caller to go on with.

How it is stated. All that the caller's explicit part (Blocks/Block.lean) holds (the list among it)
is the public data Ξ of the sumcheck, and all of the caller's honest state (its copy of the list
among it) is the state A of the sumcheck's prover; they are carried along unchanged. The stage ends
with the old data and the new list side by side; the caller arranges them as it likes. Q and QH are
conditions of the caller that are carried along.
 * `SCB`: the format (what the protocol uses). `SCB.Vecs`: the true objects A_b, B_b, an argument T
   of relations and theorems only, so that no true object occurs in the term of a protocol.
   `SCB.sc`, `SCB.phi T`: the sumcheck's format and true polynomial. `SCB.Prover`: the honest
   prover.
 * `SCB.Prover.core`, `stage`; `cIn`, `cOut`; `props_stage`.
 * `rounds_stage` (one round for each variable and one for the end scalars); `len_finH` (the
   prover's copy of the list gains 2 nb opened forms and one REL).

The scalars of a round are a parameter of the format (`SCB.bas`; Alg/RoundBasis.lean). By default
they are the value at 0 and the coefficients of X², X³, .. (Blocks/SumCheckBlock.lean). For degree
3, `Alg.Basis.cubic` sends the values at 0 and -1 and the coefficient of X³; outside
Alg/RoundBasis.lean no file of this library uses it.
The verifier's only check during the run is that of step 3; it reads the explicit part only.
Notation: `Y`, `P`: types: Y the type of implicit parts, P the set of pads; `e : ι → ℕ`: the round
that binds the variable i has e i + 1 masked scalars; `idx : (i : ι) → Fin (e i + 1) → P`: their
pads (these four: `SC`, Blocks/SumCheckBlock.lean); `proj : Y → N → E`, `place : P → N`: proj gives
the entries of the implicit part, and place says which entry holds a pad (`Forms.ofForm`,
Blocks/RelForm.lean); `W : Ξ → Fin nb → (ι → E) → E`: the W_b of the claim above.
-/
import Blocks.StageRows
import Blocks.HLed
import Blocks.StageNums
import Blocks.StageCount
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Iop Prob Alg Finset
open scoped ENNReal

/-- The format of a batched sumcheck: what the protocol uses. N: the entries of forms, Ξ: the
caller's explicit part, ι: the variables. -/
structure SCB (E Y P N Ξ ι : Type) [Field E] where
  proj : Y → N → E
  place : P → N
  /-- the list, in the caller's explicit part -/
  led : Ξ → Ledger N E
  e : ι → ℕ
  idx : (i : ι) → Fin (e i + 1) → P
  nb : ℕ
  W : Ξ → Fin nb → (ι → E) → E
  /-- the pads of A*_b (false) and B*_b (true) -/
  idxE : Fin nb × Bool → P
  /-- in which scalars the polynomial of the round that binds i is sent (Alg/RoundBasis.lean); by
  default the value at 0 and the coefficients of X², ..., X^(e i + 1) -/
  bas : (i : ι) → Basis E (e i) := fun i => Basis.coeff E (e i)

/-- The true objects of a batched sumcheck: the two hidden families, as functions of the implicit
part. They occur in relations and theorems only, never in the protocol. -/
structure SCB.Vecs (E Y Ξ ι : Type) (nb : ℕ) where
  Af : Ξ → Y → Fin nb → (ι → E) → E
  Bf : Ξ → Y → Fin nb → (ι → E) → E

namespace SCB

variable {E Y P N Ξ ι A : Type} [Field E] [Fintype E] [DecidableEq E] [DecidableEq ι] [Fintype N]
  [DecidableEq N] (B : SCB E Y P N Ξ ι)

/-- the sumcheck, in the plain form; no block divides by its challenges -/
def sc : SC E Y P Ξ ι where
  forms := Forms.ofForm B.proj B.place
  wt := fun _ => plainW
  e := B.e
  idx := B.idx
  nzv := fun _ => false
  bas := B.bas

/-- the true polynomial Φ = ∑_b W_b A_b B_b -/
def phi (T : SCB.Vecs E Y Ξ ι B.nb) (ξ : Ξ) (y : Y) (z : ι → E) : E :=
  ∑ b, B.W ξ b z * T.Af ξ y b z * T.Bf ξ y b z

/-- the member and the side of the end scalar number k -/
def key (k : Fin (2 * B.nb)) : Fin B.nb × Bool :=
  (⟨k.val / 2, by have := k.2; omega⟩, decide (k.val % 2 = 1))

/-- the forms of the end scalars, in the order A*_0, B*_0, A*_1, B*_1, ... -/
def os (m : Fin B.nb × Bool → E) : List (Form N E) :=
  List.ofFn fun k : Fin (2 * B.nb) => Form.masked (m (B.key k)) (B.place (B.idxE (B.key k)))

/-- the terms of the REL, with coefficients w -/
def ts (w : Fin B.nb → E) : List (E × ℕ × ℕ) :=
  (List.finRange B.nb).map fun b => (w b, 2 * b.val, 2 * b.val + 1)

theorem length_os (m : Fin B.nb × Bool → E) : (B.os m).length = 2 * B.nb := List.length_ofFn

theorem ts_lt (w : Fin B.nb → E) (m : Fin B.nb × Bool → E) :
    ∀ t ∈ B.ts w, t.2.1 < (B.os m).length ∧ t.2.2 < (B.os m).length := by
  intro t ht
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp ht
  rw [length_os]
  have := b.2
  exact ⟨by show 2 * b.val < _; omega, by show 2 * b.val + 1 < _; omega⟩

theorem getD_ofFn' {α : Type} {n : ℕ} (f : Fin n → α) (d : α) {i : ℕ} (hi : i < n) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]

/-- What the REL says: for any list of 2 nb values u, in the order of the end scalars. -/
theorem termSum_ofFn (w : Fin B.nb → E) (u : Fin B.nb × Bool → E) :
    termSum (fun i => (List.ofFn fun k : Fin (2 * B.nb) => u (B.key k)).getD i 0) (B.ts w) =
      ∑ b, w b * u (b, false) * u (b, true) := by
  unfold termSum ts
  rw [List.map_map, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  have hb := b.2
  have h0 : 2 * b.val < 2 * B.nb := by omega
  have h1 : 2 * b.val + 1 < 2 * B.nb := by omega
  show w b * (List.ofFn fun k : Fin (2 * B.nb) => u (B.key k)).getD (2 * b.val) 0 *
      (List.ofFn fun k : Fin (2 * B.nb) => u (B.key k)).getD (2 * b.val + 1) 0 = _
  rw [getD_ofFn' _ _ h0, getD_ofFn' _ _ h1]
  have k0 : B.key ⟨2 * b.val, h0⟩ = (b, false) := by
    unfold key
    refine Prod.ext (Fin.ext ?_) ?_
    · show 2 * b.val / 2 = b.val
      omega
    · show decide (2 * b.val % 2 = 1) = false
      exact decide_eq_false (by omega)
  have k1 : B.key ⟨2 * b.val + 1, h1⟩ = (b, true) := by
    unfold key
    refine Prod.ext (Fin.ext ?_) ?_
    · show (2 * b.val + 1) / 2 = b.val
      omega
    · show decide ((2 * b.val + 1) % 2 = 1) = true
      exact decide_eq_true (by omega)
  rw [k0, k1]

theorem map_val_os (y : N → E) (m : Fin B.nb × Bool → E) :
    (B.os m).map (fun g => Form.val y g) =
      List.ofFn fun k : Fin (2 * B.nb) => m (B.key k) - y (B.place (B.idxE (B.key k))) := by
  unfold os
  rw [List.map_ofFn]
  congr 1
  funext k
  exact Form.val_masked _ _ _

theorem termSum_os (y : N → E) (w : Fin B.nb → E) (m : Fin B.nb × Bool → E) :
    termSum (fun i => Form.val y ((B.os m).getD i 0)) (B.ts w) =
      ∑ b, w b * (m (b, false) - y (B.place (B.idxE (b, false)))) *
        (m (b, true) - y (B.place (B.idxE (b, true)))) := by
  rw [← B.termSum_ofFn w fun k => m k - y (B.place (B.idxE k))]
  refine termSum_congr (fun i => ?_) _
  rw [← B.map_val_os y m, ← map_zero (Form.val y), List.getD_map]

/-! ## The honest prover -/

/-- The honest prover's data: its copy of the list, and the three families of polynomials, as
functions of its state. -/
structure Prover (A : Type) where
  hl : A → HLed E
  W : A → Fin B.nb → (ι → E) → E
  Af : A → Fin B.nb → (ι → E) → E
  Bf : A → Fin B.nb → (ι → E) → E
  deg : ∀ a, DegLE (fun i => B.e i + 1) fun z => ∑ b, W a b z * Af a b z * Bf a b z
  /-- a condition on the format's scalars, which completeness uses (`SC.Prover.cmp`); for the
  default scalars its proof is filled in -/
  cmp : ∀ i, Function.Injective (node (B.e i) : Fin (B.e i + 2) → E) →
      ∀ w : Bool → E, w true ≠ 0 → (B.bas i).Complete w := by
    exact fun _ hn _ hw => Alg.Basis.complete_coeff hn hw

namespace Prover

variable {B} (H : B.Prover A)

/-- the honest prover of the sumcheck -/
def pr : B.sc.Prover A where
  wt := fun _ => plainW
  Φ := fun a z => ∑ b, H.W a b z * H.Af a b z * H.Bf a b z
  deg := H.deg
  cmp := H.cmp

/-- the honest values of the end scalars -/
def endVal (s : A × (ι → E)) (k : Fin B.nb × Bool) : E :=
  if k.2 = true then H.Bf s.1 k.1 s.2 else H.Af s.1 k.1 s.2

/-- the statement types: during the sumcheck; with the end scalars; at the end -/
abbrev t0 (_H : B.Prover A) : Sorts := ⟨B.sc.X, Y, A × (ι → E)⟩
abbrev t1 (_H : B.Prover A) : Sorts := ⟨B.sc.X × (Fin B.nb × Bool → E), Y, A × (ι → E)⟩
abbrev t2 (_H : B.Prover A) : Sorts :=
  ⟨(Ξ × Ledger N E) × (ι → E) × (Fin B.nb × Bool → E), Y, (A × HLed E) × (ι → E)⟩

/-- what the verifier does at the end: it checks that its list is well-formed, opens the forms of
the end scalars and adds the REL -/
def fin (x : B.sc.X × (Fin B.nb × Bool → E)) :
    Option ((Ξ × Ledger N E) × (ι → E) × (Fin B.nb × Bool → E)) :=
  if (B.led x.1.2.2).wf = true then
    some ((x.1.2.2, (B.led x.1.2.2).addRel x.1.1 (B.os x.2) (B.ts fun b => B.W x.1.2.2 b x.1.2.1)),
      x.1.2.1, x.2)
  else none

/-- what the honest prover adds to its list -/
def finH (s : A × (ι → E)) : (A × HLed E) × (ι → E) :=
  ((s.1, (H.hl s.1).addRel (List.ofFn fun k : Fin (2 * B.nb) => H.endVal s (B.key k))
        (B.ts fun b => H.W s.1 b s.2)),
    s.2)

/-- The protocol. -/
def core (l : List ι) : Core P E H.t0 H.t2 :=
  (H.pr.core l).seq ((Core.nameScalars H.t0 B.idxE H.endVal).seq (Core.pure fin id H.finH))

variable [Fintype P] [DecidableEq P]

/-- The batched sumcheck that binds the variables of l, as a stage. -/
def stage (l : List ι) : Stage P E H.t0 H.t2 :=
  (H.pr.stage l).seq ((Stage.nameScalars H.t0 B.idxE H.endVal).seq (Stage.pure fin id H.finH))

theorem toCore_stage (l : List ι) : (H.stage l).toCore = H.core l := rfl

section Cuts
variable (T : SCB.Vecs E Y Ξ ι B.nb) (Link : A → (P → E) → Ξ → Y → Prop) (Q : Ξ → Y → Prop)
  (QH : A → (P → E) → Ξ → Y → Prop) (V : A → Prop)

/-- what is carried along during the sumcheck -/
def KS (x : B.sc.X) (y : Y) : Prop := (B.led x.2.2).True (B.proj y) ∧ Q x.2.2 y
def KHS (s : A × (ι → E)) (π : P → E) (x : B.sc.X) (y : Y) : Prop :=
  (H.hl s.1).Good (B.led x.2.2) (B.proj y) ∧ QH s.1 π x.2.2 y

/-- Before: the start claim; the list is true; the caller's conditions. -/
def cIn (l : List ι) : Cut P E H.t0 :=
  Cut.and ⟨B.sc.Rsum (B.phi T) l, H.pr.Hsum Link l, fun s => V s.1⟩ (KS Q) (H.KHS QH)
/-- after the rounds -/
def cMid : Cut P E H.t0 :=
  Cut.and ⟨B.sc.Reval (B.phi T), H.pr.Hsum Link [], fun s => V s.1⟩ (KS Q) (H.KHS QH)

/-- the value of an end scalar -/
def valE (y : Y) (m : Fin B.nb × Bool → E) (k : Fin B.nb × Bool) : E :=
  m k - B.proj y (B.place (B.idxE k))
/-- the true end values -/
def trueE (x : B.sc.X) (y : Y) (k : Fin B.nb × Bool) : E :=
  if k.2 = true then T.Bf x.2.2 y k.1 x.2.1 else T.Af x.2.2 y k.1 x.2.1

/-- with the end scalars -/
def cNamed : Cut P E H.t1 :=
  ⟨fun xo y =>
      ((Form.val (B.proj y) xo.1.1 =
          ∑ b, B.W xo.1.2.2 b xo.1.2.1 * valE y xo.2 (b, false) * valE y xo.2 (b, true)) ∧
        KS Q xo.1 y) ∧
      valE y xo.2 = trueE T xo.1 y,
    fun s π xo y =>
      (H.cMid T Link Q QH V).Hn s π xo.1 y ∧ xo.2 = fun k => H.endVal s k + π (B.idxE k),
    fun s => V s.1⟩

/-- After: the new list is true; the caller's conditions; the end scalars have the values of the two
families at the end point. -/
def cOut : Cut P E H.t2 :=
  ⟨fun x y =>
      x.1.2.True (B.proj y) ∧
      Q x.1.1 y ∧
      ∀ b,
        valE y x.2.2 (b, false) = T.Af x.1.1 y b x.2.1 ∧
        valE y x.2.2 (b, true) = T.Bf x.1.1 y b x.2.1,
    fun s π x y =>
      Link s.1.1 π x.1.1 y ∧ x.2.1 = s.2 ∧ s.1.2.Good x.1.2 (B.proj y) ∧ QH s.1.1 π x.1.1 y ∧
      x.2.2 = fun k => H.endVal (s.1.1, s.2) k + π (B.idxE k),
    fun s => V s.1.1⟩

end Cuts

/-- What the caller's relation `Link` between the honest state and the statement has to give: the
families are the prover's, and the pads of the stage are entries of the implicit part. -/
structure LinkOK (T : SCB.Vecs E Y Ξ ι B.nb) (Link : A → (P → E) → Ξ → Y → Prop) (l : List ι) :
    Prop where
  W : ∀ a π ξ y, Link a π ξ y → B.W ξ = H.W a
  Af : ∀ a π ξ y, Link a π ξ y → T.Af ξ y = H.Af a
  Bf : ∀ a π ξ y, Link a π ξ y → T.Bf ξ y = H.Bf a
  pads : ∀ a π ξ y, Link a π ξ y → ∀ p ∈ B.sc.padsOf l, B.proj y (B.place p) = π p
  padsE : ∀ a π ξ y, Link a π ξ y → ∀ k, B.proj y (B.place (B.idxE k)) = π (B.idxE k)

variable (T : SCB.Vecs E Y Ξ ι B.nb) {Link : A → (P → E) → Ξ → Y → Prop} {Q : Ξ → Y → Prop}
  {QH : A → (P → E) → Ξ → Y → Prop} {V : A → Prop}

theorem props_rounds (hdeg : ∀ ξ y, DegLE (fun i => B.e i + 1) (B.phi T ξ y))
    (hnode : ∀ i, Function.Injective (node (B.e i) : Fin (B.e i + 2) → E))
    (hbas : ∀ i, (B.bas i).Sound (plainW i)) {l : List ι} (hp : B.sc.PlacesOnceOn l)
    (hl : l.Nodup) (hL : H.LinkOK T Link l) :
    (H.pr.stage l).Props (H.cIn T Link Q QH V l) (H.cMid T Link Q QH V) := by
  refine (H.pr.props_stage ⟨Forms.ofForm_ok _ _, hdeg, fun _ i _ => hbas i⟩ hnode (fun _ => rfl)
      hp hl (Link := Link)
      (fun a π ξ y h => ⟨rfl, fun p hpp => (Form.val_ent _ _).trans (hL.pads a π ξ y h p hpp)⟩)
      V).frame
    (K := KS Q) (K' := KS Q) (KH := H.KHS QH) (KH' := H.KHS QH)
    (fun x y τ xo hxo _ _ hK => ?_) fun s π x y ρ xo _ hxo _ _ hK => ?_
  · have h1 : xo.2.2 = x.2.2 := B.sc.data_of_pub_sc _ _ _ _ _ hxo
    have h2 : (B.sc.sc l).imp y τ = y := B.sc.imp_sc _ _ _
    have hK' : KS Q xo ((B.sc.sc l).imp y τ) := hK
    rw [h2] at hK'
    unfold KS at hK' ⊢
    rwa [h1] at hK'
  · have h1 : xo.2.2 = x.2.2 := B.sc.data_of_pub_sc _ _ _ _ _ hxo
    have h2 : ∀ τ, (B.sc.sc l).imp y τ = y := fun τ => B.sc.imp_sc _ _ _
    have h3 : ((H.pr.sc l []).next s ρ).1 = s.1 := H.pr.next_fst _ _ _ _
    show H.KHS QH ((H.pr.sc l []).next s ρ) π xo ((B.sc.sc l).imp y _)
    rw [h2]
    unfold KHS at hK ⊢
    rwa [h1, h3]

theorem props_named (hidx : Function.Injective B.idxE) :
    (Stage.nameScalars (E := E) H.t0 B.idxE H.endVal).Props
      (H.cMid T Link Q QH V) (H.cNamed T Link Q QH V) :=
  (Stage.props_nameScalars (a := H.t0) B.idxE hidx H.endVal
      (fun y p => B.proj y (B.place p)) (trueE T)
      (fun T x y =>
        (Form.val (B.proj y) x.1 = ∑ b, B.W x.2.2 b x.2.1 * T (b, false) * T (b, true)) ∧ KS Q x y)
      (H.cMid T Link Q QH V).Hn fun s => V s.1).conseq
    (fun _ _ h => ⟨fun _ => h.1, h.2⟩) (fun _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
    (fun _ h => h) fun _ h => h

theorem props_fin {l : List ι} (hL : H.LinkOK T Link l) :
    (Stage.pure (P := P) (E := E) (a := H.t1) (b := H.t2) fin id H.finH).Props
      (H.cNamed T Link Q QH V) (H.cOut T Link Q QH V) := by
  refine Stage.props_pure (fun x y xo hxo hR => ?_) (fun s π x y hH => ?_) fun _ h => h
  · unfold fin at hxo
    by_cases hwf : (B.led x.1.2.2).wf = true
    · rw [if_pos hwf] at hxo
      obtain rfl := Option.some.inj hxo
      obtain ⟨hT, hQ, hE⟩ := hR
      obtain ⟨hT0, hrel⟩ := (Ledger.true_addRel hwf _ _ _ _).mp hT
      rw [B.termSum_os] at hrel
      refine ⟨⟨hrel, hT0, hQ⟩, funext fun k => ?_⟩
      obtain ⟨b, c⟩ := k
      cases c
      · exact (hE b).1
      · exact (hE b).2
    · rw [if_neg hwf] at hxo
      exact absurd hxo (by simp)
  · obtain ⟨⟨⟨hLk, hz, -, -, hval⟩, hG, hQH⟩, hm⟩ := hH
    have hW := hL.W _ _ _ _ hLk
    have hpad := hL.padsE _ _ _ _ hLk
    have hv : ∀ k, x.2 k - B.proj y (B.place (B.idxE k)) = H.endVal s k := fun k => by
      rw [hm, hpad k]
      exact add_sub_cancel_right _ _
    have hrel : Form.val (B.proj y) x.1.1 =
        termSum (fun i => Form.val (B.proj y) ((B.os x.2).getD i 0))
          (B.ts fun b => B.W x.1.2.2 b x.1.2.1) := by
      have hval' : Form.val (B.proj y) x.1.1 =
          ∑ b, H.W s.1 b s.2 * H.Af s.1 b s.2 * H.Bf s.1 b s.2 := hval
      rw [B.termSum_os, hval']
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hv, hv, hW, hz]
      rfl
    have hG' := hG.addRel (B.ts_lt (fun b => B.W x.1.2.2 b x.1.2.1) x.2) hrel
    refine ⟨_, if_pos hG.2.1, hLk, hz, ?_, hQH, ?_⟩
    · have e1 : (B.os x.2).map (fun g => Form.val (B.proj y) g) =
          List.ofFn fun k : Fin (2 * B.nb) => H.endVal s (B.key k) := by
        rw [B.map_val_os]
        congr 1
        funext k
        exact hv _
      have e2 : (B.ts fun b => B.W x.1.2.2 b x.1.2.1) = B.ts fun b => H.W s.1 b s.2 := by
        rw [hW, hz]
      show ((H.hl s.1).addRel (List.ofFn fun k : Fin (2 * B.nb) => H.endVal s (B.key k))
          (B.ts fun b => H.W s.1 b s.2)).Good
        ((B.led x.1.2.2).addRel x.1.1 (B.os x.2) (B.ts fun b => B.W x.1.2.2 b x.1.2.1)) (B.proj y)
      rw [← e1, ← e2]
      exact hG'
    · exact hm

/-- `Stage.Props`, under the hypotheses below, from the start claim to the claims on the end
scalars. Each round has at most e i + 1 bad values; `Hon.withheld` (Blocks/BlockHon.lean) is empty.
hbas: whatever scalars are sent in a round, they and the round's equation determine a polynomial of
degree at most e i + 1 (for the default scalars: `Alg.Basis.sound_coeff`). -/
theorem props_stage (hdeg : ∀ ξ y, DegLE (fun i => B.e i + 1) (B.phi T ξ y))
    (hnode : ∀ i, Function.Injective (node (B.e i) : Fin (B.e i + 2) → E))
    (hbas : ∀ i, (B.bas i).Sound (plainW i)) {l : List ι} (hp : B.sc.PlacesOnceOn l)
    (hl : l.Nodup) (hidx : Function.Injective B.idxE)
    (hdisj : Disjoint (B.sc.padsOf l) (Set.range B.idxE)) (hL : H.LinkOK T Link l) :
    (H.stage l).Props (H.cIn T Link Q QH V l) (H.cOut T Link Q QH V) :=
  (H.props_rounds T hdeg hnode hbas hp hl hL).seq
    ((H.props_named T hidx).seq (H.props_fin T hL) (Set.disjoint_empty _) (Set.disjoint_empty _))
    (by show Disjoint (B.sc.padsOf l) (Set.range B.idxE ∪ ∅); rw [Set.union_empty]; exact hdisj)
    (by show Disjoint (B.sc.padsOf l) (Set.range B.idxE ∪ ∅); rw [Set.union_empty]; exact hdisj)

/-- The pads with which the stage masks. -/
theorem stage_U (l : List ι) : (H.stage l).U = B.sc.padsOf l ∪ Set.range B.idxE := by
  show B.sc.padsOf l ∪ (Set.range B.idxE ∪ ∅) = _
  rw [Set.union_empty]

theorem stage_D (l : List ι) : (H.stage l).D = B.sc.padsOf l ∪ Set.range B.idxE := by
  show B.sc.padsOf l ∪ (Set.range B.idxE ∪ ∅) = _
  rw [Set.union_empty]

/-- One round for each variable, and one for the end scalars. -/
theorem rounds_stage (l : List ι) : (H.stage l).rounds = l.length + 1 := by
  unfold stage
  rw [Stage.rounds_seq, Stage.rounds_seq, SC.Prover.rounds_stage]
  rfl

/-- A common bound for the errors. -/
theorem below_stage {κ : ℝ≥0∞}
    (h : ∀ i, ((B.e i + 1 : ℕ) : ℝ≥0∞) ≤ κ * Fintype.card E) (l : List ι) : (H.stage l).Below κ :=
  (SC.Prover.below_stage H.pr h l).seq
    ((Stage.below_nameScalars κ B.idxE H.endVal).seq
      (Stage.below_pure (a := H.t1) (b := H.t2) κ fin id H.finH))

/-- The honest prover's copy of the list gains no LIN, 2 nb opened forms and one REL. -/
theorem len_finH (s : A × (ι → E)) :
    (H.finH s).1.2.len =
      ((H.hl s.1).len.1, (H.hl s.1).len.2.1 + 2 * B.nb, (H.hl s.1).len.2.2 + 1) := by
  unfold finH
  rw [HLed.len_addRel, List.length_ofFn]

section Track
variable {F : Type} [Field F] [Algebra F E]

/-- what is exposed at the end: what was exposed at the start -/
abbrev readsOut (ra : Reads F E H.t0) : Reads F E H.t2 := ⟨ra.N, ra.rd, ra.mat⟩

abbrev readsMid (ra : Reads F E H.t0) : Reads F E H.t1 :=
  Stage.readsX (B.sc.X × (Fin B.nb × Bool → E)) (A × (ι → E)) ra

/-- The stage sends no vector. -/
def track (l : List ι) (ra : Reads F E H.t0) : (H.core l).Track ra (H.readsOut ra) :=
  (H.pr.track l ra).seq
    ((Core.trackNameScalars B.idxE H.endVal ra).seq
      (Core.trackPure (a := H.t1) (b := H.t2) fin id H.finH (H.readsMid ra)
        (H.readsOut ra) fun n => n))

theorem track_ok (l : List ι) (ra : Reads F E H.t0) : (H.track l ra).OK :=
  (H.pr.track_ok l ra).seq
    ((Stage.trackNameScalars_ok B.idxE H.endVal ra).seq
      (Stage.trackPure_ok (P := P) (a := H.t1) (b := H.t2) fin id H.finH (H.readsMid ra)
        (H.readsOut ra) (fun n => n) (fun _ _ => rfl) fun _ => rfl))

theorem all_track {Qv : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop} (l : List ι) (ra : Reads F E H.t0) :
    (H.track l ra).All Qv :=
  (SC.Prover.all_track H.pr l ra).seq
    ((Stage.all_trackNameScalars B.idxE H.endVal ra).seq
      (Stage.all_trackPure (P := P) (a := H.t1) (b := H.t2) fin id H.finH (H.readsMid ra)
        (H.readsOut ra) fun n => n))

end Track

end Prover

end SCB

end Blocks
