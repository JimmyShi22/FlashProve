-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbChain.lean: the typed rounds of a chain (OnBytes/TypedOracleCompiler/Run/PlanQS.lean) are the typed rounds
of the chain with every round's proof of work set to 0, with the bits added (E2E/ClimbPair.lean).

A round's data (`RD`) hold an entry of the type that a round has in the list of rounds with error
bounds (the library's word: the plan), and the entry holds the number of proof-of-work bits
(`work`). The typed round (`roundS`) has a nonce in its plain part and these bits in its verifier
message. `rd0 d` is d with `work := 0`: its typed round has neither.

Main names:
  `entry0`, `rd0`: an entry, a round's data, with no proof of work.
  `KitFree C`: the kit C of verifier messages does not read an entry's proof of work: the types at e
    and at `entry0 e` are in bijection, and what is sampled is the same. `kitFree_ck`,
    `kitFree_ckP`: so it is at sampled values and at hash blocks, with the identity as bijection.
  `Z0 l₀ l`: l₀ is the list l of rounds' data with every round's proof of work set to 0.
    `z0 ds : Z0 (ds.map rd0) ds`.
  `rpZ`, `pairZ`: the pair with bits, one round and a chain: the nonce 0 and bits 0 put in; nonce
    and bits dropped; the test is the round's proof-of-work check.
  `bitsZ`, `pairZ_bits`: the list of the numbers of bits; the round with proof of work has 2^b times
    the verifier messages.
  `rv_strip`, `drawn_strip`, `col_strip`, `treeSh_z0`: what a view is made of is the same at a
    transcript and at the stripped transcript. `pass_pairZ`: the pair's test is the chain's
    proof-of-work checks. `pass_zero`: without proof of work every transcript passes them.

Limits: definitions and equations. Nothing on soundness here.

"Without proof of work" is a reading of this folder's writers: the same rounds' data with the number
of proof-of-work bits set to 0, under the same decision functions. Whether that protocol may stand
for "the IOP without proof of work" is an open question, which no theorem here settles.

This file's definitions may be read as part of a goal: they fix the protocol of which the clauses of
E2E/ClimbFiles.lean are stated. They count as none.




-/
import E2E.ClimbPair
import Iop.GrindProofs
import OnBytes.TypedOracleCompiler.Run.PlanQS
import Run.PlanPull
import Run.PlanDrawsQ

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Climb
open Iop Prob
open TypedOracleCompiler.Run.PQ (RD roundS SL uL drawnSL passSL rhoSL rvSL colAtS treeSh posAtT colT)
open _root_.Run.PQ (CK PlainOf)

/-! ## 1. Data without proof of work -/

/-- The entry with no proof of work. -/
def entry0 (e : _root_.Fmt.Entry) : _root_.Fmt.Entry := { e with work := 0 }

/-- A round's data with no proof of work. -/
def rd0 (d : RD) : RD := ⟨entry0 d.entry, d.kind, d.items, d.trees, d.opens⟩

/-- The kit does not read an entry's proof of work. -/
structure KitFree (C : CK) where
  eqv : ∀ (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind), C.Ch (entry0 e) k ≃ C.Ch e k
  dr : ∀ (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) (c : C.Ch (entry0 e) k),
    C.dr e k (eqv e k c) = C.dr (entry0 e) k c

/-- The list of what a round samples does not read the proof of work. -/
theorem dsOf_entry0 (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) :
    _root_.Fmt.dsOf (entry0 e) k = _root_.Fmt.dsOf e k := rfl

/-- Verifier messages as sampled values. -/
def kitFree_ck (f : _root_.Fmt.Fld) : KitFree (_root_.Run.ck f) :=
  ⟨fun e k => Equiv.refl ((_root_.Run.ck f).Ch e k), fun _ _ _ => rfl⟩

/-- Verifier messages as hash blocks. -/
def kitFree_ckP (f : _root_.Fmt.Fld) : KitFree (_root_.Run.ckP f) :=
  ⟨fun e k => Equiv.refl ((_root_.Run.ckP f).Ch e k), fun _ _ _ => rfl⟩

/-- l₀ is l with every round's proof of work set to 0. -/
inductive Z0 : List RD → List RD → Type
  | nil : Z0 [] []
  | cons (d : RD) {l₀ l : List RD} (z : Z0 l₀ l) : Z0 (rd0 d :: l₀) (d :: l)

/-- The list made by `rd0`. -/
def z0 : (ds : List RD) → Z0 (ds.map rd0) ds
  | [] => .nil
  | d :: ds => .cons d (z0 ds)

/-! ## 2. The pair with bits -/

theorem KitFree.dr_symm {C : CK} (K : KitFree C) (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind)
    (c : C.Ch e k) : C.dr (entry0 e) k ((K.eqv e k).symm c) = C.dr e k c := by
  rw [← K.dr, Equiv.apply_symm_apply]

variable (C : CK) (K : KitFree C)

/-- One round: the nonce 0 put in and dropped; through the kit's bijection, bits 0 put in and
dropped; the proof-of-work check. -/
def rpZ (d : RD) : RPair (roundS C (rd0 d)).up (roundS C d).up where
  fill := fun m => (m.1, GPlain.mk d.entry.work (m.2 : PlainOf d.items) (default : ℕ))
  strip := fun m' => (m'.1, (GPlain.old (b := d.entry.work) m'.2 : PlainOf d.items))
  zero := fun c => GChal.zero d.entry.work (K.eqv d.entry d.kind c)
  old := fun c' => (K.eqv d.entry d.kind).symm (GChal.old (b := d.entry.work) c')
  pass := fun c' => GChal.pass (b := d.entry.work) c'
  strip_fill := fun m =>
    Prod.ext rfl (GPlain.old_mk d.entry.work (m.2 : PlainOf d.items) (default : ℕ))
  old_zero := fun c => by
    show (K.eqv d.entry d.kind).symm (GChal.old (b := d.entry.work)
      (GChal.zero d.entry.work (K.eqv d.entry d.kind c))) = c
    rw [GChal.old_zero, Equiv.symm_apply_apply]
  pass_zero := fun c => GChal.pass_zero d.entry.work (K.eqv d.entry d.kind c)
  zero_old := fun c' h => by
    show GChal.zero d.entry.work (K.eqv d.entry d.kind
      ((K.eqv d.entry d.kind).symm (GChal.old (b := d.entry.work) c'))) = c'
    rw [Equiv.apply_symm_apply]
    exact GChal.zero_old h

/-- The typed rounds with proof of work are the typed rounds without, with the bits added. -/
def pairZ : {l₀ l : List RD} → Z0 l₀ l → Pair (uL C l₀) (uL C l)
  | _, _, .nil => ()
  | _, _, .cons d z => (rpZ C K d, pairZ z)

/-- The numbers of proof-of-work bits, round by round. -/
def bitsZ : {l₀ l : List RD} → Z0 l₀ l → GBits (uL C l₀)
  | _, _, .nil => ()
  | _, _, .cons d z => (d.entry.work, bitsZ z)

theorem pairZ_bits : ∀ {l₀ l : List RD} (z : Z0 l₀ l), (pairZ C K z).toEmb.Bits (bitsZ C z)
  | _, _, .nil => trivial
  | _, _, .cons d z =>
    ⟨(GChal.card_eq d.entry.work (C.Ch d.entry d.kind)).trans
      (congrArg (· * 2 ^ d.entry.work) (Fintype.card_congr (K.eqv d.entry d.kind)).symm),
      pairZ_bits z⟩

/-! ## 3. What a view is made of -/

/-- The rounds of a view. -/
theorem rv_strip : ∀ {l₀ l : List RD} (z : Z0 l₀ l) (τ : Tr (uL C l)),
    rvSL C l₀ ((pairZ C K z).strip τ) = rvSL C l τ
  | _, _, .nil, _ => rfl
  | _, _, .cons (l₀ := l₀) (l := l) d z, (m, c, τ) => by
      show (⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
          C.dr (entry0 d.entry) d.kind
            ((K.eqv d.entry d.kind).symm (GChal.old (b := d.entry.work) c))⟩ ::
          rvSL C l₀ ((pairZ C K z).strip τ) : List _root_.Fmt.RoundView) =
        ⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
          C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ :: rvSL C l τ
      rw [K.dr_symm, rv_strip z τ]

/-- What was sampled. -/
theorem drawn_strip : ∀ {l₀ l : List RD} (z : Z0 l₀ l) (τ : Tr (uL C l)),
    drawnSL C l₀ (rhoSL C l₀ ((pairZ C K z).strip τ)) = drawnSL C l (rhoSL C l τ)
  | _, _, .nil, _ => rfl
  | _, _, .cons (l₀ := l₀) (l := l) d z, (m, c, τ) => by
      show C.dr (entry0 d.entry) d.kind
            ((K.eqv d.entry d.kind).symm (GChal.old (b := d.entry.work) c)) ::
          drawnSL C l₀ (rhoSL C l₀ ((pairZ C K z).strip τ)) =
        C.dr d.entry d.kind (GChal.old (b := d.entry.work) c) :: drawnSL C l (rhoSL C l τ)
      rw [K.dr_symm, drawn_strip z τ]

/-- The pair's test is the chain's proof-of-work checks. -/
theorem pass_pairZ : ∀ {l₀ l : List RD} (z : Z0 l₀ l) (τ : Tr (uL C l)),
    (pairZ C K z).passTr τ = passSL C l (rhoSL C l τ)
  | _, _, .nil, _ => rfl
  | _, _, .cons (l := l) d z, (m, c, τ) => by
      show (GChal.pass (b := d.entry.work) c && (pairZ C K z).passTr τ) =
        (GChal.pass (b := d.entry.work) c && passSL C l (rhoSL C l τ))
      rw [pass_pairZ z τ]

/-- Without proof of work the checks are passed by all verifier messages. -/
theorem pass_zero : ∀ {l₀ l : List RD} (_ : Z0 l₀ l) (ρ : Rho (uL C l₀)), passSL C l₀ ρ = true
  | _, _, .nil, _ => rfl
  | _, _, .cons (l₀ := l₀) d z, (c, ρ) => by
      show (GChal.pass (b := 0) (C := C.Ch (entry0 d.entry) d.kind) c && passSL C l₀ ρ) = true
      rw [pass_zero z ρ, Bool.and_true]
      exact (GChal.pass_iff (b := 0) c).2 fun i => i.elim0

/-- The column at (tree, leaf). -/
theorem col_strip : ∀ {l₀ l : List RD} (z : Z0 l₀ l) (τ : Tr (uL C l)) (n x : ℕ),
    colAtS C l₀ ((pairZ C K z).strip τ) n x = colAtS C l τ n x
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons (l₀ := l₀) (l := l) d z, (m, c, τ), n, x => by
      show (if n < d.trees.length then (posAtT d.trees n x).map fun p => colT d.trees p (m.1 p)
          else colAtS C l₀ ((pairZ C K z).strip τ) (n - d.trees.length) x) =
        if n < d.trees.length then (posAtT d.trees n x).map fun p => colT d.trees p (m.1 p)
          else colAtS C l τ (n - d.trees.length) x
      rw [col_strip z τ]

end AtPublicFiles.Climb

namespace AtPublicFiles.Climb
open TypedOracleCompiler.Run.PQ (RD treeSh)

/-- The trees' shapes. -/
theorem treeSh_z0 : ∀ {l₀ l : List RD} (_ : Z0 l₀ l) (n : ℕ), treeSh l₀ n = treeSh l n
  | _, _, .nil, _ => rfl
  | _, _, .cons (l₀ := l₀) (l := l) d z, n => by
      show (if n < d.trees.length then d.trees[n]? else treeSh l₀ (n - d.trees.length)) =
        if n < d.trees.length then d.trees[n]? else treeSh l (n - d.trees.length)
      rw [treeSh_z0 z]

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.kitFree_ckP
#print axioms AtPublicFiles.Climb.pairZ_bits
#print axioms AtPublicFiles.Climb.rv_strip
#print axioms AtPublicFiles.Climb.col_strip
