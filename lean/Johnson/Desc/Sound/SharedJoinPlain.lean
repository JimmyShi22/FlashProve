-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedJoinPlain.lean: THE STRETCH OF THE SHARED CHAIN BEHIND "LIN point", IN THE PLAIN FORM FOR A BATCH, FROM EACH BLOCK's PLAIN LAW FOR ONE
STATEMENT: the call of another file's rule "key alone, by make" (Johnson/Desc/Plain/KeyAlone.lean: `leadsK_of_handsAct`, `LeadsK.beside_sure`) at the
table's own terms (`onQ₂`, `relQ₂`). Definitions, one statement written as `def … : Prop`, and its proof.

What a block's files owe for the block at place k (2 ≤ k), AND NO MORE:
  `EachPlainSh`: ITS PLAIN LAW FOR ONE STATEMENT (`Leads`, at the block's own errors), OF THE SHARED ITEMS ALONE, AT THE ACTING PARTS' VALUES: "the shared promise
    behind holds; and every witness at which the shared items that are open behind hold gives, by the extractor e₀ k (a function of the acting part in
    front and the witness), one at which those that are open in front hold".
  `EachRides`: FOR CERTAIN (at every transcript): the slot's own condition goes on, and the own items ride back along e₀ k. (At `dot` that asks, among
    others, that the shared record's psi_sh is turned by no block behind the point: a debt that has a name and no payer.)
`SharedJoinPlain`: then, for lifted blocks that tile and open no tree below lo: `EachLawsBN` (Johnson/Desc/Sound/KeysByMake.lean: each block's
`LeadsBN` and the hand-over of the condition) at the acting parts as keys, `onQ₂`, and `stepE` with E k a b w := e₀ k (the acting part of a) w: AT EVERY n: NOTHING
OF A SLOT's OWN IS PAID (εO = 0). The laws of keys come by make (that file's keysByMake).

Limits. Those of BordersSharedQ.lean and of KeyAlone.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Plain.KeyAlone
import Johnson.Desc.Sound.KeysByMake
import Johnson.Desc.Sound.StepE
import Johnson.Desc.Sound.BordersSharedQProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (oneExternalString)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Plain (leadsK_of_handsAct)

/-- The type of an acting part's values: one at all borders. -/
abbrev ActV (S₂ : Type) (Fr : Frame) : Type :=
  S₂ × (oneExternalString (2 ^ Fr.a) SgX).Str × (ℕ → ℕ → Option (List UInt64))

section
variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
  (e₀ : ℕ → ActV S₂ Fr → Wt → Wt)

/-- Every shared item that is open at border k holds, at a value of the acting part. -/
def shV (k : ℕ) (v : ActV S₂ Fr) (w : Wt) : Prop :=
  ∀ i, openAfter (insSh split) (outsSh split) startSh k i → muQ N Mg p l i k v w

/-- What a block's plain law for one statement leads to: of the two acting parts' values alone. -/
def stepV (k : ℕ) (v v' : ActV S₂ Fr) : Prop :=
  promQ N Pm split p l (k + 1) v' ∧
    ∀ w, shV N Mg split p l (k + 1) v' w → shV N Mg split p l k v (e₀ k v w)

/-- **Each block's plain law for one statement, of the shared items alone.** -/
def EachPlainSh : ℕ → List (Piece C Fr (P₁ × S₂) Cl Wt) → Prop
  | _, [] => True
  | k, x :: m =>
    x.ior.red.Leads (onQ₂ N Pm Oc split p l k)
        (fun a b => stepV N Mg Pm split p l e₀ k ((actQ N p l k).2 a) ((actQ N p l (k + 1)).2 b))
        x.err ∧
      EachPlainSh (k + 1) m

/-- **For certain: what each slot has of its own rides.** -/
def EachRides : ℕ → List (Piece C Fr (P₁ × S₂) Cl Wt) → Prop
  | _, [] => True
  | k, x :: m =>
    (∀ a τ b, onQ₂ N Pm Oc split p l k a → x.ior.red.out a τ = some b →
      Oc b.1.1 (strsOf Fr b.2) ∧
        ∀ w, relOwn N Mg 2 b w → relOwn N Mg 2 a (e₀ k ((actQ N p l k).2 a) w)) ∧
      EachRides (k + 1) m

end

/-- **The stretch behind "LIN point", in the plain form for a batch, from plain laws for one statement.** -/
def SharedJoinPlain : Prop :=
  ∀ (P₁ S₂ Cl Wt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
    (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool) (n : ℕ)
    (f pt q : Piece C Fr (P₁ × S₂) Cl Wt) (r : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (e₀ : ℕ → ActV S₂ Fr → Wt → Wt),
    Tiled q r →
    (∀ x ∈ q :: r, ∃ b₀ : Block S₂ Cl, x.b = b₀.lift Prod.snd fun t s => (t.1, s)) →
    (∀ x ∈ q :: r, ∀ d ∈ x.ds, ∀ j ∈ d.opens, N.lo ≤ j) →
    EachPlainSh N Mg Pm Oc split f (pt :: q :: r) e₀ 2 (q :: r) →
    EachRides N Mg Pm Oc split f (pt :: q :: r) e₀ 2 (q :: r) →
    EachLawsBN (keyE N f (pt :: q :: r)) (onQ₂ N Pm Oc split f (pt :: q :: r))
      (stepE N Mg Pm Oc split f (pt :: q :: r)
        fun k a _ w => e₀ k ((actQ N f (pt :: q :: r) k).2 a) w) n 2 (q :: r)

section
variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
  (e₀ : ℕ → ActV S₂ Fr → Wt → Wt)

theorem eachLawsBN_plain (n : ℕ) :
    ∀ (m : List (Piece C Fr (P₁ × S₂) Cl Wt)) (k : ℕ), 2 ≤ k → EachHands (actQ N p l) k m →
      EachPlainSh N Mg Pm Oc split p l e₀ k m → EachRides N Mg Pm Oc split p l e₀ k m →
      EachLawsBN (keyE N p l) (onQ₂ N Pm Oc split p l)
        (stepE N Mg Pm Oc split p l fun k a _ w => e₀ k ((actQ N p l k).2 a) w) n k m
  | [], _, _, _, _, _ => trivial
  | x :: m, k, hk, hh, hp, hr => by
    refine ⟨?_, fun a b _ hq => hq.1,
      eachLawsBN_plain n m (k + 1) (Nat.le_succ_of_le hk) hh.2 hp.2 hr.2⟩
    have h1 := leadsK_of_handsAct x (actQ N p l k) (actQ N p l (k + 1)) hh.1
      (onQ₂ N Pm Oc split p l k) (stepV N Mg Pm split p l e₀ k) hp.1
    have h2 := h1.beside_sure
      (fun a b => Oc b.1.1 (strsOf Fr b.2) ∧
        ∀ w, relOwn N Mg 2 b w → relOwn N Mg 2 a (e₀ k ((actQ N p l k).2 a) w)) hr.1
    refine (h2.conseq (fun _ h => h) fun a τ b _ _ hq => ?_).bothN n
    obtain ⟨⟨hprom, hsh⟩, hoc, hown⟩ := hq
    refine ⟨⟨hprom, hoc⟩, fun w hw => ?_⟩
    have hw2 : relOwn N Mg 2 b w := by
      have := hw.2
      rw [relOwn_behind N Mg (k + 1) (Nat.le_succ_of_le hk)] at this
      exact this
    refine ⟨hsh w hw.1, ?_⟩
    rw [relOwn_behind N Mg k hk]
    exact hown w hw2

end

theorem sharedJoinPlain : SharedJoinPlain := by
  intro P₁ S₂ Cl Wt C Fr N Mg Pm Oc split n f pt q r e₀ ht hb ho hp hr
  exact eachLawsBN_plain N Mg Pm Oc split f (pt :: q :: r) e₀ n (q :: r) 2 (Nat.le_refl 2)
    (each_hands Prod.snd (fun t s => (t.1, s)) (fun _ _ => rfl) (fun _ _ _ => rfl) N.lo r q 2
      (actQ N f (pt :: q :: r))
      (fun k => by
        show actAt Fr Prod.snd N.lo (hiAt (2 + k) f (pt :: q :: r)) = _
        rw [Nat.add_comm]
        rfl) ht hb ho) hp hr

#check @SharedJoinPlain

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.sharedJoinPlain
