-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/KindSheet.lean: three statements that stand beside a kind's rows, general
in the kind.

  `ShowsSome`   at every state that `Good.exact` speaks of and at which the part does not stop, the part
                   shows something at every coin. `exact` alone does not say so: a part that errs beside a
                   simulator that says nothing meets it
  `OwnerFreshAt`   the equation of `Good.fresh` at one owner's member and one later part
  `filter_one_of_kind`, `filter_none_of_kind`   among the halves of lots of which each has one kind, the halves of a
                   kind are those of the one lot of that kind

Definitions and two lemmas on lists. This file proves nothing about soundness, completeness, hiding or
any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place KindName)

section
variable {S Cl V W X Pb : Type}

/-- **The part shows something**, at every coin, wherever `Good.exact` speaks and the part does not stop. -/
def ShowsSome (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Prop :=
  ∀ u ∈ σ.members, ∀ ca m front ds asks, On u ca m front → m.seen = front.seen →
    m.opened = front.opened (readsBefore pre front) →
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    front.holds chain firstTree (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (φ.sees m.st.input) m.loc ds = none →
    ∀ c : Cs u.part.takes × CsAll u.part.spends, σ.shows φ u (c.1, c.2, ca) m ds asks ≠ none

/-- **The equation of `Good.fresh`** at one member u of an owner's side and one part p. -/
def OwnerFreshAt (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (u : Member V W X Pb)
    (p : Addr) : Prop :=
  ∀ sp ca m ds asks, drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p), σ.shows φ u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
      (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))

/-- **It is the field**, word for word: `Good.fresh` at a member gives it. -/
theorem ownerFresh_of_good {pre : List (Nat × Nat × List Fmt.DeclaredRound)} {φ : Face V W Pb}
    {σ : Side S Cl V W X Pb} {Bk : ProverCoinCounts} {ord : List Place} {chain firstTree : Nat}
    {A B : Coins Bk → S → Mid W X → Env → Prop}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (g : Good pre φ σ Bk ord chain firstTree A B On bud) {u : Member V W X Pb}
    (hu : u ∈ σ.members) (p : Addr) : OwnerFreshAt φ σ Bk ord bud u p :=
  g.fresh u hu p

end

section
variable {V W X : Type} {Zp : Pub} {G : Ground} {κ : KindName}

/-- Where no lot of a list is of the kind, none of their halves is. -/
theorem filter_none_of_kind : ∀ ps : List (HLot V W X × KindName),
    (∀ q ∈ ps, ∀ x ∈ q.1.halves Zp G, x.place.kind = q.2) → (∀ q ∈ ps, q.2 ≠ κ) →
    (ps.flatMap fun q => q.1.halves Zp G).filter (fun x => x.place.kind == κ) = [] := by
  intro ps hk hn
  rw [List.filter_eq_nil_iff]
  intro x hx e
  obtain ⟨q, hq, hxq⟩ := List.mem_flatMap.1 hx
  exact hn q hq ((hk q hq x hxq).symm.trans (beq_iff_eq.1 e))

/-- **Among lots of which each has one kind, the halves of a kind are the one lot's.** -/
theorem filter_one_of_kind {L : HLot V W X} : ∀ ps : List (HLot V W X × KindName),
    (∀ q ∈ ps, ∀ x ∈ q.1.halves Zp G, x.place.kind = q.2) → (ps.map (·.2)).Nodup →
    (L, κ) ∈ ps →
    (ps.flatMap fun q => q.1.halves Zp G).filter (fun x => x.place.kind == κ) = L.halves Zp G
  | [], _, _, hm => by cases hm
  | q :: t, hk, hn, hm => by
    have hk' : ∀ r ∈ t, ∀ x ∈ r.1.halves Zp G, x.place.kind = r.2 :=
      fun r hr => hk r (List.mem_cons_of_mem _ hr)
    have hn' := (List.nodup_cons.1 hn)
    rw [List.flatMap_cons, List.filter_append]
    rcases List.mem_cons.1 hm with rfl | hm'
    · have e1 : ((L, κ).1.halves Zp G).filter (fun x => x.place.kind == κ) = L.halves Zp G := by
        rw [List.filter_eq_self]
        intro x hx
        exact beq_iff_eq.2 (hk (L, κ) (List.mem_cons_self) x hx)
      have e2 := filter_none_of_kind (κ := κ) t hk' fun r hr e =>
        hn'.1 (List.mem_map.2 ⟨r, hr, e⟩)
      rw [e1, e2, List.append_nil]
    · have e1 : (q.1.halves Zp G).filter (fun x => x.place.kind == κ) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx e
        have hq := hk q (List.mem_cons_self) x hx
        have hκ : q.2 = κ := hq.symm.trans (beq_iff_eq.1 e)
        exact hn'.1 (List.mem_map.2 ⟨(L, κ), hm', hκ.symm⟩)
      rw [e1, List.nil_append]
      exact filter_one_of_kind t hk' hn'.2 hm'

end

end ProofFile.Honest

#print axioms ProofFile.Honest.ShowsSome
#print axioms ProofFile.Honest.OwnerFreshAt
#print axioms ProofFile.Honest.ownerFresh_of_good
#print axioms ProofFile.Honest.filter_none_of_kind
#print axioms ProofFile.Honest.filter_one_of_kind
