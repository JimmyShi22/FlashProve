-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/GuestsTie.lean: THE TIE tGuests OF THE THREE SORTS OF LINK
(`LayersTies`, `AttentionTies`, `HeadTies`: Johnson/Desc/First/Link/Law/Pay….lean), WHOLE, AT THE
SEAT: the run that a seated link states at a lookup's «guests» stands under the run that returns no
claim and hands the verifier's state back (`idle0`). (In the Lean names a «block» is a
sub-protocol.)

How it goes. The lookups' lot lays, at each of its addresses, `K3.theStated`
(Johnson/Desc/First/Look/K3Stated.lean): `theOwn`'s sub-protocol (the kind's own with NO guest
handed: the empty list), joined with a step without a round that states no run, and at some
addresses with a run «planes» behind its own. So its run «guests» maps over the empty list.

What is said.
  `GuestsIdle b`: whatever run b states under «guests» returns no claim and the state, at every
    count and state. `own_guests`, `whole_guests`, `stated_guests`: it holds of the sub-protocol
    that `theOwn`, `theWhole` (runs stated), `theStated` gives at an address. `lot_guests`: so of
    every sub-protocol of the lookups' lot. `guests_tie`: at a seated link, at a number i of its
    hearing sub-protocols whose kind is K3: every run at (i, «guests») stands under `idle0`.
    `k3_at`: these numbers: 1 and 6; at the output head's link 2 and 7. `guests_ties_16`,
    `guests_ties_27`: **the tie in the field's own form, at a layers' or an attention link, and at
    the output head's.**

Limits. The seat's four premises (the base returns; the parts' base; the chain; the link's sort)
stand as in TiesAtSeat.lean. Nothing on soundness.

-/
import Johnson.LPFK9R.TiesAtSeat
import Johnson.Desc.ProofFile.Lot.K3

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open VerifiableInference.Desc (Block Chain Link Place KindName roundlessBlock)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.LinkJoin (At Under idle0)
open VerifiableInference.Desc.K3 (theOwn theWhole theStated withCaller)
open ProofFile (Cl)

/-- What is said of a sub-protocol: its run «guests» returns no claim and the state. -/
def GuestsIdle {C : Type} (b : Block S C) : Prop :=
  ∀ r, b.claims.lookup "guests" = some r → ∀ n s, r n s = .ok ([], s)

theorem own_guests {C : Type} (claim : OnBytes.Model.Aff → C) (X : OnBytes.Model.Verify.Public)
    (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape) (a : Place) (b : Block S C)
    (h : theOwn claim true X codes shape a = some b) : GuestsIdle b := by
  unfold theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, h⟩ := Option.map_eq_some_iff.1 h
      subst h
      intro r hr n s
      have e : r = fun _ s => VerifiableInference.Desc.named "K3 guests: a guest refuses"
          ((([] : List (VerifiableInference.Desc.First.Look.Guest S C)).mapM
            fun (g : VerifiableInference.Desc.First.Look.Guest S C) => g.form s).map
              fun l => (l, s)) := (Option.some.inj hr).symm
      subst e
      rfl

theorem whole_guests {C : Type} (claim : OnBytes.Model.Aff → C) (X : OnBytes.Model.Verify.Public)
    (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape) (a : Place) (b : Block S C)
    (h : theWhole claim true X codes shape a = some b) : GuestsIdle b := by
  unfold theWhole at h
  obtain ⟨b₀, h0, h⟩ := Option.map_eq_some_iff.1 h
  have g := own_guests claim X codes shape a b₀ h0
  split at h
  · subst h
    intro r hr
    have hr' : (b₀.claims ++ []).lookup "guests" = some r := hr
    rw [List.append_nil] at hr'
    exact g r hr'
  · subst h
    exact g

theorem stated_guests {C : Type} (claim : OnBytes.Model.Aff → C)
    (readers : ℕ → Option (VerifiableInference.Desc.K3.Readers S))
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block S C) (h : theStated claim readers X codes shape a = some b) :
    GuestsIdle b := by
  unfold theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have g := whole_guests claim X codes shape a b₀ h0
  split at h
  · obtain rfl := Option.some.inj h
    exact g
  · split at h
    · obtain rfl := Option.some.inj h
      exact g
    · split at h
      · obtain rfl := Option.some.inj h
        exact g
      · obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
        intro r hr
        have hr' : (b₀.claims ++ [("planes", _)]).lookup "guests" = some r := hr
        rw [List.lookup_append] at hr'
        cases e : b₀.claims.lookup "guests" with
        | some r₀ =>
          rw [e] at hr'
          obtain rfl : r₀ = r := Option.some.inj hr'
          exact g r₀ e
        | none =>
          rw [e] at hr'
          exact nomatch hr'

/-- So of every sub-protocol of the lookups' lot. -/
theorem lot_guests {Z : ProofFile.Pub} {G : ProofFile.Ground} {b : Block S Cl}
    (hb : b ∈ (K3Lot.lot Z).blocks G) : GuestsIdle b := by
  have h : b ∈ K3Lot.hear Z := by
    unfold ProofFile.Lot.blocks ProofFile.asCl at hb
    rcases List.mem_append.1 hb with h | h
    · obtain ⟨x, hx, _⟩ := List.mem_map.1 h
      exact nomatch hx
    · exact h
  unfold K3Lot.hear at h
  obtain ⟨x, _, h⟩ := List.mem_filterMap.1 h
  exact stated_guests _ _ _ _ _ _ b h

variable {o : ProofFile.SecondHashFunctionArgument}

/-- **THE TIE tGuests, WHOLE, AT THE SEAT.** -/
theorem guests_tie {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K3) (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9) :
    ∃ Lk, c.links[l]? = some Lk ∧ ∀ run, At Lk (i, "guests") run → Under run idle0 := by
  obtain ⟨Lk, e1, L, hL, b', hb', ep, t1, _⟩ :=
    ties_at_seat hB hb hc l sub hl i .K3 hk (by decide) (by decide) hi
  obtain rfl : L = K3Lot.lot Z := IM.lot_of_kind hL hb' (by rw [ep]; rfl)
  refine ⟨Lk, e1, fun run h => ?_⟩
  obtain ⟨r', h1, hu⟩ := t1 "guests" run h
  intro n e cl e₁ hrun
  have h2 := hu n e cl e₁ hrun
  rw [lot_guests hb' r' h1 n e] at h2
  exact h2

/-- Which numbers of a sort's hearing sub-protocols are of the kind K3. -/
theorem k3_at (sub : ModelPart) (first : Bool) :
    (sub ≠ .head → (kindsBeforeBatching sub first)[1]? = some KindName.K3 ∧
      (kindsBeforeBatching sub first)[6]? = some KindName.K3) ∧
    (sub = .head → (kindsBeforeBatching sub first)[2]? = some KindName.K3 ∧
      (kindsBeforeBatching sub first)[7]? = some KindName.K3) := by
  cases sub <;> cases first <;> simp [kindsBeforeBatching]

/-- **tGuests IN THE FIELD's OWN FORM, AT A LAYERS' OR AN ATTENTION LINK.** -/
theorem guests_ties_16 {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (hs : sub ≠ .head) :
    ∃ Lk, c.links[l]? = some Lk ∧
      ∀ k ∈ [1, 6], ∀ run, At Lk (k, "guests") run → Under run idle0 := by
  obtain ⟨h1, h6⟩ := (k3_at sub (l == 0)).1 hs
  obtain ⟨Lk, e1, t1⟩ := guests_tie hB hb hc l sub hl 1 h1 (by omega)
  obtain ⟨Lk', e6, t6⟩ := guests_tie hB hb hc l sub hl 6 h6 (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e6)
  refine ⟨Lk, e1, fun k hk => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact t1
  · exact t6

/-- **AT THE OUTPUT HEAD's LINK.** -/
theorem guests_ties_27 {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ)
    (hl : (ProofFile.subsOf Z)[l]? = some ModelPart.head) :
    ∃ Lk, c.links[l]? = some Lk ∧
      ∀ k ∈ [2, 7], ∀ run, At Lk (k, "guests") run → Under run idle0 := by
  obtain ⟨h2, h7⟩ := (k3_at .head (l == 0)).2 rfl
  obtain ⟨Lk, e2, t2⟩ := guests_tie hB hb hc l .head hl 2 h2 (by omega)
  obtain ⟨Lk', e7, t7⟩ := guests_tie hB hb hc l .head hl 7 h7 (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (e2.symm.trans e7)
  refine ⟨Lk, e2, fun k hk => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact t2
  · exact t7

end LPFK9

#print axioms LPFK9.stated_guests
#print axioms LPFK9.lot_guests
#print axioms LPFK9.guests_tie
#print axioms LPFK9.k3_at
#print axioms LPFK9.guests_ties_16
#print axioms LPFK9.guests_ties_27
