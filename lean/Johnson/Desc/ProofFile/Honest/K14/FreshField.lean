-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshField.lean: kind K14: THE FIELD fresh OF Good
(Honest/Side.lean) AT EVERY SIDE WHOSE ROW IS THE PART AT "send o_omega", in the field's own form
(FreshMember, Honest/Small/Field.lean), at every address p: from coin_apart
(Honest/K14/FreshShows.lean) and two tests on the book (Honest/K14/FreshDefs.lean).

  oneCoin, oneCoinEq   one coin of the extension field, as a run of one entry of a book; the
                  bijection with the field
  cutAll_one      what the frame's cutAll cuts for one entry of one coin of the extension field:
                  that coin
  fresh_of_one    **the field's equation at a list of ONE entry of ONE coin**, from the like
                  sentence with eAt in the first place. General: no part is named
  cutAll_below    at a count without a coin of the base field: two lists of coins with the same cut
                  of the first coins have the same runs at entries that end below
  spentBy_filter  the entries by which p spends of o, among the entries by which any part spends of
                  o
  fresh_at_omega  **the field**

WHAT THE PART SHOWS IS NOT ALL THAT A RUN SHOWS OF THIS ENTRY: both proximity tests behind "SPLIT"
are handed o_sp whole; nothing is said here of what they show.

What is assumed. coin_apart's premises; hB, hK: the two tests on the book and on the order of
places; hbud: ANY bound that gives spBud at the part's number: Good has one bud for its fields
exact and fresh.
What is not claimed. At a book without a spending entry of this owner, and at every p that is not
the one spender, the equation is the frame's fresh_of_nil (Honest/Law/ToyLaw.lean) and says nothing
of a coin. That a book passes the tests. That a run's positions meet the bound. All that
coin_apart does not claim. Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.FreshShows
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open ProofFile.Honest.Small (FreshMember)
open Prob

/-- One coin of the extension field. -/
def oneCoin (x : Cb.Gl.E) : Cs ⟨0, 1⟩ := { f := fun i => i.elim0, e := fun _ => x }

/-- One run of one coin of the extension field, under any name, as an element of the field. -/
def oneCoinEq (name : String) : CsAll [(name, (⟨0, 1⟩ : Due))] ≃ Cb.Gl.E where
  toFun c := (show Cs ⟨0, 1⟩ × Unit from c).1.e ⟨0, Nat.one_pos⟩
  invFun x := (show CsAll [(name, (⟨0, 1⟩ : Due))] from (oneCoin x, ()))
  left_inv c := by
    obtain ⟨c1, c2⟩ : Cs ⟨0, 1⟩ × Unit := c
    refine Prod.ext (Cs.ext' (fun i => i.elim0) fun i => ?_) rfl
    exact congrArg c1.e (Fin.ext (by
      have h : i.1 < 1 := i.2
      show 0 = i.1
      omega))
  right_inv _ := rfl

/-- What cutAll cuts for one entry of one coin of the extension field. -/
theorem cutAll_one {d : Due} (c : Cs d) (name : String) (owner spender : Addr) (once : Bool)
    (s : Nat) (hs : s < d.e) :
    cutAll c [{ name := name, owner := owner, start := ⟨0, s⟩, count := ⟨0, 1⟩,
                spender := spender, once := once }] =
      some ((oneCoinEq name).symm (c.e ⟨s, hs⟩)) := by
  have hc : (⟨0, s⟩ : Due).f + (⟨0, 1⟩ : Due).f ≤ d.f ∧
      (⟨0, s⟩ : Due).e + (⟨0, 1⟩ : Due).e ≤ d.e := ⟨Nat.zero_le _, hs⟩
  show ((c.cut ⟨0, s⟩ ⟨0, 1⟩).bind fun x => (some ()).map fun y => (x, y)) = _
  unfold Cs.cut
  rw [dif_pos hc]
  refine congrArg some (Prod.ext (Cs.ext' (fun i => i.elim0) fun i => ?_) rfl)
  exact congrArg c.e (Fin.ext (by
    have h : i.1 < 1 := i.2
    show s + i.1 = s
    omega))

/-- **The field's equation at a list of one entry of one coin.** Sh: what the owner shows. K: its
other coins that are handed on. -/
theorem fresh_of_one {γ δ : Type} {d : Due} (es : List Ahead) (e : Ahead) (hes : es = [e])
    (s : Nat) (hst : e.start = ⟨0, s⟩) (hct : e.count = ⟨0, 1⟩) (hs : s < d.e) (Sh : Cs d → γ)
    (K : Cs d → δ)
    (h : (unif (Cs d)).map (fun c => (c.eAt s, Sh c, K c)) =
      (unif (Cb.Gl.E × Cs d)).map fun a => (Except.ok a.1, Sh a.2, K a.2)) :
    (unif (Cs d)).map (fun c => (cutAll c es, Sh c, K c)) =
      (unif (CsAll (es.map Ahead.named) × Cs d)).map fun a => (some a.1, Sh a.2, K a.2) := by
  subst hes
  obtain ⟨name, owner, start, count, spender, once⟩ := e
  obtain rfl : start = ⟨0, s⟩ := hst
  obtain rfl : count = ⟨0, 1⟩ := hct
  have h1 : (unif (Cs d)).map (fun c =>
      (cutAll c [{ name := name, owner := owner, start := ⟨0, s⟩, count := ⟨0, 1⟩,
                   spender := spender, once := once }], Sh c, K c)) =
      (unif (Cb.Gl.E × Cs d)).map fun a => (some ((oneCoinEq name).symm a.1), Sh a.2, K a.2) := by
    refine map_eq_of_factor _ _ (fun c a hg => ?_) h
    have g1 : c.eAt s = Except.ok a.1 := congrArg Prod.fst hg
    have g2 : (Sh c, K c) = (Sh a.2, K a.2) := congrArg Prod.snd hg
    unfold Cs.eAt at g1
    rw [dif_pos hs] at g1
    rw [cutAll_one c name owner spender once s hs, Except.ok.inj g1]
    exact congrArg _ g2
  rw [h1]
  exact (map_unif_by_equiv (Equiv.prodCongr (oneCoinEq name) (Equiv.refl (Cs d)))
    (fun a => (some ((oneCoinEq name).symm a.1), Sh a.2, K a.2))
    (fun a => (some a.1, Sh a.2, K a.2)) fun a =>
      Prod.ext (congrArg some ((oneCoinEq name).left_inv a.1).symm) rfl).symm

/-- **At a count without a coin of the base field (hf): coins with the same cut of the first coins
have the same runs at entries that end below.** -/
theorem cutAll_below {d : Due} (hf : d.f = 0) (room : Nat) (hroom : room ≤ d.e) (c c' : Cs d)
    (h : c.cut ⟨0, 0⟩ ⟨0, room⟩ = c'.cut ⟨0, 0⟩ ⟨0, room⟩) :
    ∀ es : List Ahead, (∀ q ∈ es, q.start.e + q.count.e ≤ room) → cutAll c es = cutAll c' es
  | [], _ => rfl
  | q :: es, hq => by
    have hc : (⟨0, 0⟩ : Due).f + (⟨0, room⟩ : Due).f ≤ d.f ∧
        (⟨0, 0⟩ : Due).e + (⟨0, room⟩ : Due).e ≤ d.e :=
      ⟨Nat.zero_le _, by show 0 + room ≤ d.e; omega⟩
    have hpt : ∀ i (hi : i < room), c.e ⟨i, by omega⟩ = c'.e ⟨i, by omega⟩ := fun i hi => by
      unfold Cs.cut at h
      rw [dif_pos hc, dif_pos hc] at h
      have h1 := congrFun (congrArg Cs.e (Option.some.inj h)) ⟨i, hi⟩
      have e1 : ∀ hlt : 0 + i < d.e, (⟨0 + i, hlt⟩ : Fin d.e) = ⟨i, by omega⟩ :=
        fun _ => Fin.ext (Nat.zero_add _)
      have h2 : c.e ⟨0 + i, by omega⟩ = c'.e ⟨0 + i, by omega⟩ := h1
      rw [e1] at h2
      exact h2
    have hcut : c.cut q.start q.count = c'.cut q.start q.count := by
      unfold Cs.cut
      by_cases hx : q.start.f + q.count.f ≤ d.f ∧ q.start.e + q.count.e ≤ d.e
      · rw [dif_pos hx, dif_pos hx]
        refine congrArg some (Cs.ext' (fun i => ?_) fun i => ?_)
        · exact absurd i.2 (by have := hx.1; omega)
        · exact hpt _ (by
            have h1 := hq q List.mem_cons_self
            have h2 := i.2
            omega)
      · rw [dif_neg hx, dif_neg hx]
    show ((c.cut q.start q.count).bind fun x => (cutAll c es).map fun y => (x, y)) =
      (c'.cut q.start q.count).bind fun x => (cutAll c' es).map fun y => (x, y)
    rw [hcut, cutAll_below hf room hroom c c' h es fun q' hq' => hq q' (List.mem_cons_of_mem _ hq')]

/-- The entries by which p spends of o, among those by which any part spends of o. -/
theorem spentBy_filter (B : ProverCoinCounts) (o p : Addr) :
    B.spentBy o p = (spendersOf B o).filter fun e => e.spender == p := by
  unfold ProverCoinCounts.spentBy spendersOf
  rw [List.filter_filter]
  refine List.filter_congr fun e _ => ?_
  cases (e.owner == o) <;> cases (e.spender == p) <;> cases e.once <;> rfl

variable {S Cl X Pb W₀ Rc Ky : Type}

/-- **The field fresh of Good at a side whose row is the part at "send o_omega".**
WHAT THE PART SHOWS IS NOT ALL THAT A RUN SHOWS OF THIS ENTRY: both proximity tests behind "SPLIT"
are handed o_sp whole; nothing is said here of what they show. -/
theorem fresh_at_omega (A : SendPub) (n : Nat) (hfit : sendingsFit A.P = true)
    (hs : A.P.S.sharedSplitNeeded = true) (H : Desc.K14.Honest.SpShape A.P.codes A.P.S n)
    (wit : Common W₀ Rc Ky → Ask) (sim : Sim Pb) (φ : Face Empty (Common W₀ Rc Ky) Pb)
    (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb)
    (hrow : σ.row = [(liftSend wit (sendingPart (jobOmega A)), sim)])
    (hr : σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobOmega A).Q)
    (hd : SendDeclared σ.block (jobOmega A)) (Bk : ProverCoinCounts) (ord : List Place)
    (hB : oneSpender Bk ⟨σ.block.place, 0⟩ (spFirstCoin A) n = true)
    (hK : knownBelow Bk ord ⟨σ.block.place, 0⟩ (spFirstCoin A) = true)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (hbud : ∀ ds asks, bud 0 ds asks → spBud A asks) :
    ∀ u ∈ σ.members, FreshMember φ σ Bk ord bud u := by
  intro u hu p sp ca m ds asks hfitD hb _
  have hca := coin_apart A n hfit hs H wit sim φ σ hrow hr hd u hu
  rw [members_send σ _ sim hrow] at hu
  obtain rfl := List.mem_singleton.1 hu
  have hbud' : spBud A asks := hbud ds asks hb
  have htk := takes_omega A hs H
  have hf : (sendingPart (jobOmega A)).takes.f = 0 := by rw [htk]
  have he : (sendingPart (jobOmega A)).takes.e =
      spFirstCoin A + (n + 1) + (spMaskCode A).r := by rw [htk]
  have hsp := spentBy_filter Bk ⟨σ.block.place, 0⟩ p
  unfold oneSpender at hB
  unfold knownBelow at hK
  match hl : spendersOf Bk ⟨σ.block.place, 0⟩, hB, hK with
  | [], _, _ =>
    rw [hl] at hsp
    exact fresh_of_nil _ hsp _ _
  | [e], hB, hK =>
    rw [hl] at hsp
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
    obtain ⟨⟨⟨hf0, hlo⟩, hhi⟩, hct⟩ := hB
    by_cases hp : e.spender = p
    · have hsp' : Bk.spentBy ⟨σ.block.place, 0⟩ p = [e] := by
        rw [hsp]
        simp [hp]
      have hst : e.start = ⟨0, spFirstCoin A + (e.start.e - spFirstCoin A)⟩ := by
        have e1 : e.start = ⟨e.start.f, e.start.e⟩ := rfl
        have e2 : e.start.e = spFirstCoin A + (e.start.e - spFirstCoin A) := by omega
        rw [e1, hf0]
        exact congrArg (Due.mk 0) e2
      have hkn : ∀ q ∈ Bk.knownBy ord ⟨σ.block.place, 0⟩ p,
          q.start.e + q.count.e ≤ spFirstCoin A := fun q hq => by
        simp only [List.all_cons, List.all_nil, Bool.and_true, List.all_eq_true,
          decide_eq_true_eq] at hK
        exact hK q (hp ▸ hq)
      refine fresh_of_one (d := (sendingPart (jobOmega A)).takes) _ e hsp' _ hst hct
        (by rw [he]; omega) _ _ ?_
      refine map_eq_of_factor _ _ (fun c a hg => ?_)
        (hca (e.start.e - spFirstCoin A) (by omega) sp ca m ds asks hfitD hbud')
      have g1 := congrArg Prod.fst hg
      have g2 := congrArg (fun y => y.2.1) hg
      have g3 := congrArg (fun y => y.2.2) hg
      exact Prod.ext g1 (Prod.ext g2
        (cutAll_below (d := (sendingPart (jobOmega A)).takes) hf (spFirstCoin A)
          (by rw [he]; omega) c a.2 g3 _ hkn))
    · have hsp' : Bk.spentBy ⟨σ.block.place, 0⟩ p = [] := by
        rw [hsp]
        simp [hp]
      exact fresh_of_nil _ hsp' _ _
  | _ :: _ :: _, hB, _ => cases hB

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.oneCoin
#print axioms ProofFile.Honest.K14.oneCoinEq
#print axioms ProofFile.Honest.K14.cutAll_one
#print axioms ProofFile.Honest.K14.fresh_of_one
#print axioms ProofFile.Honest.K14.cutAll_below
#print axioms ProofFile.Honest.K14.spentBy_filter
#print axioms ProofFile.Honest.K14.fresh_at_omega
