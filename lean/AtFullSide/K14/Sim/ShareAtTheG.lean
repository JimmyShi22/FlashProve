-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/Sim/ShareAtTheG.lean: THE KIND K14's ROW: `KindShare` AT THE KIND K14, AT `theGOfReturn`, AT EVERY PROVER, RELATION AND FAMILY OF INVARIANTS, FROM THE KIND'S `KindPays`.

  `base_own_letters`   a row of the six of kind K14 asks nothing: On and bud are True
  `k14_rows_true`      so at the lists of the kind
  `k14_share_of_pays`  **the share**, from its `pays` (`theG_pays_of_holds`): bud and on by those two; the first chain has no place of the kind, the second no row of it

Limits. This is the kind K14's: its four rows; the two sendings are of kind K1: their On and bud are K1's row. `pays`, K14's whole `KindPays`, is a premise here: `theG_pays_of_holds` pays it. `hsh`: K's shared rows of the kind are among the six; `hse`, `noFirst`: no last row and no first sub-protocol is of the kind. `Good` at predicates that never hold. No property of the protocol is claimed.
-/
import AtFullSide.K14.Sim.AtBase
import E2E.TheG
import Johnson.SendSim.Seat.AtDesc
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsByKind

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open ProofFile.Honest.K14 (k14On k14Bud ownRows sendingRows simRows sendPlace place)
open ProofFile.Honest.Term (matrixInput baseRows)
open Johnson.M1 (KindBud)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.TheSides AtPublicFiles.TheG
open ProofFile.Honest.FirstThread (HeadAtReturn)
open OnBytes (TableKey)

variable {files : VerifierAndGoals.PublicFiles} {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- A row of the six of kind K14 asks nothing. -/
theorem base_own_letters {Zp : ProofFile.Pub} {Np : H2U.Places4}
    (r : Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey) (hr : r ∈ baseRows Zp Np)
    (hk : r.place.kind = KindName.K14) : r.On = k14On ∧ r.bud = k14Bud := by
  rcases List.mem_append.1 hr with g | g
  · unfold ownRows at g
    rcases List.mem_append.1 g with g | g
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at g
      rcases g with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
    · split at g
      · obtain rfl := List.mem_singleton.1 g
        exact ⟨rfl, rfl⟩
      · cases g
  · unfold sendingRows at g
    simp only [List.mem_cons, List.not_mem_nil, or_false] at g
    rcases g with rfl | rfl <;> simp [sendPlace] at hk

/-- **At the lists of the kind On and bud hold at every argument.** -/
theorem k14_rows_true (hd : HeadAtReturn files A₀) (T : ThreadParts A₀ Wt)
    (K : KindRows (ProofFile.Honest.Term.baseFilling files) A₀.Z A₀.G)
    (hsh : ∀ r ∈ K.slots.shared, r.place.kind = KindName.K14 → r ∈ baseRows A₀.Z hd.places) :
    ∀ L ∈ (theG hd T K).shared, L.place.kind = KindName.K14 →
      (∀ u ca m front, L.On u ca m front) ∧ ∀ n ds asks, L.bud n ds asks := by
  intro L hL hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hL
  obtain ⟨e₁, e₂⟩ := base_own_letters r (hsh r hr hk) hk
  refine ⟨fun u ca m front => ?_, fun n ds asks => ?_⟩
  · show r.On u ca m front
    rw [e₁]
    trivial
  · show r.bud n ds asks
    rw [e₂]
    trivial

/-- **K14's three shares of `RowDebtsP`, AS ONE END, FROM ITS `KindPays`.** At every H, Rel and family of invariants. `hsh`, `hse`, `noFirst`: K's shared rows of the kind are among the six; K's last rows are of no such kind; no sub-protocol of the first chain is of the kind. -/
theorem k14_share_of_pays (hd : HeadAtReturn files A₀)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (ProofFile.Honest.Term.baseFilling files) = .ok A₀)
    (T : ThreadParts A₀ Wt) (K : KindRows (ProofFile.Honest.Term.baseFilling files) A₀.Z A₀.G)
    (pays : VerifiableInference.Compilation.KindPays (theGOfReturn made hd T K) KindName.K14)
    (hsh : ∀ r ∈ K.slots.shared, r.place.kind = KindName.K14 → r ∈ baseRows A₀.Z hd.places)
    (hse : ∀ r ∈ K.slots.second, r.place.kind ≠ KindName.K14)
    (noFirst : ∀ b ∈ A₀.F.first.blocksInOrder, b.place.kind ≠ KindName.K14)
    (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A₀.F A₀.B ((theGOfReturn made hd T K).prover H) w₀ rc x k = .ok R →
      ThreadsP A₀.F A₀.B ((theGOfReturn made hd T K).prover H) w₀ rc x k R) :
    KindShare A₀ (theGOfReturn made hd T K) H Rel Th KindName.K14 := by
  have nf : ∀ {S Cl V W Y Pb : Type} {Bk : ProverCoinCounts} {bs : List (Block S Cl)}
      (_ : ∀ b ∈ bs, b.place.kind ≠ KindName.K14) (L : Lettered Bk S Cl V W Y Pb)
      (_ : L.place.kind = KindName.K14) (f : List (Fall S)) (σ : Side S Cl V W Y Pb)
      (_ : L.side bs f = some σ), False := by
    intro S Cl V W Y Pb Bk bs hno L hk f σ hσ
    have hf := OnBytes.SendSim.Seat.find_of_seated hσ
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some (p := fun b : Block S Cl => b.place == L.place) hf
    have e : σ.block.place = L.place := beq_iff_eq.1 hp
    exact hno _ hm (e ▸ hk)
  have tr : ∀ L ∈ (theGOfReturn made hd T K).shared, L.place.kind = KindName.K14 →
      (∀ u ca m front, L.On u ca m front) ∧ ∀ n ds asks, L.bud n ds asks :=
    castSides_of (Q := fun _ G => ∀ L ∈ G.shared, L.place.kind = KindName.K14 →
      (∀ u ca m front, L.On u ca m front) ∧ ∀ n ds asks, L.bud n ds asks) _
      (k14_rows_true hd T K hsh)
  have noLast : ∀ L ∈ (theGOfReturn made hd T K).second, L.place.kind ≠ KindName.K14 :=
    castSides_of (Q := fun _ G => ∀ L ∈ G.second, L.place.kind ≠ KindName.K14) _
      (fun L hL' hk => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hL'
        exact hse r hr hk)
  refine ⟨pays, ⟨fun L _ hk σ hσ => (nf noFirst L hk _ σ hσ).elim,
      fun L hL' hk _ _ u _ _ _ _ _ _ ρ _ => (tr L hL' hk).2 _ _ _,
      fun L hL' hk => absurd hk (noLast L hL')⟩, ?_⟩
  intro w₀ rc x hrel k R hR ρ r _ _ _
  exact ⟨fun L _ hk σ hσ => (nf noFirst L hk _ σ hσ).elim,
    fun L hL' hk => onAtRun₂_of_always _ ρ r (tr L hL' hk).1,
    fun L hL' hk => absurd hk (noLast L hL')⟩

end AtFullSide.M1

#print axioms AtFullSide.M1.base_own_letters
#print axioms AtFullSide.M1.k14_rows_true
#print axioms AtFullSide.M1.k14_share_of_pays
