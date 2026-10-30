-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/StandsAtTheG.lean: that the one premise of KindPaysAtTheG.lean on the kinds' rows can be
met, and that the kind's row stands among the lists with a side.

  k11_slot_by_name        a lot of the base filling that bears the kind's lot's name is the filling's
                          lot of the kind
  k11_named, k11Lot_fit   the two facts that a kind hands in for the K of record
  kindRowsWithK11sLotExist   a value K that lays the kind's lot exists
  K11Stands, k11Stands_at_the_sides, k11Stands_at_theGOfReturn
                          a list that bears the lot's row is among the first chain's lists, and has
                          a side over the description, at member 346
  k11_stands_and_pays_at_some_rows   with no premise on K

Limits. The witness K lays the kind's lot alone: the other lots stand beside simulators that tell
nothing. At the base filling's return.
-/
import AtFullSide.K11.KindPaysAtTheG
import AtFullSide.K11.BitesAtTheStand
import Johnson.Desc.ProofFile.Honest.K13.AtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K11
open VerifiableInference.Desc (Chain KindName FileDescription)
open VerifiableInference.Compilation (KindPays)
open ProofFile (Pub Ground Inst)
open ProofFile.Honest
open ProofFile.Honest.K11
open ProofFile.Honest.Term (matrixInput theGAtBase baseFilling)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.TheSides (Letters theSides overlaySlots overlayLot find_name KindRows castSides
  castSides_of)
open AtPublicFiles.TheG (ThreadParts theLetters theG theGOfReturn)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.AtFiles.HonestTerm.K11Term
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)

/-- The filling's lot of the kind. -/
noncomputable abbrev k11FillLot : HLot (Input FullSizeMatrix) (Input FullSizeMatrix) Unit :=
  lotK11 matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest

/-- That lot is among the filling's. -/
theorem k11FillLot_mem (files : VerifierAndGoals.PublicFiles) : k11FillLot ∈ (baseFilling files).lots := by
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots]
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  exact List.mem_map.2 ⟨(k11FillLot, KindName.K11), by simp [widerPairs], rfl⟩

/-- **A lot of the base filling that bears the name of the kind's lot is the filling's lot of the
kind.** -/
theorem k11_slot_by_name (files : VerifierAndGoals.PublicFiles) :
    ∀ L ∈ (baseFilling files).lots, L.name = "the merge of the weights' claims" → L = k11FillLot := by
  intro L hL hn
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots] at hL
  simp only [widerPairs, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hL
  rcases hL with (((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl) | rfl
  all_goals first | exact absurd hn (by decide) | rfl

/-- **A lot of the filling bears the name of the kind's lot.** -/
theorem k11_named (files : VerifierAndGoals.PublicFiles) :
    (baseFilling files).lots.any (fun L => L.name == k11LotAtBase.name) = true :=
  List.any_eq_true.2 ⟨_, k11FillLot_mem files, by rfl⟩

/-- **With the simulator forgotten the rows of the kind's lot are the sides of the filling's lot of
that name.** -/
theorem k11Lot_fit (files : VerifierAndGoals.PublicFiles) (Zq : Pub) (G : Ground) :
    ∀ L ∈ (baseFilling files).lots, L.name = k11LotAtBase.name →
      (k11LotAtBase.rows Zq G).map (·.half) = L.halves Zq G := by
  intro L hL hn
  rw [k11_slot_by_name files L hL hn]
  exact k11SimLot_fit matrixInput _ _ Zq G

/-- **A value of the kinds' rows that lays the kind's lot exists**, at every public part and ground. -/
theorem kindRowsWithK11sLotExist (files : VerifierAndGoals.PublicFiles) (Zq : Pub) (G : Ground) :
    ∃ K : KindRows (baseFilling files) Zq G, k11LotAtBase ∈ K.lots :=
  ⟨{ lots := [k11LotAtBase]
     named := fun s hs => by
       rw [List.mem_singleton.1 hs]
       exact k11_named files
     apart := by simp
     lots_fit := fun L hL s hs => by
       have hm := List.mem_of_find?_eq_some hs
       have hp := List.find?_some hs
       obtain rfl := List.mem_singleton.1 hm
       exact k11Lot_fit files Zq G L hL (beq_iff_eq.1 hp).symm
     shared := []
     shared_named := fun _ hr => by cases hr
     shared_apart := by simp
     shared_fit := fun _ _ _ hr => by simp at hr
     second := []
     second_named := fun _ hr => by cases hr
     second_apart := by simp
     second_fit := fun _ _ _ hr => by simp at hr }, List.mem_singleton.2 rfl⟩

/-- **A list that bears a row of the kind's lot stands in the first chain's lists, and has a side over
the description, at member 346.** -/
def K11Stands {W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Inst} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (rows : List (Unlettered (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)) : Prop :=
  ∃ L ∈ G.first, L.bare ∈ rows ∧
    ∃ σ, L.side F.first.blocksInOrder G.falls₁ = some σ ∧ F.first.blocksInOrder[346]? = some σ.block

section
variable {files : VerifierAndGoals.PublicFiles} {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : ProofFile.Honest.Term.baseMaker files = .ok returned) (h : HeadAtReturn files returned)
    (mine : List (SLot (Input FullSizeMatrix) (Input FullSizeMatrix) Unit Inst))
    (named : ∀ s ∈ mine, (baseFilling files).lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ (baseFilling files).lots, ∀ s,
      (mine.find? fun s => s.name == L.name) = some s →
      (s.rows returned.Z returned.G).map (·.half) = L.halves returned.Z returned.G)
    (shared : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins OnBytes.TableKey) Unit OnBytes.TableKey))
    (hs : shared.map (·.half) = (baseFilling files).shared returned.Z returned.G)
    (second : List (Unlettered (Input FullSizeMatrix) (Input FullSizeMatrix) Unit Inst))
    (h₃ : second.map (·.half) = (baseFilling files).second returned.Z returned.G)
    (Ls : Letters h.description returned.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (f₁ : List (Fall h.description.S₁)) (f₂ : List (Fall h.description.S₂))
    (f₃ : List (Fall h.description.S₃))
    (laid : k11LotAtBase ∈ mine)
include made laid

/-- **The kind's row stands, with a side.** -/
theorem k11Stands_at_the_sides
    (whole : ∀ u ∈ k11LotAtBase.rows returned.Z returned.G, (Ls.first u).bare = u) :
    K11Stands (theSides h.description Ls
      (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs second
        h₃).rows f₁ f₂ f₃) (k11LotAtBase.rows returned.Z returned.G) := by
  obtain ⟨r, hr⟩ : ∃ r, r ∈ k11LotAtBase.rows returned.Z returned.G :=
    ⟨_, List.mem_singleton.2 rfl⟩
  have found : overlayLot mine k11FillLot = k11LotAtBase := by
    unfold overlayLot
    have f' : (mine.find? fun t => t.name == k11FillLot.name) = some k11LotAtBase :=
      find_name apart laid
    rw [f']
  have inRows : r ∈ rowsOfLots returned.Z returned.G
      ((baseFilling files).lots.map (overlayLot mine)) :=
    List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, k11FillLot_mem files, found⟩, hr⟩
  obtain ⟨Bs, -, name, hB, -, -, -, -, hf, -⟩ := headMergeAtFull _ _ _ _ _ _ _ h.head
  obtain ⟨-, eG⟩ := k11_ground h.head made hB
  have hpl := k11_member_place h.head hf
  have hrp : r.place = IM.k11Place := by
    rw [eG] at hr
    obtain rfl := List.mem_singleton.1 hr
    exact k11_place_is h.head hB
  have hfind := find_at h.firstChain.blocksInOrder 346 _ (places_nodup h.head) hf
  have hseat : ∃ σ, Side.seated h.firstChain.blocksInOrder r.place r.row f₁ = some σ ∧
      h.firstChain.blocksInOrder[346]? = some σ.block := by
    unfold Side.seated
    rw [hrp, ← hpl, hfind]
    exact ⟨_, rfl, hf⟩
  obtain ⟨σ, hσ, at346⟩ := hseat
  refine ⟨Ls.first r, List.mem_map_of_mem inRows, ?_, σ, ?_, at346⟩
  · rw [whole r hr]
    exact hr
  · show Side.seated _ (Ls.first r).place (Ls.first r).row f₁ = some σ
    rw [(Ls.keeps₁ r).1, (Ls.keeps₁ r).2]
    exact hσ

end

section
variable {Wt : Type} {files : VerifierAndGoals.PublicFiles} {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : ProofFile.Honest.Term.baseMaker files = .ok returned) (h : HeadAtReturn files returned)
    (T : ThreadParts returned Wt) (K : KindRows (baseFilling files) returned.Z returned.G)
    (laid : k11LotAtBase ∈ K.lots)
include laid

/-- **The kind's row stands in theGOfReturn made h T K, with a side at member 346.** -/
theorem k11Stands_at_theGOfReturn :
    K11Stands (theGOfReturn made h T K) (k11LotAtBase.rows returned.Z returned.G) :=
  castSides_of (Q := fun _ G => K11Stands G (k11LotAtBase.rows returned.Z returned.G))
    (atPure_at_laid h.head.laid made).2
    (k11Stands_at_the_sides made h K.lots K.named K.apart K.lots_fit _ _ _ _ (theLetters h T) _ _ _
      laid fun _ _ => rfl)

end

/-- **With no premise on the kinds' rows**: at the base maker's return with the head there is a value
K at which the kind's row stands with a side and the kind pays. -/
theorem k11_stands_and_pays_at_some_rows {Wt : Type} {files : VerifierAndGoals.PublicFiles}
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : ProofFile.Honest.Term.baseMaker files = .ok returned)
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt) :
    ∃ K : KindRows (baseFilling files) returned.Z returned.G,
      K11Stands (theGOfReturn made h T K) (k11LotAtBase.rows returned.Z returned.G) ∧
      KindPays (theGOfReturn made h T K) .K11 ∧
      Johnson.M1.KindBud (theGOfReturn made h T K) .K11 := by
  obtain ⟨K, laid⟩ := kindRowsWithK11sLotExist files returned.Z returned.G
  exact ⟨K, k11Stands_at_theGOfReturn made h T K laid, k11KindPays_at_theGOfReturn made h T K laid,
    k11KindBud_at_theGOfReturn made h T K laid⟩

end AtFullSide.K11

#print axioms AtFullSide.K11.k11_named
#print axioms AtFullSide.K11.k11Lot_fit
#print axioms AtFullSide.K11.k11Stands_at_theGOfReturn
#print axioms AtFullSide.K11.k11_stands_and_pays_at_some_rows
