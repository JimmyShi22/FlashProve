-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the list of the test on G_omega at a run, at the maker's return.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListOAtReturn.lean: CONDITIONAL.

Can the hypotheses be met together at a real run? NOT KNOWN. hP has a payer in form: theGAtBase_prover
(E2E/TheG.lean:99-102); hAr: atPure_returns_fillW_at (AtFullSide/K12/ReturnsAtAnyIndex.lean:112-117): each by
reading. WHAT LACKS: a K : KindRows whose shared rows hold rowAtOmega's: without it the place holds the
filling's own side and `IsListAtO`.on fails; a value of `ThreadsP`; ready's and runC's return; that the part is
called; hleft.

What is here. `onAtRun_O` (Sim2/ListO.lean) at the prover that the maker returns at the term
onlineProverPartsInUse I secondHashFunction S' O, at every I, S', O: hα, hB, hg and hgO are paid. The wide filling
is defined in Honest/K1/Law/WSideAtFill.lean. That the maker returns at it is not shown here.
The base filling is that term at matrixInput, Sz.ref, openHonest. Two things are not shown here
or beneath: W's rows ready · the lent o_sp words tied at U and O through OnlineProverParts.through:
THE SECOND IS AT THIS VERY PLACE.
NOT THE ONLINE PROVER: that is onlineFilling = OnlineProverParts.through … (baseFilling): the crossing is not here.

  `find_of_twice`, `twice_of_ready`   private; copied from ProofFile.Honest.Term's (AtFullSide/K12/Sim/OmegaAtBase.lean),
      which imports the term's files: where no two halves stand at one place the search finds a half
  `four_at_return`   the book, the key, the two halves, at the return's own prover
  `onAtRun_O_at_return`   the statement

THE PREMISES, SORTED. PUBLIC: h · hO (there is such a pO: `someO_at_head`) · hb. THE MAKER: hAr (the wide
filling). THE RUN: T · hρ · hR · hrun. WHICH OBJECTS: hP · hL. ON's FIELD asks, WHOLE: hleft.

Limits. All of Sim2/ListO.lean's. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListO
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesSharedTest
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.K14.SharedSendsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Chain K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St blocks)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K14 (jobOmega sendingPart liftSend sendPlace)

/-- **The search at a place where no two halves stand.** Copied from ProofFile.Honest.Term. -/
private theorem find_of_twice {V W X : Type} (hs : List (Placed V W X)) (h : twice hs = [])
    (g : Placed V W X) (hg : g ∈ hs) : hs.find? (fun x => x.place == g.place) = some g := by
  have hone : (hs.filter fun x => x.place == g.place).length ≤ 1 := by
    by_contra hn
    have hm : g.place ∈ (hs.map (·.place)).filter fun a =>
        1 < (hs.filter fun x => x.place == a).length :=
      List.mem_filter.2 ⟨List.mem_map_of_mem hg, by simpa using Nat.lt_of_not_le hn⟩
    unfold twice at h
    have := List.mem_eraseDups.2 hm
    rw [h] at this
    cases this
  have hsome : (hs.find? fun x => x.place == g.place).isSome = true :=
    List.find?_isSome.2 ⟨g, hg, beq_self_eq_true _⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
  have hy1 : y ∈ hs := List.mem_of_find?_eq_some hy
  have hy2 : (y.place == g.place) = true := by
    have := List.find?_some hy
    simpa using this
  have m1 : y ∈ hs.filter fun x => x.place == g.place := List.mem_filter.2 ⟨hy1, hy2⟩
  have m2 : g ∈ hs.filter fun x => x.place == g.place := List.mem_filter.2 ⟨hg, beq_self_eq_true _⟩
  cases hl : hs.filter (fun x => x.place == g.place) with
  | nil =>
    rw [hl] at m1
    cases m1
  | cons a l =>
    rw [hl] at hone m1 m2
    have hl0 : l = [] := by
      cases l with
      | nil => rfl
      | cons b l' => simp at hone
    subst hl0
    obtain rfl := List.mem_singleton.1 m1
    obtain rfl := List.mem_singleton.1 m2
    exact hy

/-- `ready` says that no two halves stand at one place of the shared chain. Copied from ProofFile.Honest.Term. -/
private theorem twice_of_ready {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : VerifiableInference.Desc.FileDescription Xi}
    {Bk : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hR : ready F Bk P w₀ rc x k = .ok R) : twice P.shared = [] := by
  have h := (ready_ok hR).1
  unfold readyTests at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i h2
      have h3 : (twice P.first ++ twice P.shared ++ twice P.second).isEmpty = true := by
        cases hx : (twice P.first ++ twice P.shared ++ twice P.second).isEmpty with
        | true => rfl
        | false =>
          rw [hx] at h2
          exact absurd rfl h2
      have h4 := List.isEmpty_iff.1 h3
      rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at h4
      exact h4.1.2

/-- **The four that the maker's return pays**: the book, the key, the test's half and the sending's, at the
return's own prover. -/
theorem four_at_return {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {pO : P12}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) (hO : (fourOf Np).O = some pO)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) = .ok Ar)
    {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins Ar.B}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B Ar.H w₀ rc x k = .ok R) :
    bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok Ar.B ∧
    (∀ x, Ar.H.key x = x.pub.key) ∧
    (Ar.H.shared.find? fun g => g.place == pO.place) =
      some (proverSideOfProximityTest (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (I.weights Zp) pO) :
        Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit).needsField ∧
    (Ar.H.shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ (fun w : Common W₀ IndexCommitterCoins TableKey => I.weights Zp w.w₀)
          (fun w => randAt (K1.qAt Zp Np) w.rc)) (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ IndexCommitterCoins TableKey) Unit)]⟩ := by
  have hm := h.toAtMg
  have eZ : Ar.Z = Zp := (atPure_at_laid h.laid hAr).1
  have hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok Ar.B := by
    have hb' := K14.atPure_book_at_head h hAr
    rw [K14.made_sends_at_files h.scope h.laid] at hb'
    exact hb'
  obtain ⟨-, hgO⟩ := sendings_found h I OnBytes.secondHashFunction S' O hAr
  have hs : Ar.H.shared = sharedWithUO I Zp := by
    obtain ⟨-, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok hAr
    rw [← eZ]
    exact hs
  have h1 : nowSharedBy (I.weights Zp) Zp =
      .ok (K14.proverSidesOfSharedRounds { S := (K1.qAt Zp Np).S, atPoint := 0, atZeta := 6 } (I.weights Zp) ++
        K14.proverSidesOfSharedSendings { P := K1.qAt Zp Np, atPoint := 0 } (I.weights Zp)
          (K14.randNow (K1.qAt Zp Np))) := K14.sixBody_at_head h _
  have hO' := halfO_at_head hm b1 b2 b3 b4 b5 b6 b7 b8 hb (I.weights Zp) hO
  have hmem : (proverSideOfProximityTest (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (I.weights Zp) pO) :
      Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit).needsField ∈ Ar.H.shared := by
    rw [hs]
    show _ ∈ (match nowSharedBy (I.weights Zp) Zp with
      | .ok six =>
        six ++ halfU (I.weights Zp) (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp ++
          halfO (I.weights Zp) Zp
      | .error _ => [])
    rw [h1, hO']
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  exact ⟨hB, key_at_pure hAr, find_of_twice Ar.H.shared (twice_of_ready hR) _ hmem, hgO⟩

/-- CONDITIONAL. **`onAtRun_O` AT THE MAKER's RETURN AT THE WIDE TERM**: not the online prover. -/
theorem onAtRun_O_at_return {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {pO : P12}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) (hO : (fourOf Np).O = some pO)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) = .ok Ar)
    {H : Prover W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B W₀ IndexCommitterCoins TableKey Cells Unit Unit}
    (hP : G.prover H = Ar.H) {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins Ar.B} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k ρ = .ok r)
    (L : Lettered Ar.B St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hL : IsListAtO L (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (I.weights Zp) pO)
      (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO
        [b1, b2, b3, b4, b5, b6, b7, b8]))
    (hleft : LeftEveryStandO T ρ r L
      (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (I.weights Zp) pO)) :
    OnAtRun₂ T ρ r L := by
  have hR' := hR
  rw [hP] at hR'
  obtain ⟨hB, hK, hf, hgO⟩ := four_at_return h hO b1 b2 b3 b4 b5 b6 b7 b8 hb I S' O hAr hR'
  refine onAtRun_O h.toAtMg hO b1 b2 b3 b4 b5 b6 b7 b8 hb hB (fun x => ?_) T hρ hR hrun (I.weights Zp) L
    hL ?_ ?_ hleft
  · rw [hP]
    exact hK x
  · rw [hP]
    exact hf
  · rw [hP]
    exact hgO

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.four_at_return
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_O_at_return
