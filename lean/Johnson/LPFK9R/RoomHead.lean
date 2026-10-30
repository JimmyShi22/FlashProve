-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/RoomHead.lean: THE FIELDS batch AND behind OF KeepShares
(Johnson/P1L20R/RoomKeep.lean), TO THE LETTER, IN THE GOALS' SCOPE, WITH NO PREMISE BESIDE THE SCOPE
AND THE OPENING: the half that Johnson/LPFK9R/RoomRuns.lean left owed (the statement stays over the
runs of the head's link's nine hearing sub-protocols) is paid here.
  `frames_runs`: the frames' sub-protocols have no run. `head_k1`: the head's link's two later
    sendings.
  `hear_runs_head`: THE SIBLING AT l = 24 OF `hear_runs` (Johnson/IMR/LinkRest.lean),
    general in a relation R that is reflexive, transitive and given by `Quiet`:
    seat by seat: K7 (`IM.k7_of`) · K2 (`IM.k2_head_of`; its mute arm falls by an accept of that
    sub-protocol) · K3 twice (`IM.k3_of`) · K6 (`IM.k6_of`) · K1 twice (`IM.k1_later`) · K8
    (`IM.k8_of_head`) · K11 (`IM.k11_of`), each with its maker's own lemma on "quiet".
  `low_reached`, `head_reached`: the statement's half where a state is reached: the accepts come out
    of "reached" (`reach_yes`).
  `field_batch_home`, `field_behind_home`: **the two fields**.
Limits. In the goals' scope alone, at OnBytes.secondHashFunction alone. Two fields of thirteen. No soundness
statement.

-/
import Johnson.LPFK9R.RoomRuns
import Johnson.IMR.K6Seat
import Johnson.IMR.K7Seat
import Johnson.IMR.K11Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl Lot Ground)
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Tied
open Meaning.K2
open P1L20 (Hands2 KeepsAt outOfGroupsB nA)

variable {R : S → S → Prop}

/-- The frames' sub-protocols have no run. -/
theorem frames_runs {Z : ProofFile.Pub} {fb : Block S Unit} (h : fb ∈ P1L20.blocksOf Z) :
    RunsKeep R fb := by
  unfold P1L20.blocksOf at h
  split at h
  · obtain ⟨f, -, hf⟩ := List.mem_flatMap.1 h
    unfold ProofFile.frameBlocks at hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> exact runs_none rfl rfl
  · obtain rfl := List.mem_singleton.1 h
    exact runs_none rfl rfl

section
variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The head's link's two later sendings (`Meaning.K2.runs_k1`'s proof at l = 24). -/
theorem head_k1 (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    (hQ : ∀ s t, Quiet s t → R s t) (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) {Lk : Link S Cl}
    {b : Block S Cl} (eL : c.links[24]? = some Lk) {j : Nat} (hj' : j = 4 ∨ j = 6)
    (e : Lk.hear[j]? = some b) : RunsKeep R b := by
  have hk : (kindsBeforeBatching (IM.subAt 24) (24 == 0))[j]? = some KindName.K1 := by
    rcases hj' with rfl | rfl <;> rfl
  obtain ⟨Lk', b', Xl, pr, pd, reads, digits, eL', e', -, -, harm⟩ :=
    IM.k1_later O 24 (IM.subAt 24) (IM.subs_scope hS hR O 24 (by omega)) j hk
      (by rcases hj' with rfl | rfl <;> decide)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  rcases harm with ⟨-, la⟩ | ⟨-, la⟩
  · exact alone_runs hr la (runs_retype hr (runs_andThen hr ht _ (runs_none rfl rfl)
      (whole_mono hQ (orLoud_whole fun b hb => readsQuietAt_quiet hb)).2))
  · exact alone_runs hr la (runs_retype hr (runs_none rfl rfl))

/-- **EVERY HEARING SUB-PROTOCOL OF THE HEAD's LINK**, given an accept of the second: the sibling at
l = 24 of `Meaning.K2.hear_runs`. -/
theorem hear_runs_head (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    (hQ : ∀ s t, Quiet s t → R s t) (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) {Lk : Link S Cl}
    (eL : c.links[24]? = some Lk)
    (hy : ∀ b₁, Lk.hear[1]? = some b₁ → ∃ s rs gs t, b₁.decide s rs gs = .ok t) :
    ∀ b ∈ Lk.hear, RunsKeep R b := by
  intro b hb
  obtain ⟨j, hj, e'⟩ := List.getElem_of_mem hb
  have e : Lk.hear[j]? = some b := by rw [List.getElem?_eq_getElem hj, e']
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk', -, -, -, -, eL', hlen, -⟩ := hfr 24 (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  rw [if_pos rfl] at hlen
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  · obtain ⟨Lk', b', eL', e', lf⟩ := IM.k7_of hS hR O
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    have hk7 : RunsKeep R (IM.k7Block Bs.G₀.W 24) := by
      unfold IM.k7Block
      exact runs_andThen hr ht _ (runs_guarded hr _ _ (runs_none rfl rfl))
        (whole_mono hQ (k7Of_quiet _ _)).2
    rcases lf with la | ⟨fb, hfb, ex⟩
    · exact alone_runs hr la (runs_retype hr hk7)
    · exact with_runs hr ht ex (runs_retype hr hk7)
        (runs_guardMark hr (runs_retype hr (frames_runs hfb)))
  · obtain ⟨Lk', b', x, eL', e', -, la, hx⟩ := IM.k2_head_of hS hR O
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    refine alone_runs hr la (runs_retype hr ?_)
    rcases hx with ⟨-, hm⟩ | ⟨P', n, -, -, h3⟩
    · obtain ⟨s, rs, gs, t, d⟩ := hy b e
      have y1 := ((IM.yes_alone la (by intro q; cases q) s t rs gs).1 d).1
      obtain ⟨er, he⟩ := hm s rs gs
      have y1' : x.decide s rs gs = .ok t := y1
      rw [he] at y1'
      cases y1'
    · rcases h3 with ⟨hn, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
      · cases hn
      · rw [ex]
        exact runs_none rfl rfl
      · rw [ex]
        exact runs_none rfl rfl
  · obtain ⟨Lk', b', x, eL', e', k3, la⟩ := IM.k3_of hS hR O 24 (by omega) false
    have e'' : Lk'.hear[2]? = some b' := e'
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e'')
    exact quiet_runs hr hQ la (theStated_quiet _ _ _ _ _ _ k3)
  · obtain ⟨Lk', b', x, ms, eL', e', -, k6, la, -⟩ := IM.k6_of hS hR O
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact quiet_runs hr hQ la (seatedClaims_quiet k6)
  · exact head_k1 hr ht hQ hS hR O eL (Or.inl rfl) e
  · obtain ⟨Lk', b', Xl, eL', e', -, la, -⟩ := IM.k8_of_head hS hR O
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact quiet_runs hr hQ la (k8Whole_quiet _)
  · exact head_k1 hr ht hQ hS hR O eL (Or.inr rfl) e
  · obtain ⟨Lk', b', x, eL', e', k3, la⟩ := IM.k3_of hS hR O 24 (by omega) true
    have e'' : Lk'.hear[7]? = some b' := e'
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e'')
    exact quiet_runs hr hQ la (theStated_quiet _ _ _ _ _ _ k3)
  · obtain ⟨Lk', b', eL', e', la, -⟩ := IM.k11_of hS hR O
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact quiet_runs hr hQ la (headMerge11_quiet _)

/-- The statement's half at a link l < 24, where a state is reached behind its first
sub-protocol. -/
theorem low_reached {Q : Type} (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (start : Q → S) {l : ℕ}
    (hl : l < 24) {Lk : Link S Cl} (eL : c.links[l]? = some Lk) {k : ℕ} {x : Q × S}
    (hk : 14 * l + 2 < k) (hreach : Reach 0 c.blocksInOrder start k x) :
    ∀ b ∈ Lk.hear, RunsKeep StS b := by
  refine hear_runs stS_refl stS_trans (fun _ _ q => q.1.1) hS hR O hl eL fun b₀ h0 => ?_
  have e0 := IM.hear_at_flat eL h0
  rw [IM.flatIx_scope hS hR O (by omega) 0] at e0
  obtain ⟨s₁, s₂, hy⟩ := reach_yes hreach (14 * l + 0 + 2) (by omega) b₀ e0
  obtain ⟨rs, gs, d⟩ := stepYes_decide hy
  exact ⟨s₁, rs, gs, s₂, d⟩

/-- The statement's half at the head's link, where a state is reached behind its second
sub-protocol. -/
theorem head_reached {Q : Type} (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (start : Q → S) {k : ℕ}
    {x : Q × S} (hk : 339 < k) (hreach : Reach 0 c.blocksInOrder start k x) (Lk : Link S Cl)
    (eL : c.links[24]? = some Lk) : ∀ b ∈ Lk.hear, RunsKeep StS b := by
  refine hear_runs_head stS_refl stS_trans (fun _ _ q => q.1.1) hS hR O eL fun b₁ h1 => ?_
  have e0 := IM.hear_at_flat eL h1
  rw [IM.flatIx_scope hS hR O (by omega) 1] at e0
  obtain ⟨s₁, s₂, hy⟩ := reach_yes hreach (14 * 24 + 1 + 2) (by omega) b₁ e0
  obtain ⟨rs, gs, d⟩ := stepYes_decide hy
  exact ⟨s₁, rs, gs, s₂, d⟩

/-- **THE FIELD batch OF KeepShares, TO THE LETTER, IN THE GOALS' SCOPE: NO PREMISE BESIDE.** -/
theorem field_batch_home {Q : Type} (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (start : Q → S) :
    ∀ l < 25, ∀ (Lk : Link S Cl) p, c.links[l]? = some Lk → IM.k9At Z l = some p →
      KeepsAt c start (14 * l + nA l + 2)
        (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p
          (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)) := by
  intro l hl Lk p e hp z s s' hreach hy ho
  by_cases h24 : l = 24
  · subst h24
    exact field_batch_scope hS hR O start
      (head_reached hS hR O start (by unfold nA; rw [if_pos rfl]; omega) hreach) 24 hl Lk p e hp
      z s s' hreach hy ho
  · refine batch_keeps c start _ p Lk (fun b hb => stIx_runs ?_ (hear_runs_stays hS hR O hl e b hb))
      z s s' hreach hy ho
    exact low_reached hS hR O start (by omega) e (by unfold nA; split <;> omega) hreach b hb

/-- **THE FIELD behind OF KeepShares, TO THE LETTER, IN THE GOALS' SCOPE: NO PREMISE BESIDE.** -/
theorem field_behind_home {Q : Type} (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (start : Q → S) :
    ∀ l < 25, ∀ Lk : Link S Cl, c.links[l]? = some Lk → ∀ z s t,
      Reach 0 c.blocksInOrder start (14 * l + nA l + 3) (z, s) → Lk.runBehind s = .ok t →
      outOfGroupsB s = true → Hands2 s t := by
  intro l hl Lk e z s t hreach h ho
  by_cases h24 : l = 24
  · subst h24
    exact field_behind_scope hS hR O start
      (head_reached hS hR O start (by unfold nA; rw [if_pos rfl]; omega) hreach) 24 hl Lk e
      z s t hreach h ho
  · refine behind_keeps Lk (fun b hb => stIx_runs ?_ (hear_runs_stays hS hR O hl e b hb)) s t h ho
    exact low_reached hS hR O start (by omega) e (by unfold nA; split <;> omega) hreach b hb

end

end LPFK9

#print axioms LPFK9.hear_runs_head
#print axioms LPFK9.field_batch_home
#print axioms LPFK9.field_behind_home
