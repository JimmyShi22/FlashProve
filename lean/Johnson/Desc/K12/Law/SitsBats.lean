-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.SitsChains
import Johnson.Desc.K12.Law.StartOfMade
import Johnson.Desc.K12.Law.MadeRounds
/-
Johnson/Desc/K12/Law/SitsBats.lean: HOW MANY DECLARED ROUNDS NAMED "BAT" STAND IN FRONT OF THE
PROXIMITY TEST's SEATS ON THE TWO LATER CHAINS: the one count that
Johnson/Desc/K12/Law/StartOfMade.lean's free_seat leaves as a premise, AT THE WRITTEN CUTS of
Johnson/Desc/K12/Law/SitsChains.lean. GENERAL IN THE PLAN.
BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  batsR_zero           no round of a list is named "BAT": the count is 0.
  entries_noBat · k1_noBat · blocksOr_noBat     the shared chain's own rounds are named "LIN
      point", "LOC", "LIN zeta", "SPLIT"; a sending's "SEND seed", "SEND answer": by these kinds'
      own texts.
  sharedPre_bats       in front of the test on G_u: 0.
  secondPre_rounds · secondPre_bats     in front of the own test NO ROUND IS DECLARED AT ALL: 0.
  lay_names · later_noBat · k12_bats     where the kind's block passes its test on the plan its
      own declared rounds hold exactly one round named "BAT", the first.
  sharedPreO_bats      in front of the test on G_omega: 1 (under G_u's test's block's yes on the
      plan).
LIMITS. At the first chain's seat («none behind») what stands behind is other lots' blocks, under
«there is» in firstChain_cut: not here.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Made (batsR bats)

theorem batsR_zero (l : List Fmt.DeclaredRound) (h : ∀ r ∈ l, (r.entry.name == "BAT") = false) :
    batsR l = 0 := by
  unfold batsR bats
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro e he
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 he
  simp [h r hr]

theorem entries_noBat (P : _root_.Desc.K14.P14) :
    ∀ e ∈ _root_.Desc.K14.entries P, (e.name == "BAT") = false := by
  intro e he
  unfold _root_.Desc.K14.entries at he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  have h1 := (List.of_mem_zip hx).1
  unfold _root_.Desc.K14.rounds at h1
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h1
  rcases h1 with (h | h | h) | h
  · rw [_root_.Desc.K14.Round.entry, h]; rfl
  · rw [_root_.Desc.K14.Round.entry, h]; rfl
  · rw [_root_.Desc.K14.Round.entry, h]; rfl
  · split at h
    · rw [List.mem_singleton] at h
      rw [_root_.Desc.K14.Round.entry, h]; rfl
    · cases h

theorem k1_noBat (Q : K1.Par) : ∀ r ∈ K1.rounds Q, (r.entry.name == "BAT") = false := by
  intro r hr
  unfold K1.rounds at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rfl

theorem cut_noBat (P : _root_.Desc.K14.P14) (i k : Nat) (f : Fmt.Entry → Fmt.DeclaredRound)
    (hf : ∀ e, (f e).entry = e) :
    ∀ r ∈ (((_root_.Desc.K14.entries P).drop i).take k).map f,
      (r.entry.name == "BAT") = false := by
  intro r hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr
  rw [hf]
  exact entries_noBat P e (List.mem_of_mem_drop (List.mem_of_mem_take he))

theorem blocksOr_noBat (P : _root_.Desc.K14.P14) :
    ∀ b ∈ _root_.Desc.K14.blocksOr P, ∀ r ∈ b.rounds, (r.entry.name == "BAT") = false := by
  intro b hb r hr
  unfold _root_.Desc.K14.blocksOr at hb
  cases hB : _root_.Desc.K14.blocks P with
  | none =>
    rw [hB] at hb
    simp only [Option.getD_none, List.mem_singleton] at hb
    subst hb
    cases hr
  | some l =>
    rw [hB] at hb
    simp only [Option.getD_some] at hb
    unfold _root_.Desc.K14.blocks at hB
    simp only [bind, Option.bind, pure] at hB
    split at hB
    · cases hB
    · cases hB
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cut_noBat P _ _ _ (fun _ => rfl) r hr
      · exact k1_noBat _ r hr
      · exact cut_noBat P _ _ _ (fun _ => rfl) r hr
      · exact cut_noBat P _ _ _ (fun _ => rfl) r hr
      · exact k1_noBat _ r hr
      · exact cut_noBat P _ _ _ (fun _ => rfl) r hr
      · exact cut_noBat P _ _ _ (fun _ => rfl) r hr
      · exact cut_noBat P _ _ _ (fun _ => rfl) r hr

/-- In front of the test on G_u no declared round is named "BAT". -/
theorem sharedPre_bats (Cl' : Type) (c : OnBytes.Model.Verify.Chains) (P : _root_.Desc.K14.P14)
    (N : H2U.Places4) : batsR ((sharedPre Cl' c P N).flatMap (·.rounds)) = 0 := by
  apply batsR_zero
  intro r hr
  obtain ⟨b, hb, hr⟩ := List.mem_flatMap.1 hr
  unfold sharedPre at hb
  rcases List.mem_cons.1 hb with rfl | hb
  · cases hr
  · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 hb
    exact blocksOr_noBat P b0 hb0 r hr

/-- In front of the own test no round is declared at all. -/
theorem secondPre_rounds (Cl' : Type) (p : Third.P₁₄) (K : Blk') :
    (secondPre Cl' p K).flatMap (·.rounds) = [] := rfl

theorem secondPre_bats (Cl' : Type) (p : Third.P₁₄) (K : Blk') :
    batsR ((secondPre Cl' p K).flatMap (·.rounds)) = 0 := by
  rw [secondPre_rounds]
  rfl

/-! ### the kind's own rounds -/

/-- layOpens keeps every round's name. -/
theorem lay_names (own : Bool) : ∀ (rs : List Fmt.Round) (seen : Bool)
    (l : List (List (Fmt.Shape × Fmt.TreeSource))) (R : List Fmt.DeclaredRound),
    H2U.layOpens own seen rs l = some R →
      R.map (·.entry.name) = rs.map (·.entry.name) := by
  intro rs
  induction rs with
  | nil =>
    intro seen l R h
    rw [H2U.layOpens.eq_def] at h
    cases l with
    | nil => cases h; rfl
    | cons x t => cases h
  | cons r rs ih =>
    intro seen l R h
    rw [H2U.layOpens.eq_def] at h
    dsimp only at h
    have hn : (if (own && !seen && (r.entry.name == "FOLD epsilon")) = true then
        { r.entry with msg := 32 + r.entry.msg, roots := 1 } else r.entry).name = r.entry.name := by
      split <;> rfl
    split at h
    · obtain ⟨R', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [List.map_cons, List.map_cons, ih _ _ _ h1]
      exact congrArg (· :: _) hn
    · split at h
      · split at h
        · cases h
        · obtain ⟨R', h1, rfl⟩ := Option.map_eq_some_iff.1 h
          rw [List.map_cons, List.map_cons, ih _ _ _ h1]
          exact congrArg (· :: _) hn
      · cases h

/-- No round of a test behind its batching's is named "BAT". -/
theorem later_noBat (work : Nat) : ∀ (rest : List Fmt.M1.Stage) (tree W : Nat) (old : Fmt.M1.Stage),
    ∀ r ∈ Fmt.M1.laterRounds work tree W old rest, (r.entry.name == "BAT") = false := by
  intro rest
  induction rest with
  | nil =>
    intro tree W old r hr
    simp only [Fmt.M1.laterRounds, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  | cons new rest ih =>
    intro tree W old r hr
    simp only [Fmt.M1.laterRounds, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_replicate] at hr
    rcases hr with ((rfl | ⟨_, rfl⟩) | (rfl | rfl)) | hr
    · rfl
    · rfl
    · rfl
    · rfl
    · exact ih _ _ _ r hr

/-- The kind's block's own declared rounds hold exactly one round named "BAT": the first. -/
theorem k12_bats {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) : batsR (proximityTestKind X p : Block T Cl).rounds = 1 := by
  obtain ⟨s, next, rest, R, _, hR, e⟩ :=
    H2K.Made.rounds_top p.nums _ (VerifiableInference.Desc.K12.k12_rounds X p hp)
  rw [e]
  have h0 : batsR R = 0 := by
    apply batsR_zero
    intro r hr
    have hm : r.entry.name ∈ R.map (·.entry.name) := List.mem_map.2 ⟨r, hr, rfl⟩
    rw [lay_names _ _ _ _ _ hR] at hm
    obtain ⟨r', hr', e'⟩ := List.mem_map.1 hm
    rw [← e']
    exact later_noBat _ _ _ _ _ r' hr'
  unfold batsR bats at h0 ⊢
  rw [List.map_cons, List.filter_cons_of_pos (by rfl), List.length_cons, h0]

/-- In front of the test on G_omega: one: G_u's test's own. -/
theorem sharedPreO_bats (Cl' : Type) (c : OnBytes.Model.Verify.Chains) (P : _root_.Desc.K14.P14)
    (N : H2U.Places4) (hp : (proximityTestKind guardedProximityTestParts (pGu N) : Blk').planOk = true) :
    batsR ((sharedPre Cl' c P N ++ [guEntry Cl' N]).flatMap (·.rounds)) = 1 := by
  have h1 := sharedPre_bats Cl' c P N
  have h2 : batsR (guEntry Cl' N).rounds = 1 := k12_bats guardedProximityTestParts (pGu N) hp
  unfold batsR bats at h1 h2 ⊢
  rw [List.flatMap_append, List.map_append, List.filter_append, List.length_append, h1]
  simpa using h2

end H2K.JointK

#print axioms H2K.JointK.k12_bats
#print axioms H2K.JointK.sharedPreO_bats
#print axioms H2K.JointK.blocksOr_noBat
#print axioms H2K.JointK.sharedPre_bats
#print axioms H2K.JointK.secondPre_bats
