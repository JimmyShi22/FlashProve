-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SwRoots.lean: what a yes of the code switch's part `switchE` leaves of the
count of roots and of the stretch of rounds.

One statement with its proof, beside `switchE_ok` (Johnson/Desc/K12/Law/SwUnfold.lean), so that no
statement there turns.
Main names:
  `switchE_roots`: at a target without kept members and with one answer, the others not sampled, on
    any stretch: a yes takes two entries and two rounds off the stretch; the roots behind are the
    roots in front and one for each tree that the switch's message lays (`layTrees` at the codes in
    front); the two numbers of the chain stay.
Limits: Nothing on what the trees hold. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.SwUnfold

set_option autoImplicit false
namespace H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc
open H2K.FoldLaw (bind_ok)

theorem switchE_roots (old : SingleRows) (T : SwitchTarget) (gp : Nat) (others : Array OracleNotice)
    (s s' : H2K.PS) (out : Switched) (theta : E) (hk : T.kept = #[])
    (h1 : T.shape.answers = 1) (ho : ∀ n ∈ others, n.shape.answers = 0)
    (h : H2K.switchE old T gp others true s = .ok ((out, theta), s')) :
    ∃ (e₁ e₂ : Fmt.Entry) (es : List Fmt.Entry) (r₁ r₂ : Fmt.RoundView) (rs : List Fmt.RoundView) (lay : TreeLay),
      s.entries = e₁ :: e₂ :: es ∧ s.rounds = r₁ :: r₂ :: rs ∧
      layTrees s.d.st.codes (sentOf T others) = some lay ∧
      s'.d.roots = s.d.roots + lay.shapes.size ∧ s'.entries = es ∧ s'.rounds = rs ∧ s'.p = s.p := by
  unfold H2K.switchE at h
  split at h
  · rename_i e₁ e₂ es r₁ r₂ rs he hr
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨ids, sd, an, took, d₂⟩, hsend, h⟩ := bind_ok h
    have hsent : Tw.L9.switchNotices T others = #[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++ others
        := by
      unfold Tw.L9.switchNotices
      rw [hk]
      simp
    rw [hsent] at hsend
    obtain ⟨lay, beta, smp, alpha, places, vs, s1, _, rfl, _, _, _, _, _, rfl, _, rfl⟩ :=
      sendOne_ok _ _ _ ⟨T.shape, T.leafClass⟩ others _ _ _ _ _ _ h1 ho (opt_ok hsend)
    dsimp only at h
    split at h
    · simp only [pure_bind] at h
      obtain ⟨o, _, h⟩ := bind_ok h
      cases h
      exact ⟨e₁, e₂, es, r₁, r₂, rs, lay, he, hr, s1, rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

end H2K.Sw
