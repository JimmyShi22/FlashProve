-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastValues.lean: the one named test on values at the first member of the key file's last chain ("no coefficient of
the row (Dot) on a pad"), from the shape: at a state of the written shape `A0` it says yes. So the premise `Values` of
'accepted_third₀' is paid.

Main names.
  `A1`, `step_A0`: the shape behind the member, by the kernel.
  `padsOkS`, `pads_A1`: the members' pads behind the member: in a mask table, or Omega's one entry behind the matrix's rows.
    A closed line: IT CAN SAY NO.
  `values_of_shape`, `values_first₃`.

By what. `padsClear_of_behind`, `dot_noPad` (E2E/KeyPadClear.lean, E2E/KeyDotRow.lean), at the written sizes by
`omega_pad_behind`. The row weights are well-formed by the mark that the shape carries.
What stays open. That a stand has the shape: `ThirdShaped`.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyPadClear
import E2E.KeyShapeSecond
import E2E.KeyQuietThird
import E2E.KeyShapeThirdFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params
open ProofFile.Honest
open VerifiableInference.Desc.Ground (has)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Third (S₃ takeOver)
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource)
open AtPublicFiles.AtFiles (Sh₃ sh₃ gSecond vSecond padB SF CF PadsClear padsClear_of_behind dot_noPad dot_form second_steps
  weights_ok omega_pad_behind borderSh KeySourced ThirdShaped Z₃Own carries_all_in_scope)
open AtPublicFiles.AtFiles.Full (A0 first_of_sourced six_sourced)

theorem ok_of_some {α : Type} {x : Except String α} {d : α} (h : x.toOption.isSome = true) :
    x = .ok (x.toOption.getD d) := by
  cases x with
  | error _ => cases h
  | ok a => rfl

/-- The shape behind the first member. -/
def A1 : Sh₃ := (gSecond SF A0).toOption.getD A0

theorem step_A0 : gSecond SF A0 = .ok A1 := ok_of_some (by decide +kernel)

/-- Omega's one pad entry, as the written layout places it. -/
def padOmega : Nat := (linLayOmega CF SF).index 3145727

/-- **The members' pads**: each lies in a mask table, or is Omega's entry. -/
def padsOkS (a : StSh) (g mine idx : Nat) : Bool :=
  has a.groups[g]? fun G => G.members.all fun o =>
    (((a.oracles[o]?).map (·.pad)).getD []).all fun q =>
      decide (q.1 = .mask) || (decide (o = mine) && decide (q.1 = .main) && decide (q.2 = idx))

theorem pads_A1 : padsOkS A1.1.st A1.2.own A1.2.omega padOmega = true := by decide +kernel

theorem w_A1 : A1.2.w ≠ A1.2.omega := by decide +kernel

theorem codes_A0 : A0.1.st.codes = CF := by decide +kernel

theorem weights_A0 : A0.2.border.map (·.weights) = some true := by decide +kernel

/-- **At a state of the written shape the test on values says yes.** -/
theorem values_of_shape (s : S₃) (hsh : sh₃ SF s = A0) : vSecond SF s = true := by
  have hg : gSecond SF (sh₃ SF s) = .ok A1 := by
    rw [hsh]
    exact step_A0
  obtain ⟨x, mine, d₂, dot, hb, -, -, hto, hdot, -, -, hcd, -, -, a₃, h3, et⟩ := second_steps SF s A1 hg
  have hc : s.st.codes = CF := (congrArg (fun a : Sh₃ => a.1.st.codes) hsh).trans codes_A0
  have e1 : A1.1 = a₃ := congrArg Prod.fst et
  have e2 : A1.2.omega = mine := congrArg (fun a : Sh₃ => a.2.omega) et
  have e3 : A1.2.own = s.loc.own := congrArg (fun a : Sh₃ => a.2.own) et
  have e4 : A1.2.w = s.loc.w := congrArg (fun a : Sh₃ => a.2.w) et
  have hp := pads_A1
  rw [e1, e2, e3] at hp
  have hwt : ∀ v ∈ x.g, v.ok = true := by
    have q : (sh₃ SF s).2.border.map (·.weights) = some true := by
      rw [hsh]
      exact weights_A0
    have q' : (s.loc.border.map (borderSh SF s.st.codes)).map (·.weights) = some true := q
    rw [hb] at q'
    have q'' : AtPublicFiles.AtFiles.weightsB SF (linLayOmega s.st.codes SF) x.g = true := Option.some.inj q'
    exact weights_ok q''
  have hne : s.loc.w ≠ mine := by
    rw [← e2, ← e4]
    exact w_A1
  have hdot' := hdot
  rw [hcd, hc] at hdot'
  obtain ⟨-, b1, b2, b3⟩ := omega_pad_behind
  unfold addRowS at h3
  split at h3
  swap
  · cases h3
  obtain rfl := Option.some.inj h3
  have hp' : has ((modAt (stSh d₂.st).groups s.loc.own fun G => { G with kinds := G.kinds ++ [RowKind.plain] })[s.loc.own]?)
      (fun G => G.members.all fun o =>
        ((((stSh d₂.st).oracles[o]?).map (·.pad)).getD []).all fun q =>
          decide (q.1 = .mask) || (decide (o = mine) && decide (q.1 = .main) && decide (q.2 = padOmega))) = true := hp
  rw [modAt_get, grp_get] at hp'
  unfold vSecond
  simp only [hb, hto, hdot]
  unfold padB
  cases hG : d₂.st.groups[s.loc.own]? with
  | none =>
    rw [hG] at hp'
    cases hp'
  | some G =>
    rw [hG] at hp'
    have hall : (G.members.toList.all fun o =>
        ((((stSh d₂.st).oracles[o]?).map (·.pad)).getD []).all fun q =>
          decide (q.1 = .mask) || (decide (o = mine) && decide (q.1 = .main) && decide (q.2 = padOmega))) = true := hp'
    have hpc : PadsClear d₂.st G dot := by
      refine padsClear_of_behind SF x.g x.shared.psi mine _ s.loc.w _ dot hdot' hwt hne b3 d₂.st G
        fun o ho X hX q hq => ?_
      have c := List.all_eq_true.1 hall o ho
      rw [orc_get, hX] at c
      have c' := List.all_eq_true.1 c q hq
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at c'
      rcases c' with c' | ⟨⟨c1, c2⟩, c3⟩
      · exact Or.inl c'
      · exact Or.inr ⟨c1, c2, 3145727, c3, b1, b2⟩
    exact dot_noPad (dot_form _ _ _ _ _ _ _ _ hdot) hpc

section
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {Bk : ProverCoinCounts} {V W Y Pb : Type}
  {T₃ : Thread Bk (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl V W Y Pb}
  {v : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}

/-- **The premise `Values` at the first member.** -/
theorem values_first₃ (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hbs : T₃.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder) (hZ : ThirdShaped T₃ v A0)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String) : Values T₃ (Z₃Own Xs Pl v) fall 0 := by
  intro blk _ k s m E ds y cols hT _ _ _ _
  obtain ⟨-, -, hlin, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  have hS : Xs.chains.made.sized.key.once.shape = SF := hlin.symm.trans (six_sourced hs scope).lin
  have hr := shape_at T₃ (Z₃Own Xs Pl v) (n := 4) (b := 0) (a₀ := A0)
    (by rw [hbs]; exact Nat.le_of_eq (AtPublicFiles.KeyThread.lengths scope hs.named).2.2.symm) (by decide) hZ.yes hZ.first
    (fun j => by rw [hbs]; exact carries_all_in_scope hs scope v T₃.ft j) hT
  have hr₁ : (Except.ok A0 : Except String Sh₃) = .ok (sh₃ Xs.chains.made.sized.key.once.shape s) := hr
  have e : sh₃ Xs.chains.made.sized.key.once.shape s = A0 := (Except.ok.inj hr₁).symm
  show vSecond Xs.chains.made.sized.key.once.shape s = true
  rw [hS] at e ⊢
  exact values_of_shape s e

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.step_A0
#print axioms AtPublicFiles.KeyLastChain.pads_A1
#print axioms AtPublicFiles.KeyLastChain.w_A1
#print axioms AtPublicFiles.KeyLastChain.codes_A0
#print axioms AtPublicFiles.KeyLastChain.weights_A0
#print axioms AtPublicFiles.KeyLastChain.values_of_shape
#print axioms AtPublicFiles.KeyLastChain.values_first₃
