-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/ChainSpend.lean: the yes of `spendOk` gives what a bound over the chain of a
proximity test (the kind K12) asks of its rounds and sizes beside `Chain.Pub`.

Definitions, statements and proofs.
Main names:
  `nSB_eq`, `sd_of_B`, `sized_of_L`: from a clause's yes (Johnson/Desc/K12/Law/SpendOk.lean) to the
    library's proposition: `SendsDraws`, by the library's `sendsDraws_of` at the round itself, and
    `Sg.Sized`.
  `SpendPub c`: by recursion on the chain: at a step `FoldRounds dE dT` and `Sized`; at the base
    case `SendsDraws dL 1 1 0 0` and `Sized`. These are the premises on rounds and sizes of
    `foldSem_of` and `baseSem_of` that `Chain.Pub` does not hold.
  `spend_walk`, `spend_of_ok`: `spendOk p = true` gives `SpendPub c` for the chain c that
    `chainFrom` makes of the place's declared rounds, at any letters.
Limits: Nothing on radii, nor on the facts on codes that the three block laws ask beside (`CodesOK`,
`ErrOK`, `ListAt`, `BaseCodes`, `Laws`). The yes of `spendOk` is a run's to show. Nothing on
soundness. Nothing on hiding. This is a statement on the library's chain; that a yes of the block
gives the chain's yes is the law of the kind, under its own premises.

-/
import Johnson.Desc.K12.Law.ChainOf
import Johnson.Desc.K12.Law.SpendOk
import OnBytes.Slice.Numbers

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK

theorem nSB_eq : ∀ l : List Fmt.Item, nSB l = nS l
  | [] => rfl
  | .e :: l => congrArg (· + 1) (nSB_eq l)
  | .answer :: l => congrArg (· + 1) (nSB_eq l)
  | .root :: l => nSB_eq l
  | .f :: l => nSB_eq l
  | .word :: l => nSB_eq l

theorem sd_of_B {w : WR} {ns ne np a : ℕ} (h : sdB w ns ne np a = true) :
    SendsDraws w.rd ns ne np a := by
  simp only [sdB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  have := sendsDraws_of (d := w.rd) (r := ⟨w.entry, w.kind, w.items, []⟩) ⟨rfl, rfl, rfl⟩ h1 h2 h3
      h4 h5
  rw [← nSB_eq] at this
  simpa only [h6, h7, h8, h9] using this

theorem sized_of_L {a : Fmt.M1.Stage} (h : ok (sizedL a) = true) : (sgOf a).Sized := by
  simp only [sizedL, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- What a spender of the chain in a bound asks of its rounds and sizes beside Chain.Pub. -/
def SpendPub : {s : Sg} → Chain s → Prop
  | _, .last s _ dL _ _ _ _ => SendsDraws dL 1 1 0 0 ∧ s.Sized
  | _, .step s _ _ _ _ dE dT _ _ _ _ _ _ _ next => FoldRounds dE dT ∧ s.Sized ∧ SpendPub next

/-- The clauses' yes from a stage on gives `SpendPub` of the chain. By recursion on the stages. -/
theorem spend_walk (X : Letters) : ∀ (rest : List Fmt.M1.Stage) (j : Nat) (a : Fmt.M1.Stage)
    (l : List WR)
    (c : Chain (sgOf a)), chainFrom X rest a l = some c → ok (spendL j a rest l) = true → SpendPub c
  | [], j, a, l, c, hc, h => by
    unfold chainFrom at hc
    split at hc
    · rename_i dL dB
      cases hc
      unfold spendL at h
      dsimp only at h
      rw [ok_tag, ok_cons, Bool.and_eq_true] at h
      exact ⟨sd_of_B h.1, sized_of_L h.2⟩
    · cases hc
  | b :: rest, j, a, l, c, hc, h => by
    unfold chainFrom at hc
    split at hc
    · rename_i dE dT l'
      split at hc
      · rename_i hh
        split at hc
        · rename_i dS dC l'' hd
          unfold spendL at h
          dsimp only at h
          rw [hd] at h
          dsimp only at h
          rw [ok_append, ok_tag, ok_cons, ok_cons, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true] at h
          cases hn : chainFrom X rest b l'' with
          | none => rw [hn] at hc; cases hc
          | some next =>
            rw [hn] at hc
            have ih := spend_walk X rest (j + 1) b l'' next hn h.2
            have hc' := Option.some.inj hc
            subst hc'
            split
            · exact ⟨⟨sd_of_B h.1.1, sd_of_B h.1.2.1⟩, sized_of_L h.1.2.2, ih⟩
            · exact ⟨⟨sd_of_B h.1.1, sd_of_B h.1.2.1⟩, sized_of_L h.1.2.2, ih⟩
        · cases hc
      · cases hc
    · cases hc

/-- At a place: whatever chain pub_of_ok gives, spendOk's yes gives SpendPub of it. -/
theorem spend_of_ok (X : Letters) (p : P12) (h : spendOk p = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage)
    (w0 : WR) (l : List WR) (c : Chain (sgOf a)) (hs : p.nums.stages = a :: rest)
    (hw : writtenOf p.nums = some (w0 :: l)) (hc : chainFrom X rest a l = some c) : SpendPub c := by
  unfold spendOk spendAll at h
  rw [hs, hw] at h
  exact spend_walk X rest 0 a l c hc h

end H2K.Pub
