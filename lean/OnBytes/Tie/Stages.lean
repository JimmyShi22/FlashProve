-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Stages.lean: what it means that the strict reader has read a chain, stage by stage.

The strict reader (`Fmt.readChain`) is a single function. The theorems of this directory need its
stages by name: the description is in order; the chain's random bytes were found; the first value
was made; the fold over the rounds ended in a state. This file states that once, for a chain that
begins at any byte of a file and under any record of tree vertices.

Main definition: `Hash`.
Main theorems: `read_stages`, `rnd_some`.
It claims nothing on what a chain proves.
-/
import Fmt.Rules8Steps

set_option autoImplicit false

namespace OnBytes.Tie

/-- A hash function of the format's type, in the monad `Id`. -/
abbrev Hash : Type := Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray

/-- If the strict reader has read a chain, then each of its stages has succeeded. The chain may
begin at any byte i, and the record `seen` of vertices may hold anything. -/
theorem read_stages (h : Hash) (S : Fmt.Spec) (seen : Fmt.Seen) (b : ByteArray) (i : Nat)
    (o : Fmt.ChainOut) (j : Nat) (e : Fmt.readChain (m := Id) h S seen b i = some (o, j)) :
    S.ok = true ∧ ∃ (x : Option ByteArray) (i0 : Nat) (hd : Fmt.ChainHead) (s : Fmt.St),
      Fmt.rndOf S b i = some (x, i0) ∧
      Fmt.startChainW (m := Id) h S.label (h 169 0 1 Fmt.zero32 S.params) S.statement x
        = some hd ∧
      Fmt.foldRounds (m := Id) h S.cfg S.plan hd.run b S.rounds
        (⟨i0, ⟨S.label, hd.rho0, 0⟩, #[], seen, #[]⟩ : Fmt.St) = some s ∧
      o = ⟨h 169 0 1 Fmt.zero32 S.params, hd.run, hd.rho0, s.chain.rho, s.seen, s.out⟩ ∧
      j = s.pos := by
  have e' : Fmt.readI h S seen b i = some (o, j) := (Fmt.readChain_readI h S seen b i).symm.trans e
  unfold Fmt.readI at e'
  split at e'
  · cases e'
  · rename_i hok
    split at e'
    · cases e'
    · rename_i x i0 hr
      split at e'
      · cases e'
      · rename_i hd hst
        split at e'
        · cases e'
        · rename_i cN os hf
          have h2 : Fmt.foldRounds (m := Id) h S.cfg S.plan hd.run b S.rounds
              (⟨i0, ⟨S.label, hd.rho0, 0⟩, #[], seen, #[]⟩ : Fmt.St)
              = (Fmt.foldI h S.cfg S.plan hd.run b S.rounds (Fmt.core0 S i0 hd seen)).map
                  fun y => y.1.st (#[] ++ y.2.toArray) :=
            Fmt.fold_foldI h S.cfg S.plan hd.run b S.rounds
              (⟨i0, ⟨S.label, hd.rho0, 0⟩, #[], seen, #[]⟩ : Fmt.St)
          rw [hf] at h2
          have h3 : Fmt.foldRounds (m := Id) h S.cfg S.plan hd.run b S.rounds
              (⟨i0, ⟨S.label, hd.rho0, 0⟩, #[], seen, #[]⟩ : Fmt.St)
              = some (cN.st os.toArray) := by
            rw [h2]
            show some (cN.st (#[] ++ os.toArray)) = some (cN.st os.toArray)
            rw [Array.empty_append]
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e')
          exact ⟨by simpa using hok, x, i0, hd, cN.st os.toArray, hr, hst, h3, rfl, rfl⟩

/-- For a chain with random bytes, in its file or given, `Fmt.rndOf` fails or finds some. -/
theorem rnd_some (S : Fmt.Spec) (b : ByteArray) (i : Nat) (x : Option ByteArray) (i0 : Nat)
    (hn : S.rand.isNone = false) (hr : Fmt.rndOf S b i = some (x, i0)) :
    ∃ rnd : ByteArray, x = some rnd := by
  unfold Fmt.rndOf at hr
  cases hS : S.rand with
  | inFile =>
    rw [hS] at hr
    dsimp only at hr
    cases hsl : Fmt.slice b i 32 with
    | none =>
      rw [hsl] at hr
      cases hr
    | some y =>
      rw [hsl] at hr
      exact ⟨y, ((Prod.mk.inj (Option.some.inj hr)).1).symm⟩
  | given y =>
    rw [hS] at hr
    exact ⟨y, ((Prod.mk.inj (Option.some.inj hr)).1).symm⟩
  | none =>
    rw [hS] at hn
    exact absurd hn (by decide)

end OnBytes.Tie

#print axioms OnBytes.Tie.read_stages
#print axioms OnBytes.Tie.rnd_some
