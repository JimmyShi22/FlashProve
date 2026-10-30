-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/BoolsOwn.lean: THE PUBLIC PREMISES OF THE OWN MASK's ARM (`AtPlaceOwn`,
OwnArm.lean), AND THE PROMISE `FirstOpensOwn`, AS TESTS WITH CODE, EACH TIED TO ITS PROPOSITION.
Statements and proofs; the tests themselves: BoolsTests.lean. Beside Bools.lean, whose laws are
called where the two arms ask the same.

  `treesOwnOk π` ⇒ `AtPlaceOwn.trees` (`treesOwn_of_ok`): the first fold's first written round sends
    a tree; else as `treesOk`.
  `firstOpensOwnB π num no base t` ⇒ `FirstOpensOwn π num no base t` (`firstOpensOwn_of_B`).
  `PlaceOwnB`, `atPlaceOwn_of`: all of `AtPlaceOwn` from the tests' yes, `CodesAt`, `numOwn`,
    `bears`.
Limits: evaluated is not proved; nothing has been evaluated. No soundness is claimed.

-/
import Johnson.Desc.K12.Coin.Bools
import Johnson.Desc.K12.Coin.OwnArm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt spendOk Letters kk)
open H2K.First (gpOf Plain)

theorem treesOwn_of_walk (X : Letters) : ∀ (rest : List Fmt.M1.Stage) (a : Fmt.M1.Stage)
    (l : List WR) (c : OnBytes.Slice.Chain (sgOf a)), chainFrom X rest a l = some c →
    treesOwnWalk rest a l = true → TreesOwn c
  | [], _, _, _, _, h => by cases h
  | b :: rest, a, l, c, hc, h => by
    unfold chainFrom at hc
    unfold treesOwnWalk at h
    split at hc
    · rename_i dE dT l'
      dsimp only at h
      split at hc
      · split at hc
        · rename_i dS dC l'' hd
          rw [hd] at h
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := h
          cases hn : chainFrom X rest b l'' with
          | none => rw [hn] at hc; cases hc
          | some next =>
            rw [hn] at hc
            have hc' := Option.some.inj hc
            subst hc'
            have ih := trees_of_walk X rest b l'' next hn h5
            split
            · exact ⟨h1, isSome_false h2, h3, isSome_false h4, ih⟩
            · exact ⟨h1, isSome_false h2, h3, isSome_false h4, ih⟩
        · cases hc
      · cases hc
    · cases hc

theorem treesOwn_of_ok (X : Letters) (π : P12) (h : treesOwnOk π = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : OnBytes.Slice.Chain (sgOf a))
    (hs : π.nums.stages = a :: rest) (hw : writtenOf π.nums = some (w0 :: l))
    (hc : chainFrom X rest a l = some c) : TreesOwn c := by
  unfold treesOwnOk at h
  rw [hs, hw] at h
  exact treesOwn_of_walk X rest a l c hc h

theorem firstOpensOwn_of_B (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (base : ℕ) (t : T12)
    (h : firstOpensOwnB π num no base t = true) : FirstOpensOwn π num no base t := by
  intro a rest G0 Ly D hf
  obtain ⟨f1, f2, f3, f4⟩ := hf
  have f5 : gpOf π { t with st := begun t.st t.g G0, pass := .nothing } a Ly = some D :=
    f4 default
  unfold firstOpensOwnB at h
  rw [f1, f2, f3] at h
  dsimp only at h
  rw [f5] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1, fun i => h.1.2 _ (List.get_mem _ i), h.2⟩

theorem atPlaceOwn_of (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (L mC mS mW : Sg → ℕ → ℕ)
    (rad : Sg → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt))
    (hB : PlaceOwnB F π num base dB dt = true) (hcodes : CodesAt L mC mS mW rad π.nums.stages)
    (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (hbears : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
      Bears c.errL εt) :
    AtPlaceOwn F π num L mC mS mW rad base dB dt εt := by
  simp only [PlaceOwnB, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩ := hB
  exact ⟨b1, b2, b3, b4, b5, hcodes, like_of_ok π _ b6, b7, b8, wants_of_B _ _ _ _ _ b9, hnum,
    fun a rest w0 l c hs hw hc => treesOwn_of_ok _ π b10 a rest w0 l c hs hw hc, hbears⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.treesOwn_of_ok
#print axioms VerifiableInference.Desc.K12.Coin.firstOpensOwn_of_B
#print axioms VerifiableInference.Desc.K12.Coin.atPlaceOwn_of
