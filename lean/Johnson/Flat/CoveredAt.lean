-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/CoveredAt.lean: the verifier program's two readers of a request return at the words of
every instance whose range of covered positions is not empty.



`stFromCall_wordsOf` (Johnson/Flat/InstanceLaws.lean) has the first reader, `Head.stFromCall`. Here
the second, `Head.coveredOf`, at what the first returns.

Main theorems:
  `tokens_wordsOf`     the first P.T words of an instance's request file are its tokens.
  `coveredOf_wordsOf`  `Head.coveredOf` returns at the words of an instance x with x.r < x.e.
  `covered_wordsOf`    both readers in a row, at x.r < x.e and (x.e < P.T → x.y = 0).
Asked: P.T < 2 ^ 32 and P.V ≤ 2 ^ 32: a number of the instance is a word of 32 bits.
Limits: nothing on what is returned beyond `coveredOf_lawful` (OnBytes/Flat/CoveredJoin.lean).

Terms: lean/GLOSSARY.md.
-/
import Johnson.Flat.InstanceLaws
import OnBytes.Flat.CoveredJoin

set_option autoImplicit false

namespace OnBytes.Flat

open Inst.Model

/-- The first P.T words of the request file are the tokens. -/
theorem tokens_wordsOf {P : Params} (x : Instance' P) :
    (requestWordsOf x).extract 0 P.T =
      Array.ofFn fun t : Fin P.T => UInt32.ofNat (x.prompt t).val := by
  unfold requestWordsOf
  simp

/-- **`Head.coveredOf` returns at the words of an instance.** -/
theorem coveredOf_wordsOf {P : Params} (x : Instance' P) (hT : P.T < 2 ^ 32) (hV : P.V ≤ 2 ^ 32)
    (hre : x.r < x.e) :
    ∃ cov, Model.Head.coveredOf { req := requestWordsOf x, r := x.r, e := x.e, y := x.y.val } P.T
      P.V = .ok cov := by
  have hrT : x.r ≤ P.T := Nat.lt_succ_iff.1 x.rF.isLt
  have heT : x.e ≤ P.T := Nat.lt_succ_iff.1 x.eF.isLt
  have hr : (UInt32.ofNat x.r).toNat = x.r := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have he : (UInt32.ofNat x.e).toNat = x.e := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  refine coveredOf_ok _ P.T P.V x.y.isLt (size_requestWordsOf x) ?_ ?_ ?_
  · intro v hv
    show v < P.V
    have hv' : v ∈ ((requestWordsOf x).extract 0 P.T).map (·.toNat) := hv
    rw [tokens_wordsOf] at hv'
    obtain ⟨w, hw, rfl⟩ := Array.mem_map.1 hv'
    obtain ⟨t, rfl⟩ := Array.mem_ofFn.1 hw
    rw [UInt32.toNat_ofNat']
    have := (x.prompt t).isLt
    rw [Nat.mod_eq_of_lt (by omega)]
    exact this
  · show ((requestWordsOf x).getD P.T 0).toNat < ((requestWordsOf x).getD (P.T + 1) 0).toNat
    rw [requestWordsOf_r, requestWordsOf_e, hr, he]
    exact hre
  · show ((requestWordsOf x).getD (P.T + 1) 0).toNat ≤ P.T
    rw [requestWordsOf_e, he]
    exact heT

/-- **Both readers in a row.** -/
theorem covered_wordsOf {P : Params} (x : Instance' P) (hT : P.T < 2 ^ 32) (hV : P.V ≤ 2 ^ 32)
    (hre : x.r < x.e) (hy : x.e < P.T → x.y.val = 0) :
    ∃ so cov, Model.Head.stFromCall (requestWordsOf x) (replyWordsOf x) P.T = .ok so ∧
      Model.Head.coveredOf so P.T P.V = .ok cov := by
  obtain ⟨cov, hc⟩ := coveredOf_wordsOf x hT hV hre
  exact ⟨_, cov, stFromCall_wordsOf x hT hV hre hy, hc⟩

end OnBytes.Flat
