-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WtK6Mono.lean: TWO FACTS ON THE SENTENCE "weights" AS THE CLOSED
CONSTANT LAYS IT (wtK6, Johnson/Desc/Kinds/Law/WtK6.lean; At.wt, Johnson/P5J/LettersAt4.lean):
what the laws on K1's later sendings ask of the letter wt (hmono · hidle:
Johnson/Desc/K1/Law/WtAt24.lean | WtBackAtReads.lean). Four theorems, each by the make of wtK6 ("m
= 24 → InRange w.cells → WeightAt Wp a.2 ‹of w› ‹of w›").

  wtK6_idle · wtK6_mono    at every value of wtK6's parameters.
  hidle_atAll · hmono_atAll  at the closed constant's h.𝔇.wt, Wp := At.X Zp.
Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.WtK6
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable
open OnBytes.Params (ReqLayout)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs Wit Chain)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT)
open OnBytes.Maker (WholeD)

variable {rows cols : Nat} {P Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem)
  (N : Numbers) (Wp : OnBytes.Model.Verify.Public) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ) (n rb : ℕ)

/-- Off segment 24 the sentence says nothing. -/
theorem wtK6_idle (l : ℕ) (hl : l ≠ 24) (a : P × S) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) : wtK6 cs arr msR N Wp lay6 num n rb l a y w :=
  fun e => absurd e hl

/-- At segment 24 it reads the state through WeightAt alone, positively, and no oracle's string. -/
theorem wtK6_mono (a a' : P × S) (y y' : Strs) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hm : ∀ cc mm, WeightAt Wp a'.2 cc mm → WeightAt Wp a.2 cc mm)
    (h : wtK6 cs arr msR N Wp lay6 num n rb 24 a' y' w) :
    wtK6 cs arr msR N Wp lay6 num n rb 24 a y w :=
  fun e hr => hm _ _ (h e hr)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem hidle_atAll (h : P5J.AtMgA o Z D r Zp Np cF x) :
    ∀ l, l ≠ 24 → ∀ a y w, h.𝔇.wt l a y w :=
  fun l hl a y w => wtK6_idle _ _ _ _ _ _ _ _ _ l hl a y w

theorem hmono_atAll (h : P5J.AtMgA o Z D r Zp Np cF x) :
    ∀ (a a' : ProofFile.InstPub × S) y y' w,
      (∀ cc mm, WeightAt (P5J.At.X Zp) a'.2 cc mm → WeightAt (P5J.At.X Zp) a.2 cc mm) →
      h.𝔇.wt 24 a' y' w → h.𝔇.wt 24 a y w :=
  fun a a' y y' w hm hw => wtK6_mono _ _ _ _ _ _ _ _ _ a a' y y' w hm hw

end VerifiableInference.Desc.Kinds.Head.Law.AtTable
