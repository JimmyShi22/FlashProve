-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/JudgeLink.lean: the library's compiled Link verifier as a judge, at the library's own
reading; and the checker on bytes of a chain with stored tables as one part of a join.

OnBytes/Slice/OneWorldJ.lean makes the step to one oracle for any compiled verifier that is given as
a `Judge` with `JudgeAt`. OnBytes/Slice/PartO.lean joins three checkers;
OnBytes/Slice/JoinThree.lean has the form in which a checker comes with the library's compiler
behind it (`Part`). This file fills the form for the first time: with the library's Link verifier,
and with the checker `chainChk` of OnBytes/Slice/OneWorldChain.lean.

Main definitions.
 `judgeL W hW sMT sFS Lg`   the compiled Link verifier with the strict format, the library's bound
                  on its queries, the two roots, the library's own reading (`Reading.wide`: every
                  symbol that stands at its leaf is kept, whatever the salt), and the language Lg of
                  the pair of strings. Nothing more is owed of a checker's output (`ok` is true).
 `partChain`      the part made of a description S0 with its statement function and decision, an
                  implementation m, a language, an error, and `pre`, which reads off the maker's
                  output what stands before the chain.
Main theorems.
 `judgeAt_L`      `LinkAt W Lg e` gives `JudgeAt` of that judge.
 `partChain_ok`   `Part.OK` of that part, from what `one_world_chain` asks, with `OneBlock m` for
                  its two conditions on m.
 `partChain_bound`  its bound is `one_world_chain`'s.

The reading is the wide one alone: a judge for the Link that is general in the reading wants the
clause of a file of this project that is not in this library with a strict form and the library's
own Link as an
instance, which do not stand yet.

All of this stands over the compiler's types as they are today.

What is not claimed. What the heads of OnBytes/Slice/OneWorldChain.lean, JoinThree.lean and
PartO.lean do not claim. The description, the language and e are variables here.
That the other two parts of a join exist is not shown.

-/
import OnBytes.Slice.JoinThree
import OnBytes.Slice.OneWorldChain

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch Run Run.PQ MeasureTheory
open OnBytes.Tie (xdOf withinX)
open scoped ENNReal

section
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- **The library's compiled Link verifier as a judge**, at the library's own reading. Its language
holds for free of a list of other than two strings; the list of roots always has two. -/
def judgeL (W : QueryLayout lam L) (hW : W.OKG) (sMT sFS : ℕ)
    (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) : Judge W (LinkOut lam L) where
  run := fun o => vLS W sMT sFS o.1 o.2.1 o.2.2
  tV := tVQB W.Lk W.depthReq
  bound := fun o => detBound_vLS W sMT sFS o.1 o.2.1 o.2.2
  roots := fun o => [o.1, o.2.1]
  R := Reading.wide hW.B.ext
  Lang := fun _ ys => ∀ y₀ y₁, ys = [y₀, y₁] → Lg () (y₀, y₁)
  ok := fun _ => True

/-- **The compiler's conclusion on an accepted Link string is the judge's.** -/
theorem judgeAt_L (W : QueryLayout lam L) (hW : W.OKG) (sMT sFS : ℕ)
    (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞) (h : LinkAt W Lg εs) :
    JudgeAt W (judgeL W hW sMT sFS Lg) εs := by
  obtain ⟨Bad, hrare, hmono, hL, hst⟩ := h
  refine ⟨Bad, hrare, hmono, fun tr o hnb _ hrun y₀ y₁ hy => ?_, fun tr tr' cm hnb ha => ?_⟩
  · obtain ⟨π', hπ'⟩ := vL_of_vLS W hW hrun
    have h2 := hL tr o.1 o.2.1 π' hnb hπ'
    have e : [extEnc W tr o.1, extEnc W tr o.2.1] = [y₀, y₁] := hy
    obtain ⟨e0, e1⟩ := List.cons.inj e
    obtain ⟨e1', -⟩ := List.cons.inj e1
    rw [← e0, ← e1']
    exact h2
  · exact hst tr tr' cm hnb ha

end

section
variable {γ : Type} (S0 : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
  (dec : View → Bool)

/-- **The checker on bytes of a chain with stored tables, as one part of a join.** -/
noncomputable def partChain (hw : withinX S0 = true)
    (Lg : Unit → (twoExternalStrings ((xdOf S0 stm).L dec).wordLength ((xdOf S0 stm).L dec).Symbol).Str → Prop) (εs : ℝ≥0∞)
    (m : OracleCoding (spec 256 (WkAny (xdOf S0 stm) dec).K ((xdOf S0 stm).L dec)) 256)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) :
    Part 256 γ SgX where
  I := Unit
  X := Unit
  L := (xdOf S0 stm).L dec
  W := WkAny (xdOf S0 stm) dec
  Out := LinkOut 256 ((xdOf S0 stm).L dec)
  J := judgeL (WkAny (xdOf S0 stm) dec)
    (okgAny (xdOf S0 stm) dec (within_work S0 stm hw) (within_okx S0 stm hw))
    (256 + 8 * S0.base.plan.salt) 256 Lg
  e := εs
  m := m
  chk := chainChk S0 stm dec pre
  rts := fun x => match chainRoots pre x with
    | some r => [r.1, r.2]
    | none => []
  tR := Tie.CostX.fileNX S0 * 2
  a := 2
  u := Equiv.refl SgX

/-- **That part meets what the join asks of a part**, under what `one_world_chain` asks: the limits;
round-by-round soundness of the written link for the language, with error e; the statement holds the
roots; the checker's reader fits m; and in m a leaf's and a vertex's answer is one block, taken as
it is. -/
theorem partChain_ok (hw : withinX S0 = true)
    (Lg : Unit → (twoExternalStrings ((xdOf S0 stm).L dec).wordLength ((xdOf S0 stm).L dec).Symbol).Str → Prop) (εs : ℝ≥0∞)
    (hs : SoundLAny (xdOf S0 stm) dec Lg εs) (hroots : RootsIn S0 stm)
    (m : OracleCoding (spec 256 (WkAny (xdOf S0 stm) dec).K ((xdOf S0 stm).L dec)) 256)
    (hm : OneBlock m) (hfits : FitsRead S0 stm dec m)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) :
    (partChain S0 stm dec hw Lg εs m pre).OK where
  judge := judgeAt_L (WkAny (xdOf S0 stm) dec)
    (okgAny (xdOf S0 stm) dec (within_work S0 stm hw) (within_okx S0 stm hw))
    (256 + 8 * S0.base.plan.salt) 256 Lg εs
    (linkAt_any (within_work S0 stm hw) (within_okx S0 stm hw) Lg εs hs)
  one := hm
  noCoin := fun x => (chainChk_bound S0 stm dec pre x).1
  queries := fun x => (chainChk_bound S0 stm dec pre x).2
  few := fun x => by
    show (match chainRoots pre x with
      | some r => [r.1, r.2]
      | none => []).length ≤ 2
    cases chainRoots pre x <;> simp
  fit := fun g x o h => ⟨chainChk_fit S0 stm dec hroots m hfits pre g x o h, trivial⟩
  named := fun g x o h r hr => by
    show r ∈ (match chainRoots pre x with
      | some r => [r.1, r.2]
      | none => [])
    rw [chainChk_roots S0 stm dec pre g x o h]
    exact hr

/-- The part's bound is `one_world_chain`'s. -/
theorem partChain_bound (hw : withinX S0 = true)
    (Lg : Unit → (twoExternalStrings ((xdOf S0 stm).L dec).wordLength ((xdOf S0 stm).L dec).Symbol).Str → Prop) (εs : ℝ≥0∞)
    (m : OracleCoding (spec 256 (WkAny (xdOf S0 stm) dec).K ((xdOf S0 stm).L dec)) 256)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (t : ℕ) :
    (partChain S0 stm dec hw Lg εs m pre).bound t =
      ((t + 2 + Tie.CostX.fileNX S0 * 2 +
          tVQB (WkAny (xdOf S0 stm) dec).Lk (WkAny (xdOf S0 stm) dec).depthReq : ℕ) : ℝ≥0∞) * εs +
        2 * ((t + 2 + Tie.CostX.fileNX S0 * 2 +
          tVQB (WkAny (xdOf S0 stm) dec).Lk (WkAny (xdOf S0 stm) dec).depthReq + 1 : ℕ) : ℝ≥0∞) ^ 2
          / 2 ^ 256 :=
  rfl

end

end OnBytes.Slice
