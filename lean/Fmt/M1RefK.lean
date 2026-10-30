-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1RefK.lean: the decision of the first toy (a product test) at tiny sizes, as theorems of Lean's
kernel: the reference's honest run is accepted; four altered runs are refused.

Statements (namespace `Fmt.M1.Ref.Spec`) and proofs, each by the kernel's own evaluation of the
closed term (decide +kernel). The reference is the program in Python of which the head of
Fmt/M1Ref.lean tells; its run is the data of that file.
Fmt/M1Ref.lean holds the same as guards: tests by Lean's evaluator, which leave no declaration. Here
the verdicts are theorems: the kernel itself reduces `Fmt.M1.decM` at the sizes `refPar` (K = 3; 21
rounds) on the view `refView`, a literal, and on four views made from its parts (`bumpSent`,
`bumpCol`: Fmt/M1Ref.lean).

Main names:
  `Spec.ref_ok`: decM refPar refView = true.
  `Spec.ref_answer`: the first sending's answer made one larger: false.
  `Spec.ref_sigma`: the second fold's first element made one larger: false.
  `Spec.ref_clear`: the last element in the clear made one larger: false.
  `Spec.ref_column`: the first word of the first opened column made one larger: false.

Notation: K: a natural number, a field of `Par`; the rows a, b, c have 2^K entries (the head of
Fmt/M1Types.lean); `bumpSent i j`: element j of what round i sends, made one larger; `bumpCol i j`:
word j of opened column number i, made one larger (both: Fmt/M1Ref.lean).

Limits:
  what these theorems say: the value of one function at five closed arguments.
  `decM` tests their (D4) and (D5) (Fmt/M1All.lean, the head), that is, the last block's linear
    check and its checks at the drawn positions. It tests them on the claim that all blocks before
    have moved. It does not test form, work, openings: no hash stands in it.
  What these theorems do not say:
    anything on soundness;
    that `decM` is what the programs (the C++ implementation that comes with this Lean code) decide;
    that the view belongs to a file.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1Ref

namespace Fmt.M1.Ref

def Spec.ref_ok : Prop := decM refPar refView = true
def Spec.ref_answer : Prop := decM refPar (bumpSent 1 0) = false
def Spec.ref_sigma : Prop := decM refPar (bumpSent 15 0) = false
def Spec.ref_clear : Prop := decM refPar (bumpSent 20 ((rd 20).sent.length - 1)) = false
def Spec.ref_column : Prop := decM refPar (bumpCol 0 0) = false

theorem ref_ok : Spec.ref_ok := by unfold Spec.ref_ok; decide +kernel
theorem ref_answer : Spec.ref_answer := by unfold Spec.ref_answer; decide +kernel
theorem ref_sigma : Spec.ref_sigma := by unfold Spec.ref_sigma; decide +kernel
theorem ref_clear : Spec.ref_clear := by unfold Spec.ref_clear; decide +kernel
theorem ref_column : Spec.ref_column := by unfold Spec.ref_column; decide +kernel

end Fmt.M1.Ref
