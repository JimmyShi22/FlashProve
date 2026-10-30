-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionConfigRefused.lean: the function config of
OnBytes/Model/AttentionConfig.lean refuses altered inputs.

The tests run when this file is compiled. The program does not import this file.

The small configuration, called the example, is spelled out in
OnBytes/Model/TestAttentionConfig.lean and OnBytes/Model/TestAttentionConfigWhole.lean. The second
of these also holds the functions that run config on it. On the unchanged example config goes
through (a guard of TestAttentionConfigWhole.lean). Here one number of the parameter file or of the
layers' layout is changed at a time. No file of the repository is read; the examples under
prover/examples may have other numbers.

What is tested: eight altered inputs are refused. For seven of them the expected name is the one
that verifier/src/cp_verify.cpp gives the same test, by a reading of that source. Six of the eight
change the layers' layout after it is made: they imitate a fault of the program, not a wrong file.
One of the six, the layout without a group, has no counterpart at this place of the C++ source:
there shape-L is the name of a test on the line L, in the function layout. These are the refusals
that need a plan, or the layers' own layout. What config does before any plan, the reading of the
call lines and two tests on the parameter file's numbers, is tested in
OnBytes/Model/TestAttentionConfig.lean.
-/
import OnBytes.Model.TestAttentionConfigWhole

namespace OnBytes.Attention.TestConfig

-- refused after the first plan
#guard refusedAs (wholeOf (withNumbers { exampleScan.h with iotaA0 := 51 })) "policy-iotaA"

-- the layers' layout says something else of qa than the attention sub-proof's plan
#guard refusedAs (wholeWith fun y => { y with filled := y.filled.setIfInBounds 3 0 })
  "internal-qa-layout"
#guard refusedAs (wholeWith fun y => { y with feat := y.feat.setIfInBounds 3 0 })
  "internal-qa-layout"
#guard refusedAs (wholeWith fun y => { y with ten := y.ten.reverse }) "plan-tensor-layout"
#guard refusedAs (wholeWith fun y => { y with dq := y.dq + 1 }) "plan-tensor-layout"
#guard refusedAs (wholeWith fun y => { y with S2 := 3 }) "plan-tensor-layout"

-- no group of layers
#guard refusedAs (wholeWith fun y => { y with NGr := 0 }) "shape-L"

-- refused after all plans: the last word of the table's digest is changed
#guard refusedAs (wholeOf { exampleScan with tblPol := exampleScan.tblPol.setIfInBounds 31 0 })
  "table-digest-exp"

end OnBytes.Attention.TestConfig
