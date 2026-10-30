-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Eq.lean: EQUALITY OF TWO RECORDS OF A CHAIN CAN BE DECIDED BY CODE. Instances
alone.
The eight innermost instances stand in Johnson/Desc/K13/Law/Bools.lean.

Why. A test with code on public records that says "this record is the start's of what was handed",
or "the message at this number is that message's copy", compares whole records. The library's
records of a statement and of a book of trees (OnBytes/Iop/Ground.lean, OnBytes/Iop/Tensor.lean) are
plain data: numbers, field elements, lists and arrays of such; they derive no test of equality
there. Johnson/Desc/K13/Law/Bools.lean derives it for Tensor, Term, Single, Coeffs, Run, Form,
MainForm and Row. Here Lean derives it for what stands over these: Oracle, Group, Statement, Tree,
TreeBook; then for the last chain's own records (Johnson/Desc/Third/State.lean): SharedOut, Border,
Loc₃, S₃.

Limits. Instances that Lean makes; no statement. They are global. WHOEVER NEEDS ONE OF THEM IMPORTS
THIS FILE: Lean names such an instance after the type and the root of the module that derives it,
and two modules that declare one such name do not load in one environment:
"environment already contains". The cost of a
comparison is linear in the two records.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Third.State
import Johnson.Desc.K13.Law.Bools

set_option autoImplicit false
set_option relaxedAutoImplicit false

deriving instance DecidableEq for OnBytes.Oracle
deriving instance DecidableEq for OnBytes.Group
deriving instance DecidableEq for OnBytes.Statement
deriving instance DecidableEq for OnBytes.Tree
deriving instance DecidableEq for OnBytes.TreeBook
deriving instance DecidableEq for VerifiableInference.Desc.Third.SharedOut
deriving instance DecidableEq for VerifiableInference.Desc.Third.Border
deriving instance DecidableEq for VerifiableInference.Desc.Third.Loc₃
deriving instance DecidableEq for VerifiableInference.Desc.Third.S₃
