-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/TestNames.lean: a test that every name and place that the program can print, those of
the checks on a model's files among them, is short and plain. The tests try these lists and prove
nothing. The program does not import this file.
-/
import OnBytes.Shell.Checks

namespace OnBytes.ShellTest

open OnBytes.Shell

-- every name is at most 80 characters: letters, digits and eight signs
#guard modelChecks.lists.names.all fun s => decide (s.length ≤ 80) && s.toList.all fun c =>
  c.isAlphanum || "-.:_@ ()".toList.contains c
-- so is every place of a round
#guard modelChecks.lists.places.all fun s => decide (s.length ≤ 80) && s.toList.all fun c =>
  c.isAlphanum || "-.:_@ ()".toList.contains c
#guard !modelChecks.lists.names.contains "unlisted-check" && !modelChecks.lists.names.contains ""

end OnBytes.ShellTest
