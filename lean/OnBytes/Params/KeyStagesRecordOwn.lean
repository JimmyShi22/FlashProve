-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyStagesRecordOwn.lean: the stages of the own test of a key of full size, at the
lines typed for the full-size parameter file: an import line alone. The definitions and theorems
stand in OnBytes/Params/KeyRec/Own.lean and the files that it imports: cut so that no module
takes more than a fraction of a GiB of memory of its own.

Limits. Nothing is stated here. What those statements leave unsaid stands in the head
of OnBytes/Params/KeyRec/Own.lean.

-/
import OnBytes.Params.KeyRec.Own
