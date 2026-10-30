-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyStagesRecordOmega.lean: the stages of the test on Omega's group of a key of full
size, at the lines typed for the full-size parameter file: an import line alone. The definitions and
theorems stand in OnBytes/Params/KeyRec/Omega.lean and the
files that it imports: cut so that no module takes more than a fraction of a GiB of memory of its
own.

Limits. Nothing is stated here. What the imported statements leave unsaid stands in the head
of OnBytes/Params/KeyRec/Omega.lean.

-/
import OnBytes.Params.KeyRec.Omega
