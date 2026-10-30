-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/EntersRequestWords.lean

Nothing on hiding. No property of the protocol is claimed.
One small law on the reply file's first word, from modules outside the executable model's folders
(Johnson/HonestTrace/Run, Johnson/HonestTrace/LookAgree): where the two files of an instance ξ are read as x
(ProofFile.instOf ξ = some x), the number that the lookups read off the reply file (ProofFile.Honest.K3.askedTok ξ) is the
number of x's reply. By ProofFile.instOf_bytes (Johnson/Desc/ProofFile/InstOf.lean) and Meaning.asked_word
(Johnson/Meaning/ReqBytes.lean).
The executable model's folders are what nothing on completeness's road may import: hence this law.

Limits. One law; that ProofFile.instOf returns at ξ is its premise. The reference sizes ppref alone.
-/
import Johnson.Desc.ProofFile.InstOf
import Johnson.Desc.ProofFile.Honest.K3.WitReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Enters

open Inst.Model (ppref Instance)
open ProofFile.Honest.K3 (askedTok)

/-- Where the two files are read as x, the first word of the reply file is the number of x's reply. -/
theorem askedTokenOfInstance {ξ : ProofFile.Inst} {x : Instance ppref} (read : ProofFile.instOf ξ = some x) :
    askedTok ξ = x.y.val := by
  obtain ⟨-, e2, w1, w2⟩ := ProofFile.instOf_bytes read
  show ((OnBytes.Model.Verify.words32 ξ.y).getD 0 0).toNat = x.y.val
  rw [← e2]
  exact Meaning.asked_word ⟨x, w1, w2⟩

end HonestTraceRun.Enters

#print axioms HonestTraceRun.Enters.askedTokenOfInstance
