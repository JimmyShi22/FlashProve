-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/IdxReadsPaid.lean: the code switch (the kind K2): THE NAMED PREMISE
`IdxReads cs` OF `words_at_new` (Johnson/Top/H0/Tw/K2C/WordsAtNew.lean) IS A THEOREM, for all
codes. By `idxReads` (Johnson/Top/H0/K2Caller/WordsNames.lean). `words_at_new_paid`: `words_at_new`
without that premise.
Limits. Arithmetic on indices alone. The three other premises of `words_at_new` stay. Nothing on
soundness. On hiding nothing.

-/
import Johnson.Top.H0.Tw.K2C.WordsAtNew
import Johnson.Top.H0.K2Caller.WordsNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Slice Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT msgsOf seatBy noFirst wordsFirst)

/-- **The arithmetic between a typed coordinate and the index in its table holds.** -/
theorem idxReads (cs : Codes) : IdxReads cs := K2Caller.idxReads cs

/-- `words_at_new` with the arithmetic paid. -/
theorem words_at_new_paid {Cells Tok : Type} (cs : Codes) (l : List (OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT) (st : Statement)
    (book : TreeBook) (n0 : ℕ) (hc : st.codes = cs)
    (hseat : ∀ i : Fin l.length, seatBy noFirst book (n0 + i.val) = some (seat i))
    (hshape : ∀ i : Fin l.length, (st.oracles[n0 + i.val]?).map (·.shape) = some (l.get i).1)
    (n : (sigOf cs l).Ent) :
    (sigOf cs l).ents (msgsOf cs l seat arr w) n =
      wordsFirst arr st book w (n0 + (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 :=
  words_at_new cs l seat arr w st book n0 hc hseat hshape (idxReads cs) n

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.idxReads
#print axioms VerifiableInference.Desc.First.K2.words_at_new_paid
