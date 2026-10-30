-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AttentionScript.lean: one definition of type Prop: what a member of
the row of the attention segments' own rounds (kind K5: the label of that sub-protocol in the
description) shows at coins that are handed to it, written with the library's own functions of the
trace, the challenges and those coins. This file proves nothing.

At a masked sumcheck that is sumMsgs (Honest/SumLaw/SumShown.lean): the first message holds each lead
value plus its entry, and one scalar that is a sum over later entries; a variable's message is a round
of the masking polynomial, which the entries make, plus the first challenge times a round of the
summand; the message at Y reads both stretches of coins; the last message holds each end value plus
the last challenge times its entry. At a round of scalars it is each value plus its entry. At a quiet
part nothing is sent. No property is claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.RowIs
import Johnson.Desc.ProofFile.Honest.SumLaw.SumShown
import Johnson.Desc.ProofFile.Honest.Small.Scalars

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open H2K5.Honest (PartShape K5In)
open ProofFile.Honest.SumLaw (sumMsgs uOf mOf gotsOf elemOf SumCoins frontOf)

variable {S Cl W₀ Rc Xi Tr X : Type}

/-- The masked sumcheck's job of part number j of the row. -/
def jobAt (Z : Seat5) (j : Nat) (k : VerifiableInference.Desc.Part.MaskedSum.Call) : SumJob K5In Unit :=
  jobOf k (fun w fr => (jobs Z.P).alone j w (chalOf Z fr.heard))
    fun w fr => (jobs Z.P).sum j w (chalOf Z fr.heard)

/-- **What a member shows at the coins that it is handed, at challenges that fit.** The member is
written from the seat, as member_at (Honest/K5/Law/RowIs.lean) says each member of the side is. The list
dv holds the variables' challenges, Y's last, so the factor on the end entries is endFactor's. -/
def ShowsItsScript (cells : Tr → Cells) (Z : Seat5) (σ : Side S Cl (Local W₀ Rc Xi Tr)
    (Local W₀ Rc Xi Tr) X Xi) (j : Nat) : PartShape → Prop
  | .sum k =>
    ∀ (c : SumCoins (nameOf Z.place j "sum") (nameOf Z.place j "ends") (jobAt Z j k))
      (m : Mid (Local W₀ Rc Xi Tr) X) ds asks,
      drawsFit ((stretchOf σ.block Z j).map (·.1)) ds = true →
      ∃ d0 dv dl, ds = d0 :: (dv ++ dl) ∧ dv.length = k.vs.length + 1 ∧
        dl.length = (if k.ends.isSome then 1 else 0) ∧
        σ.shows .own ⟨j, stretchOf σ.block Z j, partOf5 cells Z j (.sum k), simOf5 Z j (.sum k)⟩ c m
            ds asks =
          some ((sumMsgs (jobAt Z j k) (inOf Z.P.S Z.link (cells m.st.input.trace))
            ⟨m.st.heard, (), m.shown⟩ (elemOf d0) (dv.map elemOf)
            ((drawnE (d0 :: dv)).getLastD OnBytes.zeroE) (uOf c) (mOf c)).map
              fun l => (⟨gotsOf l, []⟩ : Shown))
  | .one 0 => True
  | .one (n + 1) =>
    ∀ (c : Cs ⟨0, 0⟩) (sp : CsAll [(nameOf Z.place j "scalars", (⟨0, n + 1⟩ : Due))])
      (m : Mid (Local W₀ Rc Xi Tr) X) ds asks,
      drawsFit ((stretchOf σ.block Z j).map (·.1)) ds = true →
      σ.shows .own ⟨j, stretchOf σ.block Z j, partOf5 cells Z j (.one (n + 1)),
          simOf5 Z j (.one (n + 1))⟩ (c, sp, ()) m ds asks =
        Small.scalarsAt (Small.valsAt (n + 1) ((jobs Z.P).alone j
            (inOf Z.P.S Z.link (cells m.st.input.trace)) (chalOf Z m.st.heard)) + sp.1.e)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.jobAt
#print axioms ProofFile.Honest.K5.ShowsItsScript
