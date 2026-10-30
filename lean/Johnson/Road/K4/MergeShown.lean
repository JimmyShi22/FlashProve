-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MergeShown.lean: THE VALUE THAT THE LEDGER SHOWS UNDER THE MERGE's SLOT IS THE WORD
THAT THE VALUES' ROUND SENT. Where the merge of the weight claims returns (`flatForkEnd`,
OnBytes/K/Kc/QuietLink.lean) from a ledger with arrays of the right sizes, its record's field `fvp`
is the one end value that `pscT` (OnBytes/Desc/First/P1/TailTape.lean) reads off the tape. So the
premise hfv of `k4_pending` (OwnPending.lean) and `tail_pendingF` (OwnAt.lean) follows where the
numbering of the one end value is 0 (`StgH.v` of `stgT` reads the word under that number). One
statement and its proof.

  `merge_shown`: `wo.fvp = (pscT 0 lay.lk (t.drop 1)).v.getD 0 zeroE`.

NO NEW ARGUMENT: `hear_ended` (Johnson/Top/H0/MergeLaw/Said.lean: the `hideRun`
equation and what the ledger shows), `hideRun_shown` (OnBytes/Desc/First/K4/ShownUnder.lean),
`shown_some` (OnBytes/Desc/First/P1/LevelKit.lean), and the tape's equation as in `merge_recAt`
(MergeRec.lean).

Limits. `Sized F` is a premise. One direction: from a return. Nothing on soundness.
-/
import Johnson.Road.K4.MergeRec
import OnBytes.Desc.First.K4.ShownUnder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork WsLay WsClaim WsForkOut)
open OnBytes.PscRun (Sized)
open OnBytes.Desc.First.K4 (hideRun_shown)
open OnBytes.Desc.First.P1 (pscT sentOf drop_length_add shown_some)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.MergeLaw (hear_ended hear_of_flat)

/-- **What the ledger shows under the merge's slot is the word that the values' round sent.** -/
theorem merge_shown {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (hF : Sized F) (h : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    wo.fvp = (pscT 0 lay.lk (t.drop 1)).v.getD 0 zeroE := by
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, hn, hq, et, hT, hE, hrm, hb, hs, hh, hsh, _⟩ :=
    hear_ended (hear_of_flat h)
  have d1 : t.drop 1 =
      ⟨some OnBytes.Model.RoundName.pscEpsilon.name, 0, r1, [mu], [wo.p.eps]⟩ ::
        (qs.map (MergeLaw.rd OnBytes.Model.RoundName.pscRound.name 0) ++
          ⟨some OnBytes.Model.RoundName.pscY.name, 1, rY, [c], [beta]⟩ ::
          ⟨some OnBytes.Model.RoundName.pscValues.name, 0, rV, [v], []⟩ :: u) := by
    rw [et]
    rfl
  have len : (qs.map (MergeLaw.rd OnBytes.Model.RoundName.pscRound.name 0)).length = qs.length :=
    List.length_map _
  have e := drop_length_add (qs.map (MergeLaw.rd OnBytes.Model.RoundName.pscRound.name 0))
    (⟨some OnBytes.Model.RoundName.pscY.name, 1, rY, [c], [beta]⟩ ::
      ⟨some OnBytes.Model.RoundName.pscValues.name, 0, rV, [v], []⟩ :: u : Tape) 1
  rw [len] at e
  have e6 : (pscT 0 lay.lk (t.drop 1)).v = [v] := by
    show sentOf ((t.drop 1).drop (lay.lk + 2)) = _
    rw [← hn, d1, show qs.length + 2 = (qs.length + 1) + 1 from rfl, List.drop_succ_cons, e]
    rfl
  have hF' : Sized ({ F with next := F.next + 1 + 2 * lay.lk + 2 } : Fork) := hF
  have q := hideRun_shown hF' hh (l := [v]) rfl (Fo.Later.refl G) 0 (by simp)
  rw [e6, (shown_some hsh).2.2, ← q]
  rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.merge_shown
