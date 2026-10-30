-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrontJoinAtClosing.lean: the code switch's law: frontB2_of_tops
(FrontJoin.lean) WITH ITS THREE PREMISES ON THE STATEMENT RIGHT BEHIND THE LAST CLOSING TAKEN BACK
TO THE STATEMENT IN FRONT OF THAT CLOSING, which is a border state's: so that a theorem along the
fold can pay them. A law file; no running text imports it.

Why. The closing's law on its output (CarriedOk, CarriedRows.lean) speaks of the statement S' right
behind the closing, which no border of the chain shows: the link's end still works on the state. But
at a yes of the frame's closing S' is the statement S in front with the group's test begun and the
fresh mask's message marked as spent, and nothing else (closeFrame_st,
Johnson/Desc/First/Close/Law/StBehind.lean): the codes and every message's shape
are S's (behind_codes, behind_shape). And S is a border state's: by tail_frame
(Johnson/IMR/TailFrame.lean) the closing of link l is called at the statement of the fold's return
at the cut 14 l + 12.

  closed_codes, closed_shape   at a yes of closeFrame: the codes and each message's shape behind are
                   those in front.
  frontB2_at_closing   frontB2_of_tops, with: hc: the frame's closing says yes from (f, S) to y;
                   er: the front's carried rows are y.1's; hf: f's shape is sh; s0: S's codes are
                   cs; e0: at olds the shapes in S are the listed ones.
Limits. Nothing is paid here. The full size alone. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.FrontJoin
import Johnson.Desc.First.Close.Law.StBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)
open VerifiableInference.Desc.First.Close (closeFrame closeFrame_st closeFrame_carried behind_codes
  behind_shape)
open Johnson.G (fxAt)

section
variable {owed : Option ℕ} {f : ReqFrame} {S : Statement} {es : List Fmt.Entry}
  {rs : List Fmt.RoundView} {y : ReqFrame × Statement}

theorem closed_codes (hc : closeFrame owed f S es rs = .ok y) : y.2.codes = S.codes := by
  obtain ⟨G, id, -, -, e⟩ := closeFrame_st hc
  rw [e]
  exact behind_codes S f.group G id

theorem closed_shape (hc : closeFrame owed f S es rs = .ok y) (o : ℕ) :
    (y.2.oracles[o]?).map (·.shape) = (S.oracles[o]?).map (·.shape) := by
  obtain ⟨G, id, -, -, e⟩ := closeFrame_st hc
  rw [e]
  exact behind_shape S f.group G id o

/-- **The test on the front accepts: the closing's side said at the statement in front of it.** -/
theorem frontB2_at_closing {fx : _root_.Tw.K2.Front} {i n0 : ℕ} {olds : List ℕ} {r : SwRow}
    {cs : Codes} {sh : Params.ReqShape}
    (hr : tableFullLit[i]? = some r) (hn0 : n0Full[i + 1]? = some n0)
    (hol : oldsFull[i]? = some olds)
    (a1 : fx.st.codes = cs) (a2 : fx.T = ((reqGroups sh).getD (i + 1) {}).target)
    (a3 : fx.f.rows.code = sh.code) (a4 : fx.f.rows.maskCode = sh.maskCode)
    (a5 : fx.f.rows.masks = 2)
    (b : (switchKept fx.f.rows).toList = olds)
    (c1 : fx.f.group = i + 1) (c2 : ∃ G, fx.st.groups[fx.f.group]? = some G ∧ G.rows = #[])
    (d : fx.st.oracles.size = n0)
    (hc : closeFrame owed f S es rs = .ok y) (er : fx.f.rows = y.1.rows) (hf : f.shape = sh)
    (s0 : S.codes = cs) (w1 : cs = csW) (w2 : sh = shW)
    (e : ∀ o, o < fx.st.oracles.size → (fx.st.oracles[o]?).map (·.shape) = MW[o]?)
    (e0 : ∀ o ∈ olds, (S.oracles[o]?).map (·.shape) = MW[o]?) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧ frontB2 (fxAt r) W₀ (i + 1) 0 n0 olds fx = true := by
  obtain ⟨Gf, G, -, -, C⟩ := closeFrame_carried hc
  rw [← er] at C
  exact frontB2_of_tops hr hn0 hol a1 a2 a3 a4 a5 b c1 c2 d C (congrArg (·.code) hf)
    (congrArg (·.maskCode) hf) ((closed_codes hc).trans s0) w1 w2 e
    fun o ho => (closed_shape hc o).trans (e0 o ho)

end

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.frontB2_at_closing
