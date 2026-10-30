--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/SendKept.lean: the linear claim's two shared sendings, "send o_u" and "send
o_omega", as the shared chain's own sub-protocols (sendAt: Johnson/Desc/K14/Blocks.lean): where such
a sub-protocol accepts, what the verifier's state notes of the new messages; and, UNDER THE PREMISE
SendSays, that tables from which the OOD answers shown are computed meet all that the statement
claims behind it.

"All that a statement claims" is Holds (Johnson/Desc/Means/Holds.lean): every open row of every
group and every sample row of every oracle message holds of the words. InOrder
(Johnson/Desc/Means/Order.lean) is carried with it; the two together are AllMet
(Johnson/Desc/Means/Forth/AllMet.lean).

THE WORDS GROW AT A SENDING. In front of a sending the words are w; behind it they are w with the
sending's messages laid at the new numbers (held: Johnson/Prover/Send/Core.lean). Between two
sendings they stay. So along the shared chain the words are: w in front of "send o_u"; held w ...
from there to "send o_omega"; chainWords (Johnson/Desc/K14/Honest/SendMoves.lean) from there on.
AllMet.lean's head speaks of one family of words for a whole run. The two do not clash: a row in
order has no coefficient at a message that is not yet there, so what holds of w in front of a
sending holds of the grown words too; the lemmas on the kind's own sub-protocols are called at the
words of their stretch.

  SendSays        A NAMED PREMISE, NOT PROVED HERE: the law of the shared sending on what its rows
                  say, at parameters Q: where Q passes its test on the plan, the two rounds have the
                  stated form, the sending's decision accepts, the OOD answers shown are the sample
                  rows' own left sides at the held words, the statement in front was in order, and
                  all that it claimed held of w: all that the statement claims behind holds of the
                  held words. Proved in Johnson/Desc/K14/Honest/SendPaid.lean, by the shared
                  sending's send_holds_of_yes
  sendAt_kept     UNDER THAT PREMISE, and by send_order (Johnson/Desc/Key/Laid/SendLaid.lean: a
                  statement in order stays in order): the two together at the shared chain's
                  sub-protocol, for every note behind the sending that leaves the statement as it
                  is. Its half on Holds is the premise, carried to the sub-protocol's own decision
  sendU_kept, sendOmega_kept   at the two sub-protocols, under the same premise
  sendU_met, sendOmega_met   the same two with AllMet in front and behind
  ids_next        the numbers that a sending returns, with their bound (the first half is also
                  ids_get, Johnson/Desc/Sound/MembersCarried.lean)
  shapeAt_of_get  a sending's shape by number, from the notice
  oU_behind       behind "send o_u" the state notes for o_u the first new number, with the layout of
                  a vector in o_u's shape
  oOmega_behind   behind "send o_omega" the state notes for o_omega and o_sp the first two new
                  numbers, and keeps what it noted for o_u
  isFold_behindU, isFold_behindU_at   so behind "send o_u" the honest table of o_u, read as the
                  state notes it, holds the rows' fold; the second at the chain's own parameters

V IS FREE in the five theorems on what is kept: they hold of any rows whatever, as long as the
answers shown are computed from them: a sample row holds by how its answer is made. An honest
prover's data enter in isFold_behindU and in Johnson/Desc/K14/Honest/SendHeld.lean alone.

What is assumed, as premises. The sub-protocol accepts; its parameters pass K1's test on the plan,
and its two rounds have the stated form. SendSays. The OOD answers shown are the core's (answersAt:
Johnson/Desc/K14/Honest/SendMoves.lean) at the held words. The public test linFits on the codes and
the shape. At "send o_omega": the two messages' codes differ, so that o_sp is sent.
What is not claimed. That a sending accepts. SendSays itself. Nothing on the written columns, on how
the random values are distributed, on soundness or on hiding.

-/
import Johnson.Desc.K14.Honest.SendHeld
import Johnson.Desc.Key.Laid.Laid2
import Johnson.Desc.K14.Law.Run
import Johnson.Desc.K14.Law.AtBlocks
import Johnson.Desc.Own.LinAgree
import Johnson.Desc.Means.Forth.AllMet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words InOrder Holds)
open OnBytes.Slice (rdE)
open Johnson.Prover.Send (Rows held shapeAt)
open VerifiableInference.Desc.Key.LaidW (inFrontOf sendAt_yes send_laid send_order)
open Desc.K14.Law

/-! ## The sending keeps what the statement claims -/

/-- **A named premise**: the shared sending's law on what its rows say, at the parameters Q. -/
def SendSays (Q : VerifiableInference.Desc.K1.Par) : Prop :=
  ∀ (d x : DState (Array Nat)) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat) (w : Words Cb.Gl.E)
    (V : ℕ → Rows),
    VerifiableInference.Desc.K1.planOkOwn Q = true →
    VerifiableInference.Desc.roundsFit (VerifiableInference.Desc.K1.rounds Q) [r₁, r₂] = true →
    VerifiableInference.Desc.K1.decideSend Q none d [r₁, r₂] = .ok (ids, x) →
    r₂.vals = answersAt Q d.st r₁ w V → InOrder d.st → Holds rdE d.st w →
    Holds rdE x.st (held w d.st.oracles.size Q V)

/-- **Under the premise SendSays, the sending as the shared chain's sub-protocol keeps what the
statement claims**, for every note behind it that leaves the statement as it is, and for any rows V.
-/
theorem sendAt_kept (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hbehind : ∀ a ids a', behind a ids = some a' → a'.st = a.st) (d d' : St) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (w : Words Cb.Gl.E) (V : ℕ → Rows) (hS : SendSays Q)
    (hB : VerifiableInference.Desc.K1.planOkOwn Q = true)
    (hfit : VerifiableInference.Desc.roundsFit (VerifiableInference.Desc.K1.rounds Q) [r₁, r₂] =
      true)
    (h : (sendAt P n Q inFront groups behind).decide d [r₁, r₂] gs = .ok d')
    (ha : r₂.vals = answersAt Q d.st r₁ w V) (hI : InOrder d.st) (hH : Holds rdE d.st w) :
    InOrder d'.st ∧ Holds rdE d'.st (held w d.st.oracles.size Q V) := by
  obtain ⟨ids, x, hx, hb⟩ := sendAt_yes _ _ _ _ _ _ _ _ _ _ h
  have k := hS (inFrontOf d) x r₁ r₂ ids w V hB hfit hx ha hI hH
  have o := send_order Q none (inFrontOf d) x r₁ r₂ ids hB hfit hx hI
  rw [hbehind _ _ _ hb]
  exact ⟨o, k⟩

/-- Under the premise SendSays: "send o_u" keeps what the statement claims. -/
theorem sendU_kept (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (d d' : St) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (w : Words Cb.Gl.E) (V : ℕ → Rows) (hS : SendSays Q)
    (hB : VerifiableInference.Desc.K1.planOkOwn Q = true)
    (hfit : VerifiableInference.Desc.roundsFit (VerifiableInference.Desc.K1.rounds Q) [r₁, r₂] =
      true)
    (h : (sendAt P n Q inFront groups (behindU P.par)).decide d [r₁, r₂] gs = .ok d')
    (ha : r₂.vals = answersAt Q d.st r₁ w V) (hI : InOrder d.st) (hH : Holds rdE d.st w) :
    InOrder d'.st ∧ Holds rdE d'.st (held w d.st.oracles.size Q V) :=
  sendAt_kept P n Q inFront groups _ (fun a ids a' e => (behindU_inv P.par a a' ids e).1) d d' r₁ r₂
    gs w V hS hB hfit h ha hI hH

/-- Under the premise SendSays: "send o_omega" keeps what the statement claims. -/
theorem sendOmega_kept (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (d d' : St) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (w : Words Cb.Gl.E) (V : ℕ → Rows) (hS : SendSays Q)
    (hB : VerifiableInference.Desc.K1.planOkOwn Q = true)
    (hfit : VerifiableInference.Desc.roundsFit (VerifiableInference.Desc.K1.rounds Q) [r₁, r₂] =
      true)
    (h : (sendAt P n Q inFront groups (behindOmega P.par)).decide d [r₁, r₂] gs = .ok d')
    (ha : r₂.vals = answersAt Q d.st r₁ w V) (hI : InOrder d.st) (hH : Holds rdE d.st w) :
    InOrder d'.st ∧ Holds rdE d'.st (held w d.st.oracles.size Q V) :=
  sendAt_kept P n Q inFront groups _ (fun a ids a' e => (behindOmega_inv P.par a a' ids e).1) d d'
    r₁ r₂ gs w V hS hB hfit h ha hI hH

/-- Under the premise SendSays: "send o_u", with AllMet in front and behind. -/
theorem sendU_met (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (d d' : St) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (w : Words Cb.Gl.E) (V : ℕ → Rows) (hS : SendSays Q)
    (hB : VerifiableInference.Desc.K1.planOkOwn Q = true)
    (hfit : VerifiableInference.Desc.roundsFit (VerifiableInference.Desc.K1.rounds Q) [r₁, r₂] =
      true)
    (h : (sendAt P n Q inFront groups (behindU P.par)).decide d [r₁, r₂] gs = .ok d')
    (ha : r₂.vals = answersAt Q d.st r₁ w V) (hM : Means.AllMet rdE d.st w) :
    Means.AllMet rdE d'.st (held w d.st.oracles.size Q V) :=
  sendU_kept P n Q inFront groups d d' r₁ r₂ gs w V hS hB hfit h ha hM.1 hM.2

/-- Under the premise SendSays: "send o_omega", with AllMet in front and behind. -/
theorem sendOmega_met (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (d d' : St) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (w : Words Cb.Gl.E) (V : ℕ → Rows) (hS : SendSays Q)
    (hB : VerifiableInference.Desc.K1.planOkOwn Q = true)
    (hfit : VerifiableInference.Desc.roundsFit (VerifiableInference.Desc.K1.rounds Q) [r₁, r₂] =
      true)
    (h : (sendAt P n Q inFront groups (behindOmega P.par)).decide d [r₁, r₂] gs = .ok d')
    (ha : r₂.vals = answersAt Q d.st r₁ w V) (hM : Means.AllMet rdE d.st w) :
    Means.AllMet rdE d'.st (held w d.st.oracles.size Q V) :=
  sendOmega_kept P n Q inFront groups d d' r₁ r₂ gs w V hS hB hfit h ha hM.1 hM.2

/-! ## What the state notes behind a sending -/

/-- The numbers that a sending returns: the next ones. -/
theorem ids_next (n base i v : ℕ) (h : ((Array.range n).map (· + base))[i]? = some v) :
    v = base + i ∧ i < n := by
  obtain ⟨hi, hv⟩ := Array.getElem?_eq_some_iff.1 h
  simp only [Array.size_map, Array.size_range] at hi
  simp only [Array.getElem_map, Array.getElem_range] at hv
  exact ⟨by omega, hi⟩

/-- A sending's shape by number, from the notice. -/
theorem shapeAt_of_get (Q : VerifiableInference.Desc.K1.Par) (k : ℕ) (n : OracleNotice)
    (h : Q.sent[k]? = some n) : shapeAt Q k = n.shape ∧ k < Q.sent.size := by
  refine ⟨?_, (Array.getElem?_eq_some_iff.1 h).1⟩
  unfold shapeAt
  rw [Array.getD_eq_getD_getElem?, h, Option.getD_some]

/-- **Behind "send o_u"** the state notes for o_u the first new number, with the layout of a vector
in o_u's shape under the sending's codes. -/
theorem oU_behind (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (d d' : St) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups (behindU P.par)).decide d [r₁, r₂] gs = .ok d') :
    d'.loc.oU = ⟨d.st.oracles.size, vectorLay Q.codes P.par.S.fold.u P.par.S.fold.rowsHigh⟩ := by
  obtain ⟨ids, x, hx, hb⟩ := sendAt_yes _ _ _ _ _ _ _ _ _ _ h
  have L := send_laid Q none (inFrontOf d) x r₁ r₂ ids hx
  obtain ⟨_, o, mask, ho, hl⟩ := behindU_inv P.par _ d' ids hb
  rw [L.idsAre] at ho
  have e := (ids_next _ _ _ _ ho).1
  have hc : x.st.codes = Q.codes := L.codes.trans L.plan
  rw [hl]
  show (⟨o, vectorLay x.st.codes P.par.S.fold.u P.par.S.fold.rowsHigh⟩ : FoldedRow) = _
  rw [hc, e]
  rfl

/-- **Behind "send o_omega"**, where o_sp is sent, the state notes for o_omega and o_sp the first
two new numbers, and keeps what it noted for o_u. -/
theorem oOmega_behind (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (d d' : St) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hS : P.par.S.sharedSplitNeeded = true)
    (h : (sendAt P n Q inFront groups (behindOmega P.par)).decide d [r₁, r₂] gs = .ok d') :
    d'.loc.oOmega = d.st.oracles.size ∧ d'.loc.oSp = d.st.oracles.size + 1 ∧
      d'.loc.oU = d.loc.oU := by
  obtain ⟨ids, x, hx, hb⟩ := sendAt_yes _ _ _ _ _ _ _ _ _ _ h
  have L := send_laid Q none (inFrontOf d) x r₁ r₂ ids hx
  unfold behindOmega at hb
  rw [if_pos hS] at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hb
  obtain ⟨i1, h1, i0, h0, rfl⟩ := hb
  rw [L.idsAre] at h0 h1
  exact ⟨(ids_next _ _ _ _ h0).1, (ids_next _ _ _ _ h1).1, rfl⟩

/-- **Behind "send o_u" the honest table of o_u, read as the state notes it, holds the rows' fold.**
-/
theorem isFold_behindU (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (d d' : St) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (w₀ : Words Cb.Gl.E) (w : ℕ → Cb.Gl.E)
    (Rw : ℕ → ℕ → Cb.Gl.E) (cU cMask : MsgCoins)
    (h : (sendAt P n Q inFront groups (behindU P.par)).decide d [r₁, r₂] gs = .ok d')
    (hfit : VerifiableInference.Desc.Own.linFits Q.codes P.par.S = true) (nU : OracleNotice)
    (h0 : Q.sent[0]? = some nU) (hn : nU.shape = P.par.S.fold.u) :
    IsFold P.par.S.fold w Rw (uOf d'.loc
      (held w₀ d.st.oracles.size Q (sendsU Q.codes P.par.S w Rw cU cMask))) := by
  obtain ⟨hsh, hsz⟩ := shapeAt_of_get Q 0 nU h0
  exact isFold_held w₀ d.st.oracles.size Q Q.codes P.par.S w Rw cU cMask d'.loc hfit hsz
    (hsh.trans hn) (oU_behind P n Q inFront groups d d' r₁ r₂ gs h)

/-- The same at the shared chain's own parameters of "send o_u", from the program's public test on
the codes and the shape. -/
theorem isFold_behindU_at (P : P14) (n part : String) (sentU : Array OracleNotice)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (d d' : St) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (w₀ : Words Cb.Gl.E) (w : ℕ → Cb.Gl.E)
    (Rw : ℕ → ℕ → Cb.Gl.E) (cU cMask : MsgCoins) (hU : withU P.S = some sentU)
    (hok : linOk P.codes P.S = true)
    (h : (sendAt P n (parK1 P 2 part sentU) inFront groups (behindU P.par)).decide d [r₁, r₂] gs =
      .ok d') :
    IsFold P.S.fold w Rw (uOf d'.loc
      (held w₀ d.st.oracles.size (parK1 P 2 part sentU) (sendsU P.codes P.S w Rw cU cMask))) := by
  obtain ⟨nU, h0, hn⟩ := withU_first P.S sentU hU
  have hfit : VerifiableInference.Desc.Own.linFits P.codes P.S = true := by
    rw [VerifiableInference.Desc.Own.linFits_eq]
    exact hok
  exact isFold_behindU P n (parK1 P 2 part sentU) inFront groups d d' r₁ r₂ gs w₀ w Rw cU cMask h
    hfit nU (by rw [parK1_sent]; exact h0) hn

end Desc.K14.Honest

#print axioms Desc.K14.Honest.sendAt_kept
#print axioms Desc.K14.Honest.sendU_kept
#print axioms Desc.K14.Honest.sendOmega_kept
#print axioms Desc.K14.Honest.sendU_met
#print axioms Desc.K14.Honest.sendOmega_met
#print axioms Desc.K14.Honest.ids_next
#print axioms Desc.K14.Honest.shapeAt_of_get
#print axioms Desc.K14.Honest.oU_behind
#print axioms Desc.K14.Honest.oOmega_behind
#print axioms Desc.K14.Honest.isFold_behindU
#print axioms Desc.K14.Honest.isFold_behindU_at
