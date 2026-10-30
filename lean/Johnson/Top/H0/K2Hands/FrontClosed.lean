-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrontClosed.lean: the code switch's law: THE CLOSED FACTS that
frontB2_of_fold (FrontOfFold.lean) and rowsLike_of_kept (FrontOfCarried.lean) take at a place's
written entry, AS TESTS WITH CODE ON PUBLIC DATA, each tied to its premise; and the two theorems
joined: ONE CALL from the fold's facts, the closing's law and two Bools to «the test on the front
accepts». A law file; no running text imports it.

x₀, W₀: the written front of the place's entry and its frame. cs: the public codes. M: the listed
shapes of the first chain's messages. n0, olds: the place's own numbers. code, maskCode: the public
shape's two code numbers. T: the target of the public shape's group at the place's link.

  targetLikeB T T₀, targetLike_of_test   the four equations of TargetLike.
  closedB x₀ W₀ cs M n0 olds code maskCode   seven clauses, by name in closedList:
      codes     the written front's codes are cs                                     (c1)
      shapes    its kept shapes are M's at olds                                       (c2)
      below     olds lie below n0                                                     (c3)
      below0    its own kept members lie below its own count                          (c4)
      keptRows  its carried rows' count of kept rows is the sum of M's main rows at olds  (k1)
      logEll    the frame's main code has the exponent of cs's code number `code`     (k2)
      ell       cs's mask code number `maskCode` is no longer than the frame's         (k3)
  Closed …, closed_of_test               the seven as Props.
  frontB2_at     THE JOIN.
Limits. The tests are evaluated nowhere here: at which closed terms they say yes is another file's.
Nothing is paid here but the passage from Bool to Prop. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.FrontOfCarried

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes
open VerifiableInference.Desc.First.Close (Plan CarriedOk)

/-- The four equations of TargetLike, as a test. -/
def targetLikeB (T T₀ : SwitchTarget) : Bool :=
  decide (T.shape = T₀.shape) && decide (T.main = T₀.main) && decide (T.rest = T₀.rest) &&
    decide (T.kept.toList.map (·.shape) = T₀.kept.toList.map (·.shape))

theorem targetLike_of_test {T T₀ : SwitchTarget} (h : targetLikeB T T₀ = true) :
    TargetLike T T₀ := by
  simp only [targetLikeB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- The seven closed clauses, by name. -/
def closedList (x₀ : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (cs : Codes) (M : List OracleShape)
    (n0 : ℕ) (olds : List ℕ) (code maskCode : ℕ) : List (String × Bool) :=
  [("codes", decide (x₀.st.codes = cs)),
   ("shapes", decide (keptShapes x₀ = olds.map fun o => M[o]?)),
   ("below", olds.all fun o => decide (o < n0)),
   ("below0", keptBelowB x₀),
   ("keptRows", x₀.f.rows.keptRows == (olds.map fun o => ((M[o]?).map (·.mainRows)).getD 0).sum),
   ("logEll", W₀.code.logEll == (cs.base.getD code default).logEll),
   ("ell", decide ((cs.mask.getD maskCode default).ell ≤ W₀.zk.ell))]

/-- All seven. -/
def closedB (x₀ : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (cs : Codes) (M : List OracleShape)
    (n0 : ℕ) (olds : List ℕ) (code maskCode : ℕ) : Bool :=
  (closedList x₀ W₀ cs M n0 olds code maskCode).all (·.2)

/-- The seven, as Props. -/
structure Closed (x₀ : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (cs : Codes) (M : List OracleShape)
    (n0 : ℕ) (olds : List ℕ) (code maskCode : ℕ) : Prop where
  c1 : x₀.st.codes = cs
  c2 : keptShapes x₀ = olds.map fun o => M[o]?
  c3 : ∀ o ∈ olds, o < n0
  c4 : keptBelowB x₀ = true
  k1 : x₀.f.rows.keptRows = (olds.map fun o => ((M[o]?).map (·.mainRows)).getD 0).sum
  k2 : W₀.code.logEll = (cs.base.getD code default).logEll
  k3 : (cs.mask.getD maskCode default).ell ≤ W₀.zk.ell

theorem closed_of_test {x₀ : _root_.Tw.K2.Front} {W₀ : SwitchFrame} {cs : Codes}
    {M : List OracleShape} {n0 : ℕ} {olds : List ℕ} {code maskCode : ℕ}
    (h : closedB x₀ W₀ cs M n0 olds code maskCode = true) :
    Closed x₀ W₀ cs M n0 olds code maskCode := by
  simp only [closedB, closedList, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7⟩

/-- **THE JOIN**: from the fold's facts at the state t in front of the switch and at the statement
S' right behind the last closing, the closing's law on its output, the walk's three facts, and the
two tests on public data: the test on the front accepts. -/
theorem frontB2_at {p : K2.P2} {t : S} {fx x₀ : _root_.Tw.K2.Front} {W₀ : SwitchFrame}
    {grp rows n0 : ℕ} {olds : List ℕ} {cs : Codes} {M : List OracleShape} {out : SingleRows}
    {P : Plan} {G : Group} {S' : Statement} {T : SwitchTarget}
    (h : K2.frontAt p t = some fx) (hc : t.st.codes = cs)
    (hM : ∀ o, o < t.st.oracles.size → (t.st.oracles[o]?).map (·.shape) = M[o]?)
    (hn : t.st.oracles.size = n0)
    (hT : ∀ g : ReqGroup, (t.check.frame.groups[t.check.frame.link]? = some g ∨
      ∃ a, t.here = .fin a ∧ a.G = some g) → g.target = T)
    (hR : ∀ f, CopyAt p t f → f.rows = out)
    (C : CarriedOk P G S' out) (hk : (switchKept out).toList = olds) (hcs : S'.codes = cs)
    (hM' : ∀ o ∈ olds, (S'.oracles[o]?).map (·.shape) = M[o]?)
    (h1 : out.code = x₀.f.rows.code) (h2 : out.maskCode = x₀.f.rows.maskCode)
    (h3 : out.masks = x₀.f.rows.masks)
    (hg : fx.f.group = grp) (hf : ∃ G, fx.st.groups[grp]? = some G ∧ G.rows.size = rows)
    (b1 : closedB x₀ W₀ cs M n0 olds P.code P.maskCode = true)
    (b2 : targetLikeB T x₀.T = true) : frontB2 x₀ W₀ grp rows n0 olds fx = true := by
  have K := closed_of_test b1
  exact frontB2_of_fold h hc hM hn
    (fun g hgr => by rw [hT g hgr]; exact targetLike_of_test b2) hR
    (rowsLike_of_kept C hk hcs hM' h1 h2 h3 K.k1 K.k2 K.k3) hg hf K.c1 K.c2 K.c3 K.c4

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.frontB2_at
#print axioms VerifiableInference.Desc.First.K2Hands.closed_of_test
