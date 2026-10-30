-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/ShowsCols.lean: the code switch: TieSym.lean's PREMISE ShowsAt FROM
TWO PLAIN THINGS: every column that the decision is shown is the oracles'; and the typed open word's
string is what the front reads off the oracles, position by position.

K2Hears/LongOne.lean's heard_is_front: at a yes, if every column shown is orc's, what the text hears
at a listed position is longFront there: a function of the place's numbers, the record in front, its
front, orc and the position.
  rowsBefore_lt, coordOf_lt  a coordinate's number is below the number of the carried rows
  StrIs         ON THE STATEMENT IN FRONT: the string's long symbol at q, at the coordinate α, is
                longFront's entry number coord α, read in the field. Nothing of the two rounds
                occurs
  shows_of_cols  ShowsAt from ColsOf (K2Hears/LongCols.lean), StrIs and the bound on the coordinates
So YesAt (TiePaid.lean) asks ColsOf (its clause cols) at a yes, and not ShowsAt. BY READING, whoever
defines the columns shown as the oracles' columns has ColsOf by definition; no lemma here says so.
LIMITS. StrIs is a premise on the letters strs and orc. BY READING it can be met by make (take the
string that longFront reads); no Lean line here makes such a string; whether that string is the one
of which the promise in front speaks is the border to the block in front. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hands.TieSym
import Johnson.Top.H0.K2Hears.LongOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H

theorem rowsBefore_lt : ∀ (ks : List OnBytes.KeptPlace) (a : ℕ) (k : OnBytes.KeptPlace) (b : ℕ),
    ks[a]? = some k → b < k.rows → rowsBefore ks a + b < (ks.map (·.rows)).sum
  | [], a, k, b, h, _ => by simp at h
  | k0 :: ks, 0, k, b, h, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [rowsBefore]
    omega
  | k0 :: ks, a + 1, k, b, h, hb => by
    have e := rowsBefore_lt ks a k b (by simpa using h) hb
    simp [rowsBefore] at e ⊢
    omega

theorem coordOf_lt {s : Sg} {K : Type} [Fintype K] [DecidableEq K] {W : OnBytes.SwitchFrame}
    {old : OnBytes.SingleRows} {mem row : K → ℕ} {pl : K → OnBytes.KeptPlace}
    (A : SlotsAll K W mem row pl) (hk : old.keptRows = (W.kept.map (·.rows)).sum)
    (hm : old.masks = 2) (α : (s.cKept K).Aa) : coordOf s K W old mem row α < old.rows := by
  unfold OnBytes.SingleRows.rows
  rcases α with ⟨_ | κ, _⟩ | _ | _
  · show 0 < _
    omega
  · show 1 + (rowsBefore W.kept (mem κ) + row κ) < _
    have := rowsBefore_lt W.kept (mem κ) (pl κ) (row κ) (A.member κ) (A.rowIn κ)
    omega
  · show old.maskRow 0 < _
    unfold OnBytes.SingleRows.maskRow
    omega
  · show old.maskRow 1 < _
    unfold OnBytes.SingleRows.maskRow
    omega

variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "LocK" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc

/-- **The typed open word's string is what the front reads off the oracles.** -/
def StrIs (p : K2.P2) (s : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front)
    (orc : ℕ → ℕ → List UInt64) (coord : (LocK).C.Aa → ℕ) (str : (LocK).C.ext.Str) : Prop :=
  ∀ (q : (LocK).P) (seg : Array OnBytes.E), K2.longFront p s fx orc q.val = some seg →
    ∀ α, (LocK).C.T str q α = readE (seg.getD (coord α) OnBytes.zeroE)

/-- **ShowsAt from the columns shown and the string.** -/
theorem shows_of_cols {p : K2.P2} {s s' : VerifiableInference.Desc.First.S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {fx : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : OnBytes.Statement} {Y : Array OnBytes.E} {rows : List OnBytes.Row} {G : OnBytes.Group}
    {c : OnBytes.Code} (Y1 : K2.AtYes p s s' r₁ r₂ gs fx y S3 Y rows G c)
    {orc : ℕ → ℕ → List UInt64} (hc : K2.ColsOf orc (K2.flat p gs)) {coord : (LocK).C.Aa → ℕ}
    (hco : ∀ α, coord α < fx.f.rows.rows) {str : (LocK).C.ext.Str}
    (hs : StrIs R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p s fx orc coord str) :
    ShowsAt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ _root_.Tw.K2.sendByL8 p s r₁ r₂ gs coord str := by
  intro q σ hl
  unfold K2.longAt at hl
  rw [Y1.heard] at hl
  simp only [Option.bind_some] at hl
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hl
  obtain ⟨hlt, hq⟩ := OnBytes.Slice.ProxRun.idxOf_some _ _ _ hi
  obtain ⟨seg, hseg, hY⟩ := K2.heard_is_front Y1 hc i hlt
  rw [hq] at hseg
  funext α
  rw [hs q seg hseg α]
  congr 1
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, hY _ (hco α)]

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.coordOf_lt
#print axioms VerifiableInference.Desc.First.K2Hands.shows_of_cols
