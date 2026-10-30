-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/ZeroAsksAtYes.lean: code switching: ZeroAsks (K2Caller/WordsNamesAt.lean), THE
SECOND CLAUSE OF T3At.typed (Tw/K2C/TieThreeR.lean), AT AN ACCEPTANCE: the two theorems together
give all six fields, from what the first clause's payer takes already (K2.AtYes · CallerAt ·
FrontLight · p.logN ≤ 32), Tied, the test on the codes' lengths, and «the way out keeps the tables».
A JOINING: every step is a call. NO SUB-PROTOCOL IMPORTS THIS FILE.
  shapesAt_of_yes   ShapesAt behind: the new messages have the typed list's shapes, at every
                    statement with the tables of the one that the decision made: by
                    K2.yes_new_shape (Tw/K2C/NewAtYes.lean) and Tied
  zeroAsks_of_yes   ZeroAsks at W₀, at the front's count of oracle messages, FROM ShapesAt (its
                    first field, handed through) at any statement; the five others are made:
                    AtSwitch as only_at_yes_light makes it
                    (Tw/K2C/OnlyAtLight.lean); then codesFit_atSwitch · newNumbers_atSwitch
                    (WordsNamesAt.lean) · paid_names · paid_namesK · paid_slots (K2Hands/Paid.lean)
LIMITS. CallerAt, FrontLight, Tied and the test on the codes' lengths stay premises. Shown at no
real state. No soundness is claimed. On hiding nothing.
-/
import Johnson.Top.H0.K2Caller.WordsNamesAt
import Johnson.Top.H0.Tw.K2C.OnlyAtLight
import Johnson.Top.H0.Tw.K2C.NewAtYes
import Johnson.Top.H0.K2Hands.SeedJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.First.K2Hands
open _root_.Tw.K2 (switchNotices)

/-- **The new messages have the typed list's shapes**, at every statement that has the tables of the
one that the decision made. -/
theorem shapesAt_of_yes {cs : Codes} {l : List (OracleShape × ℕ)} {p : K2.P2} {s s' : Rec}
    {r₁ r₂ : Fmt.RoundView} {gs : Gs} {fx : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement}
    {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (Y1 : K2.AtYes p s s' r₁ r₂ gs fx y S3 Y rows G c)
    (hT : K2Hands.Tied l (switchNotices fx.T fx.others)) (hcs : fx.st.codes = cs) {st : Statement}
    (K : K2.SameTables s'.st st) : ShapesAt cs l fx.st.oracles.size st where
  codes := K.codes.trans (Y1.tables.codes.trans
    ((Y1.same.codes.trans Y1.sent.codes).trans hcs))
  shape := fun i => by
    obtain ⟨n, hn, hs, -⟩ := hT i
    rw [K.shape, K2.yes_new_shape Y1 i.val, hn]
    exact congrArg some hs

section
variable {S : Sig GE} (R : RowsK S)
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)

/-- **ZeroAsks at an acceptance, from ShapesAt**: that field is handed through; five are made. -/
theorem zeroAsks_of_yes {W₀ : OnBytes.SwitchFrame} {p : K2.P2} (h32 : p.logN ≤ 32)
    {mem row : R.Kp → ℕ} {pl : R.Kp → OnBytes.KeptPlace} {s s' : Rec} {r₁ r₂ : Fmt.RoundView} {gs : Gs}
    {fx : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : OnBytes.Statement}
    {Y : Array OnBytes.E} {rows : List OnBytes.Row} {G : OnBytes.Group} {c : OnBytes.Code}
    (Y1 : K2.AtYes p s s' r₁ r₂ gs fx y S3 Y rows G c)
    (C : CallerAt R cs l iJ iQ mem row pl W₀) (P : FrontLight cs l W₀ fx)
    (hL : cs.lengthsOk = true) {st : Statement} (N : ShapesAt cs l fx.st.oracles.size st) :
    ZeroAsks R cs l iJ iQ W₀ mem row pl fx.st.oracles.size st := by
  obtain ⟨W, carried, L⟩ := laid_of Y1.made
  have eW : W₀ = W := by
    have h1 := L.frame
    rw [K2.frame_of_front Y1, P.frameIs] at h1
    exact Option.some.inj h1
  subst eW
  have hKO := K2.keptOld_of Y1.check P.keptPos
  have hold : ∀ (a : ℕ) (k : OnBytes.KeptPlace), W₀.kept[a]? = some k →
      k.old < fx.st.oracles.size := fun a k hk => by
    obtain ⟨hi, e, -⟩ := kept_rec S3 fx.f.rows fx.T _ _ W₀ L.frame a k hk
    rw [e]
    exact hKO _ (Array.getElem_mem_toList hi)
  have hc3 : S3.codes = fx.st.codes := Y1.same.codes.trans Y1.sent.codes
  have A : AtSwitch S3 fx.f.rows fx.T (y.ids.getD 0 OnBytes.noId)
      (y.ids.extract 1 (1 + fx.T.kept.size)) W₀ l R.s R.Kp mem row pl
      (fun i => fx.st.oracles.size + i) :=
    K2.atSwitch_of Y1.sent Y1.same P.keptPos Y1.check L l R.s R.Kp mem row pl Y1.code
      (by rw [Y1.logN]; exact h32) P.z32 P.keptRows
      (fun a k hk => by
        rw [hc3, (old_at_yes Y1 k.old (hold a k hk)).1]
        exact P.ell a k hk)
      P.first P.next C.codeC C.codeZ C.slots
  have hc : S3.codes = cs := hc3.trans P.codes
  obtain ⟨-, -, hg, hk⟩ := K2.six_paid Y1.sent Y1.same hKO Y1.check A.frame
  have eJ := C.mapJ
  have eQ := C.mapQ
  have hD := paid_names A
  have hDK := paid_namesK A
  have hSl := paid_slots A
  have hA := A.fit
  have hNN := newNumbers_atSwitch A hg hk
  have hCF := codesFit_atSwitch A hg hk (by rw [hc]; exact hL)
  clear P C
  subst hc
  rw [eJ hA, eQ hA]
  exact ⟨N, hCF, hNN, ⟨_, _, _, _, _, hD⟩, ⟨_, hDK⟩, hSl⟩

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.shapesAt_of_yes
#print axioms VerifiableInference.Desc.First.K2Caller.zeroAsks_of_yes
