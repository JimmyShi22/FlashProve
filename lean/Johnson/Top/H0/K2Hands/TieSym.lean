-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/TieSym.lean: the code switch: TWO OF THE FIVE CLAUSES OF TieN
(HandsOn.lean) AT A YES OF THE KIND's OWN DECISION, at the typed statement behind that sel_law's tie
speaks of: «draw», from the yes and the reading of the positions; «symbol», from these AND THE
PREMISE ShowsAt.

TieN ties the typed statement x behind the positions to the record. In TieT.lean x is ((inX s).1.1,
(Qs, fun i => C.T y (Qs i))): the positions read off the second round, and the open word's string y
read at them. Here:
  tie_draw    the program's list of draws is the typed tuple Qs, if Qs is read off the view's drawn
              positions modulo 2 ^ logN and there are as many as the tuple is long: by the text's
              own guard that every drawn position lies below 2 ^ logN (Tw/K2C/Laws.lean's
              inRangeOfYes)
  ShowsAt     THE PREMISE: what the text hears as the old group's long symbol at a drawn position q
              is the open word's string read at q (that the string's long symbols at Qs are the
              symbols that stand as the generator rows' targets is shown inside tieN_of's proof, by
              K2Hears/LongSym.lean's yes_long_sym)
  tieN_of     TieN from its three other clauses (target, vector, sample: all on inX), ShowsAt, the
              reading of Qs (hlen, hQ) and ho: what the text has read of the old rows
              (K2Hears/Whole.lean's AtYes has it at a yes)
LIMITS. ShowsAt is a premise: that the columns shown are the committed words' is the oracle model's
matter, not the text's. (Brought further, not paid: ShowsCols.lean's shows_of_cols makes ShowsAt
from two premises, ColsOf and StrIs.) target, vector and sample stay premises on the letter inX. No
soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.HandsOn
import Johnson.Top.H0.K2Hears.LongSym

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H

/-- **The program's list of draws is the typed tuple.** -/
theorem tie_draw {snd : _root_.Tw.K2.SendFn} {p : K2.P2} {s s' : VerifiableInference.Desc.First.S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : K2.decideWith snd p s [r₁, r₂] gs = .ok s') {t a : ℕ} (Qs : Fin t → Fin (2 ^ a))
    (hlen : r₂.drawn.poss.length = t)
    (hQ : ∀ i, (Qs i).val = r₂.drawn.poss.getD i.val 0 % 2 ^ p.logN) (i : Fin t) :
    (OnBytes.Positions.ofDraws p.logN r₂.drawn.poss).draws.toList[i.val]? = some (Qs i).val ∧
      (Qs i).val ∈ r₂.drawn.poss := by
  have hi : i.val < r₂.drawn.poss.length := by rw [hlen]; exact i.isLt
  have hg : r₂.drawn.poss.getD i.val 0 = r₂.drawn.poss[i.val] := List.getD_eq_getElem _ _ hi
  have hm : r₂.drawn.poss[i.val] ∈ r₂.drawn.poss := List.getElem_mem hi
  have hlt := K2.inRangeOfYes snd p s r₁ r₂ gs s' h _ hm
  have e : (Qs i).val = r₂.drawn.poss[i.val] := by rw [hQ i, hg, Nat.mod_eq_of_lt hlt]
  refine ⟨?_, e ▸ hm⟩
  show r₂.drawn.poss.toArray.toList[i.val]? = _
  rw [List.toList_toArray, List.getElem?_eq_getElem hi, e]

variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "LocK" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc

/-- **The premise**: what the text hears at a drawn position is the open word's string read
there. -/
def ShowsAt (snd : _root_.Tw.K2.SendFn) (p : K2.P2) (s : VerifiableInference.Desc.First.S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (coord : (LocK).C.Aa → ℕ)
    (y : (LocK).C.ext.Str) : Prop :=
  ∀ (q : (LocK).P) (σ : (LocK).C.Aa → GE),
    K2.longAt coord snd p s r₁ r₂ gs q.val = some σ → σ = (LocK).C.T y q

/-- **TieN from the three clauses on inX, ShowsAt and the reading of the positions.** -/
theorem tieN_of {snd : _root_.Tw.K2.SendFn} {p : K2.P2} {s s' : VerifiableInference.Desc.First.S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : K2.decideWith snd p s [r₁, r₂] gs = .ok s')
    (xc : (LocK).Xc × (LocK).hd.Smp) (Qs : Fin (LocK).t → (LocK).P) (y : (LocK).C.ext.Str)
    {St : OnBytes.Statement} {W : OnBytes.SwitchFrame} {ids : ℕ → ℕ} {old : OnBytes.SingleRows}
    {Y : Array OnBytes.E} {mem row : R.Kp → ℕ} {pl : R.Kp → OnBytes.KeptPlace}
    {aOf : (LocK).hd.K → ℕ} {iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ}
    (ho : K2.oldRead snd p s r₁ r₂ gs =
      some (old, OnBytes.Positions.ofDraws p.logN r₂.drawn.poss, Y))
    (hlen : r₂.drawn.poss.length = (LocK).t)
    (hQ : ∀ i, (Qs i).val = r₂.drawn.poss.getD i.val 0 % 2 ^ p.logN)
    (hV : ShowsAt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ snd p s r₁ r₂ gs
      (coordOf R.s R.Kp W old mem row) y)
    (target : xc.1.1 = readE old.target) (vector : xc.1.2 = vecOf R.s R.Kp old row pl)
    (sample : ∀ ks : Σ k, ((LocK).hd.o k).Z.S, ∃ (k : OnBytes.KeptPlace) (smp : OnBytes.Row),
      W.kept[aOf ks.1]? = some k ∧ (samplesOf St k)[iOf ks.1 ks.2]? = some smp ∧
        Slots R.s R.Kp cs l W ids mem row (aOf ks.1) k ∧ (xc.2 ks.1).2 ks.2 = readE smp.target ∧
        pushTo ((LocK).hd.sJ ks.1) (((LocK).hd.o ks.1).Z.mat (xc.2 ks.1).1 ks.2) =
          slotVec R.s R.Kp mem row (aOf ks.1) k.rowBits (formOn smp)) :
    TieN R Hd Sb sl Z A₀ cs l iJ iQ t w₀ (xc, (Qs, fun i => (LocK).C.T y (Qs i))) St W ids old
      (OnBytes.Positions.ofDraws p.logN r₂.drawn.poss) Y mem row pl aOf iOf where
  target := target
  vector := vector
  sample := sample
  draw := fun i => (tie_draw h Qs hlen hQ i).1
  symbol := fun i α => by
    obtain ⟨x, w, y', S3, Y', rows, -, ho', -, -, -, -, hl⟩ :=
      K2.yes_long_sym _ (coordOf R.s R.Kp W old mem row) snd p s r₁ r₂ gs s' h
    rw [ho] at ho'
    have e := Option.some.inj ho'
    have e1 : old = x.f.rows := congrArg (·.1) e
    have e2 : Y = Y' := congrArg (·.2.2) e
    have hl' := hl _ (tie_draw h Qs hlen hQ i).2
    rw [← e1, ← e2] at hl'
    exact congrFun (hV (Qs i) _ hl').symm α

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.tie_draw
#print axioms VerifiableInference.Desc.First.K2Hands.tieN_of
