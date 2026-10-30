-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TypedAtT3.lean: `typed_first` (K2Caller/TypedFirst.lean) HELD AGAINST THE
FIELD `T3At.typed` (Johnson/Top/H0/Tw/K2C/TieThreeR.lean) BY
LEAN, not by reading: in what `k02_t3R`'s premise hAt has in hand there (the decision's own accept
beside AtYes). NO BLOCK IMPORTS THIS FILE.

  typed_of_yes   the field's own sentence (∃ W₀ mem row pl, the three conjuncts): the first by
                 `typed_first`, its range of the drawn positions from the decision's accept
                 (`K2.inRangeOfYes`); the third is `CallerAt.slots`; the second, ZeroAsks, stays a
                 premise
  t3At_of        **the structure T3At** from its eight other fields, as premises in the fields' own
                 letters, and `typed_of_yes`: Lean holds the sentence against the field's type

Premises that stay for «typed»: CallerAt (once) · FrontLight at the front · Held · ZeroAsks · p.logN
≤ 32. hlen and ht are in hAt's hand.
Limits. A joining: it pays nothing beyond `typed_first`. Shown at no real state. No soundness
statement.

-/
import Johnson.Top.H0.Tw.K2C.TieThreeR
import Johnson.Top.H0.K2Caller.TypedFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.K2Hands

/-- **The field's own sentence.** -/
theorem typed_of_yes {r : SwRow} (H : r.OK)
    (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    {p : K2.P2} (h32 : p.logN ≤ 32) {W₀ : SwitchFrame}
    {mem row : (selR (Letters.plain r H)).Kp → ℕ} {pl : (selR (Letters.plain r H)).Kp → KeptPlace}
    {aOf : (selLoc (Letters.plain r H) iJ iQ).hd.K → ℕ}
    {iOf : ∀ k, ((selLoc (Letters.plain r H) iJ iQ).hd.o k).Z.S → ℕ} {t t' s' : Rec}
    {r₁ r₂ : Fmt.RoundView} {gs : Gs} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement}
    {Y : Array E} {rows : List OnBytes.Row} {Gg : Group} {c : Code}
    (ht : K2.decideWith _root_.Tw.K2.sendByL8 p t [r₁, r₂] gs = .ok t')
    (Y1 : K2.AtYes p t t' r₁ r₂ gs x y S3 Y rows Gg c)
    (C : CallerAt (selR (Letters.plain r H)) r.cs r.l iJ iQ mem row pl W₀)
    (P : FrontLight r.cs r.l W₀ x) (Hh : Held S3 W₀ aOf iOf)
    (hlen : r₂.drawn.poss.length = baseCount r.set .request r.g)
    (hZ : ZeroAsks (selR (Letters.plain r H)) r.cs r.l iJ iQ W₀ mem row pl x.st.oracles.size
      s'.st) :
    ∃ (W₀ : SwitchFrame) (mem row : (selR (Letters.plain r H)).Kp → ℕ)
      (pl : (selR (Letters.plain r H)).Kp → KeptPlace),
      (∀ ρ ∈ rows, OnlyAt r.cs r.l (fun i => x.st.oracles.size + i)
        (Inside (selR (Letters.plain r H)).s W₀ pl) ρ) ∧
      ZeroAsks (selR (Letters.plain r H)) r.cs r.l iJ iQ W₀ mem row pl x.st.oracles.size s'.st ∧
      SlotsAll (selR (Letters.plain r H)).Kp W₀ mem row pl :=
  ⟨W₀, mem, row, pl,
    typed_first H iJ iQ h32 Y1 C P Hh hlen (K2.inRangeOfYes _ p t r₁ r₂ gs t' ht), hZ, C.slots⟩

/-- **T3At, with «typed» paid so.** The eight other fields: premises in the fields' own letters. -/
theorem t3At_of {r : SwRow} (H : r.OK)
    (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (seatN : Fin r.l.length → ℕ × ℕ) (N : Numbers) (m n0 grp : ℕ)
    {p : K2.P2} (h32 : p.logN ≤ 32) {W₀ : SwitchFrame}
    {mem row : (selR (Letters.plain r H)).Kp → ℕ} {pl : (selR (Letters.plain r H)).Kp → KeptPlace}
    {aOf : (selLoc (Letters.plain r H) iJ iQ).hd.K → ℕ}
    {iOf : ∀ k, ((selLoc (Letters.plain r H) iJ iQ).hd.o k).Z.S → ℕ} {t t' s' : Rec}
    {r₁ r₂ : Fmt.RoundView} {gs : Gs} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement}
    {Y : Array E} {rows : List OnBytes.Row} {Gg : Group} {c : Code}
    (ht : K2.decideWith _root_.Tw.K2.sendByL8 p t [r₁, r₂] gs = .ok t')
    (Y1 : K2.AtYes p t t' r₁ r₂ gs x y S3 Y rows Gg c)
    (C : CallerAt (selR (Letters.plain r H)) r.cs r.l iJ iQ mem row pl W₀)
    (P : FrontLight r.cs r.l W₀ x) (Hh : Held S3 W₀ aOf iOf)
    (hlen : r₂.drawn.poss.length = baseCount r.set .request r.g)
    (hZ : ZeroAsks (selR (Letters.plain r H)) r.cs r.l iJ iQ W₀ mem row pl x.st.oracles.size
      s'.st)
    (keptPos : K2.KeptPos x.T) (fresh : Gg.rows = #[]) (groupIs : N.groupAt m = x.f.group)
    (carried : ∀ W₀, K2.frameAt x = some W₀ →
      N.rowsAt m .carried = (0, 1 + K2.keptSamples x W₀))
    (position : ∀ W₀, K2.frameAt x = some W₀ → N.rowsAt m .position =
      (1 + K2.keptSamples x W₀, r₂.drawn.poss.length * (1 + K2.targetRows x.T + 2)))
    (seats : ∀ i : Fin r.l.length,
      seatBy noFirst s'.book (x.st.oracles.size + i.val) = some (seatN i))
    (count : x.st.oracles.size = n0) (groupNo : x.f.group = grp) :
    T3At H iJ iQ seatN N m n0 grp s' x rows r₂ Gg :=
  { keptPos := keptPos, fresh := fresh, groupIs := groupIs, carried := carried,
    position := position, seats := seats, count := count, groupNo := groupNo,
    typed := typed_of_yes H iJ iQ h32 ht Y1 C P Hh hlen hZ }

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.typed_of_yes
#print axioms VerifiableInference.Desc.First.K2Caller.t3At_of
