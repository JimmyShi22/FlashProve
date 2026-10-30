-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyCondThree.lean: PUBLIC FACTS, IN SCOPE, ON THE SHARED CHAIN's TWO SENDINGS OF THE KEY FILE (o_u with the first mask; o_omega with o_sp), ON WHICH A MEMBER OF THAT CHAIN's INVARIANT LEANS: the sending kind's public condition condPort holds at each. (The file's name says three: the third, W's sending in the first chain, is in the tables' files.) AND THE LINE BENEATH THEM: the shared chain's parameters p14At X P are one structure of written values. Statements with proofs: calls, and evaluations in the kernel on written values. IT PAYS NO FIELD OF THE KEY FILE's TABLES.
OBJECT. K1's condPort at K14's two sendings' parameters at p14At X P. USER. The tables' files' member of chain 2 off the history: the premise hC of other lemmas on the OOD sample's row at these two sendings, which take any radii; and, at the list of six's own radii, these sendings' own laws.
LETTERS. X P. PREMISE. hkey: scope's equation (the sized key is the written one). The forms that end in _scope take the scope's four in its place.

  p14Key_eta: p14Key bp (Johnson/RunOne/KeyRowsInScope.lean) is ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, 0, bp⟩.
  p14At_eta, p14At_eta_scope: p14At X P = ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, 0, beforeSharedPoint P⟩: p14At_key, then p14Key_eta.
  cond_u, cond_omega (and _scope): condPort at the shared chain's two sendings, at SOME radii: out of k14_key (Johnson/Goal/Numbers/K14CondAt.lean).
  cond_u_full, cond_omega_full (by the kernel), cond_u_six, cond_omega_six (and _scope): the same AT THE RADII OF THE TABLES' LIST OF SIX: 8342420 at o_u's sending; 3138896 and 6130 at o_omega's and o_sp's.
WHAT IT DOES NOT SAY. That the messages of these two are sampled · a member · soundness.
THE TWO STRINGS "o_u and the first mask" and "o_omega and o_sp" are the base's own literals (K14's blocks; pU | pO of K14CondAt.lean), lifted. THE THREE NUMERALS are the radii of the last three entries of the tables' list of six: six_345, by rfl.
The statements of cond_u and cond_omega are taken over.

-/
import Johnson.RunOne.KeyMsgAll
import Johnson.RunOne.KeyCut23
import Johnson.RunOne.KeyRowsInScope
import Johnson.RunOne.KeySplitShape
import Johnson.Goal.Numbers.K14CondAt
import Johnson.Top.Fire.Code.KeyPublicAtSeat
import Johnson.Desc.Key.KeyFillAtSizes

set_option autoImplicit false

namespace Johnson.RunOne.KeyMsg

open OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps Johnson.RunOne.KeySendGood
open VerifiableInference.Desc (Block noDigest viewWordsBelowPrime roundsFit)
open VerifiableInference.Desc.Sound (held)
open VerifiableInference.Desc.Plain (held_decide)
open VerifiableInference.Desc.Keeps (ebind_ok)
open VerifiableInference.Desc.ChainEnd (bind_ok)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K1 (Par SeedIs Tie Seeds ReadsAs decideSend shapesOf shapeAt sampledAt condPort seedIs_behind_len draw_len SameMsgs)
open LPFD (Reached Hist₁ Hist₃)
open Johnson.Pack (bitsZ)

open Lk6.AtPlan (keyFull)
open Johnson.RunOne.KeyRows23 (p14At p14Key p14At_key)
open _root_.Desc.K14 (P14 parK1 withU withOmega)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-! ## The line -/

theorem set_full : keyFull.set = recordSet := rfl
theorem once_full : keyFull.once.lines.oneTime = true := by decide +kernel

theorem p14Key_eta (bp : List (ℕ × ℕ)) : p14Key bp = ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, 0, bp⟩ := by
  unfold p14Key
  simp only [once_full, if_true, set_full]

/-- **The shared chain's parameters are one structure of written values.** -/
theorem p14At_eta (hkey : X.chains.made.sized.key = keyFull) :
    p14At X P = ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, 0, beforeSharedPoint P⟩ :=
  (p14At_key hkey P).trans (p14Key_eta _)

theorem p14At_eta_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public}
    (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) :
    p14At X P = ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, 0, beforeSharedPoint P⟩ :=
  p14At_eta (Johnson.RunOne.KeySplit.key_of_scope hZ hP hm hX)

/-! ## The shared chain's two -/

theorem cond_u (hkey : X.chains.made.sized.key = keyFull) :
    ∃ (sentU : Array OracleNotice) (radU : ℕ → ℕ), withU (p14At X P).S = some sentU ∧
      condPort (parK1 (p14At X P) 2 "o_u and the first mask" sentU) radU = true := by
  obtain ⟨sentU, hU, ⟨yU, -, -, hCU⟩, -⟩ := (_root_.Desc.K14.Law.k14_key 0 [(1, 0)] (by simp)).sendU
  rw [p14At_eta hkey]
  exact ⟨sentU, _, hU, hCU⟩

theorem cond_omega (hkey : X.chains.made.sized.key = keyFull) :
    ∃ radO : ℕ → ℕ, condPort (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S)) radO = true := by
  obtain ⟨⟨yO, -, -, hCO⟩, -⟩ := (_root_.Desc.K14.Law.k14_key 0 [(1, 0)] (by simp)).sendO
  rw [p14At_eta hkey]
  exact ⟨_, hCO⟩

/-! ### At the list of six's own radii -/

/-- The written parameters; what stands before the point is not read by a sending's parameters. -/
abbrev pFull : P14 := ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, 0, [(1, 0)]⟩

theorem six_345 : (VerifiableInference.Desc.Key.Fill.six.drop 3).map (·.2) = [8342420, 3138896, 6130] := rfl

theorem cond_u_full : condPort (parK1 pFull 2 "o_u and the first mask" ((withU keyFull.once.shape).getD #[]))
    (fun _ => 8342420) = true := by decide +kernel
/-- A negative test: at the code's whole length as the radius the test rejects. -/
theorem cond_u_no : condPort (parK1 pFull 2 "o_u and the first mask" ((withU keyFull.once.shape).getD #[]))
    (fun _ => 2 ^ 24) = false := by decide +kernel

theorem cond_omega_full : condPort (parK1 pFull 5 "o_omega and o_sp" (withOmega keyFull.once.shape))
    (fun k => if k = 0 then 3138896 else 6130) = true := by decide +kernel
/-- A negative test: with the two radii changed about the test rejects. -/
theorem cond_omega_no : condPort (parK1 pFull 5 "o_omega and o_sp" (withOmega keyFull.once.shape))
    (fun k => if k = 0 then 6130 else 3138896) = false := by decide +kernel

theorem cond_u_six (hkey : X.chains.made.sized.key = keyFull) :
    ∃ sentU : Array OracleNotice, withU (p14At X P).S = some sentU ∧
      condPort (parK1 (p14At X P) 2 "o_u and the first mask" sentU) (fun _ => 8342420) = true := by
  obtain ⟨sentU, hU, -, -⟩ := (_root_.Desc.K14.Law.k14_key 0 [(1, 0)] (by simp)).sendU
  have hU' : withU keyFull.once.shape = some sentU := hU
  have e : sentU = (withU keyFull.once.shape).getD #[] := by rw [hU']; rfl
  rw [p14At_eta hkey]
  exact ⟨sentU, hU, by rw [e]; exact cond_u_full⟩

theorem cond_omega_six (hkey : X.chains.made.sized.key = keyFull) :
    condPort (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S))
      (fun k => if k = 0 then 3138896 else 6130) = true := by
  rw [p14At_eta hkey]
  exact cond_omega_full

theorem cond_u_six_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public}
    (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) :
    ∃ sentU : Array OracleNotice, withU (p14At X P).S = some sentU ∧
      condPort (parK1 (p14At X P) 2 "o_u and the first mask" sentU) (fun _ => 8342420) = true :=
  cond_u_six (Johnson.RunOne.KeySplit.key_of_scope hZ hP hm hX)

theorem cond_omega_six_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public}
    (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) :
    condPort (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S))
      (fun k => if k = 0 then 3138896 else 6130) = true :=
  cond_omega_six (Johnson.RunOne.KeySplit.key_of_scope hZ hP hm hX)

theorem cond_u_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public}
    (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) :
    ∃ (sentU : Array OracleNotice) (radU : ℕ → ℕ), withU (p14At X P).S = some sentU ∧
      condPort (parK1 (p14At X P) 2 "o_u and the first mask" sentU) radU = true :=
  cond_u (Johnson.RunOne.KeySplit.key_of_scope hZ hP hm hX)

theorem cond_omega_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public}
    (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) :
    ∃ radO : ℕ → ℕ, condPort (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S)) radO = true :=
  cond_omega (Johnson.RunOne.KeySplit.key_of_scope hZ hP hm hX)

end Johnson.RunOne.KeyMsg

#print axioms Johnson.RunOne.KeyMsg.set_full
#print axioms Johnson.RunOne.KeyMsg.once_full
#print axioms Johnson.RunOne.KeyMsg.p14Key_eta
#print axioms Johnson.RunOne.KeyMsg.p14At_eta
#print axioms Johnson.RunOne.KeyMsg.p14At_eta_scope
#print axioms Johnson.RunOne.KeyMsg.cond_u
#print axioms Johnson.RunOne.KeyMsg.cond_omega
#print axioms Johnson.RunOne.KeyMsg.cond_u_scope
#print axioms Johnson.RunOne.KeyMsg.cond_omega_scope
#print axioms Johnson.RunOne.KeyMsg.six_345
#print axioms Johnson.RunOne.KeyMsg.cond_u_full
#print axioms Johnson.RunOne.KeyMsg.cond_u_no
#print axioms Johnson.RunOne.KeyMsg.cond_omega_full
#print axioms Johnson.RunOne.KeyMsg.cond_omega_no
#print axioms Johnson.RunOne.KeyMsg.cond_u_six
#print axioms Johnson.RunOne.KeyMsg.cond_omega_six
#print axioms Johnson.RunOne.KeyMsg.cond_u_six_scope
#print axioms Johnson.RunOne.KeyMsg.cond_omega_six_scope
