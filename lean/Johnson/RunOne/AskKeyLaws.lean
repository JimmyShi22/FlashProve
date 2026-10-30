-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/AskKeyLaws.lean: what a run of Johnson/RunOne/AskKey.lean answers at a parsed key
file, as plain data, is the one term verifyKeyAskSmall, whose last part is the guarded verdict of
the compiled verifier (verifyGuard, OnBytes/Maker/Page/GuardVerify.lean) at the very string that is
laid of that file. Proofs.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Main names:
  `keyAnswer_eq`: for every parsed key file k of which a proof string π is laid: the test of the
    slot's salt, "written" and the verdict of the stages, all three together, are
    verifyGuard (pageAt C Z Kn O) O at the key file's wire record (wqWhole) and π.
  `keyLastRun_eq`: so the last part in the form that runs is the last part as a term (keyLast): at
    every parsed key file; no where no record is drawn or no string is laid. No premise.
  `keyParts_answer`: the answer of a run as plain data is "every test in front, and the last part in
    the form that runs".
  `verifyKeyAskRun_eq`: **verifyKeyAskRun is verifyKeyAskSmall.** No premise. What runs stands at
    the kit made for a run (ckPT, Johnson/RunOne/DrawT.lean); carry_ckPT
    (Johnson/RunOne/CarryKit.lean) carries it to the kit of the descriptions.
  `verifyKeyAskSmall_parts`: verifyKeyAskSmall is the "and" of its parts.
keyAnswer_eq joins behindOf_answer (Johnson/RunOne/AskShellLaws.lean), verifyCarrier_eq
(OnBytes/Maker/ListedCarrierTop.lean), famT_eq (Johnson/RunOne/FamT.lean) and runGuard_fast
(OnBytes/Maker/Page/GuardFastLaws.lean).
Limits: they speak of the run as plain data (keyParts); that the run with its print (keyTell)
returns the same is by the two texts. The limits of verifyGuard hold: a yes is a yes under the
page's family gJ, at the carrier hollowTX, which is that of no theorem on soundness. Nothing on time
or memory. Nothing on soundness.
The program does not import this file.


-/
import Johnson.RunOne.AskKey
import Johnson.RunOne.AskShellLaws
import Johnson.RunOne.CarryKit
import OnBytes.Maker.Page.GuardFastLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Ask

/-- The tests up to the first no all say yes just where all tests do. -/
theorem upToNo_all : ∀ l : List (String × Thunk Bool),
    ((upToNo l).all fun x => x.2) = l.all fun x => x.2.get
  | [] => rfl
  | x :: l => by
    show ((if x.2.get = true then (x.1, true) :: upToNo l else [(x.1, false)]).all fun y => y.2) =
      (x.2.get && l.all fun y => y.2.get)
    cases x.2.get
    · rfl
    · exact upToNo_all l

end Johnson.RunOne.Ask

namespace Johnson.RunOne.Ask.Key
open Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Compile hiding ON
open OnBytes.Flat OnBytes.Maker _root_.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section At
variable (C : _root_.Run.PQ.CK) (Z : Ground) (Kn : Nat)
  (chal : ∀ e k, (Fin Kn → Dig 256) → C.Ch e k)

/-- **The stages' answer is the guarded verdict of the compiled verifier at the parsed file's own
string.** -/
theorem keyAnswer_eq (O : ByteArray → ByteArray) (k : Carrier.File)
    (c : RecSmall) (cfg : ByteArray) (places : Nat) (pF : FrontMsg (List OnBytes.E))
    (pJ : _root_.Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) (p3 : ByteArray)
    (π : OneProtocolProof 256 (QAt C Z.D Z.tF Z.tJ silK Z.rn))
    (h : Carrier.File.toBPrf C Z.D Z.tF Z.tJ ByteArray.empty silK Z.rn k cfg places pF pJ
      p3 = some π) :
    (guardOf C Z π && (((judge C Z Kn chal).run (inOf C Z Kn O k c π)).written &&
      ((judge C Z Kn chal).run (inOf C Z Kn O k c π)).verdict)) =
      Page.verifyGuard (pageAt C Z Kn O) O (256 + 8 * sbSmall) (8 * 32) .test
        (QAt C Z.D Z.tF Z.tJ silK Z.rn)
        (wqWhole C Kn chal Z.D Z.tF Z.tJ ByteArray.empty silK Z.rn)
        (SCode.emb _ (scWhole sbSmall C Z.D Z.tF Z.tJ ByteArray.empty)) id
        (fun _ => none) (TypedOracleCompiler.Run.PQ.bodyS Z.D.a sbSmall).embE
        Z.key.oneTime.binding.logLeaves (bytesToDig (tableOf k).root :: codeA c.2) c π := by
  have e := behindOf_answer C Z.D Z.tF Z.tJ silK Z.rn Kn chal (LAt C Z) .test
    (inOf C Z Kn O k c π)
  have e2 := verifyCarrier_eq (L := LAt C Z) C Kn chal Z.D Z.tF Z.tJ
    ByteArray.empty silK Z.rn (256 + 8 * sbSmall) (8 * 32) .test
    (SCode.emb _ (scWhole sbSmall C Z.D Z.tF Z.tJ ByteArray.empty)) id (fun _ => none)
    (TypedOracleCompiler.Run.PQ.bodyS Z.D.a sbSmall).embE Z.key.oneTime.binding.logLeaves
    (bytesToDig (tableOf k).root :: codeA c.2) c k cfg places pF pJ p3 π h
  refine (congrArg (fun b => guardOf C Z π && b) e).trans ?_
  show (guardOf C Z π &&
    (Page.detG (S := typedOracleFamily 256 (Kn + 1) (LAt C Z)) (Page.okJF (pageAt C Z Kn O))
      (famT (pageAt C Z Kn O) (runAt C Z Kn O) O)
      (verifyWholeL (L := LAt C Z) C Kn chal Z.D Z.tF Z.tJ ByteArray.empty silK
        Z.rn (256 + 8 * sbSmall) (8 * 32) .test
        (SCode.emb _ (scWhole sbSmall C Z.D Z.tF Z.tJ ByteArray.empty)) id
        (fun _ => none) (TypedOracleCompiler.Run.PQ.bodyS Z.D.a sbSmall).embE
        Z.key.oneTime.binding.logLeaves (bytesToDig (tableOf k).root :: codeA c.2) c π
        (ownOfCarrier Z.D k) (listedOfCarrier Z.D.a k))).getD false) = _
  rw [e2, famT_eq, Page.runGuard_fast]
  unfold Page.verifyGuard Page.verifyBSR
  show _ = (Page.runGuard (pageAt C Z Kn O) O
    (if guardOf C Z π = true then _ else pure false)).getD false
  cases guardOf C Z π <;> rfl

/-- **The last part in the form that runs is the last part as a term.** -/
theorem keyLastRun_eq (O : ByteArray → ByteArray) (k : Carrier.File) :
    keyLastRun C Z Kn chal O k = keyLast C Z Kn chal O k := by
  unfold keyLastRun keyLast keyTyped
  cases recSmall O Z.p.cfg (tableOf k) with
  | none => rfl
  | some c =>
    cases h : Carrier.File.toBPrfAt C Z.D Z.tF Z.tJ ByteArray.empty silK Z.rn k
        Z.key.oneTime.given.cfg Z.key.oneTime.binding
        (OnBytes.Maker.frontOf (tableOf k).answers k.copy) ⟨(tableOf k).answers, k.run2⟩
        k.run3 with
    | none => rfl
    | some π =>
      have h' : Carrier.File.toBPrf C Z.D Z.tF Z.tJ ByteArray.empty silK Z.rn k
          Z.key.oneTime.given.cfg (2 ^ Z.key.oneTime.binding.logLeaves)
          (OnBytes.Maker.frontOf (tableOf k).answers k.copy) ⟨(tableOf k).answers, k.run2⟩
          k.run3 = some π := by
        unfold Carrier.File.toBPrfAt at h
        split at h
        · exact h
        · cases h
      exact keyAnswer_eq C Z Kn chal O k c _ _ _ _ _ π h'

/-- **The answer of a run as plain data.** -/
theorem keyParts_answer (O : ByteArray → ByteArray) (id : String)
    (k : Carrier.File) :
    (keyParts C Z Kn chal O id k).answer =
      (keyTestsOk Z Kn O id k && keyLastRun C Z Kn chal O k) := by
  unfold keyParts keyFront keyLastRun
  cases h : keyTestsOk Z Kn O id k with
  | false => rfl
  | true =>
    have h' : ((claimOf Z Kn O id k).all fun x => x.2) = true := h
    cases keyTyped C Z O k with
    | error e => rfl
    | ok x =>
      show (partsOf (judge C Z Kn chal)
          ({ notes := notesOf k
             lines := claimOf Z Kn O id k ++ [(guardLine, guardOf C Z x.2)]
             guard := some (guardOf C Z x.2)
             input := if guardOf C Z x.2 then some (inOf C Z Kn O k x.1 x.2) else none } :
            Front (InK C Z Kn))).answer =
        (true && (guardOf C Z x.2 && (((judge C Z Kn chal).run (inOf C Z Kn O k x.1 x.2)).written &&
          ((judge C Z Kn chal).run (inOf C Z Kn O k x.1 x.2)).verdict)))
      cases guardOf C Z x.2 with
      | false => rfl
      | true =>
        have hf : ((claimOf Z Kn O id k ++ [(guardLine, true)]).all fun y => y.2) = true := by
          rw [List.all_append, h']
          rfl
        show ((some (((judge C Z Kn chal).run (inOf C Z Kn O k x.1 x.2)).written &&
            ((judge C Z Kn chal).run (inOf C Z Kn O k x.1 x.2)).verdict) == some true) && true &&
            ((claimOf Z Kn O id k ++ [(guardLine, true)]).all fun y => y.2) && true) =
          (true && (true && (((judge C Z Kn chal).run (inOf C Z Kn O k x.1 x.2)).written &&
            ((judge C Z Kn chal).run (inOf C Z Kn O k x.1 x.2)).verdict)))
        rw [hf]
        cases (((judge C Z Kn chal).run (inOf C Z Kn O k x.1 x.2)).written &&
          ((judge C Z Kn chal).run (inOf C Z Kn O k x.1 x.2)).verdict) <;> rfl

end At

section Kit
variable (C : _root_.Run.PQ.CK) (Kn : Nat) (chal : ∀ e k, (Fin Kn → Dig 256) → C.Ch e k)

/-- At every kit: verifyKeyAskRunAt is the term verifyKeyAskAt. -/
theorem verifyKeyAskRunAt_eq (H : ByteArray → ByteArray) (U : User) (k : Carrier.File) :
    verifyKeyAskRunAt C Kn chal H U k = verifyKeyAskAt C Kn chal H U k := by
  unfold verifyKeyAskRunAt verifyKeyAskAt
  cases groundOf H U.pol U.lay U.KL with
  | error e => rfl
  | ok Z =>
    show (keyParts C Z Kn chal H U.id k).answer =
      (((keyTests Z Kn H U.id k).all fun x => x.2.get) && keyLast C Z Kn chal H k)
    rw [keyParts_answer, keyLastRun_eq, ← upToNo_all]
    rfl

/-- At every kit: the term is the "and" of its parts. -/
theorem verifyKeyAskAt_parts (H : ByteArray → ByteArray) (U : User) (k : Carrier.File) :
    verifyKeyAskAt C Kn chal H U k = (verifyKeyAskPartsAt C Kn chal H U k).all fun x => x.2 := by
  unfold verifyKeyAskAt verifyKeyAskPartsAt
  cases groundOf H U.pol U.lay U.KL with
  | error e => rfl
  | ok Z =>
    show (((keyTests Z Kn H U.id k).all fun x => x.2.get) && keyLast C Z Kn chal H k) =
      (((planLine, true) :: ((keyTests Z Kn H U.id k).map fun x => (x.1, x.2.get)) ++
        [(lastLine, keyLast C Z Kn chal H k)]).all fun x => x.2)
    simp [List.all_append, List.all_map, Function.comp_def]

end Kit

/-- **verifyKeyAskRun is the one term**: the stages at the kit made for a run answer what
verifyKeyAskSmall answers, at the kit of the library's descriptions. No premise. -/
theorem verifyKeyAskRun_eq (Kn : Nat) (H : ByteArray → ByteArray) (U : User) (k : Carrier.File) :
    verifyKeyAskRun Kn H U k = verifyKeyAskSmall Kn H U k :=
  (verifyKeyAskRunAt_eq (ckPT .two) Kn (chalP .two Kn) H U k).trans
    (carry_ckPT (fun C c => verifyKeyAskAt C Kn c H U k) .two (chalP .two Kn))

/-- **The one term is the "and" of its parts.** -/
theorem verifyKeyAskSmall_parts (Kn : Nat) (H : ByteArray → ByteArray) (U : User)
    (k : Carrier.File) :
    verifyKeyAskSmall Kn H U k = (verifyKeyAskSmallParts Kn H U k).all fun x => x.2 :=
  verifyKeyAskAt_parts (ckP .two) Kn (chalP .two Kn) H U k

end Johnson.RunOne.Ask.Key

#print axioms Johnson.RunOne.Ask.Key.keyAnswer_eq
#print axioms Johnson.RunOne.Ask.Key.keyLastRun_eq
#print axioms Johnson.RunOne.Ask.Key.keyParts_answer
#print axioms Johnson.RunOne.Ask.Key.verifyKeyAskRun_eq
#print axioms Johnson.RunOne.Ask.Key.verifyKeyAskSmall_parts
