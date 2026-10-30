-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ScriptCopiesAt.lean: the closing of a segment (K10): the tie on the message of every message of a code switch's sending, kept
copies too (`msgs_of_switch_all`, AtFullSide/K10/ScriptCopies.lean), IN THE LETTERS OF THE FIRST CHAIN's THREAD AT A RETURN OF THE MAKER
(`firstThread`, Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean): the script is the base prover's; the inputs that are meant are the
thread's valid ones; the number of rounds and the seat are said as the closing's records say them (`fxAt`, `seatSw`:
Johnson/Desc/ProofFile/Honest/K10/Pay/XchSwitchPub.lean, XchSeatsAt.lean). The index's type, its reader and the opening are variables.

  `valid_okStart`       an input that the thread calls valid has a public instance that passes the description's test on the instance
  `place_of_written`    the written place of the code switch that leads into a segment is a place of the return's plan
  **`msgs_at_thread`**    at the written place pS of a segment l and EVERY message n of its sending
  **`copies_at_thread`**  the same in the form of a premise on the kept copies alone: 1 ≤ l < 25, every message but the last of which the
                        switch is not the first sender

Limits. Those of AtFullSide/K10/ScriptCopies.lean: the sizes `Sz.ref` alone; where a text answers nothing the tie says nothing. The head at
the return and the maker's return are premises. The full size and the older hash alone. No property is claimed.
-/
import AtFullSide.K10.ScriptCopies
import AtFullSide.K10.ScriptSwitch
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchSwitchPub
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchSeatsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K10
open OnBytes.HonestTrace (Sz)
open ProofFile.Honest ProofFile.Honest.FirstThread ProofFile.Honest.K10
open ProofFile.Honest.K1 (firstScriptAt LocB)
open ProofFile.Honest.K2 (SwitchPlace switchPlaces switchSent switchSeatIn switchMsgOff lotClosingAt segmentsOf firstSender)
open ProofFile.Honest.K2.Law (placesW)

variable {W₀ : Type} {I : WiderIn W₀} {Op : OnlineProverArguments} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- An input that the thread calls valid has a public instance that passes the description's test on the instance. -/
theorem valid_okStart (head : HeadAtReturn files A) (parts : FirstThreadParts A) (input v : LocB W₀)
    (hv : (firstThread head parts input).valid v) :
    (P5J.F0T OnBytes.secondHashFunction A.Z head.places head.firstChain).okStart v.x = true :=
  hv.2.1

/-- The written place of the code switch that leads into a segment is a place of the return's plan. -/
theorem place_of_written {S : Sz} (head : HeadAtReturn files A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {l : Nat} {pS : SwitchPlace} (hpw : placesW.find? (·.link == l) = some pS) : pS ∈ switchPlaces A.Z A.G := by
  obtain ⟨Bs, base₀, O⟩ := head.head.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground head.head.laid O.blank made
  rw [eG, K2.Law.places_at_head head.head.toAtMg O]
  exact List.mem_of_find?_eq_some hpw

/-- **EVERY MESSAGE OF THE SWITCH THAT LEADS INTO A SEGMENT**, in the thread's letters. -/
theorem msgs_at_thread (head : HeadAtReturn files A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (input : LocB W₀) {l : Nat} {pS : SwitchPlace}
    (hpw : placesW.find? (·.link == l) = some pS) {n : Nat} (hn : n < (switchSent pS.sizes pS.others).size) :
    OwnMsgs (firstScriptAt I Sz.ref Op A head.firstChain)
      (firstThread head ⟨firstScriptAt I Sz.ref Op A head.firstChain, numbers⟩ input).valid (fxAt head.firstChain pS)
      (P5J.At.arr A.Z (seatSw A.Z pS n).1 (seatSw A.Z pS n).2) (fxAt head.firstChain pS)
      (switchMsgOff 0 (widerRows Sz.ref A.Z A.G) (fun v => ⟨v.trace, I.weights A.Z v.w₀, v.rc⟩)
        (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) pS n) := by
  have hP := place_of_written head made hpw
  obtain ⟨q, -, e1, -⟩ := seat_of_switch head.head made hP hn
  have es : seatSw A.Z pS n = (q.j, q.t) := by
    unfold seatSw
    rw [e1]
    rfl
  rw [es]
  exact msgs_of_switch_all head.head made _ (fun v hv => valid_okStart head _ input v hv) hP hn e1

/-- **THE KEPT COPIES**, as a premise on them reads. -/
theorem copies_at_thread (head : HeadAtReturn files A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (input : LocB W₀) :
    ∀ (l : Nat) (pS : SwitchPlace), 1 ≤ l → l < 25 → placesW.find? (·.link == l) = some pS →
      ∀ n, n + 1 < (switchSent pS.sizes pS.others).size → firstSender pS n = false →
      OwnMsgs (firstScriptAt I Sz.ref Op A head.firstChain)
        (firstThread head ⟨firstScriptAt I Sz.ref Op A head.firstChain, numbers⟩ input).valid (fxAt head.firstChain pS)
        (P5J.At.arr A.Z (seatSw A.Z pS n).1 (seatSw A.Z pS n).2) (fxAt head.firstChain pS)
        (switchMsgOff 0 (widerRows Sz.ref A.Z A.G) (fun v => ⟨v.trace, I.weights A.Z v.w₀, v.rc⟩)
          (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) pS n) :=
  fun _ _ _ _ hpw n hn _ => msgs_at_thread head made numbers input hpw (by omega)

end AtFullSide.K10

#print axioms AtFullSide.K10.valid_okStart
#print axioms AtFullSide.K10.place_of_written
#print axioms AtFullSide.K10.msgs_at_thread
#print axioms AtFullSide.K10.copies_at_thread
