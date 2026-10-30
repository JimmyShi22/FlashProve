-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/FamCutQ.lean: **THE FAST FAMILY FOR A LONG EVALUATION AT ANY bk: NO STUB.**
  Johnson/PV/FamCutL.lean paid for «no query held under the proof file's tag» with a constant bk.
  HERE THE PRICE FALLS: at a chain query under the proof file's tag that FITS and whose
calls ALL lie in the format's domain, no block goes behind the escape: so the kept function needs
  neither bk nor the query. Whether all K + 1 calls lie in the domain is ONE test a query
  (OnceJ.allIn): a row's calls part in the half and the call's number alone, and neither
the domain's test nor the bytes' length hangs on these (size_roundBytes | half_ok:
  OnBytes/K/Arm/CallDom.lean). At every other query (the three first calls of a file; a query that
  does not fit) the kept function holds the query and bk, as famCut's.
  OnceJ.allIn c · allIn_call: where it says yes every block's call is there, in callIn and in inDom
    · rowBytes_free: there rowBytes does not read the escape
  famCutQ P ΦK ΦP R bk O mK mP
  **famCutQ_eq : famCutQ P ΦK ΦP R bk O mK mP = famCut P ΦK ΦP R bk O**: AT EVERY bk AND EVERY HINT;
    no premise.
SO WHAT RUNS CAN BE THE FAMILY OF THE m WHOSE bk IS ONE TO ONE. Under the key file's tag the query
  is held, as before (the seeds' spelling reads it). What an evaluator keeps is the run's to show.
  No soundness.


-/
import Johnson.PV.FamCutL
import OnBytes.K.Arm.CallDom

set_option autoImplicit false

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
    TypedOracleCompiler.Run.PageRun
open OnBytes.K.Arm OnBytes.K.Arm.FileInj OnBytes.Maker OnBytes.Maker.Page Johnson.RunOne
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bitsOfByte bytesToBits bitsToBytes toBytes strOf digS roundBytes blockNo)

/-- Do all calls of a chain query lie in the format's domain? One test a query. No at a query of
  which one block alone has a call. -/
def allIn : OnceJ → Bool
  | .row lab idx st msg kind work nonce _ => Fmt.hDom 162 lab idx st (roundBytes msg kind work 0
      nonce)
  | _ => false

/-- The domain's test at the number 162 reads the bytes' length alone. -/
theorem hDom_162 (lab idx : ℕ) (st b b' : ByteArray) (h : b.size = b'.size) :
    Fmt.hDom 162 lab idx st b = Fmt.hDom 162 lab idx st b' := by
  unfold Fmt.hDom Fmt.leafOK
  rw [h]
  rfl

/-- Where the test says yes, every block has a call, in both domains. -/
theorem allIn_call (c : OnceJ) (h : allIn c = true) (K : ℕ) (j : Fin (K + 1)) :
    ∃ cl, c.call K j = some cl ∧ callIn cl = true ∧ inDom cl = true := by
  cases c with
  | row lab idx st msg kind work nonce ow =>
    refine ⟨_, rfl, ?_, ?_⟩
    · show Fmt.hDom 162 lab idx st (roundBytes msg kind work (blockNo ow K j / 2) nonce) = true
      rw [hDom_162 lab idx st _ (roundBytes msg kind work 0 nonce)
        (by rw [size_roundBytes, size_roundBytes])]
      exact h
    · show ((UInt8.ofNat (blockNo ow K j % 2) == 0 || UInt8.ofNat (blockNo ow K j % 2) == 1) &&
        Fmt.hDom 162 lab idx st (roundBytes msg kind work (blockNo ow K j / 2) nonce)) = true
      rw [half_ok, Bool.true_and, hDom_162 lab idx st _ (roundBytes msg kind work 0 nonce)
        (by rw [size_roundBytes, size_roundBytes])]
      exact h
  | tail _ => cases h
  | nothing => cases h

/-- There the bytes of a block do not read the escape. -/
theorem rowBytes_free (c : OnceJ) (h : allIn c = true) (K : ℕ) (j : Fin (K + 1)) (e e' : Unit → List
    Bool) :
    rowBytes true (c.call K j) e = rowBytes true (c.call K j) e' := by
  obtain ⟨cl, h1, h2, h3⟩ := allIn_call c h K j
  rw [h1]
  unfold rowBytes
  simp only [h2, h3, Bool.and_self, if_true]

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}
  (P : PageJ L K) (ΦK : FitJ L .test) (ΦP : FitJ L .onl) (R : RunJ P)
  (bk : AllPts 256 K L → List Bool) (O : ByteArray → ByteArray) (mK mP : ℕ → ℕ)

/-- **The answer to a typed query as data.** -/
def famCutQB : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf 256 L o → AnsC K
  | .fb .test, q =>
    let fit := fitPart ΦK q.round q.rt q.plain q.head
    let c := R.key q
    .cells (cellsOf K (mK q.round) fun j =>
      match P.seeds (q, j) with
      | some s => O (toBytes s)
      | none => O (rowBytes fit (c.call K j) fun _ => bk (.inl (fbPt .test q j))))
  | .fb .onl, q =>
    let fit := fitPart ΦP q.round q.rt q.plain q.head
    let c := R.proof q
    if fit && allIn c then .cells (cellsOf K (mP q.round) (blockP O (fun _ => []) K true c))
    else .cells (cellsOf K (mP q.round) fun j => O (rowBytes fit (c.call K j) fun _ => bk (.inl
        (fbPt .onl q j))))
  | o, q => .arr (famRunB (fun _ => L) (cutAll (bothOf P ΦK ΦP)) bk O o q)

/-- **The typed oracle functions, for a long evaluation, at any bk.** -/
def famCutQ : Fam (typedOracleFamily 256 K L) := fun o q => decC K o (famCutQB P ΦK ΦP R bk O mK mP o q)

/-- **THE EQUATION: AT EVERY bk AND EVERY HINT IT IS famCut.** No premise. -/
theorem famCutQ_eq : famCutQ P ΦK ΦP R bk O mK mP = famCut P ΦK ΦP R bk O := by
  funext o q
  cases o with
  | fb t =>
    cases t with
    | test =>
      show decC K (.fb .test) (.cells (cellsOf K (mK q.round) _)) =
        decRun K (.fb .test) (PageRun.thunksOf (K + 1) _)
      rw [decC_fb, decRun_fb] <;> rfl
    | onl =>
      show decC K (.fb .onl) (if (fitPart ΦP q.round q.rt q.plain q.head && allIn (R.proof q)) =
          true then _ else _) =
        decRun K (.fb .onl) (PageRun.thunksOf (K + 1) _)
      by_cases hh : (fitPart ΦP q.round q.rt q.plain q.head && allIn (R.proof q)) = true
      · rw [if_pos hh, decC_fb, decRun_fb]
        rw [Bool.and_eq_true] at hh
        have e : ∀ j : Fin (K + 1), blockP O (fun _ => []) K true (R.proof q) j =
            O (rowBytes (fitPart ΦP q.round q.rt q.plain q.head) ((R.proof q).call K j)
              fun _ => bk (.inl (fbPt .onl q j))) := fun j => by
          unfold blockP
          rw [hh.1]
          exact congrArg O (rowBytes_free _ hh.2 K j _ _)
        refine Prod.ext ?_ ?_
        · funext k
          exact congrArg digS (e k.castSucc)
        · exact congrArg digS (e (Fin.last K))
      · rw [if_neg hh, decC_fb, decRun_fb] <;> rfl
    | link => rfl
  | _ => rfl

end W4M

#print axioms W4M.allIn_call
#print axioms W4M.famCutQ_eq
