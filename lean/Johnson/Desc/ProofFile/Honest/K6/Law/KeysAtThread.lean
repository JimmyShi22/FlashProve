-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/KeysAtThread.lean: THE OUTPUT HEAD'S OWN ROUNDS, AT A CHAIN'S
THREAD: THE KEYS' SENTENCE HOLDS IN FRONT OF THE MEMBER (Johnson/Desc/Kinds/Law/JoinFromFront.lean:
KeysTrueInFront), AT WHAT THE LAW READS OFF THE THREAD'S WITNESS (Law/K6Cut.lean: compCut), AT EVERY
CONTINUATION: the field "keys" of K6Script (Honest/K6/Law/OutAtThread.lean) at that reader.
WHAT IT IS NOT. CONDITIONAL ON TWO MORE STRUCTURES OF PREMISES, K6KeysLetters AND K6KeysFront, WHICH
ARE SHOWN HERE OF NO THREAD; beside K6Fronted and the member's test on the plan. It calls:
keys_back_left (Law/KeysRoadBack.lean) has fifteen premises; each is laid here from a named field or
from the state in front. The thread T and the sentence Said are variables. The letter r
(K6Fronted's: how many numbers of the ledger are left free) reaches no conclusion. The row of the
mask's places is at rb := 0: the library's mask_mg speaks there alone. The sizes d = 5120 and V =
202048 are premises: the library's sameCells_mg asks them: SO K6KeysLetters HAS NO MEMBER AT ANY
SMALL SIZE, and no example by evaluation can stand beside this law. Nothing on soundness, on
completeness or on what a proof hides.
  K6KeysLetters   WHAT THE THREAD'S LETTERS ARE ASKED TO MEET: no state of a run stands in it.
       opened     the item is open at the border: the table's own rows (it is an "in" of this
                  member's row).
       means      what the thread's item says gives the composed meaning's worth 24 3 "keys": at the
                  first chain's thread by unfolding, as Share.lean's k6_means_at the other way.
       meets, named, inRange   on the data and the witness at valid inputs: the library's
                  CallerMeets; "each seat is named once"; the witness's cells are in range.
       ranges, inFour, laid, d, V, nums, calls   on public numbers.
  K6KeysFront     ON THE STATE IN FRONT, each from the pair ThrS T Said:
       left24     what the public item left 24 says beside its test: K6FrontItems.left
                  (Johnson/Desc/K6/Honest/Law/FrontItems.lean) has it of the table's promise.
       tokSmall   every element in the reply's seat is an entry of the vocabulary
                  (Law/TokenSmall.lean: TokSmall): a fact on reached states, which the next token's
                  sub-protocol makes and every step that leaves the reply keeps; no item of the
                  table says it (the public test on the token's size reads the element's first word
                  alone). With replyTok_is (Law/ReplyTokIs.lean) the state's two readers of the
                  reply agree.
       request    the data's request off the public part is the seat's reading of the state.
  keys_at_thread  THE TOP.
CALLED: keys_back_left, sameCells_mg, mask_mg, replyTok_is, given_of_parts, planFacts,
K6MemberIs.plan, start_pays, tokSmall_pays.
OF THE FOLDER Johnson/Goal/ it names Meaning.sizesOf and Meaning.laidThere, as arguments of the
library's compCut, seatLay and sameCells_mg; nothing else of that folder is called.

-/
import Mathlib
import Johnson.Desc.ProofFile.Honest.K6.Law.OutAtThread
import Johnson.Desc.Kinds.Law.KeysRoadBack
import Johnson.Desc.Kinds.Law.K6GivenOfLeft
import Johnson.Desc.Kinds.Law.ReplyTokIs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Model.Verify (borderOf)
open OnBytes.Params (ReqLayout)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll)
open ProofFile.Honest (Thread ThrS ProverCoinCounts Coins Local Mid drawsFit)
open ProofFile.Honest.K6 (K6Seated K6Fronted K6Script HeadAsk k6_out_at_thread)

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X Pb Xi P Tok : Type} {rows cols nR : ℕ}
  {Wp : OnBytes.Model.Verify.Public}

/-- **WHAT THE THREAD'S LETTERS ARE ASKED TO MEET, FOR THE KEYS.** iK: the thread's item for worth
24 3 "keys". x: the place of the lookup on the head's calls. A definition: a premise's form. Nothing
is claimed of it. -/
structure K6KeysLetters
    (T : Thread Bk S Claim (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X Pb) (b : Nat)
    (iK : T.ι)
    (toP : T.P → P) (toW : T.Wt → Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (Dof : Local W₀ Rc ProofFile.Inst Tr → MgData Xi P Tok rows cols nR Wp)
    (Mg₀ : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ) (n : ℕ) (x : First.Look.Place) : Prop where
  opened : iK ∈ T.opened b
  means : ∀ w a y v, T.means w iK a y v →
    (mgAll (Dof w) Mg₀).worth 24 3 "keys" (toP a.1, a.2) y (toW v)
  meets : ∀ w, T.valid w → CallerMeets (Dof w) lay6 num n x
  named : ∀ w, T.valid w → ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
    r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
    ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
    Sound.namedOnce (Dof w).arr (Dof w).N 24 (seatLay Wp lay6 num 24 μ r c).1 = true
  inRange : ∀ k w hd, T.valid w →
    VerifiableInference.OnPublicFiles.Flat.InRange (toW (T.wit k w hd)).cells
  ranges : @InRanges (parOf Wp.hS (workOf Wp)).sizes Wp.hS Wp.HLy (borderOf Wp.y)
  inFour : ∀ a r c, InFour Wp.hS Wp.HLy (borderOf Wp.y) a r c →
    a < (Meaning.sizesOf Wp 24).NM ∧ c < (Meaning.sizesOf Wp 24).k a ∧
      r < (Meaning.sizesOf Wp 24).m a
  laid : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay6 = true
  d : Wp.hS.d = 5120
  V : Wp.hS.V = 202048
  nums : FoNums.ok x.fs = true
  calls : x.fs.NC = 6

/-- **ON THE STATE IN FRONT, FOR THE KEYS**, each from the pair "the thread and what is said". A
definition: a premise's form. Nothing is claimed of it. -/
structure K6KeysFront
    (T : Thread Bk S Claim (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (b : Nat) (toP : T.P → P)
    (Dof : Local W₀ Rc ProofFile.Inst Tr → MgData Xi P Tok rows cols nR Wp) : Prop where
  left24 : ∀ k s m E, ThrS T Said b k s m E → VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 s
  tokSmall : ∀ k s m E, ThrS T Said b k s m E → TokSmall Wp.hS.V s
  request : ∀ k s m E, ThrS T Said b k s m E →
    (Dof m.st.input).rq (toP (T.seat k m s).1) = (seatAt Wp.hS (readsOf Wp)).request s

variable {T : Thread Bk S Claim (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X Pb}
  {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {b : Nat} {iK : T.ι}
  {toP : T.P → P} {toW : T.Wt → Wit (Fin rows → Fin cols → GE) Tok MsgT}
  {Dof : Local W₀ Rc ProofFile.Inst Tr → MgData Xi P Tok rows cols nR Wp}
  {Mg₀ : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
  {lay6 : ReqLayout} {num : ℕ → ℕ → ℕ} {n : ℕ} {x : First.Look.Place}
  {blk : Block S Claim} {r : Nat}

/-- **THE KEYS' SENTENCE IN FRONT OF THE MEMBER, AT WHAT THE LAW READS OFF THE THREAD'S WITNESS, AT
EVERY CONTINUATION.** -/
theorem keys_at_thread (L : K6KeysLetters T b iK toP toW Dof Mg₀ lay6 num n x)
    (Fk : K6KeysFront T Said b toP Dof) (Hf : K6Fronted T Said b Wp r blk)
    (hpl : blk.planOk = true) :
    ∀ k s m E, ThrS T Said b k s m E → ∀ ds, KeysTrueInFront Wp s
      (compCut (Dof m.st.input).cs (Dof m.st.input).arr (Dof m.st.input).ms (Dof m.st.input).N
        (Meaning.sizesOf Wp) (seatLay Wp lay6 num) Wp (plAt n 0)
        (toW (T.wit k m.st.input (m.st.heard ++ ds)))).1
      (compCut (Dof m.st.input).cs (Dof m.st.input).arr (Dof m.st.input).ms (Dof m.st.input).N
        (Meaning.sizesOf Wp) (seatLay Wp lay6 num) Wp (plAt n 0)
        (toW (T.wit k m.st.input (m.st.heard ++ ds)))).2 := by
  intro k s m E hT ds
  have hv : T.valid m.st.input := hT.1.2.2.2.2.2.2
  have hitem := L.means _ _ _ _ (hT.1.2.2.2.1 ds iK L.opened)
  have R := Hf.front k s m E hT
  obtain ⟨z, y0, hz, hy0, hP⟩ := R.letters
  obtain ⟨g0, hg0⟩ := given_of_parts _ _ s z y0 hz hy0 hP
  have M := L.meets _ hv
  have hR := L.inRange k m.st.input (m.st.heard ++ ds) hv
  have hPF : (letI := (parOf Wp.hS (workOf Wp)).sizes
      letI := (parOf Wp.hS (workOf Wp)).policy
      PlanFacts) := by
    letI := (parOf Wp.hS (workOf Wp)).sizes
    letI := (parOf Wp.hS (workOf Wp)).policy
    exact planFacts (Hf.member.plan hpl).1
  exact keys_back_left Mg₀ M.fits (toP (T.seat k m s).1, s) (T.strs E) _ _ hitem hR
    (Fk.left24 k s m E hT) g0 hg0 y0 hy0
    ((replyTok_is Wp.hS.V (by rw [L.V]; decide) s (Fk.tokSmall k s m E hT)).trans hy0)
    (Fk.request k s m E hT)
    hPF (start_pays Wp s R.start) (tokSmall_pays Wp s (Fk.tokSmall k s m E hT) y0 hy0)
    (sameCells_mg M L.ranges L.inFour L.laid (L.named _ hv) (plAt n 0) _ hR L.d L.V)
    (mask_mg M _) L.nums L.calls

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.keys_at_thread
