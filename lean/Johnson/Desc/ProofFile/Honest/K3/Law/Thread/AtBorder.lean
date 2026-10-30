-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AtBorder.lean: the honest side of the kind "lookup"
(K3): what the first chain's thread gives at the border in front of a lookup's sub-protocol. The
thread is the frame's (Honest/Thread/Thr.lean, Honest/Thread/First.lean): a form of a hypothesis.
General in the first chain's letters. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there thread, border, letters, frame, half, seat, site, member,
step and coins. In this file: L is the structure of the first chain's letters (`Letters`,
Honest/Thread/First.lean), and b is a border's number. The table of borders is
Johnson/Desc/First/Borders.lean, whose head calls it the table of joints; its promise at a border is
`onAt`.

What is shown.
  `k3At_honest`: the frame's honest letters (`honest`, First.lean) change none of the fields of
    which the library's `K3At` (Johnson/Desc/First/Look/K3At.lean) speaks.
  `failed_of_thr`: the thread's clause on the form: the state bears no mark (`s.failed = none`).
  `onAt_of_thr`: the same clause: the table's promise at the border.
  `heard_of_thr`: the thread's clause on the challenges: as many were heard as there are rounds in
    front.
  `front_thr_calls`, `front_thr_digits`: so the state in front of a lookup's sub-protocol is as the
    theorems on the lookup ask it (`FrontOk`, Honest/K3/Law/Thread/Front.lean).

Hypotheses that remain, in the last two. All are public but the thread.
  `h`: the thread at the border (`Thr`).
  `hK`: `K3At` of the letters' meaning of the promise.
  `hfit`: the test on the promise's table passes (`pubFit`).
  `hk`, `hl`, `hs`, `hpc`, `hpa`, `hlook`: where the sub-protocol stands: its place at the border,
    its link and the link's sort, its piece, and the lookup's place.

Imported. Files under Honest/Thread/.

Users. Honest/K3/Law/Thread/SiteThr.lean calls the first four;
Honest/K3/Law/Thread/AtThreadSite.lean calls `failed_of_thr`, and Honest/K3/Law/Thread/Plays.lean
calls `heard_of_thr`.

Limits. Nothing is shown of any run: the thread is a hypothesis. No instance of these hypotheses is
exhibited in this file. Nor is a thread of a description.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.FrontAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff)
open VerifiableInference.Desc (Place Strs Wit)
open VerifiableInference.Desc.K3 (seatCalls seatDigits pieceAt)
open VerifiableInference.Desc.First (ModelPart Meaning onAt pubFit pubSets openSets start shift)
open VerifiableInference.Desc.First.Look (P Sent lookAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (K3At K3Letters)
open ProofFile.Honest.FirstThread (Letters honest noStrs)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **The frame's honest letters change none of the fields of which `K3At` speaks.** -/
theorem k3At_honest {Pp Cells Tok : Type} {X : OnBytes.Model.Verify.Public} {D : Sent}
    {Lk : K3Letters Cells Tok} {Mg : Meaning Pp (Wit Cells Tok MsgT)} (hK : K3At X D Lk Mg)
    (ans : Nat → Nat → Pp × FS → Strs → Wit Cells Tok MsgT → Prop)
      (test : Nat → FS → Option String) :
    K3At X D Lk (honest Mg ans test) :=
  ⟨hK.lookIn, hK.lookOut, hK.linkFresh, hK.left, hK.leftOn, hK.pLeft, hK.pLeftOn, hK.worth⟩

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)
  {b : Nat} {k : Coins Bk} {s : FS} {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env}

/-- The thread's clause on the form: the state bears no mark. -/
theorem failed_of_thr (h : Thr L.thread b k s m E) : s.failed = none :=
  Option.isNone_iff_eq_none.1 h.2.2.1.1

/-- The same clause: the promise of the table of borders at the border, at the honest letters, at no
oracle. -/
theorem onAt_of_thr (h : Thr L.thread b k s m E) :
    onAt L.N L.mgP L.links L.ps[b]? (((openSets L.links L.ps (start L.links))[b]?).getD [])
      (((pubSets L.mgP.more L.links L.ps)[b]?).getD []) (L.pubOf m.st.input.x, s) noStrs :=
  h.2.2.1.2

/-- The thread's clause on the challenges: as many were heard as the members in
front have rounds. -/
theorem heard_of_thr (h : Thr L.thread b k s m E) : m.st.heard.length = roundsTo L.bs b := by
  have e := Thread.heard_length L.thread h.2.1
  have e0 : L.thread.front = 0 := rfl
  rw [e0, Nat.zero_add] at e
  exact e

variable {X : OnBytes.Model.Verify.Public} {D : Sent} {Lk : K3Letters Cells Tok}

/-- **In front of the sub-protocol of a link's lookup on the calls the verifier's state bears no
mark and is as the theorems on the lookup ask it.** Conditional on the thread at the border, `K3At`,
the table's test and the sub-protocol's place. No instance of these hypotheses is exhibited in this
file. -/
theorem front_thr_calls (hK : K3At X D Lk L.MgP) {Cl' : Type} (claim : Aff → Cl') (a : Place)
    (i : Nat)
    (sub : ModelPart) {x : VerifiableInference.Desc.First.Look.Place}
    (hfit : pubFit L.MgP.more L.links L.ps = true) (hk : L.ps[b]? = some a) (hl : a.link = some i)
    (hs : L.links[i]? = some sub) (hpc : a.piece = 2 + shift sub)
    (hpa : pieceAt X i false = 2 + shift sub) (hlook : lookAt X i false = some x)
    (h : Thr L.thread b k s m E) :
    s.failed = none ∧ ∃ hh F, FrontOk (seatCalls claim)
      (P.ofPlace (OnBytes.Params.settingOf X.P.frame) false x) hh s F :=
  ⟨failed_of_thr L h, front_at_calls (k3At_honest hK L.ans L.test) claim L.N L.links L.ps b a i sub
    hfit
    hk hl hs hpc hpa hlook _ s noStrs (onAt_of_thr L h) (failed_of_thr L h)⟩

/-- **The same in front of the sub-protocol of a link's lookup on the digits.** Conditional on the
same. No instance of these hypotheses is exhibited in this file. -/
theorem front_thr_digits (hK : K3At X D Lk L.MgP) {Cl' : Type} (claim : Aff → Cl') (a : Place)
    (i : Nat)
    (sub : ModelPart) {x : VerifiableInference.Desc.First.Look.Place}
    (hfit : pubFit L.MgP.more L.links L.ps = true) (hk : L.ps[b]? = some a) (hl : a.link = some i)
    (hs : L.links[i]? = some sub) (hpc : a.piece = 7 + shift sub)
    (hpa : pieceAt X i true = 7 + shift sub) (hlook : lookAt X i true = some x)
    (h : Thr L.thread b k s m E) :
    s.failed = none ∧ ∃ hh F, FrontOk (seatDigits claim)
      (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x) hh s F :=
  ⟨failed_of_thr L h, front_at_digits (k3At_honest hK L.ans L.test) claim L.N L.links L.ps b a i sub
    hfit
    hk hl hs hpc hpa hlook _ s noStrs (onAt_of_thr L h) (failed_of_thr L h)⟩

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.k3At_honest
#print axioms ProofFile.Honest.K3.Law.AtThr.failed_of_thr
#print axioms ProofFile.Honest.K3.Law.AtThr.onAt_of_thr
#print axioms ProofFile.Honest.K3.Law.AtThr.heard_of_thr
#print axioms ProofFile.Honest.K3.Law.AtThr.front_thr_calls
#print axioms ProofFile.Honest.K3.Law.AtThr.front_thr_digits
