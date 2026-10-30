-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/BehindCallsR.lean: the honest side of the kind "lookup"
(K3): THE THREAD'S CLAUSE ON THE FORM, ONE BORDER ON, at the sub-protocol of a link's lookup on the
calls, OVER THE LIBRARY'S RULE IN ITS SECOND FORM (`calls_behindR`,
Johnson/Desc/First/Look/K3CallsBehindR.lean). A sorting and one call. General in the first chain's
letters.

  `form_callsR`   CONDITIONAL, see below: `L.thread.Form (b + 1) k s' m'`

WHY THE SECOND FORM. Honest/K3/Law/Thread/BehindCalls.lean [not in this library]'s `form_calls`
stands over the first form, whose premise `BehindParts` asks that the public item of the name
"frame.liveIs" be open in front (askLive) and says what it means (fLive). The library's composed
meaning strikes that name from its list of extra public tests (`First.leavesName`,
Johnson/Desc/First/SmallDoor.lean; Johnson/Desc/Sound/MgAll.lean), and the frame's letters at the
library's own lay that meaning: SO AT THESE LETTERS `form_calls` CAN NEVER BE CALLED. The second
form's `BehindPartsR` has neither field. The library pays it at its composed meaning
(Johnson/Desc/Sound/MgAt/K3Calls.lean), at a letter for "accepts" of its own.

WHAT IT ASKS. Of the run: the thread in front; that the input stays. Of the two states: an
acceptance in the sense of the letter "Yes" (hY: an acceptance by the decision of the library's
first sub-protocol for the kind, `K3.block`, at rounds whose words are below the prime); "the same
but for what the lookup lays" (`SameBut`); the library's promise behind (`k3OnOut`); no mark of
failure behind. AND `BehindPartsR` AT THE LETTERS' MEANING OF THE PROMISE, AT THE HONEST LETTERS.
THE LIBRARY'S LETTER Rc, HERE "Reach" (meant: "this state is reached from the start by the
sub-protocols in front"), STAYS A LETTER: six fields of `BehindPartsR` are asked at states of which
it holds alone, and that it holds of the state in front is a premise (hr). Laid as the condition
that always holds it would ask these six at every state: more than the library pays. No instance of
these hypotheses is exhibited in this file.

Limits. On the verifier's side alone. The thread's letters "rides" and "keeps" are not spoken of.
Nothing on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Look.K3CallsBehindR
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.Behind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff)
open VerifiableInference.Desc (Place Oracle)
open VerifiableInference.Desc.K3 (k3OnOut seatCalls)
open VerifiableInference.Desc.First (onAt pubSets openSets start)
open VerifiableInference.Desc.First.Look (P)
open VerifiableInference.Desc.Sound (MsgT Frame strsOf onQ)
open VerifiableInference.OnPublicFiles (SameBut BehindPartsR calls_behindR)
open ProofFile.Honest.FirstThread (Letters noStrs)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)

/-- **CONDITIONAL ON what this file's head lists: behind the sub-protocol of a link's lookup on the
calls the thread's clause on the form holds one border on.** Fr, y₀: any frame of the library's and
any of its strings: the promise reads none. No instance of these hypotheses is exhibited in this
file. -/
theorem form_callsR {Cl' : Type} (claim : Aff → Cl') (Fr : Frame) (y₀ : Fr.E.Str)
    {x : VerifiableInference.Desc.First.Look.Place} {set : OnBytes.Params.Setting}
    {b i pc : Nat} {arrs : Array (Nat × String)} {p p' : Place} {told : List (List Oracle)}
    {Yes : FS × Fr.E.Str → FS × Fr.E.Str → Prop} {Reach : FS × Fr.E.Str → Prop}
    {k : Coins Bk}
    {s s' : FS}
    {m m' : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env}
    (hs : (P.ofPlace set false x).shape = some x.fs)
    (hY : ∀ u c, Yes u c →
      ∃ (piece : Nat) (laid : Array Nat) (before : List (Nat × Nat))
        (guests : List (VerifiableInference.Desc.First.Look.Guest FS Cl')) (rs : List Fmt.RoundView)
        (cols : List (List (Nat × List UInt64))),
        VerifiableInference.OnPublicFiles.okRoundsE rs = true ∧
        (VerifiableInference.Desc.K3.block (seatCalls claim) piece laid before
          (P.ofPlace set false x) guests).decide u.1 rs cols = .ok c.1)
    (B : BehindPartsR (Fr := Fr) x set L.N L.mgP L.links L.ps (L.pubOf m.st.input.x) b i pc arrs p
      p' told Yes Reach)
    (hA : Thr L.thread b k s m E) (hr : Reach (s, y₀)) (hm : m'.st.input = m.st.input)
    (hy : Yes (s, y₀) (s', y₀)) (hsb : SameBut s s')
    (hout : k3OnOut (P.ofPlace set false x) s' = true) (hf : s'.failed = none) :
    L.thread.Form (b + 1) k s' m' := by
  have hon : onQ (Fr := Fr) L.N L.mgP L.links L.ps (fun t => (L.pubOf m.st.input.x, t)) b
      (s, y₀) := onAt_strs (strsOf Fr y₀) (onAt_of_thr L hA)
  have hnext := calls_behindR claim hs hY B (s, y₀) (s', y₀) hon hr (failed_of_thr L hA) hy
    hsb hout trivial
  refine ⟨?_, ?_⟩
  · show s'.failed.isNone = true
    rw [hf]
    rfl
  · show onAt L.N L.mgP L.links L.ps[b + 1]?
      (((openSets L.links L.ps (start L.links))[b + 1]?).getD [])
      (((pubSets L.mgP.more L.links L.ps)[b + 1]?).getD []) (L.pubOf m'.st.input.x, s') noStrs
    rw [hm]
    exact onAt_strs noStrs hnext

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.form_callsR
