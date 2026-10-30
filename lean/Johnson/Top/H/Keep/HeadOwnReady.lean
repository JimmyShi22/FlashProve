--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
NOT TRIED FOR EMPTINESS AT ANY REAL PLACE.
Johnson/Top/H/Keep/HeadOwnReady.lean: THE FOUR ENDS OF Johnson/Top/H/Keep/HeadOwnAtSeat.lean AGAIN,
WITH THE NAMED PREMISE ON THE STATE IN FRONT IN THE SHAPE IN WHICH ANOTHER HOUSE's THEOREM ENDS:
hReady' : ∀ z U, seenOf s = some z → s.fork? = some U → K6Ready h iU3 p z U. Statements and proofs:
calls.

OBJECT: the other house's Sees, seenOf, K6Ready (Johnson/Desc/Kinds/Law/RunsStill.lean).
USER: nobody yet. Meant: whoever holds K6Ready in front of the head's lookup on the digits along
  "reached" (Johnson/P5J/K03ReadyAt345.lean: k03_ready_345; NOT IMPORTED: it lay not in our lane).
LETTERS: those of HeadOwnAtSeat.lean.

NOT TYPECHECKED BY US: that k03_ready_345 meets hReady' as it is typed here.

Main names:
  ready_of_seen: hReady' gives HeadOwnAtSeat.lean's hReady, where a ledger is open at s.
  own_fwd_ready, own_formsIn_pass_ready; join_fwd_ready, join_formsIn_pass_ready.

Limits. Those of HeadOwnAtSeat.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.HeadOwnAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (seatCalls joinRun unpaid)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink formsIn holesAt)
open VerifiableInference.Desc.Kinds.Head (seatAt asClaim callerKeys)
open VerifiableInference.Desc.Kinds.Head.Law (SamePlanes Alike K6States K6Ready Sees seenOf)
open VerifiableInference.Reads.Pass (Fwd)

/-- From "shows z, and a ledger U is open" to "stands in the head's link, shows z, its ledger is
U". -/
theorem ready_of_seen (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Desc.Kinds.Head.Par) {s : S}
    {F : Fork} (hF : s.fork? = some F)
    (hR : ∀ z U, seenOf s = some z → s.fork? = some U → K6Ready h iU3 p z U) :
    ∀ z U, Sees s z U → K6Ready h iU3 p z U := by
  rintro z U ⟨o, ho, rfl, rfl⟩
  have hop : o.opened = true := by
    cases hc : o.opened with
    | true => rfl
    | false => simp [S.fork?, ho, hc] at hF
  exact hR _ _ (by simp only [seenOf, ho]) (by simp [S.fork?, ho, hop])

section
variable (X : Verify.Public) (mH m : ℕ) (hm : (m == mH) = true) (l : Link S Claim) (b : ℕ)
  (own : List (ℕ × ℕ)) (h : OnBytes.Model.Head.Shape) (iU3 lk piece : ℕ)
  (p : Desc.Kinds.Head.Par) {s s' : S} {F G : Fork} (P : K3Pass s s' F G) (A : SamePlanes s s')
  (a : Alike s s') (K : K6States h iU3 p lk piece (statesOfLink l) b)
  (hR : ∀ z U, seenOf s = some z → s.fork? = some U → K6Ready h iU3 p z U)
include hm P A a K hR

section Own
variable
  (hBo : ∀ name run run', (statesOfLink l b).find? (fun r => r.1 == name) = some (name, run) →
    (Desc.Kinds.Head.kind asClaim (seatAt h iU3) lk piece p).claims.lookup name = some run' →
    ∀ k t y, run' k t = .ok y → y.2.out.reply = t.out.reply → run k t = .ok y)
include hBo

theorem own_fwd_ready {name : String} (hn3 : name = "norm" ∨ name = "policy" ∨ name = "logits") :
    Fwd (readersOfLink (holesAt X mH m l) l) b name s s' :=
  own_fwd_seat X mH m hm l b h iU3 lk piece p P A a K (ready_of_seen h iU3 p P.front hR) hBo hn3

theorem own_formsIn_pass_ready {name : String}
    (hn3 : name = "norm" ∨ name = "policy" ∨ name = "logits")
    (hin : formsIn (readersOfLink (holesAt X mH m l) l) own b name s = true) :
    formsIn (readersOfLink (holesAt X mH m l) l) own b name s' = true :=
  own_formsIn_pass_seat X mH m hm l b own h iU3 lk piece p P A a K
    (ready_of_seen h iU3 p P.front hR) hBo hn3 hin

end Own

section Join
variable
  (hBj : ∀ run, (statesOfLink l b).find? (fun r => r.1 == "join") = some ("join", run) →
    ∀ k t y, joinRun (seatCalls asClaim) (callerKeys p (seatAt h iU3)) k t = .ok y →
      y.2.out.reply = t.out.reply → run k t = .ok y)
  (hA : AtS2 (seatCalls asClaim))
  (hh : (seatCalls asClaim).heard s' = (seatCalls asClaim).heard s)
  (hob : ∀ i, unpaid G i = true → unpaid F i = true)
include hBj hA hh hob

theorem join_fwd_ready : Fwd (readersOfLink (holesAt X mH m l) l) b "join" s s' :=
  join_fwd_seat X mH m hm l b h iU3 lk piece p P A a K (ready_of_seen h iU3 p P.front hR) hBj hA hh
    hob

theorem join_formsIn_pass_ready
    (hin : formsIn (readersOfLink (holesAt X mH m l) l) own b "join" s = true) :
    formsIn (readersOfLink (holesAt X mH m l) l) own b "join" s' = true :=
  join_formsIn_pass_seat X mH m hm l b own h iU3 lk piece p P A a K
    (ready_of_seen h iU3 p P.front hR) hBj hA hh hob hin

end Join

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.ready_of_seen
#print axioms VerifiableInference.OnPublicFiles.own_fwd_ready
#print axioms VerifiableInference.OnPublicFiles.own_formsIn_pass_ready
#print axioms VerifiableInference.OnPublicFiles.join_fwd_ready
#print axioms VerifiableInference.OnPublicFiles.join_formsIn_pass_ready
