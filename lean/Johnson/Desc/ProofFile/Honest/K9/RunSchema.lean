-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RunSchema.lean: ONE FORM FOR "MY KIND's RUN OF CLAIMS IS ACCEPTED INSIDE THE BATCHING",
with a hole for the entry of the order, AND THE THEOREM THAT GATHERS THE FILLED FORMS INTO `AcceptedS` AT THE BATCHING.

FOR A READER WHO HAS NEVER SEEN THIS KIND. The batching is one sub-protocol in each of the 25 segments. The prover sends
nothing in it; the verifier draws one element chi. Inside the same decision the verifier then calls, one behind the
other, the "runs of claims" of the segment's other sub-protocols, in the order `Lk.order` (7, 10 or 11 entries by the
sort of segment). Each run is a function `Nat → S → Except String (List Claim × S)`: it is handed the number of claims
made so far and the verifier's state, and returns its claims and a state, or refuses. Behind each run the batching makes
one test of its own on the run's claims (`Lk.each`: no claim of another kind names a slot of the smallness test's
window). If any run or test refuses, the batching refuses. So "the batching accepts the honest prover" needs, of each
run's kind, that the run returns AT THE STATE AT WHICH IT IS CALLED THERE: behind the draw and behind the runs in front.

WHAT TO FILL. For each entry j of the order that names a run of your kind: one term of `RunPays St Lk p j n`. Its fields:
  `returns`   at every state at which entry j is called (`Called`), the run in the description's own list returns, and
              the batching's test behind it accepts
  `count`     its list has at most n s claims (n: your number, which may be read off the state s in front; the sum over
              the order is held against the plan's number)
  `fits`      each of its claims fits the arrays and the number of slots behind the draw (`K9H.claimFits`)
  `mark`, `reply`   it leaves the mark of failure and the reply as they were
The last four are asked FROM A YES of the run; only `returns` asks for one.
`St s tr a` is "s is a state in front of the batching at which the honest run can stand, tr is the drawn element's
three words, a is the batching's part of s". In the gathering theorem it is `StandAt T Said b front`: the thread's
invariant holds at s, and the test `front` (the fall at the batching's own place) is silent at s and tr.

HOW TO REACH `returns` WITHOUT READING THE OTHER KINDS' RUNS. `Called Lk p s tr j cs u` is the exact set of call states;
it speaks of the runs in front. `called_since` turns it into one fact that names no run: `Since j u`, "u is the state in
front of the batching but for what the draw and the runs in front of entry j may have done", for any family `Since` that
holds behind the draw and that a yes of each run in front hands on (`RunHands`). `Transport` is `returns` asked from
`Since` alone, at every number of claims, and `returns_of_transport` passes from it to `returns`. ONE `Since` for all kinds,
written out on the state's fields, and the record that a kind fills over it, stand in Honest/K9/RunFrame.lean: A KIND's
AUTHOR FILLS THAT RECORD (`RunRecord`), NOT THIS FORM.

  `StandAt`, `Called`                     the stand in front; the states at which the runs are called
  `RunPays`                               THE FORM
  `sumTo`                                 the sum of the first j numbers
  `RunHands`, `called_since`, `Transport`, `returns_of_transport`   the road to `returns`
  **`accepted_of_runs_find`**, `accepted_of_runs`   THE GATHERING THEOREM: where the search at the batching's place finds no
                                          side; where no side of this kind stands in the list

Limits. No term of `RunPays` is made here. `accepted_of_runs` keeps four premises that are no run's: `ready` (the draw's
own guards at the stand), `plan` (the numbers' sum is at most the plan's number of claims), `clean` (no mark of failure
at a stand) and `hfall` (where the table of falls is silent at the batching's number, `front` is silent): the last is
a premise on whoever lays the table of falls. The prover has no side at the batching's place (`hn`, `hno`). It is not proved
that the invariant holds at any run. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.BatNoSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **A stand in front of the batching**: the invariant holds at s at some coins and some state of the prover's run; the
test `front` is silent at s and the drawn words tr; the batching's lens reads the part a. -/
def StandAt (T : Thread Bk S Claim V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop) (b : ℕ)
    (front : S → List Fmt.Drawn → Option String) (s : S) (tr : UInt64 × UInt64 × UInt64)
    (a : Desc.K9.Part) : Prop :=
  (∃ κ m En, ThrS T Said b κ s m En) ∧ front s [⟨[tr], [], [], none⟩] = none ∧ Desc.K9.atS.get? s = some a

/-- **The states at which the runs are called.** `Called Lk p s tr j cs u`: from s, behind a yes of the draw at tr and
yeses of the runs at the entries in front of j, each with a yes of the batching's test behind it: cs are the claims made
so far, u is the state. -/
inductive Called (Lk : Link S Claim) (p : Desc.K9.Where) (s : S) (tr : UInt64 × UInt64 × UInt64) :
    ℕ → List Claim → S → Prop
  | draw {t₁ : S} :
      (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁ →
      Called Lk p s tr 0 [] t₁
  | run {j : ℕ} {o : ℕ × String} {cs : List Claim} {u : S} {r : ClaimsRun} {z : List Claim × S} :
      Called Lk p s tr j cs u → Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r →
      r cs.length u = .ok z → Lk.each o z.1 z.2 = .ok () → Called Lk p s tr (j + 1) (cs ++ z.1) z.2

/-- **THE FORM.** St: which (state in front, drawn words, part) are spoken of. j: the entry of the order. n: a bound on
the number of the run's claims, which may be read off the state in front. -/
structure RunPays (St : S → UInt64 × UInt64 × UInt64 → Desc.K9.Part → Prop) (Lk : Link S Claim)
    (p : Desc.K9.Where) (j : ℕ) (n : S → ℕ) : Prop where
  returns : ∀ o, Lk.order[j]? = some o → ∀ s tr a cs u, St s tr a → Called Lk p s tr j cs u →
    ∃ r z, claimsRunOf Lk.hear o = some r ∧ r cs.length u = .ok z ∧ Lk.each o z.1 z.2 = .ok ()
  count : ∀ o r, Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → ∀ s tr a cs u z, St s tr a →
    Called Lk p s tr j cs u → r cs.length u = .ok z → z.1.length ≤ n s
  fits : ∀ o r, Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → ∀ s tr a t₁ a₁ cs u z, St s tr a →
    (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁ →
    Desc.K9.atS.get? t₁ = some a₁ → Called Lk p s tr j cs u → r cs.length u = .ok z →
    z.1.all (Desc.K9H.claimFits a₁.F.trees a₁.F.ns) = true
  mark : ∀ o r, Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → ∀ s tr a cs u z, St s tr a →
    Called Lk p s tr j cs u → r cs.length u = .ok z → z.2.failed = u.failed
  reply : ∀ o r, Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → ∀ s tr a cs u z, St s tr a →
    Called Lk p s tr j cs u → r cs.length u = .ok z → z.2.out.reply = u.out.reply

/-- The sum of the first j numbers. -/
def sumTo (n : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => sumTo n j + n j

/-! ## The road to `returns` -/

/-- **A run hands a family on**: from `Since j` in front of a yes of the run at entry j to `Since (j + 1)` behind it, at
every number of claims. -/
def RunHands (Since : ℕ → S → Prop) (Lk : Link S Claim) (j : ℕ) : Prop :=
  ∀ o r, Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → ∀ m u z, Since j u → r m u = .ok z →
    Since (j + 1) z.2

/-- **From the exact set of call states to a fact that names no run.** `Since j u`: "u is the state in front of the
batching but for what the draw and the runs at the entries in front of j may have done". It holds behind the draw, and
each run in front hands it on. -/
theorem called_since {Lk : Link S Claim} {p : Desc.K9.Where} {s : S} {tr : UInt64 × UInt64 × UInt64}
    (Since : ℕ → S → Prop)
    (hdraw : ∀ t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] =
      .ok t₁ → Since 0 t₁) :
    ∀ {j : ℕ} {cs : List Claim} {u : S}, Called Lk p s tr j cs u →
      (∀ i, i < j → RunHands Since Lk i) → Since j u := by
  intro j cs u h
  induction h with
  | draw hd => exact fun _ => hdraw _ hd
  | @run j o cs u r z _ ho hr hz _ ih =>
    intro hl
    exact hl j (by omega) o r ho hr _ u z (ih fun i hi => hl i (by omega)) hz

/-- **`returns`, asked from that fact alone**, at every number of claims. `Since s tr j u`: as above, at the state s in
front and the drawn words tr. -/
def Transport (St : S → UInt64 × UInt64 × UInt64 → Desc.K9.Part → Prop)
    (Since : S → UInt64 × UInt64 × UInt64 → ℕ → S → Prop) (Lk : Link S Claim) (j : ℕ) : Prop :=
  ∀ o, Lk.order[j]? = some o → ∀ s tr a m u, St s tr a → Since s tr j u →
    ∃ r z, claimsRunOf Lk.hear o = some r ∧ r m u = .ok z ∧ Lk.each o z.1 z.2 = .ok ()

/-- From `Transport` at entry j and `RunHands` at the entries in front to the field `returns`. -/
theorem returns_of_transport {St : S → UInt64 × UInt64 × UInt64 → Desc.K9.Part → Prop} {Lk : Link S Claim}
    {p : Desc.K9.Where} (Since : S → UInt64 × UInt64 × UInt64 → ℕ → S → Prop) (j : ℕ)
    (hdraw : ∀ s tr a t₁, St s tr a →
      (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁ →
      Since s tr 0 t₁)
    (hands : ∀ s tr a, St s tr a → ∀ i, i < j → RunHands (Since s tr) Lk i) (tp : Transport St Since Lk j) :
    ∀ o, Lk.order[j]? = some o → ∀ s tr a cs u, St s tr a → Called Lk p s tr j cs u →
      ∃ r z, claimsRunOf Lk.hear o = some r ∧ r cs.length u = .ok z ∧ Lk.each o z.1 z.2 = .ok () := by
  intro o ho s tr a cs u hS hC
  exact tp o ho s tr a cs.length u hS
    (called_since (Since s tr) (fun t₁ hd => hdraw s tr a t₁ hS hd) hC (hands s tr a hS))

/-! ## The gathering theorem -/

/-- **`AcceptedS` at the batching, from the form filled at every entry of the order.** hn: the search of the thread's list of
prover's sides at the batching's place finds none. -/
theorem accepted_of_runs_find {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (T : Thread Bk S Claim V W X Pb)
    {Said : ℕ → Coins Bk → Mid W X → Prop} {b : ℕ}
    (Sd : SeatedFree c Z l k Lk p w)
    (hblk : T.bs[b]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)))
    (hn : (T.hs.find? fun h => h.place == (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).place) = none)
    (fall : ℕ → S → List Fmt.Drawn → Option String) (front : S → List Fmt.Drawn → Option String)
    (hfall : ∀ s ds, fall b s ds = none → front s ds = none)
    (ready : ∀ κ s m En, ThrS T Said b κ s m En →
      ∃ a, Desc.K9.atS.get? s = some a ∧ drawReady a = true ∧ a.F.doorShutF = false)
    (clean : ∀ κ s m En, ThrS T Said b κ s m En → s.failed = none)
    (n : ℕ → S → ℕ)
    (plan : ∀ s tr a, StandAt T Said b front s tr a → sumTo (fun j => n j s) Lk.order.length ≤ a.F.planClaimsF)
    (pays : ∀ j, j < Lk.order.length → RunPays (StandAt T Said b front) Lk p j (n j)) :
    AcceptedS T Said fall b := by
  refine accepted_noSide T Sd hblk hn fall front hfall ready ?_
  intro κ s m En tr a hT hfr ha
  have hS : StandAt T Said b front s tr a := ⟨⟨κ, m, En, hT⟩, hfr, ha⟩
  refine ⟨fun j cs u => Called Lk p s tr j cs u ∧ cs.length ≤ sumTo (fun j => n j s) j ∧
    (∀ t₁ a₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] =
      .ok t₁ → Desc.K9.atS.get? t₁ = some a₁ → cs.all (Desc.K9H.claimFits a₁.F.trees a₁.F.ns) = true) ∧
    u.failed = none ∧ u.out.reply = s.out.reply, ?_, ?_, ?_⟩
  · intro t₁ hd
    have e := draw_is p s t₁ _ a ha hd
    refine ⟨.draw hd, Nat.le_refl _, fun _ _ _ _ => rfl, ?_, ?_⟩
    · rw [e, set_failed]
      exact clean κ s m En hT
    · rw [e, set_out]
  · intro j o ho cs u hJ
    obtain ⟨hC, hc, hf, hm, hr⟩ := hJ
    have hj : j < Lk.order.length := by
      by_contra hn
      rw [List.getElem?_eq_none (by omega)] at ho
      exact nomatch ho
    have P := pays j hj
    obtain ⟨r, z, h1, h2, h3⟩ := P.returns o ho s tr a cs u hS hC
    refine ⟨r, z, h1, h2, h3, .run hC ho h1 h2 h3, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append]
      have := P.count o r ho h1 s tr a cs u z hS hC h2
      show cs.length + z.1.length ≤ sumTo (fun j => n j s) j + n j s
      omega
    · intro t₁ a₁ hd h4
      rw [List.all_append, hf t₁ a₁ hd h4, P.fits o r ho h1 s tr a t₁ a₁ cs u z hS hd h4 hC h2]
      rfl
    · rw [P.mark o r ho h1 s tr a cs u z hS hC h2]
      exact hm
    · rw [P.reply o r ho h1 s tr a cs u z hS hC h2]
      exact hr
  · intro t₁ a₁ cs u hd h4 _ hJ
    obtain ⟨_, hc, hf, hm, hr⟩ := hJ
    exact ⟨Nat.le_trans hc (plan s tr a hS), hf t₁ a₁ hd h4, hm, hr⟩

/-- The same from "no side of this kind stands in the thread's list". -/
theorem accepted_of_runs {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (T : Thread Bk S Claim V W X Pb)
    {Said : ℕ → Coins Bk → Mid W X → Prop} {b : ℕ}
    (Sd : SeatedFree c Z l k Lk p w)
    (hblk : T.bs[b]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)))
    (hno : ∀ g ∈ T.hs, g.place.kind ≠ KindName.K9)
    (fall : ℕ → S → List Fmt.Drawn → Option String) (front : S → List Fmt.Drawn → Option String)
    (hfall : ∀ s ds, fall b s ds = none → front s ds = none)
    (ready : ∀ κ s m En, ThrS T Said b κ s m En →
      ∃ a, Desc.K9.atS.get? s = some a ∧ drawReady a = true ∧ a.F.doorShutF = false)
    (clean : ∀ κ s m En, ThrS T Said b κ s m En → s.failed = none)
    (n : ℕ → S → ℕ)
    (plan : ∀ s tr a, StandAt T Said b front s tr a → sumTo (fun j => n j s) Lk.order.length ≤ a.F.planClaimsF)
    (pays : ∀ j, j < Lk.order.length → RunPays (StandAt T Said b front) Lk p j (n j)) :
    AcceptedS T Said fall b :=
  accepted_of_runs_find T Sd hblk (none_at_batching Sd T.hs hno) fall front hfall ready clean n plan pays

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.called_since
#print axioms ProofFile.Honest.K9.returns_of_transport
#print axioms ProofFile.Honest.K9.accepted_of_runs_find
#print axioms ProofFile.Honest.K9.accepted_of_runs
