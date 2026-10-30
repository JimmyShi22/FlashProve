-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03HeadSixAt.lean: THREE PREMISES OF THE LOOKUPS' FOUR ENDS AT THE OUTPUT HEAD's SEGMENT
  ("norm" | "policy" | "logits" | "join" pass the lookup on the digits:
  Johnson/Top/H/Keep/HeadOwnAtSeat.lean),
  IN THEIR OWN TEXTS,
  AT THE CLOSED CONSTANT, UNDER THE HEAD; AND
  THE TWO KEPT TESTS' ENDS CALLED WITH THEM.

Why. That file's head says that it is NOT TYPECHECKED THERE that other files' payer of K6States and
  K6Back meets K, hBo, hBj as typed there. Here Lean holds
  the three texts against that payer.
  k03_six_K: K : K6States h iU3 p 24 4 (statesOfLink Lk) 3 · k03_six_hBo · k03_six_hBj: the two
    clauses of K6Back WRITTEN OUT, as that file binds them: at h := (At.X Zp).hS · iU3 := readsOf
    (At.X Zp) · p := parOf (At.X Zp).hS (workOf (At.X Zp)): THE LETTERS OF P5J.k03_ready_345
    (Johnson/P5J/K03ReadyAt345.lean); at every Lk with 𝔇.lk 24 = some Lk.
  **k03_own_pass_head · k03_join_pass_head**: own_formsIn_pass_seat | join_formsIn_pass_seat CALLED
    with the three, at X := At.X Zp · mH := m := 24 · l := Lk · b := 3: GENERAL IN THE TWO STATES s,
    s' OF AN ACCEPT: SO THAT THE THREE ARE TAKEN AS THE BINDERS IS LEAN's WORD. THE TWO HAVE NO
    CALLER: THEY ARE TRIPWIRES OF THE FIT (the sister file Johnson/P5J/K03HeadOwnAt.lean calls the
    lookups' ends itself). What stays in their binders: P : K3Pass s s' F G · A : SamePlanes s s' ·
    a : Alike s s' · hReady · for "join" besides hh · hob
    (and hA : AtS2 (seatCalls asClaim), a fact on the seat):
    FACTS ON THE FRONT STATE OR ON THE PAIR:
    NOT PAID IN THIS FILE.
NOTHING IS ARGUED: each of the three is a field of P4.six_of_link_at_head
  (Johnson/Desc/Kinds/Law/K6StateAtHead.lean). The credit is that file's.
NOT HERE, BUT PAID IN THE SISTER FILE Johnson/P5J/K03HeadOwnAt.lean (k03_head_pair), across the
  whole seated accept, from the promise in front, "reached" and "no mark": hReady · K3Pass ·
  SamePlanes · Alike · hh · hob.

Limits. The three: implications between returns of runs, at closed terms: nothing on a state. The
  two calls: implications from the kept test at s to the kept test at s', under six | eight premises
  on the pair: the sister file pays them at every accept of the seated piece under the ledger's
  hands; that such an accept exists is not shown. The head is a premise; a member of it is proved at
  storedPublicFiles and zGap alone (at secondHashFunction; side library AtFullSide/Top/).
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.ChainFree
import Johnson.Desc.Kinds.Law.K6StateAtHead
import Johnson.Desc.Kinds.Law.K6SilentRides
import Johnson.Top.H.Keep.HeadOwnAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.Desc (Chain Link Claim)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (seatCalls joinRun)
open VerifiableInference.Desc.K9 (statesOfLink readersOfLink holesAt formsIn)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K3 (unpaid)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **K** (HeadOwnAtSeat.lean). -/
theorem k03_six_K (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Lk : Link S Claim}
    (hk : (h.toAtMg.𝔇 h.𝔇).lk 24 = some Lk) :
    K6States (At.X Zp).hS (readsOf (At.X Zp)) (parOf (At.X Zp).hS (workOf (At.X Zp))) 24 4
      (statesOfLink Lk) 3 :=
  (P4.six_of_link_at_head h ((h.laid.linkAt 24).symm.trans hk)).1

/-- **hBo** (HeadOwnAtSeat.lean): K6Back's field own. -/
theorem k03_six_hBo (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Lk : Link S Claim}
    (hk : (h.toAtMg.𝔇 h.𝔇).lk 24 = some Lk) :
    ∀ name run run', (statesOfLink Lk 3).find? (fun r => r.1 == name) = some (name, run) →
      (kind asClaim (seatAt (At.X Zp).hS (readsOf (At.X Zp))) 24 4
        (parOf (At.X Zp).hS (workOf (At.X Zp)))).claims.lookup name = some run' →
      ∀ k t y, run' k t = .ok y → y.2.out.reply = t.out.reply → run k t = .ok y :=
  (P4.six_of_link_at_head h ((h.laid.linkAt 24).symm.trans hk)).2.1.own

/-- **hBj** (HeadOwnAtSeat.lean): K6Back's field join. -/
theorem k03_six_hBj (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Lk : Link S Claim}
    (hk : (h.toAtMg.𝔇 h.𝔇).lk 24 = some Lk) :
    ∀ run, (statesOfLink Lk 3).find? (fun r => r.1 == "join") = some ("join", run) →
      ∀ k t y, joinRun (seatCalls asClaim)
          (callerKeys (parOf (At.X Zp).hS (workOf (At.X Zp)))
            (seatAt (At.X Zp).hS (readsOf (At.X Zp)))) k t = .ok y →
        y.2.out.reply = t.out.reply → run k t = .ok y :=
  (P4.six_of_link_at_head h ((h.laid.linkAt 24).symm.trans hk)).2.1.join

/-- **The kept test at one of the head's own three runs passes: the lookups' end, called.** -/
theorem k03_own_pass_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Lk : Link S Claim}
    (hk : (h.toAtMg.𝔇 h.𝔇).lk 24 = some Lk) (own : List (ℕ × ℕ)) {s s' : S} {F G : Fork}
    (P : K3Pass s s' F G) (A : SamePlanes s s') (a : Alike s s')
    (hReady : ∀ z U, Sees s z U → K6Ready (At.X Zp).hS (readsOf (At.X Zp))
      (parOf (At.X Zp).hS (workOf (At.X Zp))) z U)
    {name : String} (hn3 : name = "norm" ∨ name = "policy" ∨ name = "logits")
    (hin : formsIn (readersOfLink (holesAt (At.X Zp) 24 24 Lk) Lk) own 3 name s = true) :
    formsIn (readersOfLink (holesAt (At.X Zp) 24 24 Lk) Lk) own 3 name s' = true :=
  own_formsIn_pass_seat (At.X Zp) 24 24 rfl Lk 3 own _ _ 24 4 _ P A a (k03_six_K h hk) hReady
    (k03_six_hBo h hk) hn3 hin

/-- **The kept test at "join" passes: the lookups' end, called.** -/
theorem k03_join_pass_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Lk : Link S Claim}
    (hk : (h.toAtMg.𝔇 h.𝔇).lk 24 = some Lk) (own : List (ℕ × ℕ)) {s s' : S} {F G : Fork}
    (P : K3Pass s s' F G) (A : SamePlanes s s') (a : Alike s s')
    (hReady : ∀ z U, Sees s z U → K6Ready (At.X Zp).hS (readsOf (At.X Zp))
      (parOf (At.X Zp).hS (workOf (At.X Zp))) z U)
    (hA : AtS2 (seatCalls asClaim))
    (hh : (seatCalls asClaim).heard s' = (seatCalls asClaim).heard s)
    (hob : ∀ i, unpaid G i = true → unpaid F i = true)
    (hin : formsIn (readersOfLink (holesAt (At.X Zp) 24 24 Lk) Lk) own 3 "join" s = true) :
    formsIn (readersOfLink (holesAt (At.X Zp) 24 24 Lk) Lk) own 3 "join" s' = true :=
  join_formsIn_pass_seat (At.X Zp) 24 24 rfl Lk 3 own _ _ 24 4 _ P A a (k03_six_K h hk) hReady
    (k03_six_hBj h hk) hA hh hob hin

end P5J

#print axioms P5J.k03_six_K
#print axioms P5J.k03_six_hBo
#print axioms P5J.k03_six_hBj
#print axioms P5J.k03_own_pass_head
#print axioms P5J.k03_join_pass_head
