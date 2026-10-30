-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/PayHead.lean: THE ASSEMBLY OF THE KINDS' LAWS AT THE HEAD's LINK:
`LinkOwes`' four duties on the runs and its hφ (Johnson/Desc/First/Link/Law/LinkOwes.lean), PAID at
the one closed φ, as far as the kinds' laws on their runs reach today. One structure of what they
take, and theorems. The like of PayLayers.lean.

What is said.
  `tmH`, `lenH`: the table of terms by the entries of the head's order. `HeadTake`: what the laws
    take: THE TIES, UP TO A GUARD (`Under`; `HeadTies`: a list of their own): the output head's
    kind's block's three runs; its «join»; the smallness test's three functions; the merge's run;
    the lookup's «guests» under the idle run · a reader of φ for what the output head's runs see
    beside the ledger · THE NAMED PREMISES ON Ok AND Fu · the equations' first four claims · AND, AS
    THEY STAND, THE THREE DUTIES OF THE LOOKUP's RUNS «objects» (blocks 2 and 7) and «planes».
  `seen_pair`: hψ and hkap can be met together. `merge_door`: the merge's run keeps the door.
    `pay_head`, `payd_head`, `quiet_head`, `quietd_head`, `phi_head`: **the five fields of
    `LinkOwes` at the head's link.**

Limits. AN IMPLICATION: `HeadTake` is shown of no record. It closes φ alone, and one φ a link (u is
that link's record); Ok and Fu stay letters. Every premise on them here is an upper bound («Ok q →
…», «Fu t → …»): they cannot cross each other; whether they can be met is decided where `LinkOwes`
asks the lower bounds: `hready` and `hend`. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.PayLayers
import Johnson.Desc.Kinds.Law.JoinRunAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.PscRun (Sized Filled)
open OnBytes.Tie.Pv.Tail (UnitRow)
open OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows
open VerifiableInference.Desc.K4Values (winOf)
open VerifiableInference.Desc.First.TailClaims (rkSelfTestP)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K11Run
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

variable {β : Type}

/-- The terms by the entries of the head's order. t3: the lookup's runs' terms, by entry. -/
noncomputable def tmH (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par) (kap : Phi β → Option Seen)
    (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8) (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (o : ℕ × String) :
    ℕ → Q β → Bound GE8 → List (ℕ × GE8) :=
  if o.2 == "norm" || o.2 == "policy" || o.2 == "logits" then
    plainTm (valsStill Reading.gl (fsK6 h iU3 p kap o.2) ent)
  else if o.2 == "join" then plainTm (valsStill Reading.gl (fsJoin h iU3 p kap) ent)
  else if o.2 == "K8.equations" then fun n q y => tm4 n q y ++ tmRest pi8 q y
  else if o.2 == "the merge" then plainTm (valsMerge Reading.gl (·.wo) ent)
  else if o.2 == "guests" then plainTm (valsStill Reading.gl fsNone ent)
  else t3 o

/-- The numbers of claims by the entries of the head's order. -/
noncomputable def lenH (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par)
    (kap : Phi β → Option Seen) (l3 : ℕ × String → Q β → ℕ) (o : ℕ × String) : Q β → ℕ :=
  if o.2 == "norm" || o.2 == "policy" || o.2 == "logits" then
    lenStill (fsK6 h iU3 p kap o.2)
  else if o.2 == "join" then lenStill (fsJoin h iU3 p kap)
  else if o.2 == "K8.equations" then len8 pi8
  else if o.2 == "the merge" then fun _ => 1
  else if o.2 == "guests" then lenStill fsNone
  else l3 o

/-- **THE TIES**: which run stands at an entry of the orders, up to a guard. -/
structure HeadTies (L : Link S Claim) (h : OnBytes.Model.Head.Shape) (iU3 l piece : ℕ)
    (p : Par) (nU : Array ℕ) :
    Prop where
  /-- TIE: the runs at (3, "norm"), (3, "policy"), (3, "logits") stand under the output head's
  kind's -/
  tK6 : ∀ name ∈ ["norm", "policy", "logits"], ∀ run, At L (3, name) run →
    ∃ r, (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some r ∧ Under run r
  /-- TIE: the run at (3, "join") -/
  tJoin : ∀ run, At L (3, "join") run →
    Under run (K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)))
  /-- TIE: the runs at (2, "guests") and (7, "guests") stand under the run that returns no claim and
  hands the record back -/
  tGuests : ∀ k ∈ [2, 7], ∀ run, At L (k, "guests") run → Under run idle0
  /-- TIE: the run at (5, "K8.equations") -/
  tEq : ∀ run, At L (5, "K8.equations") run → Under run k8Run.2
  /-- TIE: the run at (8, "the merge") -/
  tMerge : ∀ run, At L (8, "the merge") run → Under run headMergeClaim
  /-- TIE: the run behind the batching at (5, "K8.lsTail") -/
  tLs : ∀ run, AtAfter L (5, "K8.lsTail") run → UnderAfter run k8LsTail
  /-- TIE: the run behind the batching at (5, "K8.tests") -/
  tTests : ∀ run, AtAfter L (5, "K8.tests") run → UnderAfter run (k8Tests nU)

/-- **WHAT THE KINDS' LAWS TAKE AT THE HEAD's LINK.** -/
structure HeadTake (L : Link S Claim) (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (Fu : S → Prop)
    (h : OnBytes.Model.Head.Shape) (iU3 l piece : ℕ) (p : Par) (kap : Phi β → Option Seen)
    (nU : Array ℕ) (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ) :
    Prop where
  /-- TIES: which run stands at an entry, up to a guard -/
  ties : HeadTies L h iU3 l piece p nU
  /-- the further kinds' letter rests under the writings behind the draw -/
  hψ : Rests u ψ
  /-- φ shows what the output head's runs see beside the ledger -/
  hkap : ∀ e, kap (phiAll u ψ e) = seenOf e
  /-- ON Ok, for the output head's three runs -/
  okK6 : K6Promise h iU3 p kap Ok
  /-- ON Ok, for "join" -/
  okJoin : JoinPromise kap Ok
  /-- ON Ok, for the equations -/
  okEq : ∀ q tlb, Ok q → (pi8 q.1).1 = some tlb → OnBytes.Tie.Pv.Tail.Port.Fits tlb
  /-- ON Ok, for the merge -/
  okMerge : ∀ q wo v, Ok q → q.1.wo = some wo → q.2 = some v → Sized v.F ∧
    ∀ x ∈ (wo.p.rowForm wo.fvp {}).slots.toList, K4Values.InWin (winOf wo.p) x.1 ∨ Filled v.F x.1
  /-- ON Fu, for the output head's three runs: the entries that their forms name -/
  fuK6 : ∀ name ∈ ["norm", "policy", "logits"], ∀ q l t b y, Fx9 (phiAll u ψ) Ok q t → Fu t →
    atS.get? t = some b → fsK6 h iU3 p kap name q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx
  /-- ON Fu, for "join" -/
  fuJoin : ∀ q l t b y, Fx9 (phiAll u ψ) Ok q t → Fu t → atS.get? t = some b →
    fsJoin h iU3 p kap q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx
  /-- ON Fu, for the equations: at a full state that goes on from q -/
  fuEq : ∀ q t b ts funs, Fx9 (phiAll u ψ) Ok q t → Fu t → atS.get? t = some b →
    t.tl? = some ts → t.funs? = some funs →
    rkSelfTestP ts b.F = .ok () ∧
      (b.F.trees.getD ts.ix.ZZ {}).rows.size = 2 * ts.zzBlocks + 2 ∧
      ∀ x ∈ readsList ts funs, UnitRow b.F (uOf ts x.1) ∧
        ∀ d, d < (ts.mats.getD x.1.mat {}).k → posOf ts x.1 x.2 d < colsU b.F (uOf ts x.1)
  /-- ON Fu, for the merge -/
  fuMerge : ∀ q wo t b y, Fx9 (phiAll u ψ) Ok q t → Fu t → atS.get? t = some b →
    q.1.wo = some wo → ∀ x ∈ (wo.p.rowForm wo.fvp {}).ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx
  /-- the equations' first four claims -/
  h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) Ok q e → good9 e → atS.get? e = some a →
    k8Run.2 front e = .ok (c, e₁) →
    ∀ t y, laterK atS (O9 (K := GE8) (phiAll u ψ) Ok Fu) e₁ t → Fu t →
      wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) =
        termsAt GE8 (tm4 (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta)
  /-- AS IT STANDS: RunOk of the lookup's runs "objects" (both blocks) and "planes" -/
  k3 : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
    RunOk Reading.gl atS (O9 (phiAll u ψ) Ok Fu) (Fx9 (phiAll u ψ) Ok) run (t3 o) (l3 o)
  /-- AS IT STANDS: these three keep the door -/
  k3d : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
    ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor atS e e₁

/-- **hψ AND hkap CAN BE MET TOGETHER**: lay what the output head's runs see into the free field of
φ, beside the other kinds' letter: it rests under the writings behind the draw, and φ shows it. -/
theorem seen_pair {γ : Type} (u : HTailF2) {ψ' : S → γ} (hψ' : Rests u ψ') :
    Rests u (fun s => (seenOf s, ψ' s)) ∧
      ∀ e, (phiAll u (fun s => (seenOf s, ψ' s)) e).more.1 = seenOf e :=
  ⟨rests_pair u (rests_seen u) hψ', fun _ => rfl⟩

/-- The merge's run keeps the door. -/
theorem merge_door (n : ℕ) (e : S) (c : List Claim) (e₁ : S)
    (hr : headMergeClaim n e = .ok (c, e₁)) : KeepsDoor atS e e₁ := by
  intro a9 ha
  obtain ⟨a, wo, G, h1, hwo, rfl, rfl, hrunG⟩ := claim_inv hr
  obtain ⟨a₁, ha₁, _, f2, f3, _⟩ := get_head e a9 ha a h1 G
  exact ⟨a₁, ha₁, by rw [f2], f3⟩

variable {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop}
  {h : OnBytes.Model.Head.Shape} {iU3 l piece : ℕ} {p : Par} {kap : Phi β → Option Seen}
  {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
  {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}

/-- **hφ AT THE CLOSED φ.** -/
theorem phi_head (A : HeadTake L u ψ Ok Fu h iU3 l piece p kap nU ent tm4 t3 l3) (s : S)
    (a : K9.Part) : phiAll u ψ (atS.set s a) = phiAll u ψ s := phi_set u ψ A.hψ s a

/-- **hpay AT THE HEAD's LINK.** -/
theorem pay_head (A : HeadTake L u ψ Ok Fu h iU3 l piece p kap nU ent tm4 t3 l3) :
    ∀ o ∈ First.orderOf .head, ∀ run, At L o run →
      RunOk Reading.gl atS (O9 (phiAll u ψ) Ok Fu) (Fx9 (phiAll u ψ) Ok) run
        (tmH h iU3 p kap ent tm4 t3 o) (lenH h iU3 p kap l3 o) := by
  have k6 : ∀ name ∈ ["norm", "policy", "logits"], ∀ run, At L (3, name) run →
      RunOk Reading.gl atS (O9 (phiAll u ψ) Ok Fu) (Fx9 (phiAll u ψ) Ok) run
        (plainTm (valsStill Reading.gl (fsK6 h iU3 p kap name) ent))
        (lenStill (fsK6 h iU3 p kap name)) := fun name hn run hr => by
    obtain ⟨r, h0, hu⟩ := A.ties.tK6 name hn run hr
    exact runOk_under _ _ _ _ hu (k6_runOk h iU3 p (phiAll u ψ) Ok kap A.hkap A.okK6 Reading.gl Fu l
      piece name r h0 ent (A.fuK6 name hn))
  rw [order_head]
  refine ⟨A.k3 _ (by simp),
    fun run hr => runOk_under _ _ _ _ (A.ties.tGuests 2 (by simp) run hr)
      (idle_runOk Reading.gl _ Ok Fu (fun _ _ => rfl) ent),
    k6 "norm" (by simp), fun run hr => ?_, k6 "policy" (by simp), A.k3 _ (by simp),
    A.k3 _ (by simp),
    fun run hr => runOk_under _ _ _ _ (A.ties.tGuests 7 (by simp) run hr)
      (idle_runOk Reading.gl _ Ok Fu (fun _ _ => rfl) ent),
    fun run hr => ?_, k6 "logits" (by simp), fun run hr => ?_⟩
  · exact runOk_under _ _ _ _ (A.ties.tJoin run hr)
      (join_runOk h iU3 p (phiAll u ψ) Ok kap A.hkap A.okK6 A.okJoin Reading.gl Fu
        (fun s a G hs => phi_k11_keep u ψ A.hψ s a G hs) ent A.fuJoin)
  · exact runOk_under _ _ _ _ (A.ties.tEq run hr)
      (k8_runOk (phiAll u ψ) Ok Fu u pi8 (fun s => phi_k8_pi u ψ s)
        (fun s tl tl' F1 h1 h2 => phi_k8_keep u ψ A.hψ s tl tl' F1 h1 h2) A.okEq A.fuEq tm4 A.h4)
  · exact runOk_under _ _ _ _ (A.ties.tMerge run hr)
      (k11_runOk Reading.gl (phiAll u ψ) Ok Fu (·.wo) (fun s a hs => phi_k11_pi u ψ s a hs)
        (fun s a G hs => phi_k11_keep u ψ A.hψ s a G hs) A.okMerge ent A.fuMerge)

/-- **hpayd AT THE HEAD's LINK.** -/
theorem payd_head (A : HeadTake L u ψ Ok Fu h iU3 l piece p kap nU ent tm4 t3 l3) :
    ∀ o ∈ First.orderOf .head, ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor atS e e₁ := by
  have k6 : ∀ name ∈ ["norm", "policy", "logits"], ∀ run, At L (3, name) run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor atS e e₁ := fun name hn run hr => by
    obtain ⟨r, h0, hu⟩ := A.ties.tK6 name hn run hr
    exact door_under atS hu (k6_door h iU3 p l piece name r h0)
  rw [order_head]
  refine ⟨A.k3d _ (by simp),
    fun run hr => door_under atS (A.ties.tGuests 2 (by simp) run hr) (idle_door fun _ _ => rfl),
    k6 "norm" (by simp), fun run hr => ?_, k6 "policy" (by simp), A.k3d _ (by simp),
    A.k3d _ (by simp),
    fun run hr => door_under atS (A.ties.tGuests 7 (by simp) run hr) (idle_door fun _ _ => rfl),
    fun run hr => ?_, k6 "logits" (by simp), fun run hr => ?_⟩
  · exact door_under atS (A.ties.tJoin run hr) (join_door h iU3 p)
  · exact door_under atS (A.ties.tEq run hr) fun n e c e₁ hr => k8Run_door n e e₁ c hr
  · exact door_under atS (A.ties.tMerge run hr) merge_door

/-- **hquiet AT THE HEAD's LINK.** -/
theorem quiet_head (A : HeadTake L u ψ Ok Fu h iU3 l piece p kap nU ent tm4 t3 l3) :
    ∀ o ∈ First.orderAfterOf .head, ∀ run, AtAfter L o run →
      QuietOk atS (O9 (K := GE8) (phiAll u ψ) Ok Fu) (Fx9 (phiAll u ψ) Ok) run := by
  rw [after_head]
  refine ⟨fun run hr => ?_, fun run hr => ?_⟩
  · exact quietOk_under _ _ _ (A.ties.tLs run hr) (k8_lsTail_quietOk (phiAll u ψ) Ok Fu u
      fun s tl tl' h1 h2 => phi_k8_keepT u ψ A.hψ s tl tl' h1 h2)
  · exact quietOk_under _ _ _ (A.ties.tTests run hr) (k8_tests_quietOk (phiAll u ψ) Ok Fu u
      (fun s tl tl' F1 h1 h2 => phi_k8_keep u ψ A.hψ s tl tl' F1 h1 h2) nU)

/-- **hquietd AT THE HEAD's LINK.** -/
theorem quietd_head (A : HeadTake L u ψ Ok Fu h iU3 l piece p kap nU ent tm4 t3 l3) :
    ∀ o ∈ First.orderAfterOf .head, ∀ run, AtAfter L o run →
      ∀ e e₁, run e = .ok e₁ → KeepsDoor atS e e₁ := by
  rw [after_head]
  refine ⟨fun run hr => ?_, fun run hr => ?_⟩
  · exact doorAfter_under atS (A.ties.tLs run hr) k8LsTail_door
  · exact doorAfter_under atS (A.ties.tTests run hr) (k8Tests_door nU)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.seen_pair
#print axioms VerifiableInference.Desc.LinkJoin.merge_door
#print axioms VerifiableInference.Desc.LinkJoin.phi_head
#print axioms VerifiableInference.Desc.LinkJoin.pay_head
#print axioms VerifiableInference.Desc.LinkJoin.payd_head
#print axioms VerifiableInference.Desc.LinkJoin.quiet_head
#print axioms VerifiableInference.Desc.LinkJoin.quietd_head
