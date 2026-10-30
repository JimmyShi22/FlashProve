-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/KapRuns.lean: THE PREMISE `KeepsKap` OF `batch_bound`
(Johnson/Desc/First/Batch/Law/AddBound.lean: what the gatherer does to the state between the
batching draw and the adding leaves the open ledger's map of handed-out weights, the plan's number
of claims and the count of claims) AT A SEGMENT's OWN GATHERER, AT EACH OF THE THREE SORTS. After
the pattern of NumRuns.lean. One reading; theorems.

  `kapOf s`: the reading: the open ledger's map of handed-out weights, the plan's number, the count;
    none where no ledger is open.
  `kap_wrote`, `kap_head`, `kap_puts`, `kap_putTl`: the writings that leave it.
  `rests_kap`: **`RunRests` (RunRel.lean) at "kapOf reads the same": the nine known runs.** K4's
    `Core` and the smallness test's `OnlySide` both hold the three fields; the laying of the
    weights turns the arrays' rows alone.
  `keepsKap_of`: a gatherer that keeps the reading has `KeepsKap atS`.
  `keepsKap_layers`, `keepsKap_attention`, `keepsKap_head`: **KeepsKap atS (claimsInBy L.each L.hear
    L.order)**, from the sort's Take (its ties alone are spent) and the lookups' runs' share (k3k: a
    yes of each of their runs keeps the reading).
Limits. IMPLICATIONS, as the three Takes are. k3k STAYS A PREMISE: left to the lookup's files.
Nothing on soundness.
-/
import Johnson.Desc.First.Batch.Law.AddBound
import Johnson.Desc.First.Link.Law.NumRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote Core blockAtC frontAtC_pays backAtC_pays hideRun_core paid_core)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (coefBody)
open VerifiableInference.Desc.First.TailClaims.Law (eq_side coefBody_inv)
open VerifiableInference.Desc.K4Run
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open K5Law

variable {α β : Type}

/-- The open ledger's map of handed-out weights, the plan's number, the count of claims. -/
def kapOf (s : S) : Option (Array Bool × ℕ × ℕ) :=
  s.fork?.map fun F => (F.kapMapF, F.planClaimsF, F.nClaim)

theorem kap_wrote {e e₁ : S} {a : First.LayOwn} {G : Fork} (hw : Wrote e a G e₁)
    (hk : G.kapMapF = a.F.kapMapF) (hp : G.planClaimsF = a.F.planClaimsF)
    (hn : G.nClaim = a.F.nClaim) : kapOf e₁ = kapOf e := by
  obtain ⟨h1, rfl⟩ := hw
  simp [kapOf, S.fork?, h1, hk, hp, hn]

theorem kap_head {e : S} {a : First.HeadOwn} {G : Fork} (h1 : e.here = .head a)
    (hk : G.kapMapF = a.F.kapMapF) (hp : G.planClaimsF = a.F.planClaimsF)
    (hn : G.nClaim = a.F.nClaim) :
    kapOf { e with here := .head { a with F := G } } = kapOf e := by
  by_cases ho : a.opened = true <;> simp [kapOf, S.fork?, h1, ho, hk, hp, hn]

theorem kap_puts (s : S) (tl tl' : HTailF2) (G G' : Fork) (ht : s.tl? = some tl)
    (hG : s.fork? = some G) (hk : G'.kapMapF = G.kapMapF)
    (hp : G'.planClaimsF = G.planClaimsF) (hn : G'.nClaim = G.nClaim) :
    kapOf ((s.putTl tl').putFork G') = kapOf s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x =>
    obtain rfl : x.F = G := Option.some.inj hG
    simp [kapOf, S.putTl, S.putFork, S.fork?, hk, hp, hn]
  | att x =>
    obtain rfl : x.F = G := Option.some.inj hG
    simp [kapOf, S.putTl, S.putFork, S.fork?, hk, hp, hn]
  | head x =>
    by_cases ho : x.opened = true
    · have e2 : x.F = G := by simpa [S.fork?, ho] using hG
      simp [kapOf, S.putTl, S.putFork, S.fork?, ho, hk, hp, hn, e2]
    · simp [S.tl?, ho] at ht
  | between => simp [S.tl?] at ht
  | fin x => simp [S.tl?] at ht
  | mem x => simp [S.tl?] at ht

theorem kap_putTl (s : S) (tl' : HTailF2) : kapOf (s.putTl tl') = kapOf s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => simp [kapOf, S.putTl, S.fork?]
  | att x => simp [kapOf, S.putTl, S.fork?]
  | head x => by_cases ho : x.opened = true <;> simp [kapOf, S.putTl, S.fork?, ho]
  | between => simp [kapOf, S.putTl, S.fork?]
  | fin x => simp [kapOf, S.putTl, S.fork?]
  | mem x => simp [kapOf, S.putTl, S.fork?]

/-- The laying of the weights leaves the map. -/
theorem coef_kap (tl : HTailF2) (g : Forest.Heard) (F : Fork) :
    (coefBody tl g F).kapMapF = F.kapMapF :=
  coefBody_inv (fun r => r.kapMapF = F.kapMapF) (fun _ _ _ _ h => h) tl g F rfl

/-- **THE NINE KNOWN RUNS.** -/
theorem rests_kap : RunRests fun e e₁ => kapOf e₁ = kapOf e where
  refl _ := rfl
  front p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, _, _⟩ := frontAtC_pays h0 hr
    exact kap_wrote hw hc.kapMapF hc.planClaimsF hc.nClaim
  back p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, _, _⟩ := backAtC_pays h0 hr
    exact kap_wrote hw hc.kapMapF hc.planClaimsF hc.nClaim
  free p r h0 e e₁ hr := by
    obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 hr
    exact kap_wrote hw rfl rfl rfl
  merge n e c e₁ hr := by
    obtain ⟨a, wo, G, h1, _, rfl, _, hrunG⟩ := claim_inv hr
    exact kap_head h1 (hideRun_core hrunG).kapMapF (hideRun_core hrunG).planClaimsF
      (hideRun_core hrunG).nClaim
  join h iU3 p n e c e₁ hr := by
    obtain ⟨a, i, h1, rfl⟩ := join_hands h iU3 p n e c e₁ hr
    exact kap_head h1 (paid_core _ i).kapMapF (paid_core _ i).planClaimsF (paid_core _ i).nClaim
  eq n e c e₁ hr := by
    obtain ⟨G, tl, funs, tl', F1, hG, ht, _, he, rfl⟩ := k8Run_ok n e e₁ c hr
    exact kap_puts e tl tl' G F1 ht hG (eq_side he).kapMap (eq_side he).plan (eq_side he).nClaim
  ls e e₁ hr := by
    obtain ⟨G, tl, _, ht, rfl⟩ := k8LsTail_ok e e₁ hr
    exact kap_putTl e _
  tests nU e e₁ hr := by
    obtain ⟨G, tl, g, hG, ht, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ hr
    obtain ⟨_, _, k3, k4, _, _⟩ := core_parts (core_coefBody tl g G)
    exact kap_puts e tl tl G _ ht hG (coef_kap tl g G) k4 k3

/-- A gatherer that keeps the reading. -/
theorem keepsKap_of {g : S → Except String (List Claim × S)} (h : MoveKeeps kapOf (.add g)) :
    KeepsKap atS g := by
  intro e c e₁ a hg ha a₁ ha₁
  have k : kapOf e₁ = kapOf e := h e c e₁ hg
  unfold kapOf at k
  rw [fork_part e a ha, fork_part e₁ a₁ ha₁] at k
  have k' := Option.some.inj k
  have k1 : a₁.F.kapMapF = a.F.kapMapF := congrArg Prod.fst k'
  exact ⟨by rw [k1], congrArg (·.2.1) k', congrArg (·.2.2) k'⟩

/-- From one duty an entry of the order. -/
theorem keepsKap_link (L : Link S Claim)
    (hp : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      kapOf e₁ = kapOf e)
    (hq : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      kapOf e₁ = kapOf e) :
    KeepsKap atS (claimsInBy L.each L.hear L.order) :=
  keepsKap_of (moves_keepL (α := Unit) kapOf L [] hp hq _
    (List.mem_append_left _ (List.mem_singleton.2 rfl)))

/-- **AT A LAYERS' SEGMENT.** -/
theorem keepsKap_layers {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .layers L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ}
    {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3)
    (k3k : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → kapOf e₁ = kapOf e) :
    KeepsKap atS (claimsInBy L.each L.hear L.order) :=
  keepsKap_link L (run_layers rests_kap hL A k3k).1 (run_layers rests_kap hL A k3k).2

/-- **AT AN ATTENTION SEGMENT.** -/
theorem keepsKap_attention {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .attention L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)}
    {c : First.Att.P.ParC} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3)
    (k3k : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run,
      At L o run → ∀ n e c' e₁, run n e = .ok (c', e₁) → kapOf e₁ = kapOf e) :
    KeepsKap atS (claimsInBy L.each L.hear L.order) :=
  keepsKap_link L (run_attention rests_kap hL A k3k).1 (run_attention rests_kap hL A k3k).2

/-- **AT THE HEAD's SEGMENT.** -/
theorem keepsKap_head {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .head L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Par}
    {kap : Phi β → Option Seen} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU ent tm4 t3 l3)
    (k3k : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → kapOf e₁ = kapOf e) :
    KeepsKap atS (claimsInBy L.each L.hear L.order) :=
  keepsKap_link L (run_head rests_kap hL A k3k).1 (run_head rests_kap hL A k3k).2

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.kap_wrote
#print axioms VerifiableInference.Desc.LinkJoin.kap_head
#print axioms VerifiableInference.Desc.LinkJoin.kap_puts
#print axioms VerifiableInference.Desc.LinkJoin.kap_putTl
#print axioms VerifiableInference.Desc.LinkJoin.coef_kap
#print axioms VerifiableInference.Desc.LinkJoin.rests_kap
#print axioms VerifiableInference.Desc.LinkJoin.keepsKap_of
#print axioms VerifiableInference.Desc.LinkJoin.keepsKap_link
#print axioms VerifiableInference.Desc.LinkJoin.keepsKap_layers
#print axioms VerifiableInference.Desc.LinkJoin.keepsKap_attention
#print axioms VerifiableInference.Desc.LinkJoin.keepsKap_head
