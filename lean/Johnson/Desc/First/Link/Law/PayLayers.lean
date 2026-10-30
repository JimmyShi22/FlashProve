-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/PayLayers.lean: THE ASSEMBLY OF THE KINDS' LAWS AT A LAYERS' LINK:
`LinkOwes`' four duties on the runs (Johnson/Desc/First/Link/Law/LinkOwes.lean: hpay, hpayd, hquiet,
hquietd) and its hφ, PAID at the one closed φ, as far as the kinds' laws on their runs reach today.
One structure of what they take, and theorems.

Why. Each kind's law on a run is typed at letters φ, Ok, Fu of its own choice. Here they meet at ONE
φ (`PhiAll.phiAll u ψ`), ONE Ok and ONE Fu: so that their premises on these letters are seen
together, and Lean holds that they fit.

What is said.
  `tmL`, `lenL`: the table of terms by the entries of the layers' order. `LayersTake`: what the laws
    take: THE TIES (`LayersTies`: a list of their own, so that whoever pays them hands one term):
    which run stands at an entry, UP TO A GUARD (`Under`: every yes of the run that stands there is
    a yes of the kind's own run, with the same return): the layers' own kind's block's; the
    smallness test's three functions; the lookup's «guests» under the idle run · THE NAMED PREMISES
    ON Ok AND Fu of the layers' two runs and of the smallness test's equations · the equations'
    first four claims (h4) · AND, AS THEY STAND, THE TWO DUTIES OF THE LOOKUP's RUN «objects» at the
    blocks 1 and 6, for which no law is called here yet.
  `pay_layers`, `payd_layers`, `quiet_layers`, `quietd_layers`, `phi_layers`: **the five fields of
    `LinkOwes` at a layers' link.**

Limits. AN IMPLICATION: `LayersTake` is shown of no record. It closes φ alone, and one φ a link (u
is that link's record); Ok and Fu stay letters. Every premise on them here is an upper bound («Ok q
→ …», «Fu t → …»): they cannot cross each other; whether they can be met is decided where `LinkOwes`
asks the lower bounds: `hready` and `hend`. The premises on the entries (fuFront, fuBack) are
payable only where what is fixed names the rows' weights (EntryUnit.lean). Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkOwes
import Johnson.Desc.First.Link.Law.K4Quiet
import Johnson.Desc.First.Link.Law.PhiAll
import Johnson.Desc.First.Link.Law.Under
import Johnson.Desc.First.Batch.Law.K8Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.PscRun (Sized Filled)
open OnBytes.Tie.Pv.Tail (UnitRow)
open OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows
open VerifiableInference.Desc.K4Values (winOf backForms frontForms frontWins)
open VerifiableInference.Desc.First.TailClaims (rkSelfTestP)
open OnBytes.Desc.First.K4 (Par blockAtC Wrote frontAtC backAtC)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K4Run
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.StillRun

variable {β : Type}

/-- The fixed part's type at the closed φ. -/
abbrev Q (β : Type) : Type := Phi β × Option Pub9

/-- The smallness test's reader of φ. -/
def pi8 (x : Phi β) : Option HTailF2 × Option (Array HFun) := (x.tl, x.funs)

/-- The terms by the entries of the layers' order. t3: the lookup's runs' terms, by entry. -/
def tmL (p : Par) (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (o : ℕ × String) :
    ℕ → Q β → Bound GE8 → List (ℕ × GE8) :=
  if o.2 == "front" then plainTm (valsFront Reading.gl p (·.own) ent)
  else if o.2 == "back" then plainTm (valsBack Reading.gl (·.own) ent)
  else if o.2 == "K8.equations" then fun n q y => tm4 n q y ++ tmRest pi8 q y
  else if o.2 == "guests" then plainTm (valsStill Reading.gl fsNone ent)
  else t3 o

/-- The numbers of claims by the entries of the layers' order. -/
def lenL (p : Par) (l3 : ℕ × String → Q β → ℕ) (o : ℕ × String) : Q β → ℕ :=
  if o.2 == "front" then lenFront p (·.own)
  else if o.2 == "back" then fun _ => 4
  else if o.2 == "K8.equations" then len8 pi8
  else if o.2 == "guests" then lenStill fsNone
  else l3 o

/-- **THE TIES**: which run stands at an entry of the orders, up to a guard. -/
structure LayersTies (L : Link S Claim) (p : Par) (nU : Array ℕ) :
    Prop where
  /-- TIE: the run at (2, "front") stands under the layers' own kind's block's -/
  tFront : ∀ run, At L (2, "front") run →
    ∃ r, (blockAtC p).claims.lookup "front" = some r ∧ Under run r
  /-- TIE: the run at (2, "back") -/
  tBack : ∀ run, At L (2, "back") run →
    ∃ r, (blockAtC p).claims.lookup "back" = some r ∧ Under run r
  /-- TIE: the runs at (1, "guests") and (6, "guests") stand under the run that returns no claim and
  hands the record back -/
  tGuests : ∀ k ∈ [1, 6], ∀ run, At L (k, "guests") run → Under run idle0
  /-- TIE: the run at (4, "K8.equations") stands under the smallness test's run of equations -/
  tEq : ∀ run, At L (4, "K8.equations") run → Under run k8Run.2
  /-- TIE: the run behind the batching at (4, "K8.lsTail") -/
  tLs : ∀ run, AtAfter L (4, "K8.lsTail") run → UnderAfter run k8LsTail
  /-- TIE: the run behind the batching at (2, "free-slot") -/
  tFree : ∀ run, AtAfter L (2, "free-slot") run →
    ∃ r, (blockAtC p).after.lookup "free-slot" = some r ∧ UnderAfter run r
  /-- TIE: the run behind the batching at (4, "K8.tests") -/
  tTests : ∀ run, AtAfter L (4, "K8.tests") run → UnderAfter run (k8Tests nU)

/-- **WHAT THE KINDS' LAWS TAKE AT A LAYERS' LINK.** -/
structure LayersTake (L : Link S Claim) (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (Fu : S → Prop)
    (p : Par) (nU : Array ℕ) (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ) :
    Prop where
  /-- TIES: which run stands at an entry, up to a guard -/
  ties : LayersTies L p nU
  /-- the further kinds' letter rests under the writings behind the draw -/
  hψ : Rests u ψ
  /-- ON Ok, for "front" -/
  okFront : ∀ q o v, Ok q → q.1.own = some o → q.2 = some v → Sized v.F ∧
    (∀ i, i < 4 * p.P.y.NI → Filled v.F (o.H.tV.sEnd + i)) ∧
    ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l → ∀ f ∈ l, ∀ x ∈ f.slots.toList,
      (∃ w ∈ frontWins o, K4Values.InWin w x.1) ∨ Filled v.F x.1
  /-- ON Ok, for "back" -/
  okBack : ∀ q o v, Ok q → q.1.own = some o → q.2 = some v → Sized v.F ∧
    ∀ f ∈ backForms o, ∀ x ∈ f.slots.toList,
      K4Values.InWin (winOf o.wo.toWsMerged.p) x.1 ∨ Filled v.F x.1
  /-- ON Ok, for the equations -/
  okEq : ∀ q tlb, Ok q → (pi8 q.1).1 = some tlb → OnBytes.Tie.Pv.Tail.Port.Fits tlb
  /-- ON Fu, for "front": the entries that its forms name -/
  fuFront : ∀ q o v t b y, Fx9 (phiAll u ψ) Ok q t → Fu t → atS.get? t = some b →
    q.1.own = some o → q.2 = some v → ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l →
    ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx
  /-- ON Fu, for "back" -/
  fuBack : ∀ q o t b y, Fx9 (phiAll u ψ) Ok q t → Fu t → atS.get? t = some b →
    q.1.own = some o → ∀ f ∈ backForms o, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx
  /-- ON Fu, for the equations: at a full state that goes on from q -/
  fuEq : ∀ q t b ts funs, Fx9 (phiAll u ψ) Ok q t → Fu t → atS.get? t = some b →
    t.tl? = some ts → t.funs? = some funs →
    rkSelfTestP ts b.F = .ok () ∧
      (b.F.trees.getD ts.ix.ZZ {}).rows.size = 2 * ts.zzBlocks + 2 ∧
      ∀ x ∈ readsList ts funs, UnitRow b.F (uOf ts x.1) ∧
        ∀ d, d < (ts.mats.getD x.1.mat {}).k → posOf ts x.1 x.2 d < colsU b.F (uOf ts x.1)
  /-- the equations' first four claims -/
  h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) Ok q e → good9 e → atS.get? e = some a →
    k8Run.2 front e = .ok (c, e₁) →
    ∀ t y, laterK atS (O9 (K := GE8) (phiAll u ψ) Ok Fu) e₁ t → Fu t →
      wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) =
        termsAt GE8 (tm4 (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta)
  /-- AS IT STANDS: RunOk of the lookup's run "objects", at both its blocks -/
  k3 : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run →
    RunOk Reading.gl atS (O9 (phiAll u ψ) Ok Fu) (Fx9 (phiAll u ψ) Ok) run (t3 o) (l3 o)
  /-- AS IT STANDS: the lookup's run "objects" keeps the door -/
  k3d : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run →
    ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor atS e e₁

variable {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop} {p : Par}
  {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
  {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}

/-- **hφ AT THE CLOSED φ.** -/
theorem phi_layers (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3) (s : S) (a : K9.Part) :
    phiAll u ψ (atS.set s a) = phiAll u ψ s := phi_set u ψ A.hψ s a

/-- **hpay AT A LAYERS' LINK.** -/
theorem pay_layers (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3) :
    ∀ o ∈ First.orderOf .layers, ∀ run, At L o run →
      RunOk Reading.gl atS (O9 (phiAll u ψ) Ok Fu) (Fx9 (phiAll u ψ) Ok) run
        (tmL p ent tm4 t3 o) (lenL p l3 o) := by
  rw [order_layers]
  refine ⟨A.k3 _ (by simp),
    fun run h => runOk_under _ _ _ _ (A.ties.tGuests 1 (by simp) run h)
      (idle_runOk Reading.gl _ Ok Fu (fun _ _ => rfl) ent), fun run h => ?_,
    A.k3 _ (by simp),
    fun run h => runOk_under _ _ _ _ (A.ties.tGuests 6 (by simp) run h)
      (idle_runOk Reading.gl _ Ok Fu (fun _ _ => rfl) ent),
    fun run h => ?_, fun run h => ?_⟩
  · obtain ⟨r, h0, hu⟩ := A.ties.tFront run h
    refine runOk_under _ _ _ _ hu ?_
    exact k4_front_runOk Reading.gl (phiAll u ψ) Ok Fu p r h0 (·.own)
      (fun s a hs => phi_k4_pi u ψ s a hs) (fun s a G s' hw => phi_k4_keep u ψ A.hψ s a G s' hw)
      A.okFront ent A.fuFront
  · refine runOk_under _ _ _ _ (A.ties.tEq run h) ?_
    exact k8_runOk (phiAll u ψ) Ok Fu u pi8 (fun s => phi_k8_pi u ψ s)
      (fun s tl tl' F1 h1 h2 => phi_k8_keep u ψ A.hψ s tl tl' F1 h1 h2) A.okEq A.fuEq tm4 A.h4
  · obtain ⟨r, h0, hu⟩ := A.ties.tBack run h
    refine runOk_under _ _ _ _ hu ?_
    exact k4_back_runOk Reading.gl (phiAll u ψ) Ok Fu p r h0 (·.own)
      (fun s a hs => phi_k4_pi u ψ s a hs) (fun s a G s' hw => phi_k4_keep u ψ A.hψ s a G s' hw)
      A.okBack ent A.fuBack

/-- What a run of the layers' own kind writes keeps the door. -/
theorem wrote_door {e e₁ : S} {a : First.LayOwn} {G : Fork} (hw : Wrote e a G e₁) :
    KeepsDoor atS e e₁ := by
  intro a9 ha
  obtain ⟨a₁, ha₁, _, f2, f3, _⟩ := get_wrote e e₁ a9 ha a G hw
  exact ⟨a₁, ha₁, by rw [f2], f3⟩

/-- **hpayd AT A LAYERS' LINK.** -/
theorem payd_layers (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3) :
    ∀ o ∈ First.orderOf .layers, ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor atS e e₁ := by
  rw [order_layers]
  refine ⟨A.k3d _ (by simp),
    fun run h => door_under atS (A.ties.tGuests 1 (by simp) run h) (idle_door fun _ _ => rfl),
    fun run h n e c e₁ hr => ?_, A.k3d _ (by simp),
    fun run h => door_under atS (A.ties.tGuests 6 (by simp) run h) (idle_door fun _ _ => rfl),
    fun run h => ?_, fun run h n e c e₁ hr => ?_⟩
  · obtain ⟨r, h0, hu⟩ := A.ties.tFront run h
    obtain ⟨a, _, _, G, _, _, _, hw⟩ := frontAtC h0 (hu n e c e₁ hr)
    exact wrote_door hw
  · exact door_under atS (A.ties.tEq run h) fun n e c e₁ hr => k8Run_door n e e₁ c hr
  · obtain ⟨r, h0, hu⟩ := A.ties.tBack run h
    obtain ⟨a, _, _, G, _, _, _, hw⟩ := backAtC h0 (hu n e c e₁ hr)
    exact wrote_door hw

/-- **hquiet AT A LAYERS' LINK.** -/
theorem quiet_layers (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3) :
    ∀ o ∈ First.orderAfterOf .layers, ∀ run, AtAfter L o run →
      QuietOk atS (O9 (K := GE8) (phiAll u ψ) Ok Fu) (Fx9 (phiAll u ψ) Ok) run := by
  rw [after_layers]
  refine ⟨fun run h => ?_, fun run h => ?_, fun run h => ?_⟩
  · exact quietOk_under _ _ _ (A.ties.tLs run h) (k8_lsTail_quietOk (phiAll u ψ) Ok Fu u
      fun s tl tl' h1 h2 => phi_k8_keepT u ψ A.hψ s tl tl' h1 h2)
  · obtain ⟨r, h0, hu⟩ := A.ties.tFree run h
    exact quietOk_under _ _ _ hu (k4_freeSlot_quietOk (phiAll u ψ) Ok Fu p r h0
      fun s a G s' hw => phi_k4_keep u ψ A.hψ s a G s' hw)
  · exact quietOk_under _ _ _ (A.ties.tTests run h) (k8_tests_quietOk (phiAll u ψ) Ok Fu u
      (fun s tl tl' F1 h1 h2 => phi_k8_keep u ψ A.hψ s tl tl' F1 h1 h2) nU)

/-- **hquietd AT A LAYERS' LINK.** -/
theorem quietd_layers (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3) :
    ∀ o ∈ First.orderAfterOf .layers, ∀ run, AtAfter L o run →
      ∀ e e₁, run e = .ok e₁ → KeepsDoor atS e e₁ := by
  rw [after_layers]
  refine ⟨fun run h => ?_, fun run h => ?_, fun run h => ?_⟩
  · exact doorAfter_under atS (A.ties.tLs run h) k8LsTail_door
  · obtain ⟨r, h0, hu⟩ := A.ties.tFree run h
    exact doorAfter_under atS hu (k4_freeSlot_door p r h0)
  · exact doorAfter_under atS (A.ties.tTests run h) (k8Tests_door nU)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.phi_layers
#print axioms VerifiableInference.Desc.LinkJoin.pay_layers
#print axioms VerifiableInference.Desc.LinkJoin.payd_layers
#print axioms VerifiableInference.Desc.LinkJoin.quiet_layers
#print axioms VerifiableInference.Desc.LinkJoin.quietd_layers
