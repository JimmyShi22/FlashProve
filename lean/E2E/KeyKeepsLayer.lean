-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyKeepsLayer.lean: THE PAYER OF `LayerKeeps` (E2E/KeyKeepsEq.lean): what the yes of a lookup's
layer leaves of the first chain's state: at the numbers 5 and 11 of the key file's first chain. By
unfolding the library's texts. On the verifier's step alone. NOTHING IS SHOWN OF ANY PROVER.

THE LIBRARY HAS THE LIKE (Johnson/RunOne/Law/LayerBehind.lean, StepSide4.lean): `layPut`: the very
state behind · `yes_layer`: the layer's yes gives that state WITH facts on the ledger behind (its
count and room are those in front; it is sized; every slot below the count is filled), that the rows
are not none, and as many claims on keys as the lookup has parts: UNDER A PREMISE on what the
lookup's own sub-protocol has left in the state · `claims_d`, `layer_d`: a yes leaves the
statement's part: no premise · AND (Johnson/RunOne/Law/AtKeyD.lean) `layerD_law`: the layer's yes,
at any gathering of claims: what is written, by name, onto the state behind the gathering: no
premise: CALLED HERE · `claimsD_law`: the gathering turns the ledger alone, with the ledger behind
by name: where a ledger is open and something was heard in front · `runIn_ok`
(Johnson/Desc/First/Look/KeyLaw/Runs.lean): the like of `step_of_run`. WHAT STANDS HERE AND NOT
THERE: that the gathering turns the ledger alone WITH NO PREMISE, and so the equation on the whole
state from the state in front of the layer. WHAT STANDS THERE AND NOT HERE: the facts on the ledger,
without which the library's Bool cannot be carried across a layer.

  `LedgerApart s t`: t is s but for the open ledger
  `fk_refl`, `fk_trans`, `fk_mark`, `step_of_run`: small ones
  `run_objects`, `run_planes`, `run_guests`: each of the three runs of a lookup's claims turns the
      open ledger alone
  **`claims_fk`**: so the gathering of a lookup's claims, which the layer is handed, turns the open
      ledger alone
  **`layer_keeps`**: the layer's yes: `LayerKeeps`: by `layerD_law` and `claims_fk`
  `dec_layer0`, `dec_layer1`: the sub-protocols number 5 and 11 of the first chain's flat list
      decide as the two lookups' layers, where the plan has just two lookups
  `layerKeeps_iff`: THE JOINT: `LayerKeeps` says that the state behind is the library's `layPut`: by
      unfolding
  **`keeps_layers`**: THE PAYER, from the sub-protocol's accepting step

Texts: `layer`, `lookupLink`, `lookupSeat` (Johnson/Desc/Key/Link.lean) · `claimsInBy`,
`claimsInStep`, `Link.blocksInOrder` (Johnson/Desc/Block.lean) · `lookupKind`
(Johnson/Desc/First/Look/K3LookupGeneral.lean).

Limits. An equation on the state, up to three values: nothing on what the rows and the claims on
keys that are written are worth. The premise on the public values is not shown here. That an item
which is open across a layer says behind it what it said in front: E2E/KeyRides.lean.

-/
import E2E.KeyKeepsEq
import Johnson.RunOne.KeyTenAt
import Johnson.RunOne.Law.LayerBehind
import Johnson.Top.H0.Walk.ReachInv
import Johnson.Desc.ProofFile.Honest.Law.Play

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block claimsInBy claimsInStep named need)
open VerifiableInference.Desc.Key (FirstState Claim Lookup lookupsOf firstChain lookupLink layer
  lookupSeat lookupPlace)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)
open ProofFile.Honest (exBind_ok)

/-- t is s but for the open ledger. -/
def LedgerApart (s t : FirstState) : Prop := ∃ F₀, t = { s with base := { s.base with fork := F₀ } }

theorem fk_refl (s : FirstState) : LedgerApart s s := ⟨s.base.fork, rfl⟩

theorem fk_trans {s t u : FirstState} (h : LedgerApart s t) (h' : LedgerApart t u) :
    LedgerApart s u := by
  obtain ⟨A, rfl⟩ := h
  obtain ⟨B, rfl⟩ := h'
  exact ⟨B, rfl⟩

theorem fk_mark (s : FirstState) (F : OnBytes.Model.Fork) : LedgerApart s (lookupSeat.mark s F) :=
  ⟨some F, rfl⟩

section
variable (one : OnBytes.Params.OneTime) (set : OnBytes.Params.Setting) (i : Nat) (x : Lookup)

/-- One step of the gathering, from a fact on its run: what the run leaves, the step leaves. -/
theorem step_of_run {o : Nat × String} {a b : List Claim × FirstState}
    (h : claimsInStep (lookupLink one set i x).each (lookupLink one set i x).hear a o = .ok b) :
    ∃ run y, named (o.2 ++ ": no such run")
        (((lookupLink one set i x).hear[o.1]?).bind fun c => c.claims.lookup o.2) = .ok run ∧
      run a.1.length a.2 = .ok y ∧ b.2 = y.2 := by
  unfold claimsInStep at h
  obtain ⟨run, hrun, h⟩ := exBind_ok h
  cases hy : run a.1.length a.2 with
  | error e =>
    rw [hy] at h
    cases h
  | ok y =>
    rw [hy] at h
    have hb : (a.1 ++ y.1, y.2) = b := Except.ok.inj h
    exact ⟨run, y, hrun, hy, by rw [← hb]⟩

theorem run_objects {a b : List Claim × FirstState}
    (h : claimsInStep (lookupLink one set i x).each (lookupLink one set i x).hear a (1, "objects") =
      .ok b) : LedgerApart a.2 b.2 := by
  obtain ⟨run, y, hrun, hy, hb⟩ := step_of_run one set i x h
  have er : _ = run := Except.ok.inj hrun
  subst er
  obtain ⟨F, -, h1⟩ := exBind_ok hy
  obtain ⟨g, -, h2⟩ := exBind_ok h1
  have e := Except.ok.inj h2
  rw [hb, ← e]
  exact fk_mark _ _

theorem run_planes {a b : List Claim × FirstState}
    (h : claimsInStep (lookupLink one set i x).each (lookupLink one set i x).hear a (1, "planes") =
      .ok b) : LedgerApart a.2 b.2 := by
  obtain ⟨run, y, hrun, hy, hb⟩ := step_of_run one set i x h
  have er : _ = run := Except.ok.inj hrun
  subst er
  obtain ⟨F, -, h1⟩ := exBind_ok hy
  obtain ⟨g, -, h2⟩ := exBind_ok h1
  obtain ⟨_, -, h3⟩ := exBind_ok h2
  obtain ⟨z, -, h4⟩ := exBind_ok h3
  obtain ⟨l, -, h5⟩ := exBind_ok h4
  have e := Except.ok.inj h5
  rw [hb, ← e]
  exact fk_mark _ _

theorem run_guests {a b : List Claim × FirstState}
    (h : claimsInStep (lookupLink one set i x).each (lookupLink one set i x).hear a (1, "guests") =
      .ok b) : LedgerApart a.2 b.2 := by
  obtain ⟨run, y, hrun, hy, hb⟩ := step_of_run one set i x h
  have er : _ = run := Except.ok.inj hrun
  subst er
  have e : (([] : List Claim), a.2) = y := Except.ok.inj hy
  rw [hb, ← e]
  exact fk_refl _

/-- **The gathering of a lookup's claims turns the open ledger alone.** -/
theorem claims_fk (s : FirstState) (b : List Claim × FirstState)
    (h : claimsInBy (lookupLink one set i x).each (lookupLink one set i x).hear
      (lookupLink one set i x).order s = .ok b) : LedgerApart s b.2 := by
  unfold claimsInBy at h
  obtain ⟨x₂, h₂, h₃⟩ := exBind_ok
    (show Except.bind _ (fun z => claimsInStep (lookupLink one set i x).each
      (lookupLink one set i x).hear z (1, "guests")) = .ok b from h)
  obtain ⟨x₁, h₁, h₂⟩ := exBind_ok
    (show Except.bind _ (fun z => claimsInStep (lookupLink one set i x).each
      (lookupLink one set i x).hear z (1, "planes")) = .ok x₂ from h₂)
  have h₀ : claimsInStep (lookupLink one set i x).each (lookupLink one set i x).hear ([], s)
      (1, "objects") = .ok x₁ := h₁
  exact fk_trans (fk_trans (run_objects one set i x h₀) (run_planes one set i x h₂))
    (run_guests one set i x h₃)

/-- **The layer's yes.** -/
theorem layer_keeps (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (layer one set i x (claimsInBy (lookupLink one set i x).each (lookupLink one set i x).hear
      (lookupLink one set i x).order)).decide s rs gs = .ok s') : LayerKeeps s s' := by
  obtain ⟨cls, t, F, g, rows, keys, hc, -, -, -, -, e⟩ := Johnson.RunOne.Law.AtKeyD.layerD_law h
  obtain ⟨F₀, hF⟩ := claims_fk one set i x s (cls, t) hc
  have hF' : t = { s with base := { s.base with fork := F₀ } } := hF
  refine ⟨F.paid g.owedJoin, rows, keys, ?_⟩
  rw [e, hF']

end

section
variable (one : OnBytes.Params.OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
  (set : OnBytes.Params.Setting) (N : H2U.PlaceNums) (x₀ x₁ : Lookup)

theorem dec_layer0 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim)
    (h : (firstChain one D told set N).blocksInOrder[5]? = some b) (s : FirstState) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = (layer one set 0 x₀ (claimsInBy (lookupLink one set 0 x₀).each
      (lookupLink one set 0 x₀).hear (lookupLink one set 0 x₀).order)).decide s rs gs := by
  simp only [firstChain, hl] at h
  have e : _ = b := Option.some.inj h
  subst e
  rfl

theorem dec_layer1 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim)
    (h : (firstChain one D told set N).blocksInOrder[11]? = some b) (s : FirstState) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = (layer one set 1 x₁ (claimsInBy (lookupLink one set 1 x₁).each
      (lookupLink one set 1 x₁).hear (lookupLink one set 1 x₁).order)).decide s rs gs := by
  simp only [firstChain, hl] at h
  have e : _ = b := Option.some.inj h
  subst e
  rfl

/-- **THE JOINT TO THE LIBRARY's NAME**: the state behind is the library's `layPut`. -/
theorem layerKeeps_iff (s s' : FirstState) :
    LayerKeeps s s' ↔ ∃ F' rows keys, s' = Johnson.RunOne.Law.LayerBehind.layPut s F' rows keys :=
  Iff.rfl

/-- **THE PAYER.** -/
theorem keeps_layers (hl : lookupsOf one = [x₀, x₁]) (ft : Nat)
    (other : Nat → FirstState → FirstState → Prop) :
    ∀ b ∈ [5, 11], ∀ blk, (firstChain one D told set N).blocksInOrder[b]? = some blk → ∀ s s',
      StepYes ft blk s s' → eq₁ one other b s s' := by
  intro b hb blk hblk s s' hy
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · rw [dec_layer0 one D told set N x₀ x₁ hl blk hblk] at e
    exact layer_keeps one set 0 x₀ s s' rs gs e
  · rw [dec_layer1 one D told set N x₀ x₁ hl blk hblk] at e
    exact layer_keeps one set 1 x₁ s s' rs gs e

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.fk_refl
#print axioms AtPublicFiles.KeyThread.fk_trans
#print axioms AtPublicFiles.KeyThread.fk_mark
#print axioms AtPublicFiles.KeyThread.step_of_run
#print axioms AtPublicFiles.KeyThread.run_objects
#print axioms AtPublicFiles.KeyThread.run_planes
#print axioms AtPublicFiles.KeyThread.run_guests
#print axioms AtPublicFiles.KeyThread.claims_fk
#print axioms AtPublicFiles.KeyThread.layer_keeps
#print axioms AtPublicFiles.KeyThread.dec_layer0
#print axioms AtPublicFiles.KeyThread.dec_layer1
#print axioms AtPublicFiles.KeyThread.layerKeeps_iff
#print axioms AtPublicFiles.KeyThread.keeps_layers
