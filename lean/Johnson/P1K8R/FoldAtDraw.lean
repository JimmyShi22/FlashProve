-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FoldAtDraw.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: A
PAYMENT BENEATH THE KIND'S FROZEN CONDITION: THE FIELD `fold` OF `K8LeftT` FROM THE HEAD ALONE, AT
ALL 25 LINKS; AND ONE CLOSED FACT OF `SmallOwes`. NO SOUNDNESS.

`K8FoldAt` (P1K8R/TightAt.lean) is nine plain equations on the open link and the statement of
oracles, at the state in front of the draw. Each is proved in other files along the fold from the
first state (Johnson/IMR/FrameEntry.lean `members_at`, HeadMembers.lean `members_head`,
ArraysOpen.lean `arrays_open`, OwnSize.lean `own_size_draw`, `own_size_head`). Here they are joined
at one open link, and carried from "reached" to the fold by `rchAt_fold`:
  `n0At Zp l`: the number of link l's messages of moments 0 and 1.
  `k08_fold_at`: **under the head, at every state that is reached at the draw's number of link l ≤
    24: `K8FoldAt Zp G l Xl (n0At Zp l)`.** Neither the promise nor "no mark" is spent.
  `k08_fold_field`: `K8LeftT`'s field `fold`, to the letter, at n₀ := `n0At Zp l`, at every
    condition that gives `RchAt`.
  `layout_at`: the ground's layout is the constant's (`SmallOwes.layout`): by
    `blank_first` (Johnson/IMR/ArraysOpen.lean).
Limits. That the head can be met is other files' to show. AT `OnBytes.secondHashFunction` ALONE. Nothing on
soundness.

-/
import Johnson.P1K8R.TightAt
import Johnson.IMR.FrameEntry
import Johnson.IMR.HeadMembers
import Johnson.IMR.ArraysOpen
import Johnson.IMR.OwnSize

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Iop
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.K8
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_fold)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

/-- The number of link l's messages of moments 0 and 1. -/
def n0At (Zp : ProofFile.Pub) (l : ℕ) : ℕ :=
  Meaning.K2.msgsAt Zp.first.shape l 0 + Meaning.K2.msgsAt Zp.first.shape l 1

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE NINE EQUATIONS, AT EVERY REACHED STATE IN FRONT OF THE DRAW, FROM THE HEAD ALONE.** -/
theorem k08_fold_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (hr : RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) (drawAt l) a) :
    K8FoldAt Zp G l Xl (n0At Zp l) a.1.2 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨-, rs, cols, f⟩ := rchAt_fold hr
  have f' : VerifiableInference.Desc.foldBlocks 0 (cF.blocksInOrder.take (drawAt l)) (ProofFile.startS Zp a.1.1) rs
      cols = .ok (a.1.2, [], []) := f
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · have ed : drawAt l = 14 * l + 6 := by
      unfold drawAt
      rw [if_neg (by omega)]
    rw [ed] at f'
    obtain ⟨L, Gr, pre, hL, -, hg, hGr, -, hmem, -, -⟩ :=
      Meaning.K2.members_at h.scope h.reads O h24 (n := 3) (by omega) f'
    obtain ⟨L₂, hL₂, -, e1, e2, -⟩ := Meaning.K2.arrays_open h.scope h.reads O (by omega : l < 25)
      e3 (k := 14 * l + 6) (by rw [if_neg (by omega)]; omega) (by rw [if_neg (by omega)]; omega) f'
    obtain ⟨L₃, hL₃, -, e5, e6, e4, -⟩ :=
      Meaning.K2.own_size_draw h.scope h.reads O h24 (n := 0) (by omega) f'
    obtain rfl : L = L₂ := Option.some.inj (hL.symm.trans hL₂)
    obtain rfl : L = L₃ := Option.some.inj (hL.symm.trans hL₃)
    exact ⟨L, Gr, pre, hL, hg, hGr, hmem, e1, e2, e5, e6, e4⟩
  · obtain rfl : l = 24 := by omega
    have f'' : VerifiableInference.Desc.foldBlocks 0 (cF.blocksInOrder.take 343) (ProofFile.startS Zp a.1.1) rs
        cols = .ok (a.1.2, [], []) := f'
    obtain ⟨L, Gr, n₁, hL, -, hg, hGr, hmem, -, -⟩ :=
      Meaning.K2.members_head h.scope h.reads O (n := 3) (by omega) f''
    obtain ⟨L₂, hL₂, -, e1, e2, -⟩ := Meaning.K2.arrays_open h.scope h.reads O (by omega : 24 < 25)
      e3 (k := 343) (by decide) (by decide) f''
    obtain ⟨L₃, hL₃, -, e5, e6, e4, -⟩ :=
      Meaning.K2.own_size_head h.scope h.reads O (n := 0) (by omega) f''
    obtain rfl : L = L₂ := Option.some.inj (hL.symm.trans hL₂)
    obtain rfl : L = L₃ := Option.some.inj (hL.symm.trans hL₃)
    exact ⟨L, Gr, #[n₁], hL, hg, hGr, hmem, e1, e2, e5, e6, e4⟩

/-- **`K8LeftT`'s FIELD `fold`, TO THE LETTER.** -/
theorem k08_fold_field (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Fr : Frame} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a) :
    ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      a.1.failed = none → K8FoldAt Zp G l Xl (n0At Zp l) a.1 :=
  fun z a _ hr _ => k08_fold_at h hG hl e3 ((z, a.1), a.2) (hRch _ _ hr)

/-- The ground's layout is the constant's. -/
theorem layout_at {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    G.first.layout = P5J.At.layout Zp :=
  congrArg (·.layout) (Meaning.K2.blank_first hG)

end P1K8T

#print axioms P1K8T.k08_fold_at
#print axioms P1K8T.k08_fold_field
#print axioms P1K8T.layout_at
