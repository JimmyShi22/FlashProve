-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3LedgerKeeps.lean: the kind "lookup" (K3): ITS OWN BLOCK AND RUNS ONLY MAKE THE
LEDGER A LATER ONE: what lies under a filled slot is kept, the number of slots stays, the next free
slot does not fall, the arrays keep their sizes (OnBytes.PscRun.Later,
OnBytes/Tie/Pv/Psc/PscLater.lean). Theorems with their proofs.

Main names:
  `decide_later`: of K3.block's decide, at a seat that reads back what it lays.
  `objects_later`, `join_later`, `planes_later`: of the three runs of claims; behind each what was
    heard still stands.
  `k3_ledgerKeeps`: decide's law for a reader "ledger" of the whole record that agrees with the
    seat.

Limits. decide_later and k3_ledgerKeeps stand under "the ledger in front has its sizes" (Sized) and
"the rounds' words are below the prime", ONLY BECAUSE they are drawn from the law on decide
(K3DecideHears), which is stated so. Neither premise is needed for the matter: the library's
hideRun_keeps (OnBytes/Tie/Pv/Psc/PscLater.lean) keeps the filled slots without any premise on
sizes; a proof that walks the hearing's text step by step would drop both. The three runs' laws have
neither. A block that always refuses meets these laws emptily.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3DecideHearsAt
import Johnson.Top.H.K3RunsLaw
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.K3 (Seat joinRun planesRun Readers)

variable {S Cl : Type}

/-- **decide.** -/
theorem decide_later (seat : Seat S Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) (hk : SeatKeeps seat)
    (hr : Desc.K3.SeatReads seat) {s s' : S} {rs : List Fmt.RoundView}
    {cols : List (List (ℕ × List UInt64))} {F : Fork} (hf : seat.fork s = some F)
    (hS : OnBytes.PscRun.Sized F) (hw : okRoundsE rs = true)
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ F', seat.fork s' = some F' ∧ OnBytes.PscRun.Later F F' := by
  obtain ⟨F1, F', g, e1, e2, _, _, hlaw⟩ :=
    k3DecideHears seat piece laid before p guests hk hr Cb.Gl.E Reading.gl 0 s s' rs cols hw hd
  obtain rfl : F = F1 := Option.some.inj (hf.symm.trans e1)
  obtain ⟨_, P, _⟩ := hlaw hS
  exact ⟨F', e2, ⟨by rw [P.next]; exact Nat.le_add_right _ _, P.rest.2.1, fun _ => P.fit, P.keep⟩⟩

/-- **decide, for one reader of the whole record.** ledger: it agrees with the seat wherever the
seat gives a ledger. -/
theorem k3_ledgerKeeps (seat : Seat S Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) (hk : SeatKeeps seat)
    (hr : Desc.K3.SeatReads seat) (ledger : S → Fork)
    (hl : ∀ s F, seat.fork s = some F → ledger s = F) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64))) (hS : OnBytes.PscRun.Sized (ledger s))
    (hw : okRoundsE rs = true)
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    OnBytes.PscRun.Later (ledger s) (ledger s') := by
  obtain ⟨F1, _, _, e1, _, _, _, _⟩ :=
    k3DecideHears seat piece laid before p guests hk hr Cb.Gl.E Reading.gl 0 s s' rs cols hw hd
  have h1 := hl s F1 e1
  obtain ⟨F', e2, hL⟩ := decide_later seat piece laid before p guests hk hr e1 (h1 ▸ hS) hw hd
  rw [h1, hl s' F' e2]
  exact hL

/-- **"objects"**: it lays a mark. -/
theorem objects_later (seat : Seat S Cl) (form : Cl → Aff) (hs : SeatFits seat form) {n : ℕ}
    {s s' : S} {cl : List Cl} {F : Fork} (hf : seat.fork s = some F)
    (hrun : objectsRun seat n s = .ok (cl, s')) :
    ∃ G, seat.fork s' = some G ∧ seat.heard s' = seat.heard s ∧ OnBytes.PscRun.Later F G := by
  unfold objectsRun at hrun
  rw [named_bind] at hrun
  obtain ⟨F1, e1, hrun⟩ := hrun
  rw [named_bind] at hrun
  obtain ⟨g, _, hrun⟩ := hrun
  obtain rfl : F = F1 := Option.some.inj (hf.symm.trans e1)
  have e3 : (g.rows.toList.map seat.claim, seat.mark s (F.paid g.owedObjects)) = (cl, s') :=
    Except.ok.inj hrun
  obtain ⟨_, rfl⟩ := Prod.mk.inj e3
  exact ⟨_, hs.markFork s F _ hf, hs.markHeard s F _ hf, OnBytes.PscRun.paid_later F _⟩

/-- **"join"**: it lays a mark. -/
theorem join_later (seat : Seat S Cl) (form : Cl → Aff) (hs : SeatFits seat form)
    (keys : S → Option (Array Aff)) {n : ℕ} {s s' : S} {cl : List Cl} {F : Fork}
    {g : Forest.Heard} (hf : seat.fork s = some F) (hg : seat.heard s = some g)
    (hrun : joinRun seat keys n s = .ok (cl, s')) :
    ∃ G, seat.fork s' = some G ∧ seat.heard s' = some g ∧ OnBytes.PscRun.Later F G := by
  obtain ⟨_, _, _, _, rfl⟩ := joinRun_cut seat keys hf hg hrun
  exact ⟨_, hs.markFork s F _ hf, (hs.markHeard s F _ hf).trans hg,
    OnBytes.PscRun.paid_later F _⟩

/-- **"planes"**: it puts the leaves' hiding coefficients under their slots and lays a mark. -/
theorem planes_later (seat : Seat S Cl) (form : Cl → Aff) (hs : SeatFits seat form) (lm : ℕ)
    (readers : Readers S) {n : ℕ} {s s' : S} {cl : List Cl} {F : Fork} {g : Forest.Heard}
    (hf : seat.fork s = some F) (hg : seat.heard s = some g)
    (hrun : planesRun seat lm readers n s = .ok (cl, s')) :
    ∃ G, seat.fork s' = some G ∧ seat.heard s' = some g ∧ OnBytes.PscRun.Later F G := by
  obtain ⟨r, rows, G, u, _, h1, _, rfl⟩ := planesRun_cut seat lm readers hf hg hrun
  obtain ⟨_, row, p', h2, _⟩ := Fo.Tp.planeClaims_run g lm _ _ (fun _ _ => quiet_need _)
    (fun _ => quiet_need _) F G [] u rows h1
  obtain ⟨-, -, -, -, -, hG, -, -⟩ := Fo.Tp.pscRow_ok _ _ _ _ _ _ _ _ _ h2
  exact ⟨_, hs.markFork s F _ hf, (hs.markHeard s F _ hf).trans hg,
    (OnBytes.PscRun.hideRun_keeps hG).trans (OnBytes.PscRun.paid_later G _)⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.decide_later
#print axioms VerifiableInference.OnPublicFiles.k3_ledgerKeeps
#print axioms VerifiableInference.OnPublicFiles.objects_later
#print axioms VerifiableInference.OnPublicFiles.join_later
#print axioms VerifiableInference.OnPublicFiles.planes_later
