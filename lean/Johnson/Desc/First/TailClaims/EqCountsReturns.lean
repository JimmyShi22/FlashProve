-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/EqCountsReturns.lean: one part of the smallness test's run of
equations (eqCounts, Johnson/Desc/First/TailClaims/Equations.lean: the three claims on the planes of
the lookup's counts) RETURNS wherever two conditions on the shape of its input hold, at all values;
with the shapes behind. General laws: nothing is evaluated.

Why. Whoever wants to show that a run of the verifier's own text returns at the full size cannot let
Lean's kernel walk it where the run builds large tables. eqCounts builds three (two tables of the
equality polynomial and a list of powers of 2, each with one entry a column of the planes' array).
Here the tables stay unopened terms inside the claims that are laid; their sizes come by a law.

  run_bind, run_err   how a run goes on behind a step that returns, and ends at one that refuses.
  eqPscRow_returns   the sumcheck's row, under the library's own condition Open
                  (OnBytes/K/Kc/Returns/FlReturns6.lean: four flags and sizes; the ledger's arrays
                  have their size; the sumcheck's own slots are there and free).
  countsClaims    the shapes of the three claims (Johnson/Desc/First/Shape/Parts.lean). The first
                  one's form is the sumcheck's row: its own slots, then the start form's entries and
                  slots (affSh_rowForm there).
  **eqCounts_returns**   tl.heard = some g and Open g.leaves F: then eqCounts returns; the record
                  behind is the record in front but for one field element; the ledger's shape behind
                  is the shape in front with the sumcheck's own slots filled and one owed mark paid;
                  three claims more lie on the list, of these shapes.
  eqCounts_no_heard, eqCounts_row_twice   the two conditions are not idle: without a heard record,
                  and with the row made already, the run refuses, each under its own name.

Limits. What the claims say is not said. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.TailClaims.RetRules
import Johnson.Desc.First.Shape.Parts
import Johnson.Road.FormsKeysEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.PscRun VerifiableInference.Desc
open VerifiableInference.Desc.First.Shape
open D6.Ret (Open taken walk_taken)

/-- Two steps compose where the first returns. -/
theorem run_bind {α β : Type} {x : EqM α} {f : α → EqM β} {front : Nat} {s s' : St} {a : α}
    (hx : x front s = .ok (a, s')) : (x >>= f) front s = f a front s' := by
  show (x front s >>= fun p => f p.1 front p.2) = _
  rw [hx]
  rfl

/-- A step that refuses ends the run. -/
theorem run_err {α β : Type} {x : EqM α} {f : α → EqM β} {front : Nat} {s : St} {e : String}
    (hx : x front s = .error e) : (x >>= f) front s = .error e := by
  show (x front s >>= fun p => f p.1 front p.2) = _
  rw [hx]
  rfl

/-- **The sumcheck's row returns where the sumcheck is open**, at all values. -/
theorem eqPscRow_returns {p : Psc} {G : Fork} (h : Open p G) (S0 : E) (kept : Aff) (front : Nat)
    (cs : Array Claim) :
    Ret (eqPscRow p S0 kept) front (G, cs) fun x s' =>
      x = (p.rowForm S0 kept, { p with rowMade := true }) ∧
      ∃ H, s' = (H, cs) ∧ Same G H ∧ Sized H ∧
        ledSh H = (ledSh G).setGot (fillB (ledSh G).got p.first (taken p)) := by
  have hsz : (Array.replicate p.walk.1.length zeroE : Array E).size = taken p := by
    rw [Array.size_replicate, walk_taken h]
  obtain ⟨H, hH, a1, a2, a3⟩ := hide_of_free (F := G) (first := p.first)
    (v := Array.replicate p.walk.1.length zeroE) h.sized (by rw [hsz]; exact h.fits)
    (fun i hi => h.own _ (by omega) (by rw [hsz] at hi; omega)) (subE zeroE oneE)
  rw [hsz] at a3
  have hv : p.vars.isEmpty = false := by
    cases hq : p.vars.toList with
    | nil => exact absurd hq h.some
    | cons a l =>
      have : p.vars.size ≠ 0 := by
        rw [← Array.length_toList, hq]
        simp
      simpa [Array.isEmpty] using this
  have hb : (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true := by
    rw [h.noRow, h.started, hv, h.sizes]
    simp
  unfold eqPscRow
  refine Ret.bind (Ret.mustAs _ hb (Q := fun _ s' => s' = (G, cs)) rfl) ?_
  rintro _ _ rfl
  refine Ret.bind (Ret.change _ hH (Q := fun _ s' => s' = (H, cs)) rfl) ?_
  rintro _ _ rfl
  exact Ret.pure _ ⟨rfl, H, rfl, a1, a2, a3⟩

/-- The shapes of the three claims. -/
def countsClaims (tl : HTailF2) (g : Forest.Heard) : List ClaimSh :=
  let KB := 2 ^ (tl.f9.kT + tl.f9.cK)
  let sz := fun z : Nat => 2 ^ (min (5 + tl.f9.kT + tl.f9.cK) z - 5)
  [ClaimSh.mk none
      (rowFormSh g.leaves.first (taken g.leaves) (affSh g.leaves.start) (AffSh.mk [] []))
      [RunSh.mk tl.ix.BZ 0 0 (sz g.zb0.size) 0 KB],
    ClaimSh.mk none (AffSh.mk [] [g.sBit]) [RunSh.mk tl.ix.BZ 1 0 (sz g.zb1.size) 0 KB],
    ClaimSh.mk none (AffSh.mk [] []) [RunSh.mk tl.ix.BZ 2 0 KB 0 KB]]

/-- **The three claims on the planes of the lookup's counts: the run returns**, at all values. -/
theorem eqCounts_returns {tl : HTailF2} {g : Forest.Heard} {F : Fork} (hg : tl.heard = some g)
    (h : Open g.leaves F) (front : Nat) (cs : Array Claim) :
    Ret (eqCounts tl) front (F, cs) fun tl' s' =>
      (∃ bf, tl' = { tl with bitFactor9 := bf }) ∧
      ledSh s'.1 = ((ledSh F).setGot (fillB (ledSh F).got g.leaves.first (taken g.leaves))).setOwed
        (paidB (ledSh F).owed g.owedPlanes) ∧
      s'.2.toList.map claimSh = cs.toList.map claimSh ++ countsClaims tl g := by
  unfold eqCounts eqPlanesAdded
  refine Ret.bind (Ret.get _ hg (Q := fun a s' => a = g ∧ s' = (F, cs)) ⟨rfl, rfl⟩) ?_
  rintro g' _ ⟨hg', rfl⟩
  rw [hg']
  dsimp only
  refine Ret.bind (eqPscRow_returns h oneE {} front cs) ?_
  rintro ⟨row, p'⟩ _ ⟨hx, H, rfl, -, -, hL⟩
  obtain ⟨rfl, -⟩ := Prod.mk.inj hx
  dsimp only
  refine Ret.bind (Ret.emit _ (Q := fun _ s' => H = s'.1 ∧ s'.2.toList.map claimSh =
    cs.toList.map claimSh ++ (countsClaims tl g).take 1) ⟨rfl, by
      rw [claims_push]
      congr 1
      show [ClaimSh.mk none (affSh (g.leaves.rowForm oneE {}))
        [RunSh.mk _ _ _ (eqTab _).size _ _]] = _
      rw [OnBytes.Road.eqTab_size, Array.size_extract, affSh_rowForm, walk_taken h]
      rfl⟩) ?_
  rintro _ ⟨_, cs₁⟩ ⟨rfl, h₁⟩
  refine Ret.bind (Ret.emit _ (Q := fun _ s' => H = s'.1 ∧ s'.2.toList.map claimSh =
    cs.toList.map claimSh ++ (countsClaims tl g).take 2) ⟨rfl, by
      rw [claims_push]
      dsimp only at h₁ ⊢
      rw [h₁, List.append_assoc]
      congr 1
      show _ :: [ClaimSh.mk none _ [RunSh.mk _ _ _ (eqTab _).size _ _]] = _
      rw [OnBytes.Road.eqTab_size, Array.size_extract]
      rfl⟩) ?_
  rintro _ ⟨_, cs₂⟩ ⟨rfl, h₂⟩
  refine Ret.bind (Ret.emit _ (Q := fun _ s' => H = s'.1 ∧ s'.2.toList.map claimSh =
    cs.toList.map claimSh ++ countsClaims tl g) ⟨rfl, by
      rw [claims_push]
      dsimp only at h₂ ⊢
      rw [h₂, List.append_assoc]
      congr 1
      show _ :: _ :: [ClaimSh.mk none _ [RunSh.mk _ _ _ (Array.map _ (Array.range _)).size _ _]] =
        _
      rw [Array.size_map, Array.size_range]
      rfl⟩) ?_
  rintro _ ⟨_, cs₃⟩ ⟨rfl, h₃⟩
  refine Ret.bind (Ret.paid _ (Q := fun _ s' => s' = (H.paid g.owedPlanes, cs₃)) rfl) ?_
  rintro _ _ rfl
  refine Ret.pure _ ⟨⟨_, rfl⟩, ?_, h₃⟩
  show ledSh (H.paid g.owedPlanes) = _
  rw [ledSh_paid, hL]
  rfl

/-- Without a heard record it refuses. -/
theorem eqCounts_no_heard {tl : HTailF2} (hg : tl.heard = none) (front : Nat) (F : Fork)
    (cs : Array Claim) : eqCounts tl front (F, cs) = .error "linBits9:883" := by
  unfold eqCounts
  rw [hg]
  rfl

/-- With the row made already it refuses. -/
theorem eqCounts_row_twice {tl : HTailF2} {g : Forest.Heard} (hg : tl.heard = some g)
    (hr : g.leaves.rowMade = true) (front : Nat) (F : Fork) (cs : Array Claim) :
    eqCounts tl front (F, cs) = .error "pscRow:198" := by
  unfold eqCounts
  rw [hg, run_bind (a := g) (s' := (F, cs)) rfl]
  dsimp only
  unfold eqPscRow
  rw [hr]
  rfl

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.run_bind
#print axioms VerifiableInference.Desc.First.TailClaims.Law.run_err
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqPscRow_returns
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqCounts_returns
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqCounts_no_heard
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqCounts_row_twice
