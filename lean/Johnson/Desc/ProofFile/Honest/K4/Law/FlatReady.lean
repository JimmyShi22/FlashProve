-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FlatReady.lean: CONDITIONAL.

What is here. THE LEDGER IS READY FOR THE PART's TEXT OF THE MASKED SUMCHECK (`LedgerReady`,
Johnson/Desc/Part/MaskedSumReady.lean) where the verifier's flat text has run from it. At a product
level: from the flat function's own return at a sized ledger. At large: from a ledger with room
(`Room`, OnBytes/K/Kc/Returns/FlReturns.lean) in which the claimed form's slots are filled.
Statements and proofs.

  `sum_twos`, `own_count`   how many slots a sumcheck has of its own
  `weights_d`   variables whose weights are a level's have three coefficients
  `ready_of_room`   from a ledger with room
  `levelWs_sum`, `level_ready`   **at a product level, from the return**

Limits. THE FLAT FUNCTIONS OF A TOKEN SUMCHECK AND OF THE MERGE LAY NOTHING UNDER THE SUMCHECK's OWN
SLOTS (their rows are made later): so their returns do not say that these slots are free, and for
them the room is a premise. A product level makes its row itself. The variables have three
coefficients each. No prover is named. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatCore
import Johnson.Desc.Part.MaskedSumReady
import Johnson.Desc.Part.MaskedSumSound
import OnBytes.K.Kc.Returns.FlReturns
import OnBytes.Desc.First.P1.Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork Level)
open OnBytes.PscRun (Sized Filled)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.Desc.First.P1 (levelWs levelIn_tape walk_length filledA_of_publicPart sum_level)
open VerifiableInference.Desc.Part.MaskedSum

/-! ## 1 How many slots a sumcheck has of its own -/

/-- Variables of three coefficients: two slots each. -/
theorem sum_twos : ∀ vs : List Var, (∀ v ∈ vs, v.d = 3) →
    (vs.map fun v => v.d - 1).sum = 2 * vs.length
  | [], _ => rfl
  | v :: vs, h => by
    rw [List.map_cons, List.sum_cons, h v (by simp),
      sum_twos vs fun u hu => h u (by simp [hu]), List.length_cons]
    omega

/-- One slot, two for each variable, and as many as the degree in the further variable. -/
theorem own_count (vs : List Var) (h : ∀ v ∈ vs, v.d = 3) (dY : ℕ) :
    ownSlots (vs ++ [Var.point zeroE (dY + 1)]) = 1 + 2 * vs.length + dY := by
  rw [ownSlots_eq, List.map_append, List.sum_append, sum_twos vs h]
  show 1 + (2 * vs.length + (dY + 1 - 1 + 0)) = _
  omega

/-- Variables whose weights all have three coefficients have three. -/
theorem weights_d (vs : List Var) (ws : List OnBytes.Psc.Weight) (hk : vs.map Var.weight = ws)
    (hw : ∀ w ∈ ws, w.d = 3) : ∀ v ∈ vs, v.d = 3 := by
  intro v hv
  rw [← Var.weight_d]
  exact hw _ (by rw [← hk]; exact List.mem_map_of_mem hv)

/-! ## 2 From a ledger with room -/

/-- **A ledger with room for the sumcheck's own slots and its end values, in which the claimed
form's slots are filled, is ready.** -/
theorem ready_of_room {C : Aff} {k : Call} {F : Fork}
    (hR : D6.Ret.Room F (ownSlots k.all + k.endsN))
    (hC : Fo.FilledA F C) : LedgerReady C k F :=
  ⟨hR.sized, hC, by have := hR.fits; omega, fun j hj _ => hR.free j hj⟩

/-! ## 3 At a product level, from the return -/

/-- **Where the flat function of a product level returns from a sized ledger, that ledger is ready
for the part's text**, at the same claimed form and at a call whose variables' weights are the
level's. -/
theorem level_ready {mu : ℕ} {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork} {t u : Tape}
    {L : Level} (hF : Fl.levelIn mu rho C order F t = some (L, G, u)) (hS : Sized F)
    (vs : List Var) (hk : vs.map Var.weight = levelWs mu rho order) :
    LedgerReady C ⟨0, vs, some ⟨2, 2⟩⟩ F := by
  obtain ⟨hom, T, mu0, eps, rs, sentY, beta, tau, w0, wY, wV, wT, ms, y, shL, shR, v, G1, p, _,
    _, _, _, _, _, _, _, hTp, a1, hy, hheld, _, hvars, hr, _, _, _, _, hfirst, _, _, hsL, _, hv2,
    hG1, _, _, hG⟩ := levelIn_tape hF
  have hvl : vs.length = mu := by
    have e := congrArg List.length hk
    rw [List.length_map] at e
    rw [e, levelWs, List.length_map, hom]
  have hd : ∀ v ∈ vs, v.d = 3 := weights_d vs _ hk (by
    intro w hw
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp hw
    rfl)
  have hown : ownSlots (Call.all ⟨0, vs, some ⟨2, 2⟩⟩) = 1 + 2 * mu + 2 := by
    show ownSlots (vs ++ [Var.point zeroE (2 + 1)]) = _
    rw [own_count vs hd 2, hvl]
  have hm1 : (ms ++ [y]).map (·.1) = levelWs mu rho order ++ [OnBytes.Psc.Weight.atZero 3] := by
    rw [List.map_append, a1, List.map_cons, List.map_nil, hy]
  have hwl : p.walk.1.length = 1 + 2 * mu + 2 := by
    rw [walk_length (ms := ms ++ [y]) (by simp) (by rw [hvars, hm1]) hr hheld, hm1,
      OnBytes.Psc.hidingEntries, List.map_append, List.sum_append, sum_level, hom]
    show 1 + (2 * mu + (2 + 0)) = _
    omega
  have hF' : Sized ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork) := hS
  obtain ⟨_, hS1, hin1, hout1⟩ := OnBytes.PscRun.hideRun_ok _ G1 L.sL v y.2.2 hF' hG1
  obtain ⟨_, _, hin2, _⟩ := OnBytes.PscRun.hideRun_ok G1 G p.first _ _ hS1 hG
  refine ⟨hS, filledA_of_publicPart hTp, ?_, ?_⟩
  · have b := (hin1 1 (by omega)).1
    have b' : L.sL + 1 < F.ns := b
    rw [hown]
    show F.next + (1 + 2 * mu + 2) + 2 ≤ F.ns
    omega
  · intro j h1 h2
    rw [hown] at h2
    have h2' : j < F.next + (1 + 2 * mu + 2) + 2 := h2
    by_cases hj : j < L.sL
    · have c := (hin2 (j - F.next) (by rw [Array.size_replicate, hwl]; omega)).2.1
      rw [hfirst, show F.next + (j - F.next) = j by omega] at c
      intro hf
      exact c ((hout1 j (Or.inl hj)).2.2.mpr hf)
    · have c := (hin1 (j - L.sL) (by omega)).2.1
      rw [show L.sL + (j - L.sL) = j by omega] at c
      exact c

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.sum_twos
#print axioms ProofFile.Honest.K4.own_count
#print axioms ProofFile.Honest.K4.weights_d
#print axioms ProofFile.Honest.K4.ready_of_room
#print axioms ProofFile.Honest.K4.level_ready
