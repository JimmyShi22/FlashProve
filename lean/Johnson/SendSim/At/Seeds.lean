-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Seeds.lean: the seed of an answer (seedAt) is one of the seeds that are cut off
the challenge; if the challenge consists of exactly the seeds, its point has at least as many
coordinates as the answer's oracle message reads.
Terms: Johnson/SendSim/At/Sim.lean; seedAt: Johnson/SendSim/At/Bridge.lean. Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves: lemmas on lists and public numbers. In each, k < P.sent.size, and i is below
the number of answers of oracle message k.
  seedAt_get, seedAt_mem   seedAt P ds i is entry i of the list seedsAt P ds, so it is a member of
                    that list and not a default value. No premise on ds.
  seedAt_len        If the challenge consists of exactly the seeds (seedsFit), the seed's point has
                    P.coordinates coordinates.
  v_le_len          Under seedsFit, oracle message k reads at most as many coordinates as the seed's
                    point has. v_le_coordinates: a sampled oracle message reads at most
                    P.coordinates.
  has_table         If the job fits its place (sendFits), oracle message k has a main row or a mask
                    row.
  shape_mem, answers_le_seeds   shapeAt P k is one of P's shapes; it has at most P.seeds answers.

How it fits. Johnson/SendSim/At/Answers.lean uses v_le_len and has_table as the premises of
value_stAt (Johnson/SendSim/At/Stat.lean). Johnson/SendSim/At/Shown.lean,
Johnson/SendSim/At/PadsOf.lean and Johnson/SendSim/At/PadSeat.lean use seedAt_mem to get "this
seed's factor is not 0" from the premise on all seeds. So the file serves rowsExact
(Johnson/SendSim/At/RowsExact.lean) and rowsFresh (Johnson/SendSim/At/RowsFresh.lean). The proofs
rest on the library's lemmas on K1.cutSeeds (Johnson/Desc/K1/Law/Writes3.lean,
Johnson/Desc/K1/Law/Joined2.lean).
-/
import Johnson.Desc.K1.Law.Joined2
import Johnson.Desc.ProofFile.Honest.K1.PadLaw
import Johnson.SendSim.At.Bridge

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

variable (P : K1.Par) (ride : Nat → Option Ride)

theorem shape_mem (k : ℕ) (hk : k < P.sent.size) : shapeAt P k ∈ K1.shapesOf P := by
  unfold K1.shapesOf shapeAt
  rw [List.mem_map]
  refine ⟨P.sent[k], Array.getElem_mem_toList _, ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
  rfl

theorem answers_le_seeds (k : ℕ) (hk : k < P.sent.size) : (shapeAt P k).answers ≤ P.seeds :=
  K1.le_seeds P _ (shape_mem P k hk)

/-- For k < P.sent.size and an answer i of oracle message k, seedAt P ds i is entry i of seedsAt P
ds: the list is long enough, so the default seed is not used. -/
theorem seedAt_get (ds : List Fmt.Drawn) (k i : ℕ) (hk : k < P.sent.size)
    (hi : i < (shapeAt P k).answers) : (seedsAt P ds)[i]? = some (seedAt P ds i) := by
  have hl : i < (seedsAt P ds).length := by
    unfold seedsAt
    rw [K1.cutSeeds_length]
    exact lt_of_lt_of_le hi (answers_le_seeds P k hk)
  unfold seedAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  rfl

/-- For such k and i, seedAt P ds i is a member of seedsAt P ds. -/
theorem seedAt_mem (ds : List Fmt.Drawn) (k i : ℕ) (hk : k < P.sent.size)
    (hi : i < (shapeAt P k).answers) : seedAt P ds i ∈ seedsAt P ds :=
  List.mem_of_getElem? (seedAt_get P ds k i hk hi)

/-- For such k and i, if the challenge consists of exactly the seeds (seedsFit), the point of the
seed of answer i has P.coordinates coordinates. -/
theorem seedAt_len (ds : List Fmt.Drawn) (hs : seedsFit P ds = true) (k i : ℕ)
    (hk : k < P.sent.size) (hi : i < (shapeAt P k).answers) :
    (seedAt P ds i).1.length = P.coordinates := by
  refine K1.cutSeeds_get P.coordinates P.seeds _ i _ ?_ (seedAt_get P ds k i hk hi)
  rw [List.length_map]
  unfold seedsFit at hs
  have := beq_iff_eq.1 hs
  cases h : ds.head? with
  | none => simpa [h] using this
  | some d => simpa [h] using this

/-- For k < P.sent.size, an oracle message k that has an answer reads at most P.coordinates
coordinates. -/
theorem v_le_coordinates (k : ℕ) (hk : k < P.sent.size) (ha : (shapeAt P k).answers ≠ 0) :
    (K1.Msg.of P.codes (shapeAt P k)).v ≤ P.coordinates := by
  refine (K1.fold_max_v P.codes P.tuple 0).2 _ ?_
  simp only [K1.Par.tuple, List.mem_filter]
  exact ⟨shape_mem P k hk, by simpa using ha⟩

/-- For such k and i, under seedsFit, oracle message k reads at most as many coordinates as the
point of the seed of its answer i has. -/
theorem v_le_len (ds : List Fmt.Drawn) (hs : seedsFit P ds = true) (k i : ℕ)
    (hk : k < P.sent.size) (hi : i < (shapeAt P k).answers) :
    (K1.Msg.of P.codes (shapeAt P k)).v ≤ (seedAt P ds i).1.length := by
  rw [seedAt_len P ds hs k i hk hi]
  exact v_le_coordinates P k hk (by omega)

/-- If the job fits its place (sendFits) and k < P.sent.size, oracle message k has a main row or a
mask row. -/
theorem has_table (hf : sendFits P ride = true) (k : ℕ) (hk : k < P.sent.size) :
    ((K1.Msg.of P.codes (shapeAt P k)).K != 0 || (K1.Msg.of P.codes (shapeAt P k)).Kzk != 0) =
      true := by
  show ((shapeAt P k).mainRows != 0 || (shapeAt P k).maskRows != 0) = true
  by_cases hz : (shapeAt P k).maskRows = 0
  · have := fits_main P ride k hf hk hz
    simp only [Bool.or_eq_true, bne_iff_ne]
    exact .inl (by omega)
  · simp only [Bool.or_eq_true, bne_iff_ne]
    exact .inr hz

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.seedAt_mem
#print axioms OnBytes.SendSim.At.v_le_len
#print axioms OnBytes.SendSim.At.has_table
