-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/SeatedAt.lean: every side whose sub-protocol has K1's own two rounds and oracle
messages, and whose row is the honest sender with its simulator, is Seated.
Terms: Johnson/SendSim/At/Sim.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves.
  seated_of_send   Let σ be a side whose row is the one part sendPart J with sendSim at the address
                   (σ's place, 0), and whose sub-protocol has the rounds K1.rounds J.P and the
                   oracle messages K1.oracles J.P. Then σ is Seated at J. Such sides exist for every
                   P and ride (seated_sideAt).
  draws_send       For every P, a list of challenges that K1's own two rounds can sample (drawsFit)
                   consists of exactly the seeds (seedsFit), and no seed's factor is 0 in the field.

Limits. The statements are on lists of sampled elements: no distribution is named. That the
sub-protocol at a place of a description has these rounds and oracle messages is not proved here.
The maker of a description wraps a sub-protocol: it guards it, joins it with a sub-protocol of
another kind, or changes the tenants that its oracle messages declare (Oracle.tenants,
Johnson/Desc/Oracle.lean). At the descriptions of the release's files, Seated is proved only for the
sides at the places of the kind K1 that result (3) of Johnson/SendSim/Defs.lean names (seatedAt_job,
if the maker of the proof file's description succeeds; seatedAt_key). The other sendings of that
kind are not covered. For the first of these the rounds and oracle messages are in
Johnson/SendSim/Seat/AtDesc.lean (member_of_own, seatedAt_w).

How it fits. seated_of_send gives Seated in Johnson/SendSim/Seat/Row.lean (seated_at), and through
it at the proof file's description (seatedAt_job, Johnson/SendSim/Seat/AtDescStands.lean), which
serves Spec.fieldsAtLots.

The other names.
  factor_ne      three words that are not all 0, each below the prime, are read as an element other
                 than 0.
  dsSeeds_succ   the format's marks for one seed more: so many plain elements, one element that is
                 never 0, then the rest.
  cut_nz         if a list of at least n * (v + 1) sampled elements passes the format's marks for n
                 seeds of v coordinates, no factor that cutSeeds returns consists of three words 0.
-/
import Johnson.SendSim.At.Shows
import Johnson.Desc.K1.Law.OkView

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc

variable {S Cl V W X Pb : Type}

/-- Three words that are not all 0, each below the prime, are read as an element other than 0. -/
theorem factor_ne {a : E} (hok : okE a = true) (hz : isZeroE a = false) : readE a ≠ 0 := fun h => by
  rw [(isZeroE_iff a hok).2 h] at hz
  cases hz

/-- The format's marks for one seed more: v plain elements, one element that is never 0, then the
marks for n seeds. -/
theorem dsSeeds_succ (n v : ℕ) : Fmt.dsSeeds (n + 1) v =
    List.replicate v Fmt.Draw.elem ++ (Fmt.Draw.elemNZ :: Fmt.dsSeeds n v) := by
  simp [Fmt.dsSeeds, List.replicate_succ]

/-- If a list of at least n * (v + 1) sampled elements passes the format's marks for n seeds of v
coordinates, no factor that cutSeeds returns consists of three words 0. -/
theorem cut_nz (v : ℕ) : ∀ (n : ℕ) (L : List Fmt.Ext3), n * (v + 1) ≤ L.length →
    (((Fmt.dsSeeds n v).zip L).all fun x => x.1 != .elemNZ || x.2 != (0, 0, 0)) = true →
    ∀ s ∈ K1.cutSeeds v n (L.map E.ofTriple), isZeroE s.2 = false
  | 0, _, _, _, s, hs => by simp [K1.cutSeeds] at hs
  | n + 1, L, hl, h, s, hs => by
    have hlen : v + 1 ≤ L.length := by
      have : (n + 1) * (v + 1) = n * (v + 1) + (v + 1) := by ring
      omega
    obtain ⟨A, x, R, rfl, hA⟩ : ∃ A x R, L = A ++ x :: R ∧ A.length = v :=
      ⟨L.take v, L[v]'(by omega), L.drop (v + 1), by
        rw [List.getElem_cons_drop, List.take_append_drop], by
        rw [List.length_take]; omega⟩
    rw [dsSeeds_succ, List.zip_append (by rw [List.length_replicate, hA]), List.zip_cons_cons,
      List.all_append, List.all_cons, Bool.and_eq_true, Bool.and_eq_true] at h
    simp only [K1.cutSeeds, List.mem_cons] at hs
    have hd : (List.map E.ofTriple (A ++ x :: R)).drop v = E.ofTriple x :: R.map E.ofTriple := by
      rw [List.map_append, List.drop_left' (by rw [List.length_map, hA])]
      rfl
    have hd' : (List.map E.ofTriple (A ++ x :: R)).drop (v + 1) = R.map E.ofTriple := by
      rw [← List.drop_drop, hd]
      rfl
    rcases hs with rfl | hs
    · show isZeroE (((List.map E.ofTriple (A ++ x :: R)).drop v).headD zeroE) = false
      rw [hd]
      show isZeroE (E.ofTriple x) = false
      have hx : x ≠ (0, 0, 0) := by simpa using h.2.1
      cases hz : isZeroE (E.ofTriple x) with
      | false => rfl
      | true => exact absurd (congrArg E.triple ((isZeroE_eq _).1 hz)) hx
    · rw [hd'] at hs
      refine cut_nz v n R ?_ h.2.2 s hs
      have : (A ++ x :: R).length = v + 1 + R.length := by
        rw [List.length_append, List.length_cons, hA]; omega
      have e : (n + 1) * (v + 1) = n * (v + 1) + (v + 1) := by ring
      omega

/-- A list of challenges that K1's own two rounds can sample (drawsFit) consists of exactly the
seeds (seedsFit), and no seed's factor is 0 in the field. -/
theorem draws_send (P : K1.Par) {ds : List Fmt.Drawn} (h : drawsFit (K1.rounds P) ds = true) :
    seedsFit P ds = true ∧ ∀ s ∈ seedsAt P ds, readE s.2 ≠ 0 := by
  obtain ⟨d₀, d₁, rfl⟩ := drawsFit_two (a₁ := { entry := K1.seedEntry P })
    (a₂ := { entry := K1.answerEntry P }) h
  have h0 : drawFit { entry := K1.seedEntry P } d₀ = true := by
    have : (drawFit { entry := K1.seedEntry P } d₀ &&
      drawsFit [{ entry := K1.answerEntry P }] [d₁]) = true := h
    exact (Bool.and_eq_true _ _ ▸ this).1
  simp only [drawFit, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h0
  obtain ⟨⟨⟨⟨⟨⟨⟨hE, _⟩, _⟩, _⟩, _⟩, hnz⟩, hw⟩, _⟩ := h0
  have hE' : d₀.elems.length = P.seeds * (P.coordinates + 1) := hE
  refine ⟨by simpa [seedsFit] using hE', fun s hs => ?_⟩
  have hs' : s ∈ K1.cutSeeds P.coordinates P.seeds (d₀.elems.map E.ofTriple) := hs
  refine factor_ne (K1.cutSeeds_ok _ _ _ (fun e he => ?_) s hs') ?_
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    exact K1.okE_ofTriple x (by simp only [Bool.and_eq_true]; exact hw x hx)
  · by_cases hp : P.seeds = 0
    · rw [hp] at hs'
      simp [K1.cutSeeds] at hs'
    · refine cut_nz P.coordinates P.seeds d₀.elems (le_of_eq hE'.symm) ?_ s hs'
      have hk : Fmt.kindOf (K1.seedEntry P).name = some .seeds := by
        show Fmt.kindOf "SEND seed" = some .seeds
        decide
      have hq : ((K1.seedEntry P).drawE - (K1.seedEntry P).drawNZ) / (K1.seedEntry P).drawNZ =
          P.coordinates := by
        show (P.seeds * (P.coordinates + 1) - P.seeds) / P.seeds = P.coordinates
        rw [Nat.mul_succ, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
      have hm : ((K1.seedEntry P).drawE - (K1.seedEntry P).drawNZ) % (K1.seedEntry P).drawNZ =
          0 := by
        show (P.seeds * (P.coordinates + 1) - P.seeds) % P.seeds = 0
        rw [Nat.mul_succ, Nat.add_sub_cancel, Nat.mul_mod_right]
      have hz : drawsMarkedNonzeroHaveNonzeroWords { entry := K1.seedEntry P } ⟨[], d₀⟩ = true := hnz
      simp only [drawsMarkedNonzeroHaveNonzeroWords, hk, Option.any_some, Fmt.dsElems, if_true, hq, hm, List.replicate_zero,
        List.append_nil] at hz
      exact hz

/-- A side whose row is the one part sendPart J with sendSim at the side's own address, and whose
sub-protocol has K1's own two rounds and oracle messages at J.P, is Seated at J. -/
theorem seated_of_send (σ : Side S Cl V W X Pb) (J : SendJob W X)
    (hrow : σ.row = [(sendPart J, sendSim J.P J.first J.ride ⟨σ.block.place, 0⟩)])
    (hr : σ.block.rounds = K1.rounds J.P) (ho : σ.block.oracles = K1.oracles J.P) :
    Seated σ J where
  row := hrow
  fits := by
    simp only [Side.fits, Side.half, Placed.rounds, hrow, hr, ho]
    simp [K1.rounds, K1.oracles, sendPart, sendSim]
  shape := by rw [hr, ho]; rfl
  draws := fun ds hd => draws_send J.P (hr ▸ hd)

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.cut_nz
#print axioms OnBytes.SendSim.At.draws_send
#print axioms OnBytes.SendSim.At.seated_of_send
