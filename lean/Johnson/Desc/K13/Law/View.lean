-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/View.lean: the written rounds of the batching, read twice: as the kind's text
reads what the verifier is shown of them, and as the library's maps read them. The two readings
agree. Statements with their proofs.
Main names:
  `ρg`: the reading in the library's field. `rvAt`: what is shown of one written round.
  `oneDrawn_read`, `sentE_read`, `oneRound_read`: one round.
  `mapZ`, `map0`, `mapK`, `mapsOf`, `mapsOf_ok`: the library's maps (OnBytes/Flat/CarrySMaps.lean,
    KindsBattSend.lean) for the round of the draw, the round of the sum and the variables' rounds.
  `rounds_read`, `whole_read`: what the text hears, as a transcript, is the maps' image.
  `maps_pass`, `rvT_len`.
Used of `verify-on-bytes`: nothing beside what Johnson/Desc/K13/Law/Law.lean names. Of the library's
reading of written rounds: `rvOf`, `gOne_of_els`, `ansOf`, `sentT`, `valsOf`, `RMap.one`,
`shortMaps`.

What is not claimed. No word is asked to be below the prime: the reading takes residues. Nothing on
the tests that stand in front of a run but for the tests of work.

-/
import Johnson.Desc.K13.Law.AtM3
import OnBytes.Flat.KindsBattSend
import OnBytes.Flat.CarrySForms
import OnBytes.Flat.CarrySProx
import OnBytes.Slice.RoundsMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Run
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open Johnson.L5.Layers (rd sRound sRounds)
open VerifiableInference.Desc.First.End (sentE)

/-- The reading in the library's field. -/
abbrev ρg : Reading GE := Reading.gl

/-- What the verifier is shown of one written round. -/
def rvAt (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) : Fmt.RoundView :=
  ⟨PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
    (ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩

/-- The element that the text reads as drawn is the one that the library's map reads. -/
theorem oneDrawn_read {name : String} {d : RDT} {m : (wT d).Msg} {c : (wT d).Chal} {x : E}
    (h : oneDrawn name (noDigest (rvAt d m c)) = .ok x) :
    ρg.val x = gOne _ (valsOf (toRD d) c) := by
  unfold oneDrawn at h
  rw [there_ok] at h
  have he : (noDigest (rvAt d m c)).drawn.elems = (rvOf (toRD d) (msgRD d m) c).els := rfl
  rw [he] at h
  split at h
  · next t ht =>
    rw [gOne_of_els (toRD d) (msgRD d m) c ht, ← Option.some.inj h]
    rfl
  · cases h

/-- The items that the text reads as sent, read in the field, are what the library reads. -/
theorem sentE_ans : ∀ (l : List Fmt.ItemValue) (q : List E),
    (l.mapM fun
      | .e x => some (E.ofTriple x)
      | _ => none) = some q →
    (l.filterMap fun g =>
      match g with
      | .e x => some (toE x)
      | .answer x => some (toE x)
      | _ => none) = q.map ρg.val
  | [], q, h => by
    obtain rfl := Option.some.inj h
    rfl
  | g :: l, q, h => by
    rw [List.mapM_cons] at h
    cases g with
    | e x =>
      cases hl : (l.mapM fun
        | .e x => some (E.ofTriple x)
        | _ => none) with
      | none =>
        simp [hl] at h
      | some q' =>
        simp [hl] at h
        subst h
        rw [List.filterMap_cons, List.map_cons, sentE_ans l q' hl]
        rfl
    | _ => simp at h

/-- Element number i that the text reads as sent is the one that the library reads. -/
theorem sentE_read {d : RDT} {m : (wT d).Msg} {c : (wT d).Chal} {q : List E}
    (h : sentE (noDigest (rvAt d m c)) = some q) (i : ℕ) :
    ρg.val (q.getD i zeroE) = sentT d m i := by
  have e : ansOf (toRD d) (msgRD d m) = q.map ρg.val := sentE_ans _ q h
  unfold sentT
  rw [e, ← ρg.zero, List.getD_map]

/-- A round in which elements are sent and one is drawn, read both ways. -/
theorem oneRound_read {d : RDT} {m : (wT d).Msg} {c : (wT d).Chal} {a : List E × E}
    (h : oneRound (noDigest (rvAt d m c)) = .ok a) :
    (∀ i, ρg.val (a.1.getD i zeroE) = sentT d m i) ∧ ρg.val a.2 = gOne _ (valsOf (toRD d) c) := by
  simp only [oneRound, bind_ok, there_ok, pure_ok] at h
  obtain ⟨q, hq, x, hx, rfl⟩ := h
  exact ⟨sentE_read hq, oneDrawn_read hx⟩

/-! ## The library's maps for the batching's written rounds -/

/-- The round of the draw: nothing is sent. -/
def mapZ (d : RDT) : RMap d (IOR.drawRound GE) := RMap.one (fun _ => ((), ())) id

/-- The round of the hiding polynomial's sum. -/
def map0 (d : RDT) : RMap d (pRound0 GE) := RMap.one (fun m => ((), sentT d m 0)) id

/-- The round of a variable: two coefficients. -/
def mapK (d : RDT) : RMap d (sRound (pfCube GE 2)) :=
  RMap.one (fun m => ((), fun i : Fin 2 => sentT d m i)) id

/-- The typed rounds of the batching over k column variables. -/
abbrev shapeK (k : ℕ) : Shape := IOR.drawRound GE :: pRound0 GE :: sRounds (fmtOf GE k)

/-- All rounds. -/
def mapsOf (dZ d0 : RDT) (ds : List RDT) : Maps (dZ :: d0 :: ds) (shapeK ds.length) :=
  .step (mapZ dZ) (.step (map0 d0) (shortMaps (pfCube GE 2) mapK ds))

/-- The maps are as the library asks, where each round draws one element and no position. -/
theorem mapsOf_ok {dZ d0 : RDT} {ds : List RDT} {nZ n0 aZ a0 : ℕ}
    (hZ : SendsDraws (toRD dZ) nZ 1 0 aZ) (h0 : SendsDraws (toRD d0) n0 1 0 a0)
    (hs : ∀ d ∈ ds, ∃ n a, SendsDraws (toRD d) n 1 0 a) : (mapsOf dZ d0 ds).OK :=
  ⟨RMap.one_ok _ hZ Function.injective_id, RMap.one_ok _ h0 Function.injective_id,
    shortMaps_ok _ _ ds fun d hd => by
      obtain ⟨n, a, h⟩ := hs d hd
      exact RMap.one_ok _ h Function.injective_id⟩

/-- What the verifier is shown of the rounds of the variables, read both ways. -/
theorem rounds_read : ∀ (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)) (inX : List (List E × E)),
    ((rvT (ckP .two) ds τ).map noDigest).mapM oneRound = (.ok inX : Ans _) →
    trRounds ρg ds.length inX = (shortMaps (pfCube GE 2) mapK ds).view τ
  | [], _, inX, h => rfl
  | d :: ds, (m, c, τ), inX, h => by
    have h' : (noDigest (rvAt d m c) :: (rvT (ckP .two) ds τ).map noDigest).mapM oneRound =
        (.ok inX : Ans _) := h
    rw [List.mapM_cons] at h'
    simp only [bind_ok, pure_ok] at h'
    obtain ⟨a, ha, l, hl, rfl⟩ := h'
    obtain ⟨h1, h2⟩ := oneRound_read ha
    show (((), rd ρg 2 a.1), ρg.val a.2, trRounds ρg ds.length l) =
      (((), fun i : Fin 2 => sentT d m i), gOne _ (valsOf (toRD d) c),
        (shortMaps (pfCube GE 2) mapK ds).view τ)
    rw [h2, rounds_read ds τ l hl]
    have e : rd ρg 2 a.1 = fun i : Fin 2 => sentT d m i := funext fun i => h1 i
    rw [e]

/-- **All rounds, read both ways.** -/
theorem whole_read (nR : ℕ) (pile : List TensorRow) (Ex : ExtSpec) (dZ d0 : RDT) (ds : List RDT)
    (τ : Tr (uLT (ckP .two) (dZ :: d0 :: ds))) (r : Fmt.RoundView) (rs' : List Fmt.RoundView) (x : E)
    (hd : Psc.Heard) (e : (rvT (ckP .two) (dZ :: d0 :: ds) τ).map noDigest = r :: rs')
    (hx : oneDrawn "K13.sigma-one-drawn" r = .ok x) (hh : heard rs' = .ok hd) :
    trOf (k := ds.length) ρg nR pile Ex x hd = (mapsOf dZ d0 ds).view τ := by
  obtain ⟨mZ, cZ, m0, c0, τ'⟩ := τ
  have e' : noDigest (rvAt dZ mZ cZ) :: noDigest (rvAt d0 m0 c0) ::
      (rvT (ckP .two) ds τ').map noDigest = r :: rs' := e
  obtain ⟨rfl, rfl⟩ := List.cons.inj e'
  simp only [heard, bind_ok, there_ok, pure_ok] at hh
  obtain ⟨a, ha, mu, hmu, inX, hX, rfl⟩ := hh
  obtain ⟨h1, h2⟩ := oneRound_read ha
  have hm : ρg.val mu = sentT d0 m0 0 := by
    rw [← h1 0]
    cases hq : a.1 with
    | nil => rw [hq] at hmu; cases hmu
    | cons b l =>
      rw [hq] at hmu
      obtain rfl := Option.some.inj hmu
      rfl
  show (((), ()), ρg.val x, ((), ρg.val mu), ρg.val a.2, trRounds ρg ds.length inX) =
    (((), ()), gOne _ (valsOf (toRD dZ) cZ), ((), sentT d0 m0 0), gOne _ (valsOf (toRD d0) c0),
      (shortMaps (pfCube GE 2) mapK ds).view τ')
  rw [oneDrawn_read hx, hm, h2, rounds_read ds τ' inX hX]

/-- The tests of work that the maps ask are those of the stretch. -/
theorem short_pass : ∀ (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)),
    (shortMaps (pfCube GE 2) mapK ds).pass τ = passT (ckP .two) ds (rhoT (ckP .two) ds τ)
  | [], _ => rfl
  | d :: ds, (_, c, τ) => congrArg (GChal.pass (b := d.entry.work) c && ·) (short_pass ds τ)

/-- The same of all rounds. -/
theorem maps_pass (dZ d0 : RDT) (ds : List RDT) (τ : Tr (uLT (ckP .two) (dZ :: d0 :: ds))) :
    (mapsOf dZ d0 ds).pass τ =
      passT (ckP .two) (dZ :: d0 :: ds) (rhoT (ckP .two) (dZ :: d0 :: ds) τ) := by
  obtain ⟨mZ, cZ, m0, c0, τ'⟩ := τ
  exact congrArg (GChal.pass (b := dZ.entry.work) cZ && ·)
    (congrArg (GChal.pass (b := d0.entry.work) c0 && ·) (short_pass ds τ'))

/-- As many rounds are shown as are written. -/
theorem rvT_len : ∀ (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)),
    (rvT (ckP .two) ds τ).length = ds.length
  | [], _ => rfl
  | _ :: ds, (_, _, τ) => congrArg (· + 1) (rvT_len ds τ)

end VerifiableInference.Desc.K13.Law
