-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/PlacesProof.lean: under the public premises on sizes, the explicit shift of
the coins is 0 outside the places.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. shiftInPlaces proves Spec.shiftInPlaces (Johnson/LinkSim/AtText/Places.lean):
for all parameters P, sizes S, data, coins and verifier challenges that meet the public premises on
sizes (Sizes, Johnson/LinkSim/AtText/SpecShift.lean), the explicit shift of the coins (shC,
Johnson/LinkSim/AtText/ShiftDefs.lean) is 0 outside the places.

How it fits. Places.lean says why this is needed: a shift of the coins can be carried down to the
finite type of random values only if it is 0 outside the places. LinkShift.lean calls shiftInPlaces
in its proof, and CoinsDown.lean and then homeExact (Johnson/LinkSim/AtHome/Home.lean) take it from
there.

Other names (namespace OnBytes.LinkSim.AtText).
  tailAt_high    the compensating tail that tailAt builds for dm is 0 from the code's tail
                 length C.r on, if it is built for at most C.r positions.
  padIx_in       where the two stages fit (CsFit), a switch's pad lies among the free entries
                 of the new mask table.
  qNext_le       the part of Sizes along the stages (FitsBody) bounds the number of positions
                 at which the next tree is opened by the next stage's two tail lengths.
  inSwitch_sh    one switch's part of the shift is 0 outside that switch's places, where the two
                 stages fit
                 and the next tree is opened at no more positions than the next stage's two tail
                 lengths.
  inBody_congr   InBody reads the coins only from the switch in hand on.
  inBody_sh      the same along the stages, under FitsBody.
  sg0_first      if the list of stages begins with first, then sg0 P, the sizes that the
                 algorithm reads for its first stage, are sgOf first (no premise on sizes).
  rest_ne, q0_le under Sizes: there is a second stage; the first tree is opened at no more
                 positions than its rows' tails are long.

Limits.
- The limits of Places.lean hold here too.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Places

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)
open Johnson.Prover.Link

open Classical in
theorem tailAt_high (C : Fmt.M1.Code) (red : ℕ → ℕ) (Q : List ℕ) (hQ : Q.length ≤ C.r)
    (dm : ℕ → GE) {q : ℕ} (hq : C.r ≤ q) : tailAt C red Q dm q = 0 :=
  tailFor_high _ _ (le_trans (le_trans (List.toFinset_card_le _)
    (by rw [List.length_map]; exact hQ)) hq)

theorem padIx_in {s s' : Sg} (hf : CsFit s s') :
    carriedN s ≤ padIx s' ∧ padIx s' < 2 ^ s'.h * s'.Z.l := by
  have h := hf.mask
  unfold carriedN padIx
  omega

section Stage
variable (p : P12) (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ)
  (t : T12) (P : PS) (col : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) (d : PS)

theorem inSwitch_sh (hf : CsFit (sgOf cur) (sgOf next))
    (hC : (qNext last cur next o D).length ≤ (sgOf next).C.r)
    (hZ : (qNext last cur next o D).length ≤ (sgOf next).Z.r) :
    InSwitch (sgOf cur) (sgOf next) last (shFr p K j cur next l o t P D d)
      (shNew p K last j cur next l o t P col D d)
      (fun σ => if last then 0 else shWAt p K last j cur next l o t P col D d σ) := by
  have hp := padIx_in hf
  cases last
  · refine ⟨fun i hi => ?_, fun _ => rfl, fun _ => rfl, fun b q hb => ?_, fun b q hb => ?_,
      fun b q hb => ?_, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun σ hσ => ?_⟩
    · unfold shFr
      rw [Pi.single_apply, if_neg fun e : i = padIx (sgOf next) => hi (by rw [e]; exact hp)]
    · show (if b < 2 ^ ((sgOf next).h + (sgOf next).g) then _ else (0 : ℕ → GE)) q = 0
      split_ifs with h1
      · exact tailAt_high _ _ _ hC _ (not_lt.mp fun h2 => hb ⟨h1, h2⟩)
      · rfl
    · show (if b < 2 ^ (sgOf next).h then _ else (0 : ℕ → GE)) q = 0
      split_ifs with h1
      · exact tailAt_high _ _ _ hZ _ (not_lt.mp fun h2 => hb ⟨h1, h2⟩)
      · rfl
    · show (if b < 2 ^ (sgOf next).h then _ else (0 : ℕ → GE)) q = 0
      split_ifs with h1
      · exact tailAt_high _ _ _ hZ _ (not_lt.mp fun h2 => hb ⟨h1, h2⟩)
      · rfl
    · show shWAt p K false j cur next l o t P col D d σ = 0
      unfold shWAt
      rw [if_neg fun e => hσ ⟨rfl, e⟩]
  · refine ⟨fun i hi => ?_, fun _ => rfl, fun _ => rfl, fun b q hb => ?_, fun b q hb => ?_,
      fun b q hb => ?_, fun b i hb => ?_, fun i hi => ?_, fun q hq => ?_, fun _ _ => rfl⟩
    · unfold shFr
      rw [Pi.single_apply, if_neg fun e : i = padIx (sgOf next) => hi (by rw [e]; exact hp)]
    · show (if b = 0 then _ else (0 : ℕ → GE)) q = 0
      split_ifs with h1
      · exact tailAt_high _ _ _ hC _
          (not_lt.mp fun h2 => hb ⟨h1 ▸ Nat.pos_of_ne_zero (by positivity), h2⟩)
      · rfl
    · show (if b = 0 then _ else (0 : ℕ → GE)) q = 0
      split_ifs with h1
      · exact tailAt_high _ _ _ hZ _
          (not_lt.mp fun h2 => hb ⟨h1 ▸ Nat.pos_of_ne_zero (by positivity), h2⟩)
      · rfl
    · show (if b = 0 then lamNext cur o D * -tailAt _ _ _ _ q else 0) = 0
      split_ifs with h1
      · rw [tailAt_high _ _ _ hZ _ (not_lt.mp fun h2 => hb ⟨h1, h2⟩), neg_zero, mul_zero]
      · rfl
    · show (if b = 0 then lamNext cur o D * maskOf _ _ i else 0) = 0
      split_ifs with h1
      · unfold maskOf
        rw [dif_neg fun h2 => hb ⟨rfl, h1, h2⟩, mul_zero]
      · rfl
    · show lamNext cur o D * mainOf _ _ i = 0
      unfold mainOf
      rw [dif_neg fun h2 => hi ⟨rfl, h2⟩, mul_zero]
    · show lamNext cur o D * -tailAt _ _ _ _ q = 0
      rw [tailAt_high _ _ _ hC _ (not_lt.mp fun h2 => hq ⟨rfl, h2⟩), neg_zero, mul_zero]

end Stage

theorem qNext_le {D : ℕ → Fmt.Drawn} {rest : List Fmt.M1.Stage} {cur next : Fmt.M1.Stage} {o : ℕ}
    (hF : FitsBody D rest next (oNext cur o)) :
    (qNext rest.isEmpty cur next o D).length ≤ (sgOf next).C.r ∧
      (qNext rest.isEmpty cur next o D).length ≤ (sgOf next).Z.r := by
  unfold qNext openAt
  rw [List.length_map]
  cases rest with
  | nil => exact ⟨hF.1, hF.2.1⟩
  | cons n r => exact ⟨hF.1, hF.2.1⟩

theorem inBody_congr : ∀ (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage) (j : ℕ) (K K' : BCoins),
    (∀ i, j ≤ i → K.fr i = K'.fr i ∧ K.new i = K'.new i) →
    (∀ σ i, j < i → K.W σ i = K'.W σ i) → InBody cur rest j K → InBody cur rest j K'
  | [], _, _, _, _, h1, h2, hK =>
    ⟨fun i hi => ⟨(h1 i hi).1 ▸ (hK.1 i hi).1, (h1 i hi).2 ▸ (hK.1 i hi).2⟩,
      fun σ i hi => h2 σ i hi ▸ hK.2 σ i hi⟩
  | next :: rest, cur, j, K, K', h1, h2, hK => by
    refine ⟨?_, inBody_congr rest next (j + 1) K K' (fun i hi => h1 i (by omega))
      (fun σ i hi => h2 σ i (by omega)) hK.2⟩
    have e : (fun σ => K'.W σ (j + 1)) = fun σ => K.W σ (j + 1) :=
      funext fun σ => (h2 σ (j + 1) (Nat.lt_succ_self j)).symm
    rw [← (h1 j le_rfl).1, ← (h1 j le_rfl).2, e]
    exact hK.1

theorem inBody_sh (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64) (d : PS),
    FitsBody D rest cur o → InBody cur rest j (shB p K D rest j cur l o t P col d)
  | [], _, _, _, _, _, _, _, _, _ => ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl⟩
  | next :: rest, j, cur, l, o, t, P, col, d, hF => by
    have hq := qNext_le (cur := cur) (o := o) hF.2.2.2.2
    have hs := inSwitch_sh p K rest.isEmpty j cur next l o t P col D d hF.2.2.2.1 hq.1 hq.2
    have hi := inBody_sh p K D rest (j + 1) next (l.drop (cur.k + 3)) (oNext cur o)
      (tNext p K rest.isEmpty j cur next l o t P col D)
      (sNext K rest.isEmpty j cur next o P (rowOf t) D)
      (sCol K rest.isEmpty j cur next o P (rowOf t) D)
      (dNext p K rest.isEmpty j cur next l o t P col D d) hF.2.2.2.2
    refine ⟨?_, inBody_congr rest next (j + 1) _ _ (fun i hi' => ⟨?_, ?_⟩) (fun σ i hi' => ?_) hi⟩
    · have e1 : (shB p K D (next :: rest) j cur l o t P col d).fr j =
          shFr p K j cur next l o t P D d := if_pos rfl
      have e2 : (shB p K D (next :: rest) j cur l o t P col d).new j =
          shNew p K rest.isEmpty j cur next l o t P col D d := if_pos rfl
      have e3 : (fun σ => (shB p K D (next :: rest) j cur l o t P col d).W σ (j + 1)) =
          fun σ => if rest.isEmpty then 0
            else shWAt p K rest.isEmpty j cur next l o t P col D d σ :=
        funext fun σ => if_pos rfl
      rw [e1, e2, e3]
      exact hs
    · exact (if_neg (by omega : ¬ i = j)).symm
    · exact (if_neg (by omega : ¬ i = j)).symm
    · exact (if_neg (by omega : ¬ i = j + 1)).symm

section Front
variable {P : P15} {S : Sz} {t : ℕ} {D : ℕ → Fmt.Drawn} {first : Fmt.M1.Stage}
  {rest : List Fmt.M1.Stage}

theorem sg0_first (hst : (p12Of P).nums.stages = first :: rest) : sg0 P = sgOf first := by
  unfold sg0
  rw [hst]
  rfl

theorem rest_ne (hS : Sizes P S t D) (hst : (p12Of P).nums.stages = first :: rest)
    (hF : FitsBody D rest first 6) : rest ≠ [] := by
  rintro rfl
  have hg : (sgOf first).g = 0 := hF.2.2.2
  rw [← sg0_first hst, hS.first] at hg
  exact Nat.succ_ne_zero _ hg

theorem q0_le (hS : Sizes P S t D) (hst : (p12Of P).nums.stages = first :: rest)
    (hF : FitsBody D rest first 6) :
    (q0 P D).length ≤ S.P.C.r ∧ (q0 P D).length ≤ S.P.Z.r := by
  have hC : (sgOf first).C = S.P.C := by rw [← sg0_first hst, hS.first]
  have hZ : (sgOf first).Z = S.P.Z := by rw [← sg0_first hst, hS.first]
  unfold q0 openAt
  rw [List.length_map, sg0_first hst, ← hC, ← hZ]
  cases rest with
  | nil => exact absurd rfl (rest_ne hS hst hF)
  | cons n r => exact ⟨hF.1, hF.2.1⟩

end Front

/-- Under the public premises on sizes, the explicit shift of the coins (shC) is 0 outside the
places. -/
theorem shiftInPlaces : Spec.shiftInPlaces := by
  intro P S t Xd Xr C D hS
  obtain ⟨first, rest, hst, hF⟩ := hS.body
  have hq := q0_le hS hst hF
  have hC : shC P S t Xd Xr C D =
      { pad := shPad S t Xd D
        tN := shTN P S t Xd D
        ψN := shPsi P S t Xd Xr C D
        body :=
          { W := fun σ i => if i = 0 then shW0 P S t Xd Xr C D σ
              else (shB (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6
                (lT P S t Xr C D) (lPS P S Xr C D) (lCol P S Xr C D)
                (d0 P S t Xd Xr C D)).W σ i
            new := (shB (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6
              (lT P S t Xr C D) (lPS P S Xr C D) (lCol P S Xr C D) (d0 P S t Xd Xr C D)).new
            fr := (shB (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6
              (lT P S t Xr C D) (lPS P S Xr C D) (lCol P S Xr C D)
              (d0 P S t Xd Xr C D)).fr } } := by
    unfold shC
    rw [hst]
  rw [hC]
  refine ⟨fun a i q h => ?_, fun q h => tailAt_high _ _ _ hq.2 _ h, fun σ h => ?_,
    fun first' rest' hst' => ?_⟩
  · show shTN P S t Xd D a i q = 0
    unfold shTN
    split_ifs with h1
    · exact tailAt_high _ _ _ hq.1 _ (not_lt.mp fun h2 => h ⟨h1, h2⟩)
    · rfl
  · show shW0 P S t Xd Xr C D σ = 0
    unfold shW0
    rw [if_neg h]
  · obtain ⟨rfl, rfl⟩ := List.cons.inj (hst.symm.trans hst')
    have hR := inBody_sh (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6
      (lT P S t Xr C D) (lPS P S Xr C D) (lCol P S Xr C D) (d0 P S t Xd Xr C D) hF
    refine inBody_congr rest first 0
      (shB (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t Xr C D)
        (lPS P S Xr C D) (lCol P S Xr C D) (d0 P S t Xd Xr C D)) _
      (fun i _ => ⟨rfl, rfl⟩) (fun σ i hi => ?_) hR
    show _ = if i = 0 then _ else _
    rw [if_neg (by omega : ¬ i = 0)]

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.inSwitch_sh
#print axioms OnBytes.LinkSim.AtText.inBody_sh
#print axioms OnBytes.LinkSim.AtText.shiftInPlaces
