-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TokRetOf.lean: CONDITIONAL.

What is here. The hypothesis `TokRet` of TokOfPub.lean (the returns at one token's corner), SHOWN
FROM THE RETURNS AT THE END POINT, which the public structure X holds as its own fields. What is
shown: each of the verifier's public functions that are named here returns at the new point if it
returns at the old one of the same length. The panels, their places and the end of the batched
sumcheck: Johnson/Desc/First/K4/Returns/Pub/Panels.lean's `panels_at` and End.lean's `stackEnd_rel`.
The weight claims: Claims.lean's `weightClaims_rel`. The claims on the end values: the library's
`termsForms_skel` (Johnson/Road/K4/Total/TermsGatedSkel.lean). The named points and the list of
tables: two laws here, after Johnson/Road/K4/C/GroundCorner.lean's for the first token sumcheck. The
honest reads and end values: the return of the honest job's maker.

  `SameSizes`, `sameSizes_refl`, `find_sizes`   two lists of named points with one list of names and
     one list of lengths
  `phiOf_sizes`, `funsOf_sizes`   `phiOf` and `funsOf` return at the first list if at the second
  `pointsOf_atT`   the verifier's list of points at another end point of the second token sumcheck
  `stackEnd_all`   the end of the batched sumcheck returns over the honest side's panels at any
     shown values
  `tokRet_of`   **the returns at a token**

Limits. On returns and lengths alone: nothing on a value or a world. THE FULL SIZE ALONE (X).
HYPOTHESES: X with its environment of the panels the honest side's (Xp); the makers of the job's
data and of the second token sumcheck's honest job return; the lookup's point is X's (hfo); i lies
below the layout's number of tokens (hi), where TokOfPub.lean's callers count below two to the
library's number of a token's bits: JoinRun.lean bridges the two by `GatedNums`; for `stackEnd_all`:
X's list of the second pass's calls is the honest side's (eTS). No example is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TokOfPub
import Johnson.Desc.First.K4.Returns.Pub.Panels
import Johnson.Desc.First.K4.Returns.Pub.Claims
import Johnson.Desc.First.K4.Returns.Pub.End
import Johnson.Road.K4.Total.TermsGatedSkel
import Johnson.Road.K4.C.GroundCorner

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E)
open OnBytes.Model (Reading Tsc Level HFun longPoint lastOf)
open OnBytes.Model.Layer (Lay Heard ClaimEnv TableAsk pointsOf phiOf funsOf stackEnd placePanels)
open OnBytes.Road (bind_some worlds_of_holds admitted_of_layout)
open OnBytes.Road.K4 (entryOf reads_true_pub)
open OnBytes.Road.K4.C (sidesEnv stack_open sides_fields tokenRows_trips jobTermsOn_whole tok_part
  mapM_isSome mapM_all_isSome cornerPt_size)
open OnBytes.Desc.First.K4.RtPub (panels_at stackEnd_rel weightClaims_rel OptRel.of_right)
open OnBytes.Desc.First.K4.Total (termsForms_skel)
open OnBytes.Desc.First.K4.Honest

/-- Two lists of named points: member by member one name and one length. -/
abbrev SameSizes (a b : List (String × Array E)) : Prop :=
  List.Forall₂ (fun x y => x.1 = y.1 ∧ x.2.size = y.2.size) a b

/-- A list has its own sizes. -/
theorem sameSizes_refl : ∀ a : List (String × Array E), SameSizes a a
  | [] => .nil
  | _ :: l => .cons ⟨rfl, rfl⟩ (sameSizes_refl l)

/-- What is found under a name: in both lists nothing, or points of one length. -/
theorem find_sizes {a b : List (String × Array E)} (h : SameSizes a b) (n : String) :
    ((a.find? fun p => p.1 == n).map (·.2.size)) =
      ((b.find? fun p => p.1 == n).map (·.2.size)) := by
  induction h with
  | nil => rfl
  | @cons x y l l' hxy _ ih =>
    rw [List.find?_cons, List.find?_cons, ← hxy.1]
    cases hq : (x.1 == n) with
    | true => exact congrArg some hxy.2
    | false => exact ih

/-- **`phiOf` returns at the list a if at the list b.** -/
theorem phiOf_sizes {y : Lay} {fo : OnBytes.Model.Forest.Heard} {a b : List (String × Array E)}
    (h : SameSizes a b) (q : TableAsk) (hq : (phiOf y fo b q).isSome = true) :
    (phiOf y fo a q).isSome = true := by
  have e := find_sizes h q.point
  unfold phiOf at hq ⊢
  by_cases c0 : (q.name == "b-bits-0") = true
  · rw [if_pos c0] at hq ⊢
    exact hq
  · rw [if_neg c0] at hq ⊢
    by_cases c1 : (q.name == "b-bits-1") = true
    · rw [if_pos c1] at hq ⊢
      exact hq
    · rw [if_neg c1] at hq ⊢
      by_cases c2 : (q.name == "b-pin") = true
      · rw [if_pos c2] at hq ⊢
        exact hq
      · rw [if_neg c2] at hq ⊢
        cases hb : (b.find? fun p => p.1 == q.point) with
        | none =>
          rw [hb] at hq
          cases hq
        | some pb =>
          rw [hb] at hq e
          cases ha : (a.find? fun p => p.1 == q.point) with
          | none =>
            rw [ha] at e
            cases e
          | some pa =>
            rw [ha] at e
            have es : pa.2.size = pb.2.size := Option.some.inj e
            dsimp only at hq ⊢
            rw [es]
            by_cases c : (pb.2.size != if q.lng = true then y.h.la else y.h.lt) = true
            · rw [if_pos c] at hq
              cases hq
            · rw [if_neg c]
              rfl

/-- **`funsOf` returns at the list a if at the list b.** -/
theorem funsOf_sizes {y : Lay} {fo : OnBytes.Model.Forest.Heard} {a b : List (String × Array E)}
    (h : SameSizes a b) {laid : List (TableAsk × List (ℕ × ℕ))} {funs : Array HFun}
    (hf : funsOf y fo b laid = some funs) : ∃ funs', funsOf y fo a laid = some funs' := by
  unfold funsOf at hf ⊢
  obtain ⟨l, hl, _⟩ := bind_some hf
  have all := mapM_all_isSome _ _ hl
  obtain ⟨L, hL⟩ := mapM_isSome (f := fun x : TableAsk × List (ℕ × ℕ) => do
      let phi ← phiOf y fo a x.1
      pure (x.2.map fun m =>
        ({ mat := m.1, len := x.1.L, phi, tree := 2, start := m.2 } : HFun))) laid
    (fun x hx => by
      have h1 : (phiOf y fo b x.1).isSome = true := by
        have h2 := all x hx
        cases hq : phiOf y fo b x.1 with
        | none =>
          rw [hq] at h2
          cases h2
        | some _ => rfl
      obtain ⟨phi, hphi⟩ := Option.isSome_iff_exists.mp (phiOf_sizes h x.1 h1)
      beta_reduce
      rw [hphi]
      rfl)
  exact ⟨_, Option.bind_eq_some_iff.mpr ⟨L, hL, rfl⟩⟩

/-- **The verifier's list of points at another end point of the second token sumcheck**: it
returns, with the names and the lengths of the list at H, where the new point has the old one's
length. -/
theorem pointsOf_atT {y : Lay} {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} (h : pointsOf y H hd hd2 = some pts) {tT : Tsc}
    (hT : H.tT = some tT) (z : Array E) (hz : z.size = tT.r.size) :
    ∃ pts', pointsOf y { H with tT := some { tT with r := z } } hd hd2 = some pts' ∧
      SameSizes pts' pts := by
  unfold pointsOf at h
  obtain ⟨Z, hZ, h⟩ := bind_some h
  rw [hT] at h
  have two : SameSizes [("Y", longPoint (Z.extract 0 y.ls) z), ("rt", z)]
      [("Y", longPoint (Z.extract 0 y.ls) tT.r), ("rt", tT.r)] :=
    .cons ⟨rfl, by unfold longPoint; rw [Array.size_append, Array.size_append, hz]⟩
      (.cons ⟨rfl, hz⟩ .nil)
  cases hd2 with
  | none =>
    obtain ⟨routed, hr, h⟩ := bind_some h
    obtain ⟨a, ha, h⟩ := bind_some h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain rfl := Option.some.inj h
    refine ⟨[("Z", Z), ("zt", H.ztF), ("Z_V", a), ("P_V", H.PV), ("Z_E", H.ZE), ("r_tV", H.tV.r),
        ("Z_a", b)] ++ [("Y", longPoint (Z.extract 0 y.ls) z), ("rt", z)] ++ routed, ?_, ?_⟩
    · unfold pointsOf
      exact Option.bind_eq_some_iff.mpr ⟨Z, hZ, Option.bind_eq_some_iff.mpr ⟨routed, hr,
        Option.bind_eq_some_iff.mpr ⟨a, ha, Option.bind_eq_some_iff.mpr ⟨b, hb, rfl⟩⟩⟩⟩
    · exact List.rel_append (List.rel_append (sameSizes_refl _) two) (sameSizes_refl _)
  | some o =>
    obtain ⟨routed, hr, h⟩ := bind_some h
    obtain ⟨a, ha, h⟩ := bind_some h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain rfl := Option.some.inj h
    refine ⟨[("Z", Z), ("zt", H.ztF), ("Z_V", a), ("P_V", H.PV), ("Z_E", H.ZE), ("r_tV", H.tV.r),
        ("Z_a", b)] ++ [("Y", longPoint (Z.extract 0 y.ls) z), ("rt", z)] ++ routed, ?_, ?_⟩
    · unfold pointsOf
      exact Option.bind_eq_some_iff.mpr ⟨Z, hZ, Option.bind_eq_some_iff.mpr ⟨routed, hr,
        Option.bind_eq_some_iff.mpr ⟨a, ha, Option.bind_eq_some_iff.mpr ⟨b, hb, rfl⟩⟩⟩⟩
    · exact List.rel_append (List.rel_append (sameSizes_refl _) two) (sameSizes_refl _)

/-- **The end of the batched sumcheck returns over the honest side's panels at any shown values**,
for some arguments, namely X's. CONDITIONAL: on Xp and eTS. THE FULL SIZE ALONE (X). -/
theorem stackEnd_all {SD : StackData} {shownT : Array E} (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E)
    (Xp : X.p = sidesEnv SD.S shownT) (eTS : X.TS = SD.S.TS) :
    ∀ sh bl places, SD.S.panels sh = some (bl, places) → ∃ rs om H1 V lam sA sB s',
      stackEnd SD.S.v.y bl rs lam om H1 V sA sB = some s' := by
  intro sh bl places hp
  obtain ⟨pans, hpan, rfl⟩ := panels_open hp
  obtain ⟨pans', hp', _, _, hsk⟩ := panels_at (p := sidesEnv SD.S sh) (p₀ := X.p)
    ⟨by rw [Xp]; rfl, by rw [Xp]; rfl, by rw [Xp]; rfl⟩ X.TS X.hp
  rw [eTS] at hp'
  obtain rfl : pans = pans' := Option.some.inj (hpan.symm.trans hp')
  have ey : X.p.v.y = SD.S.v.y := by rw [Xp]; rfl
  have e := stackEnd_rel X.p.v.y X.lam X.om X.H1 X.V X.om X.H1 X.V X.shownA X.shownB X.shownA
    X.shownB hsk (rfl : X.c.rs.size = _)
  rw [X.hst, ey] at e
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp e
  exact ⟨_, _, _, _, _, _, _, s', hs'⟩

/-- **THE RETURNS AT TOKEN NUMBER i, FROM THE RETURNS AT THE END POINT.** CONDITIONAL: on every
hypothesis named. THE FULL SIZE ALONE (X). -/
theorem tokRet_of {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) {J : Job} (hJ : jobTermsOn SD.S = some J)
    (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (Xp : X.p = sidesEnv SD.S shownT)
    (hfo : p.fo.zx = X.H.fo.zx)
    {i : ℕ} (hi : i < SD.S.v.y.T) : TokRet X SD i := by
  have hS := (stack_open h).1
  obtain ⟨_, _, _, _, ⟨Z, hZ, hzl⟩, _, _⟩ := sides_fields hS
  obtain ⟨rows, hrows, _⟩ := jobTermsOn_whole hJ
  obtain ⟨R0, sh0, tr, hR0, hsh0, _, _⟩ := tokenRows_trips hrows hi
  have ev : X.p.v = SD.S.v := by rw [Xp]; rfl
  have ey : X.p.v.y = SD.S.v.y := by rw [ev]
  obtain ⟨_, tbI, I⟩ := OnBytes.Road.K4.C.stackIs_of h
  -- the end point's length
  have hrt : X.tT.r.size = SD.S.v.y.h.lt := by
    obtain ⟨_, _, _, q⟩ := worlds_of_holds X.ρ
      ⟨fun _ => 0, entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 fun _ _ _ => 0⟩ X.hy X.S X.hg X.hrd
      X.hl X.ht X.Z X.hZ X.hzt X.h4 X.hcrt X.htm X.hNM X.hpts X.hfun X.hT (fun _ _ _ => 0)
      (reads_true_pub X _ rfl)
    rw [← X.hcrt, q, X.Z.lT, ← (admitted_of_layout X.hy X.S.p3).shape, ey]
  have hz : (OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i).size = X.tT.r.size := by
    rw [hrt]
    exact cornerPt_size _ _
  obtain ⟨pts, hpts, hss⟩ := pointsOf_atT X.hpts X.hT _ hz
  obtain ⟨funs, hfun⟩ := funsOf_sizes hss X.hfun
  obtain ⟨pans, hp, _, hpl, hsk⟩ := panels_at (p := { X.p with shownT := sh0 }) (p₀ := X.p)
    ⟨rfl, rfl, rfl⟩ X.TS X.hp
  obtain ⟨cl, hcl, _⟩ := OptRel.of_right (weightClaims_rel
    (c := { X.c with rt := OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i }) (c₀ := X.c)
    ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩ X.TS) X.hcl
  obtain ⟨fin, hst⟩ : ∃ fin, stackEnd X.p.v.y (placePanels pans.bl).1 X.c.rs X.lam X.om X.H1 X.V
      X.shownA X.shownB = some fin := by
    have e := stackEnd_rel X.p.v.y X.lam X.om X.H1 X.V X.om X.H1 X.V X.shownA X.shownB X.shownA
      X.shownB hsk (rfl : X.c.rs.size = _)
    rw [X.hst] at e
    exact Option.isSome_iff_exists.mp e
  obtain ⟨H0, T0, hT0, h0⟩ := OnBytes.Road.K4.C.sides_ends hS
  obtain ⟨lE, hlE⟩ : ∃ lE, OnBytes.Desc.First.K4.termsForms SD.S.v
      { X.H with
        tT := some { X.tT with r := OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i } } =
      some lE := by
    have e := termsForms_skel (v := SD.S.v) (v₀ := SD.S.v) ⟨rfl, rfl, rfl⟩
      (H := { X.H with
        tT := some { X.tT with r := OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i } })
      (H₀ := H0) (by rw [hT0]; rfl)
    rw [h0] at e
    exact Option.isSome_iff_exists.mp e
  refine ⟨R0, sh0, pts, funs, pans, cl, fin, lE, hR0, hsh0, hpts, hfun, hp, hcl, hst,
    by rw [hpl]; exact X.hlam, hlE, ?_⟩
  have hZ' : (lastOf X.H.fo.zx X.p.v.y.h.la).toOption = some Z := by
    rw [← hfo, ey, I.y]
    exact hZ
  have q := tok_part hpts
    (tT := { X.tT with r := OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i }) rfl hZ'
  have e2 : Z.extract 0 X.p.v.y.ls = SD.S.zlow := by
    rw [ey, I.y]
    exact hzl.symm
  rw [e2] at q
  exact q

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.sameSizes_refl
#print axioms ProofFile.Honest.K4.find_sizes
#print axioms ProofFile.Honest.K4.phiOf_sizes
#print axioms ProofFile.Honest.K4.funsOf_sizes
#print axioms ProofFile.Honest.K4.pointsOf_atT
#print axioms ProofFile.Honest.K4.stackEnd_all
#print axioms ProofFile.Honest.K4.tokRet_of
