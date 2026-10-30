-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpScan.lean

What the parameter file, the scale file and the goals' reader "VerifierAndGoals.readFiles" (Ladder.lean) say
of the free numbers, at files in scope ("VerifierAndGoals.InScope"). Two definitions, and theorems.

Main definitions: "freeNames": the names of the eleven free lines; "kept": true of a name that is
none of them.

Main theorems:
* "scan_turn": the scan of "policyFile v" is the scan of "policyFile v₀", turned ("scanTurn",
  Johnson/HonestTrace/Run/SetUpTurnDefs.lean), where both scans return.
* "hPar_in_scope": where "publicOfO" returns at the stored files "VerifierAndGoals.storedPublicFiles", the digest of the
  three files ("hParO") is made at all files in scope.
* "sh_of_read", "shifts_of_read": in scope the scale file's shift of a layer is the shift in what
  "VerifierAndGoals.readFiles" returns; a group of four layers has one shift, and it lies in 4 to 12.
* "free_bounds": where the reader returns, of the free numbers as it read them: 1 ≤ e < 2^59 for
  eps1, eps2, epsF; 24 ≤ MF ≤ 47; MF ≤ KF + 14; 17 ≤ KF ≤ 32; theta ≤ C < 2^32; cap ≤ 1024.
* "shape_turn_in_scope": the layers' shape of the scan in scope is that of the stored files' scan
  with eps1, eps2, epsF set.

Where a text comes from. Twins of the library's lemmas: "hdrOf_free" of "VerifierAndGoals.Lines.hdrOf_pol"
(Johnson/Goal/Meaning/ScopeScan.lean), for eleven names; "hPar_returns2" of "LPFPol.hPar_returns"
(Johnson/LPFPol/HashReturns.lean), for another scale file too; "sh_of_read" of
"Meaning.Att.sh_in_scope" (Johnson/Goal/Meaning/AttScope.lean), with no return of "publicOf".
"hPar_of_public" repeats the walk of "publicSteps_of_O"
(Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean).

Limits. "hPar_in_scope" is stated at "OnBytes.secondHashFunction" alone, and the return at the stored files is
its hypothesis. "attribute [-instance]" takes "Inst.Model.Scl.ref" out for this file.

No property of a release, of a verifier or of a prover is claimed.
-/
import Johnson.HonestTrace.Run.SetUpTurnDefs
import Johnson.LPFPol.PublicInScope
import Johnson.Goal.Meaning.ScalesReturn
import Johnson.Desc.Ok.PlanWritten.PublicAtSteps
import Ladder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun

namespace SetUp

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open LPFPol (bind_ok refuseIf_no)
open VerifierAndGoals (FreeLines policyFile)
open VerifierAndGoals.Lines (freeValues valuesAt scanAt frameRef)
open VerifiableInference.PlanWritten (publicOfO hParO)

/-! ## (a) the scan at other free numbers -/

/-- The names of the eleven free lines. -/
def freeNames : List String :=
  ["eps1_lo", "eps1_hi", "eps2_lo", "eps2_hi", "MF", "KF", "epsF_lo", "epsF_hi", "C", "theta", "cap"]

/-- True of a name that is none of the eleven. -/
def kept (n : String) : Bool := freeNames.all fun m => n != m

theorem names_free (v : FreeLines) : (freeValues v).map Prod.fst = freeNames := rfl

theorem kept_ne {n : String} (h : kept n = true) {v : FreeLines} {p : String × Nat}
    (hp : p ∈ freeValues v) : (n == p.1) = false := by
  have hm : p.1 ∈ freeNames := by
    rw [← names_free v]
    exact List.mem_map_of_mem hp
  have a := List.all_eq_true.1 h p.1 hm
  have b : n ≠ p.1 := bne_iff_ne.1 a
  simpa using b

theorem lookup_skip (n : String) : ∀ (a b : List (String × Nat)), (∀ p ∈ a, (n == p.1) = false) →
    (a ++ b).lookup n = b.lookup n
  | [], _, _ => rfl
  | q :: a, b, h => by
    rw [List.cons_append, List.lookup_cons, h q List.mem_cons_self]
    exact lookup_skip n a b fun p hp => h p (List.mem_cons_of_mem _ hp)

theorem lookup_tail (n : String) : ∀ (a b b' : List (String × Nat)), b.lookup n = b'.lookup n →
    (a ++ b).lookup n = (a ++ b').lookup n
  | [], _, _, h => h
  | q :: a, b, b', h => by
    rw [List.cons_append, List.cons_append, List.lookup_cons, List.lookup_cons, lookup_tail n a b b' h]

/-- Under a name that is none of the eleven the list of values does not hang on the free numbers. -/
theorem lookup_values {n : String} (h : kept n = true) (v v' : FreeLines) :
    (valuesAt v).lookup n = (valuesAt v').lookup n := by
  have s1 : ∀ w : FreeLines, ∀ p ∈ (freeValues w).take 4, (n == p.1) = false :=
    fun w p hp => kept_ne h (List.mem_of_mem_take hp)
  have s2 : ∀ w : FreeLines, ∀ p ∈ ((freeValues w).drop 4).take 4, (n == p.1) = false :=
    fun w p hp => kept_ne h (List.mem_of_mem_drop (List.mem_of_mem_take hp))
  have s3 : ∀ w : FreeLines, ∀ p ∈ (freeValues w).drop 8, (n == p.1) = false :=
    fun w p hp => kept_ne h (List.mem_of_mem_drop hp)
  unfold VerifierAndGoals.Lines.valuesAt
  simp only [List.append_assoc]
  refine lookup_tail n _ _ _ ?_
  rw [lookup_skip n _ _ (s1 v), lookup_skip n _ _ (s1 v')]
  refine lookup_tail n _ _ _ ?_
  rw [lookup_skip n _ _ (s2 v), lookup_skip n _ _ (s2 v')]
  refine lookup_tail n _ _ _ ?_
  rw [lookup_skip n _ _ (s3 v), lookup_skip n _ _ (s3 v')]

/-- The twin of the library's VerifierAndGoals.Lines.hdrOf_pol (Johnson/Goal/Meaning/ScopeScan.lean:688) for eleven names. -/
theorem hdrOf_free {g g' : String → Nat} (k : ∀ n, kept n = true → g' n = g n) :
    hdrOf g' = { hdrOf g with
      eps := (hdrOf g').eps, MF := (hdrOf g').MF, KF := (hdrOf g').KF, epsF := (hdrOf g').epsF,
      clipC := (hdrOf g').clipC, theta := (hdrOf g').theta, cap := (hdrOf g').cap } := by
  have w : (["qk", "v", "o", "g", "u", "gs", "us", "gr", "ur", "dn", "dnr", "r"].map
      fun x => g' ("wb_" ++ x)) =
      ["qk", "v", "o", "g", "u", "gs", "us", "gr", "ur", "dn", "dnr", "r"].map
        fun x => g ("wb_" ++ x) := by
    simp only [List.map_cons, List.map_nil]
    rw [k ("wb_" ++ "qk") (by decide), k ("wb_" ++ "v") (by decide), k ("wb_" ++ "o") (by decide),
      k ("wb_" ++ "g") (by decide), k ("wb_" ++ "u") (by decide), k ("wb_" ++ "gs") (by decide),
      k ("wb_" ++ "us") (by decide), k ("wb_" ++ "gr") (by decide), k ("wb_" ++ "ur") (by decide),
      k ("wb_" ++ "dn") (by decide), k ("wb_" ++ "dnr") (by decide), k ("wb_" ++ "r") (by decide)]
  have i8 : ((List.range 8).map fun c => g' ("iota_" ++ toString c)) =
      (List.range 8).map fun c => g ("iota_" ++ toString c) := by
    apply List.map_congr_left
    intro c hc
    have : ∀ c, c < 8 → kept ("iota_" ++ toString c) = true := by decide
    exact k _ (this c (List.mem_range.1 hc))
  have i6 : ((List.range 6).map fun c => g' ("iotaH_" ++ toString c)) =
      (List.range 6).map fun c => g ("iotaH_" ++ toString c) := by
    apply List.map_congr_left
    intro c hc
    have : ∀ c, c < 6 → kept ("iotaH_" ++ toString c) = true := by decide
    exact k _ (this c (List.mem_range.1 hc))
  simp only [hdrOf, w, i8, i6]
  rw [k "prof" (by decide), k "lt" (by decide), k "L" (by decide), k "ll" (by decide),
    k "d" (by decide), k "H" (by decide), k "G" (by decide), k "dh" (by decide), k "f" (by decide),
    k "fe" (by decide), k "NE" (by decide), k "V" (by decide), k "cs" (by decide),
    k "hq" (by decide), k "hv" (by decide), k "ho" (by decide), k "hgD" (by decide),
    k "huD" (by decide), k "hdD" (by decide), k "hr" (by decide), k "ut" (by decide),
    k "la" (by decide), k "nmin" (by decide), k "D" (by decide), k "tau" (by decide),
    k "lmaf" (by decide), k "NAf" (by decide), k "lmad" (by decide), k "NAd" (by decide),
    k "lmar" (by decide), k "lmb" (by decide), k "lmq" (by decide), k "lmx" (by decide),
    k "lB" (by decide), k "S" (by decide), k "rx" (by decide), k "kFM" (by decide),
    k "kFD" (by decide), k "lmS" (by decide), k "NAs" (by decide), k "lmh" (by decide),
    k "lmo" (by decide), k "lmbA" (by decide), k "iotaA_0" (by decide), k "toksrc" (by decide),
    k "lmhf" (by decide), k "NHf" (by decide),
    k "lmhd" (by decide), k "lmhr" (by decide), k "lmbH" (by decide), k "wb_emb" (by decide),
    k "wb_head" (by decide), k "s" (by decide), k "sh" (by decide), k "sT" (by decide),
    k "F" (by decide),
    k ("theta0" ++ "_lo") (by decide), k ("theta0" ++ "_hi") (by decide),
    k ("seed" ++ "_lo") (by decide), k ("seed" ++ "_hi") (by decide)]

/-- **The scan at other free numbers is the scan, turned.** -/
theorem scan_turn {v v₀ : FreeLines} {P P₀ : PolScan} (h : polScan (policyFile v) = .ok P)
    (h₀ : polScan (policyFile v₀) = .ok P₀) : P = scanTurn P₀ (valuesAt v) v := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := VerifierAndGoals.Lines.hdr_free h
  have c := VerifierAndGoals.Lines.scan_closed h
  have c₀ := VerifierAndGoals.Lines.scan_closed h₀
  have hh : P.h = hdrTurn P₀.h v := by
    have a := hdrOf_free (g := fun n => ((valuesAt v₀).lookup n).getD 0)
      (g' := fun n => ((valuesAt v).lookup n).getD 0)
      fun n hn => by
        show ((valuesAt v).lookup n).getD 0 = ((valuesAt v₀).lookup n).getD 0
        rw [lookup_values hn v v₀]
    have b : P.h = hdrOf fun n => ((valuesAt v).lookup n).getD 0 := congrArg PolScan.h c
    have b₀ : P₀.h = hdrOf fun n => ((valuesAt v₀).lookup n).getD 0 := congrArg PolScan.h c₀
    rw [← b, ← b₀] at a
    rw [e1, e2, e3, e4, e5, e6, e7] at a
    exact a
  calc P = scanAt frameRef v := c
    _ = { scanAt frameRef v₀ with values := valuesAt v, h := (scanAt frameRef v).h } := rfl
    _ = scanTurn P₀ (valuesAt v) v := by
      unfold scanTurn
      rw [← c, ← c₀, hh]

/-! ## p7 · the digest of the three files is made -/

/-- The twin of LPFPol.hPar_returns (Johnson/LPFPol/HashReturns.lean:196) for another scale file too. -/
theorem hPar_returns2 {pol pol' KL KL' : ByteArray} {layout : Option ByteArray} {x : ByteArray}
    (h : hPar pol KL layout = .ok x) (hl : pol'.size < 2 ^ 32) (k4 : KL'.size % 4 = 0)
    (k32 : 32 ≤ KL'.size) (kb : KL'.size < 2 ^ 40) : ∃ x', hPar pol' KL' layout = .ok x' := by
  unfold hPar at h ⊢
  obtain ⟨D, hD, h⟩ := exc_bind h
  obtain ⟨p, k, l, hp, a1, hk, a3, rfl⟩ := LPFPol.parDigests_parts hD
  obtain ⟨p', hp'⟩ := LPFPol.textTH_returns pol' hl
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.1 (LPFPol.isSome_olderTK_of KL' k4 k32 kb)
  have a1' : klHeld KL' = .ok () := by
    unfold klHeld
    refine refuseIf_no ?_
    have q1 : (KL'.size % 4 != 0) = false := by simp [k4]
    have q2 : decide (KL'.size < 32) = false := decide_eq_false (by omega)
    rw [q1, q2]
    rfl
  have e : (secondHashFunctionTree (p'.1 ++ word32 p'.2 ++ k' ++ word32 (klWords KL') ++ l.1 ++ word32 l.2)).isSome =
      (secondHashFunctionTree (p.1 ++ word32 p.2 ++ k ++ word32 (klWords KL) ++ l.1 ++ word32 l.2)).isSome := by
    apply OnBytes.K.isSome_olderTK
    simp only [ByteArray.size_append, OnBytes.K.size_word32, LPFPol.textTH_size hp,
      LPFPol.textTH_size hp', OnBytes.K.size_olderTK hk, OnBytes.K.size_olderTK hk']
  have s : (secondHashFunctionTree (p.1 ++ word32 p.2 ++ k ++ word32 (klWords KL) ++ l.1 ++ word32 l.2)).isSome =
      true := by
    unfold hParOf at h
    dsimp only at h
    split at h
    · rename_i x0 hx
      rw [hx]
      rfl
    · cases h
  obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.1 (e.trans s)
  refine ⟨x', ?_⟩
  refine (bind_ok (LPFPol.parDigests_of hp' a1' hk' a3)).trans ?_
  unfold hParOf
  dsimp only
  rw [hx']
  rfl

/-- Where publicOfO returns, its seventh step has returned. (The walk of publicSteps_of_O, PublicAtSteps.lean:124.) -/
theorem hPar_of_public {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Public} (h : publicOfO o pol KL layout = .ok X) :
    ∃ x, hParO o pol KL layout = .ok x := by
  unfold VerifiableInference.PlanWritten.publicOfO at h
  obtain ⟨⟨P, y⟩, _, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨sc, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  have h := Fo.Pub.ite_unit_ok h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨x, hx, _⟩ := exc_bind h
  exact ⟨x, hx⟩

/-- **p7 in scope**, from the return at the stored files. -/
theorem hPar_in_scope {X₀ : Public}
    (h₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    {F : VerifierAndGoals.PublicFiles} (hC : VerifierAndGoals.InScope F = true) :
    ∃ hp, hParO OnBytes.secondHashFunction F.pol F.KL (some F.lay) = .ok hp := by
  obtain ⟨x, hx⟩ := hPar_of_public h₀
  rw [VerifiableInference.PlanWritten.hParO_older] at hx ⊢
  have hlay : F.lay = VerifierAndGoals.storedPublicFiles.lay := by
    unfold VerifierAndGoals.InScope at hC
    rw [Bool.and_eq_true, decide_eq_true_eq] at hC
    exact hC.1
  obtain ⟨pp, hR⟩ : ∃ pp, VerifierAndGoals.readFiles F = .ok pp := by
    unfold VerifierAndGoals.InScope at hC
    rw [Bool.and_eq_true] at hC
    have h2 := hC.2
    split at h2
    · rename_i pp hpp
      exact ⟨pp, hpp⟩
    · cases h2
  obtain ⟨P, f, hP, hf, -⟩ := OnBytes.Flat.settingsAny_parts (OnBytes.Flat.settingsAtRef_eq hR)
  have hpol := OnBytes.Road.Hd.policy_of_scope hC hR
  rw [hpol] at hP
  have hl : F.pol.size < 2 ^ 32 := by
    rw [hpol]
    exact LPFPol.size_policyFile hP
  have hL : P.h.L = 48 := by
    rw [VerifierAndGoals.Lines.scan_closed hP]
    rfl
  have hn := Meaning.Ret.len_of_klFile hL hf
  have hn' : F.KL.size / 4 = 13 * 48 + 3 * 24 := by
    rw [← hn]
    simp [fileWords]
  have k4 : F.KL.size % 4 = 0 := by
    unfold OnBytes.Flat.klFileOf at hf
    dsimp only at hf
    split at hf
    · rename_i c
      exact c.2.1
    · cases hf
  rw [hlay]
  exact hPar_returns2 hx hl k4 (by omega) (by omega)

/-! ## what the goals' reader says of the free things -/

/-- The twin of Meaning.Att.sh_in_scope with no return of publicOf. -/
theorem sh_of_read {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (L : Fin 48) :
    (Meaning.Ret.recOf Z.KL).klSh L.val = (pp.w L).sh := by
  obtain ⟨P, f, hP, hf, ho⟩ := OnBytes.Flat.settingsAny_parts (OnBytes.Flat.settingsAtRef_eq hR)
  have ew : (pp.w L).sh = f.lay L 11 := by
    unfold Inst.Model.ofKL at ho
    split at ho
    · cases ho
      rfl
    · cases ho
  rw [OnBytes.Road.Hd.policy_of_scope hZ hR] at hP
  have hL : P.h.L = 48 := by
    rw [VerifierAndGoals.Lines.scan_closed hP]
    rfl
  rw [ew, Meaning.Ret.lay_word hL hf L 11]
  rfl

/-- In scope a group of four layers has one shift, and it lies in 4 to 12. -/
theorem shifts_of_read {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) {g l : Nat} (hg : g < 12) (hl : l < 4) :
    (Meaning.Ret.recOf Z.KL).klSh (g * 4 + l) = (Meaning.Ret.recOf Z.KL).klSh (g * 4) ∧
      4 ≤ (Meaning.Ret.recOf Z.KL).klSh (g * 4) ∧ (Meaning.Ret.recOf Z.KL).klSh (g * 4) ≤ 12 := by
  obtain ⟨-, -, -, hLaw⟩ := OnBytes.Flat.settingsAny_iff.1 (OnBytes.Flat.settingsAtRef_eq hR)
  have one := hLaw.one ⟨g, hg⟩ ⟨l, hl⟩
  have h1 : 4 * g + l < 48 := by omega
  have h0 : 4 * g < 48 := by omega
  have k1 : (pp.kap (4 * g + l)).sh = (pp.w ⟨4 * g + l, h1⟩).sh := by
    unfold Inst.Model.ScalesAndPolicy.kap
    rw [dif_pos h1]
    rfl
  have k0 : (pp.kap (4 * g)).sh = (pp.w ⟨4 * g, h0⟩).sh := by
    unfold Inst.Model.ScalesAndPolicy.kap
    rw [dif_pos h0]
    rfl
  have one' : (pp.kap (4 * g + l)).sh = (pp.kap (4 * g)).sh := one
  rw [k1, k0, ← sh_of_read hZ hR ⟨4 * g + l, h1⟩, ← sh_of_read hZ hR ⟨4 * g, h0⟩] at one'
  have r := hLaw.sh ⟨4 * g, h0⟩
  rw [← sh_of_read hZ hR ⟨4 * g, h0⟩] at r
  have e1 : g * 4 + l = 4 * g + l := by omega
  have e0 : g * 4 = 4 * g := by omega
  rw [e1, e0]
  exact ⟨one', r⟩

/-- The eight free numbers, as the goals' reader read them, lie in these bounds. -/
theorem free_bounds {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hR : VerifierAndGoals.readFiles Z = .ok pp) :
    (1 ≤ (VerifierAndGoals.freeLinesOf pp).eps1 ∧ (VerifierAndGoals.freeLinesOf pp).eps1 < 2 ^ 59) ∧
    (1 ≤ (VerifierAndGoals.freeLinesOf pp).eps2 ∧ (VerifierAndGoals.freeLinesOf pp).eps2 < 2 ^ 59) ∧
    (1 ≤ (VerifierAndGoals.freeLinesOf pp).epsF ∧ (VerifierAndGoals.freeLinesOf pp).epsF < 2 ^ 59) ∧
    (24 ≤ (VerifierAndGoals.freeLinesOf pp).MF ∧ (VerifierAndGoals.freeLinesOf pp).MF ≤ 47 ∧
      (VerifierAndGoals.freeLinesOf pp).MF ≤ (VerifierAndGoals.freeLinesOf pp).KF + 14) ∧
    (17 ≤ (VerifierAndGoals.freeLinesOf pp).KF ∧ (VerifierAndGoals.freeLinesOf pp).KF ≤ 32) ∧
    (VerifierAndGoals.freeLinesOf pp).theta ≤ (VerifierAndGoals.freeLinesOf pp).C ∧
    (VerifierAndGoals.freeLinesOf pp).cap ≤ 1024 ∧ (VerifierAndGoals.freeLinesOf pp).C < 2 ^ 32 := by
  have hw := OnBytes.Flat.settingsAtRef_lawful hR
  have n1 := (hw.ff 0).n1
  have n2 := (hw.ff 0).n2
  have nf := hw.nf
  unfold Inst.Model.NormPar.OK at n1 n2 nf
  obtain ⟨pC, pt, pc⟩ := hw.pol
  have a1 : (1 : Int) ≤ (pp.w 0).n1.eps := n1.1
  have a2 : (pp.w 0).n1.eps < 2 ^ 48 := n1.2.1
  have b1 : (1 : Int) ≤ (pp.w 0).n2.eps := n2.1
  have b2 : (pp.w 0).n2.eps < 2 ^ 48 := n2.2.1
  have c1 : (1 : Int) ≤ pp.nf.eps := nf.1
  have c2 : pp.nf.eps < 2 ^ 48 := nf.2.1
  have m1 : 24 ≤ pp.nf.M := nf.2.2.1
  have m2 : pp.nf.M ≤ 47 := nf.2.2.2.1
  have k1 : 17 ≤ pp.nf.K := nf.2.2.2.2.1
  have k2 : pp.nf.K ≤ 32 := nf.2.2.2.2.2.1
  have mk : pp.nf.M - 14 ≤ pp.nf.K := nf.2.2.2.2.2.2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨m1, m2, ?_⟩, ⟨k1, k2⟩, pt, pc, pC⟩
  · show 1 ≤ (pp.w 0).n1.eps.toNat
    omega
  · show (pp.w 0).n1.eps.toNat < 2 ^ 59
    omega
  · show 1 ≤ (pp.w 0).n2.eps.toNat
    omega
  · show (pp.w 0).n2.eps.toNat < 2 ^ 59
    omega
  · show 1 ≤ pp.nf.eps.toNat
    omega
  · show pp.nf.eps.toNat < 2 ^ 59
    omega
  · show pp.nf.M ≤ pp.nf.K + 14
    omega

/-- The layers' shape of Z's scan is that of the stored files' scan with the three free numbers set. -/
theorem shape_turn_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) {P P₀ : PolScan} (hP : polScan Z.pol = .ok P)
    (hP₀ : polScan VerifierAndGoals.storedPublicFiles.pol = .ok P₀) :
    layerShape P = { layerShape P₀ with
      eps1 := (VerifierAndGoals.freeLinesOf pp).eps1,
      eps2 := (VerifierAndGoals.freeLinesOf pp).eps2, epsF := (VerifierAndGoals.freeLinesOf pp).epsF } := by
  obtain ⟨P', hP', e⟩ := Meaning.Ret.shape_of_read hZ hR
  obtain rfl : P' = P := Except.ok.inj (hP'.symm.trans hP)
  have e₀ : layerShape P₀ = { OnBytes.Road.hKF with
      eps1 := (scanAt frameRef VerifierAndGoals.storedLines).h.eps.getD 0 0,
      eps2 := (scanAt frameRef VerifierAndGoals.storedLines).h.eps.getD 1 0,
      epsF := (scanAt frameRef VerifierAndGoals.storedLines).h.epsF } := by
    rw [VerifierAndGoals.Lines.scan_closed (v := VerifierAndGoals.storedLines) hP₀]
    exact Meaning.P34.shape_of_closed _
  rw [e, e₀]

end SetUp

end HonestTraceRun

#print axioms HonestTraceRun.SetUp.scan_turn
#print axioms HonestTraceRun.SetUp.hPar_in_scope
#print axioms HonestTraceRun.SetUp.sh_of_read
#print axioms HonestTraceRun.SetUp.shifts_of_read
#print axioms HonestTraceRun.SetUp.free_bounds
#print axioms HonestTraceRun.SetUp.shape_turn_in_scope
