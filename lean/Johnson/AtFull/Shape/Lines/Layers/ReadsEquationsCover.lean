-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/ReadsEquationsCover.lean: the smallness test's run "K8.equations"
on shapes, with two entries in the place of a read's claim's entries where these lie in one row: a
third text of the run, beside eqRunG and eqRunGO; and the one-way tie: where this light run returns,
the library's run returns, the light claims standing under its claims (ClaimStandsUnder,
ClaimCovers.lean), with the same shape after. Five definitions and general laws without a premise;
nothing is evaluated.

Why. A read's claim names one entry for each column of its matrix: entry number st + col * sgs + sg
of the vector's array, as (array, number / c, number % c), c the array's number of columns (readSh,
Johnson/Desc/K8/Honest/EqShapes.lean). The numbers rise with col. Where the last is below c, all
lie in row 0, between the first and the last.

  entriesCover_self       a list covers itself.
  readClaimCover          no entry where the matrix has no column; the first and the last entry
                          where the last number is below c; else the whole list, as readSh has it.
  readClaimCover_covers   it covers readSh's list.
  readClaimCovered, readClaimCovered_standsUnder   the read's claim's shape with readClaimCover; it
                          may stand for readSh's.
  readClaimsCovered, readClaimsCovered_standUnder   the reads' claims in order.
  equationClaimsCovered, equationsRunCovered   the texts of eqClaimsG and eqRunGO with
                          readClaimsCovered.
  **equationsRunCovered_standsUnder**   where equationsRunCovered returns y', eqRunG returns some y
                          with y'.1 under y.1, member by member, and y'.2 = y.2.

Limits. One way. The two entries are entries of the claim itself, so they pass wherever all pass.
Where the last number is not below c nothing is lightened. What either text costs Lean's kernel is
not measured here. That either returns at a shape which the chain reaches is not shown. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.ClaimCovers
import Johnson.AtFull.Shape.K8AllOr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K9.Shape (EntriesCover ClaimStandsUnder ClaimsStandUnder
    claimStandsUnder_ofCover claimsStandUnder_cons)
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- A list covers itself. -/
theorem entriesCover_self (l : List EntSh) : EntriesCover l l :=
  fun x hx => ⟨x.2.2, x.2.2, hx, hx, Nat.le_refl _, Nat.le_refl _⟩

/-- The entries that stand for a read's claim's: k: the matrix's columns; st, sgs, sg: the numbers
of readSh's text; c: the array's columns; tU: the array. -/
def readClaimCover (k st sgs sg c tU : Nat) : List EntSh :=
  if k = 0 then []
  else if st + (k - 1) * sgs + sg < c then [(tU, 0, st + sg), (tU, 0, st + (k - 1) * sgs + sg)]
  else (List.range k).map fun col =>
    (tU, (st + col * sgs + sg) / c, (st + col * sgs + sg) % c)

/-- readClaimCover covers the entries of readSh's text. -/
theorem readClaimCover_covers (k st sgs sg c tU : Nat) :
    EntriesCover (readClaimCover k st sgs sg c tU) ((List.range k).map fun col =>
      (tU, (st + col * sgs + sg) / c, (st + col * sgs + sg) % c)) := by
  unfold readClaimCover
  split
  · rename_i h0
    subst h0
    intro x hx
    cases hx
  · split
    · rename_i hk hlt
      intro x hx
      obtain ⟨col, hc, rfl⟩ := List.mem_map.1 hx
      have hc' : col < k := List.mem_range.1 hc
      have hm : col * sgs ≤ (k - 1) * sgs := Nat.mul_le_mul_right _ (by omega)
      have hl : st + col * sgs + sg < c := by omega
      refine ⟨st + sg, st + (k - 1) * sgs + sg, ?_, ?_, ?_, ?_⟩
      · show (tU, (st + col * sgs + sg) / c, st + sg) ∈ _
        rw [Nat.div_eq_of_lt hl]
        exact List.mem_cons_self
      · show (tU, (st + col * sgs + sg) / c, st + (k - 1) * sgs + sg) ∈ _
        rw [Nat.div_eq_of_lt hl]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · show st + sg ≤ (st + col * sgs + sg) % c
        rw [Nat.mod_eq_of_lt hl]
        omega
      · show (st + col * sgs + sg) % c ≤ st + (k - 1) * sgs + sg
        rw [Nat.mod_eq_of_lt hl]
        omega
    · exact entriesCover_self _

/-- readSh's text with readClaimCover for the entries. -/
def readClaimCovered (tl : HTailF2) (F : Fork) (Fn : HFun) (sg laid tU : Nat) : ClaimSh :=
  ClaimSh.mk (some (tl.eqFirst.getD tl.NM 0 + laid * tl.stepF))
    (AffSh.mk (readClaimCover (tl.mats.getD Fn.mat {}).k Fn.start (segs tl Fn) sg (colsOf F tU) tU)
        [])
    [RunSh.mk tl.ix.ZZ tl.zzRowReads (tl.off.getD Fn.mat 0 + sg * Fn.len) Fn.phi.size 0 Fn.len,
      RunSh.mk tl.ix.ZZ tl.zzRowReads (tl.mz + tl.off.getD Fn.mat 0 + sg * Fn.len) Fn.phi.size 0
        Fn.len]

/-- The light claim may stand for readSh's. -/
theorem readClaimCovered_standsUnder (tl : HTailF2) (F : Fork) (Fn : HFun) (sg laid tU : Nat) :
    ClaimStandsUnder (readClaimCovered tl F Fn sg laid tU) (readSh tl F Fn sg laid tU) :=
  claimStandsUnder_ofCover _ _ [] _ (readClaimCover_covers _ _ _ _ _ _)

/-- readsSh's text with readClaimCovered. -/
def readClaimsCovered (tl tl' : HTailF2) (F : Fork) : Nat → List (HFun × Nat) →
    Option (List ClaimSh)
  | _, [] => some []
  | q, x :: l =>
    (tl.ix.U.getD x.1.tree none).bind fun tU =>
      (readClaimsCovered tl tl' F (q + 1) l).map fun r => readClaimCovered tl' F x.1 x.2 q tU :: r

/-- Where the light list of the reads' claims returns, readsSh returns a list, and the light list
stands under it. -/
theorem readClaimsCovered_standUnder (tl tl' : HTailF2) (F : Fork) : ∀ (q : Nat) (l : List (HFun ×
    Nat))
    (r' : List ClaimSh), readClaimsCovered tl tl' F q l = some r' →
    ∃ r, readsSh tl tl' F q l = some r ∧ ClaimsStandUnder r' r
  | _, [], r', h => by
    obtain rfl : [] = r' := Option.some.inj h
    exact ⟨[], rfl, trivial⟩
  | q, x :: l, r', h => by
    unfold readClaimsCovered at h
    unfold readsSh
    cases hU : tl.ix.U.getD x.1.tree none with
    | none =>
      rw [hU] at h
      cases h
    | some tU =>
      rw [hU] at h
      cases hr : readClaimsCovered tl tl' F (q + 1) l with
      | none =>
        have h' : (readClaimsCovered tl tl' F (q + 1) l).map
            (fun r => readClaimCovered tl' F x.1 x.2 q tU :: r) = some r' := h
        rw [hr] at h'
        cases h'
      | some s' =>
        have h' : (readClaimsCovered tl tl' F (q + 1) l).map
            (fun r => readClaimCovered tl' F x.1 x.2 q tU :: r) = some r' := h
        rw [hr] at h'
        obtain rfl : readClaimCovered tl' F x.1 x.2 q tU :: s' = r' := Option.some.inj h'
        obtain ⟨s, es, hu⟩ := readClaimsCovered_standUnder tl tl' F (q + 1) l s' hr
        refine ⟨readSh tl' F x.1 x.2 q tU :: s, ?_, claimsStandUnder_cons.2
            ⟨readClaimCovered_standsUnder _ _ _ _ _ _, hu⟩⟩
        show (readsSh tl tl' F (q + 1) l).map (fun r => readSh tl' F x.1 x.2 q tU :: r) = _
        rw [es]
        rfl

/-- eqClaimsG's text with readClaimsCovered. -/
def equationClaimsCovered (a t : ChainSh) : Option (List ClaimSh) :=
  match a.tl, a.tables, t.tl, t.led with
  | some t0, some fs, some t1, some L1 =>
    t0.heard.bind fun g =>
      (readClaimsCovered t0.blank t1.blank (ledBlank L1) 0
        (readsList t0.blank ((fs.map FunSh.blank).toArray))).map fun reads =>
          allClaimsU t0 t1 g ++ reads
  | _, _, _, _ => none

/-- Where the light claims return, eqClaimsG returns claims that they stand under. -/
theorem equationClaimsCovered_standUnder {a t : ChainSh} {cs' : List ClaimSh} (h :
    equationClaimsCovered a t = some cs') :
    ∃ cs, eqClaimsG a t = some cs ∧ ClaimsStandUnder cs' cs := by
  unfold equationClaimsCovered at h
  unfold eqClaimsG
  cases h1 : a.tl <;> cases h2 : a.tables <;> cases h3 : t.tl <;> cases h4 : t.led <;>
    rw [h1, h2, h3, h4] at h <;> first | cases h | skip
  rename_i t0 fs t1 L1
  dsimp only at h ⊢
  cases hg : t0.heard with
  | none =>
    rw [hg] at h
    cases h
  | some g =>
    rw [hg] at h
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1
      (show (readClaimsCovered t0.blank t1.blank (ledBlank L1) 0
        (readsList t0.blank ((fs.map FunSh.blank).toArray))).map
          (fun reads => allClaimsU t0 t1 g ++ reads) = some cs' from h)
    obtain ⟨r, er, hu⟩ := readClaimsCovered_standUnder _ _ _ _ _ r' hr'
    refine ⟨allClaimsU t0 t1 g ++ r, ?_, ClaimsStandUnder.append (ClaimsStandUnder.refl _) hu⟩
    show (readsSh t0.blank t1.blank (ledBlank L1) 0
      (readsList t0.blank ((fs.map FunSh.blank).toArray))).map
        (fun reads => allClaimsU t0 t1 g ++ reads) = _
    rw [er]
    rfl

/-- eqRunGO's text with equationClaimsCovered. -/
def equationsRunCovered (n : Nat) (a : ChainSh) : Except String (List ClaimSh × ChainSh) :=
  (eqGO n a).bind fun t =>
    match equationClaimsCovered a t with
    | some cs => .ok (cs, t)
    | none => .error "K8.equations: the claims' shapes cannot be said"

/-- **Where the light run returns, the library's returns**, the light claims under its claims, with
the same shape after. -/
theorem equationsRunCovered_standsUnder {n : Nat} {a : ChainSh} {y' : List ClaimSh × ChainSh}
    (h : equationsRunCovered n a = .ok y') : ∃ y, eqRunG n a = .ok y ∧ ClaimsStandUnder y'.1 y.1 ∧
        y'.2 = y.2 := by
  unfold equationsRunCovered at h
  rw [eqRunG_eqO]
  unfold eqRunGO
  cases ht : eqGO n a with
  | error e =>
    rw [ht] at h
    cases h
  | ok t =>
    rw [ht] at h
    have h' : (match equationClaimsCovered a t with
      | some cs => (.ok (cs, t) : Except String (List ClaimSh × ChainSh))
      | none => .error "K8.equations: the claims' shapes cannot be said") = .ok y' := h
    cases hc : equationClaimsCovered a t with
    | none =>
      rw [hc] at h'
      cases h'
    | some cs' =>
      rw [hc] at h'
      obtain rfl : (cs', t) = y' := Except.ok.inj h'
      obtain ⟨cs, ec, hu⟩ := equationClaimsCovered_standUnder hc
      refine ⟨(cs, t), ?_, hu, rfl⟩
      show (match eqClaimsG a t with
        | some cs => (.ok (cs, t) : Except String (List ClaimSh × ChainSh))
        | none => .error "K8.equations: the claims' shapes cannot be said") = _
      rw [ec]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.entriesCover_self
#print axioms VerifiableInference.Desc.First.K8.Honest.readClaimCover
#print axioms VerifiableInference.Desc.First.K8.Honest.readClaimCover_covers
#print axioms VerifiableInference.Desc.First.K8.Honest.readClaimCovered
#print axioms VerifiableInference.Desc.First.K8.Honest.readClaimCovered_standsUnder
#print axioms VerifiableInference.Desc.First.K8.Honest.readClaimsCovered
#print axioms VerifiableInference.Desc.First.K8.Honest.readClaimsCovered_standUnder
#print axioms VerifiableInference.Desc.First.K8.Honest.equationClaimsCovered
#print axioms VerifiableInference.Desc.First.K8.Honest.equationClaimsCovered_standUnder
#print axioms VerifiableInference.Desc.First.K8.Honest.equationsRunCovered
#print axioms VerifiableInference.Desc.First.K8.Honest.equationsRunCovered_standsUnder
