-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Run.lean: the linear claim's shared rounds from their first place to the two
proximity tests: what the state that is handed to the tests means, with no premise on the
statement's tables.

Along a run of the places ("LIN point"; o_u is received; what the kind notes behind it;
"(rec_gamma)"; "LOC"; o_omega and o_sp are received; what the kind notes behind them; the joinings;
"LIN zeta"; "SPLIT") the statement only grows and each group's list of constraints only grows at its
end (Onward). So at the tests, each at its own state (Reaches): if all constraints on the two groups
hold of words, the three families' equations hold of these words (shared_means).
Main names: Onward, its lemmas for the plain ground functions and for the places, behindU_inv,
behindOmega_inv, SharedRun, shared_means.

What is not claimed. What lies between a receiving and the kind's note behind it (the sample's
admitting, another kind's) is asked as a premise: it goes Onward and leaves the small record. That
the state behind "SPLIT" reaches each test's state (Reaches: the statement grows; that test's own
group's list grows at its end alone) is a premise. That the constraints hold of words is the
proximity tests' law's to give. Nothing on the three equations
pinning the folded row to the encoded index. Nothing on soundness of a verifier.

-/
import Johnson.Desc.K14.Law.Carry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows)
open VerifiableInference.Desc.Ground

variable {K : Type} [Field K] (ρ : Reading K)

/-- The statement has grown, and each group's list of constraints has grown at its end alone. -/
structure Onward (d e : St) : Prop where
  grows : Grows d.st e.st
  later : ∀ g, Later d e g

/-- A state is onward of itself. -/
theorem Onward.refl (d : St) : Onward d d := ⟨Grows.refl _, fun _ => ⟨[], by simp⟩⟩

/-- Onward of onward is onward. -/
theorem Onward.trans {a b c : St} (h : Onward a b) (k : Onward b c) : Onward a c := by
  refine ⟨h.grows.trans k.grows, fun g => ?_⟩
  obtain ⟨x, hx⟩ := h.later g
  obtain ⟨y, hy⟩ := k.later g
  exact ⟨x ++ y, by rw [hy, hx, List.append_assoc]⟩

/-- The same statement. -/
theorem Onward.of_st {d e : St} (h : e.st = d.st) : Onward d e := by
  refine ⟨by rw [h]; exact Grows.refl _, fun g => ⟨[], ?_⟩⟩
  simp [rowsOn, h]

/-- A constraint more: onward. -/
theorem onward_addRowP (d d' : St) (g : Nat) (row : Row) (h : addRowP d g row = some d') :
    Onward d d' := by
  refine ⟨addRowP_grows d d' g row h, fun g' => ?_⟩
  by_cases e : g = g'
  · subst e; exact ⟨[row], rowsOn_addRowP_same d d' g row h⟩
  · exact ⟨[], by rw [rowsOn_addRowP_other d d' g g' row h e]; simp⟩

/-- Constraints more: onward. -/
theorem onward_addRowsP (d d' : St) (g : Nat) (rows : List Row)
    (h : addRowsP d g rows = some d') : Onward d d' := by
  obtain ⟨a, b, _⟩ := rowsOn_addRowsP g rows d d' h
  refine ⟨addRowsP_grows d d' g rows h, fun g' => ?_⟩
  by_cases e : g' = g
  · subst e; exact ⟨rows, a⟩
  · exact ⟨[], by rw [b g' e]; simp⟩

/-- A message joins a group: onward. -/
theorem onward_joinP (d d' : St) (g o : Nat) (kept : Bool) (h : joinP d g o kept = some d') :
    Onward d d' :=
  ⟨joinP_grows d d' g o kept h, fun g' => ⟨[], by rw [(rowsOn_joinP d d' g o kept h).1 g']; simp⟩⟩

/-- A mask entry is taken: onward. -/
theorem onward_takeMaskP (d d' : St) (o k : Nat) (h : takeMaskP d o = some (k, d')) :
    Onward d d' :=
  ⟨takeMaskP_grows d d' o k h, fun g => ⟨[], by rw [rowsOn_takeMaskP d d' o k g h]; simp⟩⟩

/-- A mask entry is taken: the small record stays. -/
theorem loc_takeMaskP (d d' : St) (o k : Nat) (h : takeMaskP d o = some (k, d')) :
    d'.loc = d.loc := by
  unfold takeMaskP at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨l, _, _, rfl⟩ := h
    rfl
  · cases h

/-- The receiving of oracle messages: onward; the small record stays. -/
theorem onward_recvP (ft : Nat) (d d' : St) (sent : Array OracleNotice) (ids : Array Nat)
    (h : recvP ft d sent = some (ids, d')) : Onward d d' ∧ d'.loc = d.loc := by
  refine ⟨⟨recvP_grows ft d d' sent ids h, fun g => ⟨[], ?_⟩⟩, ?_⟩
  · rw [List.append_nil]
    unfold rowsOn
    rw [(recvP_inv ft d d' sent ids h).1]
    rfl
  · unfold recvP at h
    split at h
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨lay, _, _, rfl⟩ := h
      rfl
    · cases h

/-! ## The places -/

/-- "LIN point": the statement grows. -/
theorem linPoint_grows (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : linPoint p d rs = some d') :
    Grows d.st d'.st := by
  unfold linPoint at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u0, _, ⟨gU, d1⟩, h1, h2⟩ := h
    have g1 := newGroupP_grows d d1 _ _ gU h1
    split at h2
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      exact g1.trans (newGroupP_grows d1 d2 _ _ gO h3)
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      simp only [Prod.mk.injEq] at h3
      rw [← h3.2]
      exact g1
  · cases h

/-- What the kind notes behind o_u's sending. -/
theorem behindU_inv (p : Par) (d d' : St) (ids : Array Nat) (h : behindU p d ids = some d') :
    d'.st = d.st ∧ ∃ o mask, ids[0]? = some o ∧ d'.loc = { d.loc with
      oU := ⟨o, vectorLay d.st.codes p.S.fold.u p.S.fold.rowsHigh⟩, firstMask := mask } := by
  unfold behindU at h
  simp only [Option.bind_eq_bind] at h
  split at h <;>
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨mask, _, o, ho, rfl⟩ := h
    exact ⟨rfl, o, mask, ho, rfl⟩

/-- What the kind notes behind o_omega's sending. -/
theorem behindOmega_inv (p : Par) (d d' : St) (ids : Array Nat)
    (h : behindOmega p d ids = some d') :
    d'.st = d.st ∧ ∃ o sp, ids[0]? = some o ∧ d'.loc = { d.loc with oOmega := o, oSp := sp } := by
  unfold behindOmega at h
  simp only [Option.bind_eq_bind] at h
  split at h <;>
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨sp, _, o, ho, rfl⟩ := h
    exact ⟨rfl, o, sp, ho, rfl⟩

/-- "(rec_gamma)": onward; the small record stays. -/
theorem onward_laysRec (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d') :
    Onward d d' ∧ d'.loc = d.loc := by
  refine ⟨?_, (laysRecW p d d' rs h).2.1⟩
  unfold laysRec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, hj, rows, _, ha⟩ := h
  exact (onward_joinP d d1 _ _ _ hj).trans (onward_addRowsP d1 d' _ rows ha)

/-- "LOC": onward; the small record stays. -/
theorem onward_loc (p : Par) (d d' : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (h : loc p d [r] [cols] = some d') : Onward d d' ∧ d'.loc = d.loc := by
  refine ⟨?_, (laysLocW p d d' r cols h).1⟩
  unfold loc at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨rows, _, ha⟩ := h
  exact onward_addRowsP d d' _ rows ha

/-- The joinings: onward; the small record stays. -/
theorem onward_joins (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : joins p d rs = some d') :
    Onward d d' ∧ d'.loc = d.loc := by
  unfold joins at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, h1, h2⟩ := h
  have o1 := onward_joinP d d1 _ _ _ h1
  have l1 := (rowsOn_joinP d d1 _ _ _ h1).2
  split at h2
  · simp only [Option.bind_eq_some_iff] at h2
    obtain ⟨d2, h3, h4⟩ := h2
    exact ⟨(o1.trans (onward_joinP d1 d2 _ _ _ h3)).trans (onward_joinP d2 d' _ _ _ h4),
      ((rowsOn_joinP d2 d' _ _ _ h4).2.trans (rowsOn_joinP d1 d2 _ _ _ h3).2).trans l1⟩
  · simp only [Option.some.injEq] at h2
    subst h2
    exact ⟨o1, l1⟩

/-- "LIN zeta" notes the drawn elements and turns nothing else. -/
theorem linZeta_inv (d d' : St) (r : Fmt.RoundView) (h : linZeta d [r] = some d') :
    d' = { d with loc := { d.loc with zFd := drawn r } } := by
  simp only [linZeta, Option.some.injEq] at h
  exact h.symm

/-- "SPLIT": onward; the small record stays. -/
theorem onward_split (p : Par) (d d' : St) (r : Fmt.RoundView) (hS : p.S.sharedSplitNeeded = true)
    (h : split p d [r] = some d') : Onward d d' ∧ d'.loc = d.loc := by
  obtain ⟨row, x, G, kappa, d₁, d₂, _, _, _, _, hk, h2, h3⟩ := split_inv p d d' r hS h
  exact ⟨((onward_takeMaskP d d₁ _ _ hk).trans (onward_addRowP d₁ d₂ _ _ h2)).trans
    (onward_addRowP d₂ d' _ _ h3),
    ((loc_addRowP d₂ d' _ _ h3).trans (loc_addRowP d₁ d₂ _ _ h2)).trans (loc_takeMaskP d d₁ _ _ hk)⟩

/-! ## A run -/

/-- **A run of the shared rounds' places**, from "LIN point" to "SPLIT". a1, a2 and b1, b2: the
states behind a receiving and in front of the kind's note: between them lies the admitting of the
samples, another kind's: it goes onward and leaves the small record. -/
structure SharedRun (p : Par) (d0 d2 d3 d7 d8 : St) (r4 : Fmt.RoundView)
    (cols : List (Nat × List UInt64)) : Prop where
  twoCodes : p.S.sharedSplitNeeded = true
  run : ∃ (d1 a1 a2 d4 b1 b2 d5 d6 : St) (rs1 rs3 rs6 : List Fmt.RoundView) (r7 r8 : Fmt.RoundView)
    (ftU ftO : Nat) (sentU : Array OracleNotice) (idsU idsO : Array Nat),
    linPoint p d0 rs1 = some d1 ∧
    withU p.S = some sentU ∧ recvP ftU d1 sentU = some (idsU, a1) ∧
    Onward a1 a2 ∧ a2.loc = a1.loc ∧ behindU p a2 idsU = some d2 ∧
    laysRec p d2 rs3 = some d3 ∧ loc p d3 [r4] [cols] = some d4 ∧
    recvP ftO d4 (withOmega p.S) = some (idsO, b1) ∧
    Onward b1 b2 ∧ b2.loc = b1.loc ∧ behindOmega p b2 idsO = some d5 ∧
    joins p d5 rs6 = some d6 ∧ linZeta d6 [r7] = some d7 ∧ split p d7 [r8] = some d8

/-- The first notice of o_u's sending, and of o_omega's. -/
theorem withU_first (S : LinShape) (sent : Array OracleNotice) (h : withU S = some sent) :
    ∃ n, sent[0]? = some n ∧ n.shape = S.fold.u := by
  unfold withU at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨x, _, rfl⟩ := h
  exact ⟨⟨S.fold.u, S.fold.leafClass⟩, by simp, rfl⟩

@[inherit_doc withU_first]
theorem withOmega_first (S : LinShape) :
    ∃ n, (withOmega S)[0]? = some n ∧ n.shape = S.omega := by
  refine ⟨⟨S.omega, S.omegaLeafClass⟩, ?_, rfl⟩
  unfold withOmega linMessageOmega
  split <;> simp

/-- The public shape's conditions hold the stored table's. -/
theorem index_ok_of_linOk (codes : Codes) (S : LinShape) (hok : linOk codes S = true) :
    S.fold.index.ok = true := by
  simp only [linOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hF : foldeqOk codes S.fold = true := by tauto
  simp only [foldeqOk, FoldeqShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hF
  tauto

/-- A list that has grown at its end alone, twice. -/
theorem Later.trans {a b c : St} {g : Nat} (h : Later a b g) (k : Later b c g) : Later a c g := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy⟩ := k
  exact ⟨x ++ y, by rw [hy, hx, List.append_assoc]⟩

/-- **What the state that a run hands to the two proximity tests means.** eU, eO: the states at the
test on G_u and at the test on G_omega. -/
theorem shared_means (p : Par) (d0 d2 d3 d7 d8 eU eO : St) (r4 : Fmt.RoundView)
    (cols : List (Nat × List UInt64)) (h : SharedRun p d0 d2 d3 d7 d8 r4 cols)
    (kU : Reaches d8 eU d8.loc.gU) (kO : Reaches d8 eO d8.loc.gOmega)
    (m : Words K) (sU : Means.AllSay ρ eU.st (rowsOn eU d8.loc.gU) m)
    (sO : Means.AllSay ρ eO.st (rowsOn eO d8.loc.gOmega) m) :
    (∀ x ∈ d2.loc.key.seeds.zipIdx,
      RecEq p.S.fold.index (x.1.z.map ρ.val) (ρ.val x.1.beta) (fun t => ρ.val (thetaE t)) x.2
        (fun r => ρ.val ((weights p.S d2.loc).getD r zeroE))
        (fun k => ρ.val (d2.loc.key.record.getD k zeroE))
        (fun k => m d2.loc.oU.oracle .main (d2.loc.oU.lay.index k))) ∧
    (∀ x ∈ locations p r4, ∃ col, cols.lookup x = some col ∧
      LocEq ρ p.S.fold (generatorAt p.S.fold.index.code x)
        (fun r => ρ.val ((weights p.S d3.loc).getD r zeroE)) (weights p.S d3.loc).size
        (fun r => ρ.val (ofF (col.toArray.getD r 0)))
        (fun k => m d3.loc.oU.oracle .main (d3.loc.oU.lay.index k))) ∧
    FoldEq p.S ((d7.loc.psiSh.take p.S.kLo).map ρ.val) (d7.loc.zFd.map ρ.val)
      (omegaOf d7.loc (linLayOmega d7.st.codes p.S) m) (uOf d7.loc m) := by
  obtain ⟨hS, d1, a1, a2, d4, b1, b2, d5, d6, rs1, rs3, rs6, r7, r8, ftU, ftO, sentU, idsU, idsO,
    h1, hU, rU, cU, cUl, h2, h3, h4, rO, cO, cOl, h5, h6, h7, h8⟩ := h
  have hok0 := linPoint_ok p d0 d1 rs1 h1
  have hok : linOk d1.st.codes p.S = true := by rw [(linPoint_grows p d0 d1 rs1 h1).1]; exact hok0
  obtain ⟨oU1, lU1⟩ := onward_recvP ftU d1 a1 sentU idsU rU
  obtain ⟨s2, o, mask, ho, l2⟩ := behindU_inv p a2 d2 idsU h2
  obtain ⟨o3, l3⟩ := onward_laysRec p d2 d3 rs3 h3
  obtain ⟨o4, l4⟩ := onward_loc p d3 d4 r4 cols h4
  obtain ⟨oO1, lO1⟩ := onward_recvP ftO d4 b1 (withOmega p.S) idsO rO
  obtain ⟨s5, oo, sp, hoo, l5⟩ := behindOmega_inv p b2 d5 idsO h5
  obtain ⟨o6, l6⟩ := onward_joins p d5 d6 rs6 h6
  have e7 := linZeta_inv d6 d7 r7 h7
  obtain ⟨o8, l8⟩ := onward_split p d7 d8 r8 hS h8
  have o7 : Onward d6 d7 := Onward.of_st (by rw [e7])
  have A : Onward a1 d4 := ((cU.trans (Onward.of_st s2)).trans o3).trans o4
  have B7 : Onward b1 d7 := ((cO.trans (Onward.of_st s5)).trans o6).trans o7
  have B : Onward b1 d8 := B7.trans o8
  have l7 : d7.loc = { d2.loc with oOmega := oo, oSp := sp, zFd := drawn r7 } := by
    rw [e7]
    show ({ d6.loc with zFd := drawn r7 } : Lin) = _
    rw [l6, l5, cOl, lO1, l4, l3]
  have hoU : d7.loc.oU = d2.loc.oU := by rw [l7]
  have hgU : d8.loc.gU = d2.loc.gU := by rw [l8, l7]
  have hcA : a2.st.codes = d1.st.codes := (oU1.trans cU).grows.1
  obtain ⟨nU, sU0, shU⟩ := withU_first p.S sentU hU
  obtain ⟨nO, sO0, shO⟩ := withOmega_first p.S
  have hSeat : Seated d8.st d1.st.codes p.S d7.loc :=
    seated_behind d1.st.codes p.S d7.loc d8.st d1 a1 d4 b1 ftU ftO sentU (withOmega p.S) idsU idsO
      nU nO rfl rU sU0 shU (by rw [hoU, l2]; exact ho) A.grows rO sO0 shO (by rw [l7]; exact hoo)
      B.grows (by rw [hoU, l2, ← hcA])
  have hi := index_ok_of_linOk _ _ hok
  have hPU := placedU_of_seated (hSeat.grows kU.grows) hok
  have hc7 : d7.st.codes = d1.st.codes := (((oU1.trans A).trans oO1).trans B7).grows.1
  have hP : Placed d8.st p.S d7.loc (linLayOmega d7.st.codes p.S) := by
    rw [hc7]; exact placed_of_seated hSeat hok
  refine ⟨?_, ?_, ?_⟩
  · exact recSays ρ p d2 d3 eU rs3 eU.st m h3
      ((((o4.trans oO1).trans B).later _).trans (by rw [← hgU]; exact kU.later))
      (by rw [← hgU]; exact sU) hi (by rw [← hoU]; exact hPU)
  · exact locSays ρ p d3 d4 eU r4 cols eU.st m h4
      (((oO1.trans B).later _).trans (by rw [l3, ← hgU]; exact kU.later))
      (by rw [l3, ← hgU]; exact sU) hi (by rw [l3, ← hoU]; exact hPU)
  · exact foldSaysAt ρ p d7 d8 eU eO r8 m hS h8 (by rw [← l8]; exact kO) (by rw [← l8]; exact kU)
      (by rw [← l8]; exact sO) (by rw [← l8]; exact sU) hP

end Desc.K14.Law
