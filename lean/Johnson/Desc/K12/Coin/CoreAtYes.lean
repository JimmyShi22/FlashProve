-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Coin.Sheet
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.K12.Law.Step8
import Johnson.Desc.K12.Law.TieFront
import Johnson.Desc.K12.Law.RowsBlankGp
import Johnson.Desc.K12.Law.SampleLaw
import Johnson.Desc.K12.Law.SampleOfSeed
import Johnson.Desc.K12.Law.FitsLen
import Johnson.Desc.K12.Law.TopF
import Johnson.Desc.K12.Coin.ShapesAtSeat
import OnBytes.Params.Fit.FitCaps
/-
Johnson/Desc/K12/Coin/CoreAtYes.lean: WHAT A YES OF THE PROXIMITY TEST's OWN DECISION ALONE PAYS OF
THE PREMISES THAT THE SEAM's CORE ASKS (tuple_core,
Johnson/Desc/Sound/SeamTuple.lean). GENERAL IN THE ARM AND IN THE SEAT; NO
CONDITION CARRIED ALONG THE CHAIN IS ASKED; NO TEST ON THE PLAN.
Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW
MATHEMATICS: calls of the library's lemmas.
  front_sampled · front_rows: two clauses of the front, as theorems. begun_same: the beginning of a
    test turns of a message neither the mark «sampled», nor the sample rows, nor the shape.
  found_of_decide: (proximityTestKind guardedProximityTestParts π).decide t rs gs = .ok tE, AT ANY rs gs ⇒ at whatever the state
    fixes: hfind (the layout finds each member at its own number) · hmembers (every member of the
    group is one of the plain data's).
  sampled_of_decide: the same yes ⇒ OF hQ's TWELVE CLAUSES THE FRONT's TWO: each member's message
  is
    in the plain data's statement, is sampled, and has as many sample rows as its shape counts
    answers.
  fit_iff · fit_least: hfit is no mathematics: e < (e0 + 1) * 2 ^ k ⟺ e / 2 ^ k ≤ e0.
  seeds_of_hQ: «seeds»' first five conjuncts from hQ, at one member (sample_of_L, SampleLaw.lean).
  pow_ceil · pows_of_mem · pows_of_decide: sampleL's two clauses on the
  codes'
    message lengths (smp.powM | smp.powZ) FROM gpL's YES AND THE DECISION's: the code of a part with
    rows is the first stage's (memL's codeM | codeZ), whose length is 2 ^ the layout's logarithm
    (k12_lens). hQ_of_yes: THE SEAM's CORE's SECOND CLAUSE AT A MEMBER, TO THE LETTER: from «the
    member's message is sampled and its one sample row is Send.form's at a seed» · gpL's yes · the
    decision's yes · FOUR FACTS ON THE MEMBER's SHAPE ALONE (one answer · not both kinds of rows ·
    some rows · the case): NO CODE's CONTENT IS ASKED (Law/SampleOfSeed.lean's sampleL_of_seed).
  hQ_of_yes₂: the same at a member with rows of BOTH kinds, under okE of
  the
    seed's last coordinate (Law/SampleOfSeed.lean's sampleL_of_seed₂).
  hQ_of_yesA: one form for every member's shape with one answer, under
    «every coordinate of the seed's point is canonical».
A TWIN, NAMED: begun_same is begun_get (Johnson/Desc/K12/Coin/MemberShape.lean), its equations'
sides turned.
WHICH «ok»: four constants of one text stand in K12/Law (H2K.Pin.ok · H2K.First.ok · two more):
gpL's yes is H2K.First.ok (as NTuple holds it); memL's, siteL's and sampleL's are H2K.Pin.ok (as the
seam's core reads them). PURE OVER THE BASE BUT FOR TWO FILES OF OURS THAT ARE
(Law/SampleOfSeed.lean ·
Coin/ShapesAtSeat.lean).
NOT HERE, SO THAT NO TWIN GROWS: hJ · ht · hk · hh: K12/Coin/YesFacts.lean
has them. found_nine | found_ten (Coin/MembersFound.lean) have hfind
| hmembers at the two seats from a carried condition; found_of_decide has them from the yes alone.
WHAT IT IS NOT: hS (siteL's yes at every member) is not here (Coin/ShapesAtSeat.lean) · that the
sample row is Send.form's at a seed is a premise: the sending block's law's · the four facts on the
shape are premises · nothing on the table's side.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K12.Seat (block_front_holds)
open H2K.JointK (comb_of_ok combOk_of_decide k12_lens bat_front)
open H2K.First (Seat1 Plain made_of memL gpL)
open H2K.Pin (sampleL sample_of_L oracle_made mainB maskB mem_of_ok sampleL_of_seed
  sampleL_of_seed₂ sampleL_of_seedA)

section clauses
variable {St : Statement} {B : TreeBook} {g : Nat} {mask : Option Nat}

/-- Every member of the group under test is sampled. -/
theorem front_sampled (h : ∀ c ∈ frontL St B g mask, c.2 = true) {G : Group}
    (hG : St.groups[g]? = some G) :
    ∀ o ∈ G.members, ∀ y, St.oracles[o]? = some y → y.sampled = true := by
  have := h ("front: every member is sampled",
    on (St.groups[g]?) fun G => G.members.all fun o => on St.oracles[o]? fun y => y.sampled)
    (by simp [frontL])
  simp only [on, hG, Option.map_some, Option.getD_some, Array.all_eq_true_iff_forall_mem] at this
  intro o ho y hy
  have e := this o ho
  rw [hy] at e
  exact e

/-- Every member has as many sample rows as its shape counts answers. -/
theorem front_rows (h : ∀ c ∈ frontL St B g mask, c.2 = true) {G : Group}
    (hG : St.groups[g]? = some G) :
    ∀ o ∈ G.members, ∀ y, St.oracles[o]? = some y → y.sampleRows.size = y.shape.answers := by
  have := h ("front: as many sample rows as answers",
    on (St.groups[g]?) fun G => G.members.all fun o =>
      on St.oracles[o]? fun y => y.sampleRows.size == y.shape.answers)
    (by simp [frontL])
  simp only [on, hG, Option.map_some, Option.getD_some, Array.all_eq_true_iff_forall_mem] at this
  intro o ho y hy
  have e := this o ho
  rw [hy] at e
  simpa using e

end clauses

/-- The beginning of a test turns of a message neither the mark «sampled», nor the sample rows, nor
the shape. -/
theorem begun_same (S : Statement) (g : Nat) (G : Group) (o : Nat) (x' : OnBytes.Oracle)
    (h : (begun S g G).oracles[o]? = some x') :
    ∃ x, S.oracles[o]? = some x ∧ x.sampled = x'.sampled ∧ x.sampleRows = x'.sampleRows ∧
      x.shape = x'.shape := by
  have e : (begun S g G).oracles[o]? = (S.oracles[o]?).map fun x =>
      if o ∈ G.members.toList then shut x else x := closeLedgers_get _ _ _
  rw [e] at h
  obtain ⟨x, hx, h⟩ := Option.map_eq_some_iff.1 h
  refine ⟨x, hx, ?_⟩
  subst h
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- What both tops below spend: the layout's members are the group's, without a double, each below
the number of messages behind the beginning. -/
theorem members_of_decide (π : P12) (t tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE) (G0 : Group)
    (Ly : GroupLayout) (hG : t.st.groups[t.g]? = some G0) (hL : t.st.layout t.g = some Ly) :
    Ly.members = G0.members ∧ Ly.members.toList.Nodup ∧
      ∀ o ∈ Ly.members.toList, o < (begun t.st t.g G0).oracles.size := by
  have ht := comb_of_ok t (combOk_of_decide π t tE rs gs h) G0 Ly hG hL
  obtain ⟨G', hG', hL', hOk, _⟩ := combineAt_gives ht
  have hLm' : Ly.members = G'.members := by
    have e' := layout_eq (begun t.st t.g G0) t.g G' hG'
    have hL'' : (begun t.st t.g G0).layout t.g = some Ly := hL'
    rw [hL''] at e'
    rw [Option.some.inj e']
    rfl
  have hLm : Ly.members = G0.members := by
    have e' := layout_eq t.st t.g G0 hG
    rw [hL] at e'
    rw [Option.some.inj e']
    rfl
  exact ⟨hLm, by rw [hLm']; exact hOk.nodup, by rw [hLm']; exact hOk.there⟩

/-- **hfind and hmembers, from the decision's own yes alone.** -/
theorem found_of_decide (π : P12) (t tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) :
    (∀ j : Fin D.mems.length, D.L.find (D.mems.get j).id = some j.val) ∧
      ∀ o ∈ G0.members.toList, ∃ j : Fin D.mems.length, (D.mems.get j).id = o := by
  have hm := made_of π _ a Ly D (hf.2.2.2 default)
  obtain ⟨hLm, hnd, _⟩ := members_of_decide π t tE rs gs h G0 Ly hf.2.1 hf.2.2.1
  refine ⟨fun j => ?_, fun o ho => ?_⟩
  · rw [hm.lay]
    exact find_of_nodup hnd (hm.mem j).1
  · rw [← hLm] at ho
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem ho
    have hi' : i < D.mems.length := by
      rw [← hm.size]
      simpa using hi
    refine ⟨⟨i, hi'⟩, ?_⟩
    have e1 := (hm.mem ⟨i, hi'⟩).1
    have e2 : Ly.members[i]? = some o := by
      rw [← Array.getElem?_toList, List.getElem?_eq_getElem hi, e]
    exact Option.some.inj (e1.symm.trans e2)

/-- **Of hQ's twelve clauses, the front's two, from the decision's own yes alone.** -/
theorem sampled_of_decide (π : P12) (t tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) :
    ∀ j : Fin D.mems.length, ∃ x, D.st.oracles[(D.mems.get j).id]? = some x ∧
      x.sampled = true ∧ x.sampleRows.size = x.shape.answers := by
  intro j
  have hm := made_of π _ a Ly D (hf.2.2.2 default)
  obtain ⟨hLm, _, hth⟩ := members_of_decide π t tE rs gs h G0 Ly hf.2.1 hf.2.2.1
  obtain ⟨_, hfr, _⟩ := block_front_holds π t tE rs gs h
  have hmem : (D.mems.get j).id ∈ Ly.members.toList := by
    have := (hm.mem j).1
    rw [← Array.getElem?_toList] at this
    exact List.mem_of_getElem? this
  have hlt : (D.mems.get j).id < (begun t.st t.g G0).oracles.size := hth _ hmem
  have e1 : D.st.oracles[(D.mems.get j).id]? = (begun t.st t.g G0).oracles[(D.mems.get j).id]? :=
    oracle_made hm _ hlt
  obtain ⟨x0, hx0, s1, s2, s3⟩ := begun_same t.st t.g G0 _ _ (Array.getElem?_eq_getElem hlt)
  have hmem0 : (D.mems.get j).id ∈ G0.members := by
    rw [← hLm]
    exact Array.mem_def.2 hmem
  refine ⟨_, e1.trans (Array.getElem?_eq_getElem hlt), ?_, ?_⟩
  · rw [← s1]
    exact front_sampled hfr hf.2.1 _ hmem0 x0 hx0
  · rw [← s2, ← s3]
    exact front_rows hfr hf.2.1 _ hmem0 x0 hx0

/-- **hfit is no mathematics.** -/
theorem fit_iff (e e0 k : ℕ) : e < (e0 + 1) * 2 ^ k ↔ e / 2 ^ k ≤ e0 := by
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]

/-- The least radius that fits. -/
theorem fit_least (e k : ℕ) : e < (e / 2 ^ k + 1) * 2 ^ k := (fit_iff e _ k).2 (Nat.le_refl _)

/-- **The first five conjuncts of «seeds», from hQ, at one member.** -/
theorem seeds_of_hQ (K : Codes) (m : Seat1) (x : OnBytes.Oracle)
    (hq : ok (sampleL K m x) = true) :
    ∃ (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
      Send.form K m.sh m.id seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ K m.sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta := by
  obtain ⟨seed, row0, tt, β, h1, h2, h3, h4, _⟩ := sample_of_L hq
  exact ⟨seed, row0, tt, β, h1, h2, h3, h4⟩

/-! ## The codes' message lengths, and the core's second clause -/

theorem pow_ceil (k : ℕ) : 2 ^ ceilLog2 (2 ^ k) = 2 ^ k := by
  have h1 : ceilLog2 (2 ^ k) ≤ k := ceilLog2_le (Nat.le_refl _)
  have h2 : 2 ^ k ≤ 2 ^ ceilLog2 (2 ^ k) := le_of_ceilLog2 (Nat.le_refl _)
  have h3 : k ≤ ceilLog2 (2 ^ k) := (Nat.pow_le_pow_iff_right (by decide)).1 h2
  rw [Nat.le_antisymm h1 h3]

/-- The code of a part with rows is the stage's: so its message length is the stage's. -/
theorem pows_of_mem (K : Codes) (a : Fmt.M1.Stage) (L : GroupLayout) (w : Nat) (m : Seat1)
    (h : H2K.Pin.ok (memL K a L w m) = true) (kC kZ : ℕ) (hC : 2 ^ kC = a.C.l)
    (hZ : 2 ^ kZ = a.Z.l) :
    (m.sh.mainRows = 0 ∨ 2 ^ ceilLog2 (mainB K m.sh).ell = (mainB K m.sh).ell) ∧
      (m.sh.maskRows = 0 ∨ 2 ^ ceilLog2 (maskB K m.sh).ell = (maskB K m.sh).ell) := by
  simp only [memL, H2K.Pin.ok, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨_, _, _, h4, h5, _⟩ := h
  constructor
  · rcases h4 with h4 | h4
    · exact Or.inl h4
    · refine Or.inr ?_
      unfold H2K.First.codeB at h4
      have e := of_decide_eq_true h4
      have e' : (mainB K m.sh).ell = a.C.l := by
        unfold mainB
        rw [Array.getD_eq_getD_getElem?, e]
        rfl
      rw [e', ← hC]
      exact pow_ceil kC
  · rcases h5 with h5 | h5
    · exact Or.inl h5
    · refine Or.inr ?_
      unfold H2K.First.codeB at h5
      have e := of_decide_eq_true h5
      have e' : (maskB K m.sh).ell = a.Z.l := by
        unfold maskB
        rw [Array.getD_eq_getD_getElem?, e]
        rfl
      rw [e', ← hZ]
      exact pow_ceil kZ

/-- **smp.powM and smp.powZ, from gpL's yes and the decision's.** -/
theorem pows_of_decide (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (t tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (row : GroupRow)
    (hok : H2K.First.ok (gpL π a row D) = true) (j : Fin D.mems.length) :
    ((D.mems.get j).sh.mainRows = 0 ∨
        2 ^ ceilLog2 (mainB D.st.codes (D.mems.get j).sh).ell =
          (mainB D.st.codes (D.mems.get j).sh).ell) ∧
      ((D.mems.get j).sh.maskRows = 0 ∨
        2 ^ ceilLog2 (maskB D.st.codes (D.mems.get j).sh).ell =
          (maskB D.st.codes (D.mems.get j).sh).ell) := by
  obtain ⟨first, rest', e, r, row', L, S', e1, _, _, _, h3, h4⟩ := k12_lens π he t tE rs gs hp h
  obtain ⟨rfl, _⟩ := List.cons.inj (e1.symm.trans hf.1)
  exact pows_of_mem _ _ _ _ _ (mem_of_ok π first row D hok j) _ _ h3 h4

/-- **The seam's core's second clause at a member, to the letter**: no code's content is asked.
-/
theorem hQ_of_yes (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (t tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (row : GroupRow)
    (hok : H2K.First.ok (gpL π a row D) = true) (j : Fin D.mems.length)
    (hseed : ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
      D.st.oracles[(D.mems.get j).id]? = some x ∧ x.sampled = true ∧
      Send.form D.st.codes (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ D.st.codes (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta)
    (h1 : (D.mems.get j).sh.answers = 1)
    (hone : ¬ (0 < (D.mems.get j).sh.mainRows ∧ 0 < (D.mems.get j).sh.maskRows))
    (hsome : 0 < (D.mems.get j).sh.mainRows ∨ 0 < (D.mems.get j).sh.maskRows)
    (hcase : (0 < (D.mems.get j).sh.maskRows ∨ (D.mems.get j).sh.mainDeg = 3) ∨
      ((D.mems.get j).sh.maskRows = 0 ∧ (D.mems.get j).sh.mainDeg = 1)) :
    ∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧
      H2K.Pin.ok (sampleL D.st.codes (D.mems.get j) o) = true := by
  obtain ⟨x, seed, row0, tt, β, hx, s1, s2, s3, s4, s5⟩ := hseed
  obtain ⟨pM, pZ⟩ := pows_of_decide π he hp t tE rs gs h a rest G0 Ly D hf row hok j
  exact ⟨x, hx, sampleL_of_seed _ _ x seed row0 tt β s1 s2 s3 s4 s5 h1 hone hsome hcase pM pZ⟩

/-- **The same at a member with rows of BOTH kinds**: the seed's last coordinate that the
message's own cube uses is canonical (`okE`): one conjunct more under hseed; of the shape: one
answer and rows of both kinds. -/
theorem hQ_of_yes₂ (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (t tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (row : GroupRow)
    (hok : H2K.First.ok (gpL π a row D) = true) (j : Fin D.mems.length)
    (hseed : ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
      D.st.oracles[(D.mems.get j).id]? = some x ∧ x.sampled = true ∧
      Send.form D.st.codes (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ D.st.codes (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
      okE (seed.z.getD (bitsZ D.st.codes (D.mems.get j).sh - 1) zeroE) = true)
    (h1 : (D.mems.get j).sh.answers = 1)
    (hboth : 0 < (D.mems.get j).sh.mainRows ∧ 0 < (D.mems.get j).sh.maskRows) :
    ∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧
      H2K.Pin.ok (sampleL D.st.codes (D.mems.get j) o) = true := by
  obtain ⟨x, seed, row0, tt, β, hx, s1, s2, s3, s4, s5, s6⟩ := hseed
  obtain ⟨pM, pZ⟩ := pows_of_decide π he hp t tE rs gs h a rest G0 Ly D hf row hok j
  exact ⟨x, hx, sampleL_of_seed₂ _ _ x seed row0 tt β s1 s2 s3 s4 s5 h1 hboth s6
    (pM.resolve_left (by omega)) (pZ.resolve_left (by omega))⟩

/-- **One form for every member's shape with one answer**: under hseed one conjunct more: every
coordinate of the seed's point is canonical; of the shape: one answer, rows of some kind, the case.
-/
theorem hQ_of_yesA (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (t tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (row : GroupRow)
    (hok : H2K.First.ok (gpL π a row D) = true) (j : Fin D.mems.length)
    (hseed : ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
      D.st.oracles[(D.mems.get j).id]? = some x ∧ x.sampled = true ∧
      Send.form D.st.codes (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ D.st.codes (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
      ∀ c ∈ seed.z, okE c = true)
    (h1 : (D.mems.get j).sh.answers = 1)
    (hsome : 0 < (D.mems.get j).sh.mainRows ∨ 0 < (D.mems.get j).sh.maskRows)
    (hcase : (0 < (D.mems.get j).sh.maskRows ∨ (D.mems.get j).sh.mainDeg = 3) ∨
      ((D.mems.get j).sh.maskRows = 0 ∧ (D.mems.get j).sh.mainDeg = 1)) :
    ∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧
      H2K.Pin.ok (sampleL D.st.codes (D.mems.get j) o) = true := by
  obtain ⟨x, seed, row0, tt, β, hx, s1, s2, s3, s4, s5, s6⟩ := hseed
  obtain ⟨pM, pZ⟩ := pows_of_decide π he hp t tE rs gs h a rest G0 Ly D hf row hok j
  exact ⟨x, hx, sampleL_of_seedA _ _ x seed row0 tt β s1 s2 s3 s4 s5 s6 h1 hsome hcase pM pZ⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.found_of_decide
#print axioms VerifiableInference.Desc.K12.Coin.sampled_of_decide
#print axioms VerifiableInference.Desc.K12.Coin.fit_iff
#print axioms VerifiableInference.Desc.K12.Coin.seeds_of_hQ
#print axioms VerifiableInference.Desc.K12.Coin.front_sampled
#print axioms VerifiableInference.Desc.K12.Coin.front_rows
#print axioms VerifiableInference.Desc.K12.Coin.begun_same
#print axioms VerifiableInference.Desc.K12.Coin.members_of_decide
#print axioms VerifiableInference.Desc.K12.Coin.fit_least
#print axioms VerifiableInference.Desc.K12.Coin.pow_ceil
#print axioms VerifiableInference.Desc.K12.Coin.pows_of_mem
#print axioms VerifiableInference.Desc.K12.Coin.pows_of_decide
#print axioms VerifiableInference.Desc.K12.Coin.hQ_of_yes
#print axioms VerifiableInference.Desc.K12.Coin.hQ_of_yes₂
#print axioms VerifiableInference.Desc.K12.Coin.hQ_of_yesA
