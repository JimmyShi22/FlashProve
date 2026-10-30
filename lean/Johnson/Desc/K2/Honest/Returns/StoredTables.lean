-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/StoredTables.lean: THE THIRD CLAUSE ON THE KEPT MEMBERS' STORED
SAMPLE ROWS, `TablesFit.stored` (Returns/BehindAt.lean), FOLLOWS FROM FOUR OTHER CLAUSES OF THE SAME
LAW WHEREVER EACH STORED SAMPLE ROW IS A ROW OF THE PROGRAM's OWN MAKER AT A SEED OF FULL LENGTH
(`SampleGoodS`, Johnson/Top/H/SwitchSeedFits.lean): SO, IN THE GOALS' SCOPE, AT EVERY STATE REACHED
IN FRONT OF THE SWITCH INTO A LATER GROUP. With Returns/StoredReached.lean: there, each of the three
clauses on these rows follows from other clauses of the law; `LinkPlain` still names all three. At
the head's and the finish's switch: Returns/StoredArms.lean. Statements with their proofs: calls,
one recursion, three unfoldings.

  `padFold_index` each single entry that the loop over a pad's places adds lies at a place's index
  `form_units` so each single entry of a row of `Send.form` lies at the index of a place of the pad
  `tableBits_main` a main table's index bits, where the message has a main row: the bits of its rows
                    and the bits of its code's message length
  `stored_is_formS` `stored_is_form` (Returns/StoredReached.lean) with: the seed's point has a
                    coordinate for each variable of the message's cube
  `stored_tables` the clause at one message that has no mask row, has a main row, and whose main
                    table has at most 63 index bits
  `keptOld_rows` where the test on the target says yes and each copy has a main row, each kept old
                    message has one
  `keptOld_bits` the bound 63, from `TablesFit.bitsKept` and `OldFits.keptCode`
  `tables_stored` `TablesFit.stored`, in its own letters, from `FrontCore.check` · `keptPos` ·
                    `OldFits.keptCode` · `TablesFit.bitsKept`, each in its own letters
  `link_goodS_reached` at a state reached in front of the switch into group m + 1, m < 23, the
                    front's statement has `SampleGoodS`; `link_good_reached`
                    (Returns/StoredReached.lean) is its weaker half
  `link_tables_reached` `TablesFit.stored` there, from these four

By, all the library's: `form_eq`, `form_parts`, `vars_sendTensor` (OnBytes/Slice/BlkSend.lean) ·
`plainRow_form` (OnBytes/Slice/BlkPlain.lean) · `pad_index_lt_pow` (Johnson/Top/H/SwitchPadsAt.lean)
· `targetOk_eq`, `targetOk_means` (Johnson/Top/H0/Tw/K2/) · `sw_link`
(Johnson/P1K2R/HstReached.lean). Near relatives, not called: `tableBits_of_shape`
(Johnson/Top/H/SwitchTie.lean): `tableBits_main` at either table, in the letters of another reading
of the codes · `fold_unit_keeps` (Johnson/Top/H0/K2Hands/FormOnReads.lean) and `fold_parts`
(Johnson/Desc/K1/Law/SaysTie.lean): `padFold_index` with the entry's message and table, the second
with its index too, over another writing of the loop · `check_kept` (Johnson/Top/H/SwitchFront.lean)
and `check_facts` (Johnson/Top/H/SwitchMapsCheck.lean): what `keptOld_rows` reads of the test, by
index · `keptOld_of` (Johnson/Top/H0/K2Hands/AtYes.lean): from the like two premises, that each kept
old number names a message; its proof passes through `keptOld_rows`' end · `both_at_front`
(Johnson/Top/H0/Tw/K2C/DebtsState.lean): `SampleGoodS` at the library's own front, where
`link_goodS_reached` speaks of this folder's `frontAt`. And this folder's own `inOrder_plain`
(Returns/FormFit.lean): it would serve the last step of `stored_tables`, which spells that step out.

Limits. OF THE FOUR CLAUSES THAT ARE SPENT, `keptPos` ALONE IS PAID AT A REACHED STATE WITH NO
FURTHER PREMISE (`link_fields_reached`, Returns/LinkReached.lean, at the frame's own link and
group). "Reached" is: over the list of the wrapped sub-protocols. THE FIVE PREMISES IN FRONT ARE
SHOWN MET TOGETHER BY NOBODY HERE: NO MEMBER. This file's imports are heavy. Nothing on any
property.


-/
import Johnson.Desc.K2.Honest.Returns.StoredReached
import Johnson.Top.H.SwitchPadsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Slice (padStep form_eq form_parts plainRow_form vars_sendTensor cube_hasMain_eq
  cube_hasMask_eq)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (SampleGoodS)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.Top.H (pad_index_lt_pow)
open P1K2 (Prep Nums numsAt prepOf sw_link)
open _root_.Tw.K2 (targetOk_eq targetOk_means)
open ProofFile (Cl)

theorem padFold_index (codes : Codes) (s : OracleShape) (o : Nat) (seed : SampleSeed) (a : Nat) :
    ∀ (places : List PadPlace) (r : OnBytes.Row),
      ∀ u ∈ (places.foldl (padStep codes s o seed a) r).units.toList,
        u ∈ r.units.toList ∨ ∃ p ∈ places, u.index = p.index
  | [], _ => fun _ hu => Or.inl hu
  | p :: places, r => fun u hu => by
    rcases padFold_index codes s o seed a places (padStep codes s o seed a r p) u hu with
      h | ⟨q, hq, e⟩
    · simp only [padStep, OnBytes.Row.addUnit, Array.toList_push, List.mem_append,
        List.mem_singleton] at h
      rcases h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨p, List.mem_cons_self, rfl⟩
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, e⟩

theorem form_units {codes : Codes} {s : OracleShape} {o : Nat} {seed : SampleSeed} {a : Nat}
    {row : OnBytes.Row} (h : Send.form codes s o seed a = some row) :
    ∀ u ∈ row.units.toList, ∃ p ∈ padPlaces codes s, u.index = p.index := by
  rw [form_eq] at h
  obtain ⟨places, hp, hrow⟩ := Option.map_eq_some_iff.1 h
  have e : padPlaces codes s = places := by
    unfold padPlaces
    rw [hp]
    rfl
  intro u hu
  have hu' : u ∈ (places.foldl (padStep codes s o seed a) { kind := .sample }).units.toList := by
    rw [← hrow] at hu
    cases hm : (Send.cube codes s).hasMain <;> cases hk : (Send.cube codes s).hasMask <;>
      simpa [hm, hk, OnBytes.Row.add] using hu
  rcases padFold_index codes s o seed a places _ u hu' with h0 | ⟨p, hp', e'⟩
  · simp at h0
  · exact ⟨p, by rw [e]; exact hp', e'⟩

theorem tableBits_main {St : Statement} {o : Nat}
    (hp : 0 < (St.oracles.getD o default).shape.mainRows) :
    St.tableBits o .main = ceilLog2 (St.oracles.getD o default).shape.mainRows +
      (St.codes.base.getD (St.oracles.getD o default).shape.code default).logEll := by
  cases hx : St.oracles[o]? with
  | none =>
    have e : St.oracles.getD o default = default := by
      rw [Array.getD_eq_getD_getElem?, hx]
      rfl
    rw [e] at hp
    exact absurd hp (Nat.lt_irrefl 0)
  | some x =>
    have e : St.oracles.getD o default = x := by
      rw [Array.getD_eq_getD_getElem?, hx]
      rfl
    rw [e] at hp ⊢
    have hb : (x.shape.rows .main == 0) = false := beq_false_of_ne (Nat.pos_iff_ne_zero.1 hp)
    unfold Statement.tableBits Statement.rowBits Statement.placeBits
    rw [hx]
    simp only [hb]
    rfl

theorem stored_is_formS {St : Statement} (h : SampleGoodS St) {o : Nat} {x : OnBytes.Oracle}
    (hx : St.oracles[o]? = some x) {r : OnBytes.Row} (hr : r ∈ x.sampleRows.toList) :
    ∃ (seed : SampleSeed) (row : OnBytes.Row) (y : OnBytes.E) (i : Nat),
      Send.form St.codes x.shape o seed i = some row ∧ r = { row with target := y } ∧
        (Send.cube St.codes x.shape).bits ≤ seed.z.length := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hi' : i < x.sampleRows.size := by simpa using hi
  obtain ⟨seeds, ⟨hsz, hall⟩, hs⟩ := h o x hx (by omega)
  obtain ⟨seed, row, y, hsd, hf, hrow⟩ := hall i (by omega)
  refine ⟨seed, row, y, i, hf, ?_, (hs seed (List.mem_of_getElem? hsd)).1⟩
  rw [Array.getElem?_eq_getElem hi'] at hrow
  simpa using Option.some.inj hrow

/-- **The clause at one message.** -/
theorem stored_tables {St : Statement} (h : SampleGoodS St) {o : Nat}
    (hm : (St.oracles.getD o default).shape.maskRows = 0)
    (hp : 0 < (St.oracles.getD o default).shape.mainRows) (h63 : St.tableBits o .main ≤ 63) :
    ∀ r ∈ (St.oracles.getD o default).sampleRows.toList,
      (∀ t ∈ r.terms.toList, t.v.pairs.length = St.tableBits o .main ∧ Own.InOrder t.v) ∧
        ∀ u ∈ r.units.toList, u.index < 2 ^ St.tableBits o .main := by
  intro r hr
  have hb := tableBits_main hp
  cases hx : St.oracles[o]? with
  | none =>
    have e : St.oracles.getD o default = default := by
      rw [Array.getD_eq_getD_getElem?, hx]
      rfl
    rw [e] at hr
    exact absurd hr List.not_mem_nil
  | some x =>
    have e : St.oracles.getD o default = x := by
      rw [Array.getD_eq_getD_getElem?, hx]
      rfl
    rw [e] at hr hm hp hb
    obtain ⟨seed, row, y, i, hf, rfl, hz⟩ := stored_is_formS h hx hr
    have hM : (Send.cube St.codes x.shape).hasMain = true := by
      rw [cube_hasMain_eq]
      exact decide_eq_true hp
    have hK : ¬ (Send.cube St.codes x.shape).hasMask = true := by
      rw [cube_hasMask_eq, hm]
      simp
    have hc : (Send.cube St.codes x.shape).mainBits =
        ceilLog2 x.shape.mainRows + (St.codes.base.getD x.shape.code default).logEll := by
      simp [Send.cube, hp]
    obtain ⟨ht, -, -⟩ := form_parts _ _ _ _ _ _ hf
    rw [if_pos hM, if_neg hK, List.append_nil] at ht
    refine ⟨fun t hmem => ?_, fun u hu => ?_⟩
    · have hmem' : t ∈ row.terms.toList := hmem
      have hd := (plainRow_form _ _ _ _ _ _ hf).1 t hmem'
      rw [ht, List.mem_singleton] at hmem'
      have hl : t.v.pairs.length = St.tableBits o .main := by
        rw [hmem', hb, ← hc]
        exact vars_sendTensor St.codes x.shape seed.z .main hz
      refine ⟨hl, ?_⟩
      unfold Own.InOrder
      rw [hd, hl]
      exact ⟨h63, Or.inl rfl, fun d hd' => absurd hd' List.not_mem_nil, List.nodup_nil⟩
    · obtain ⟨p, hp', e'⟩ := form_units hf u hu
      rw [e', hb]
      exact pad_index_lt_pow St.codes x.shape hm hp p hp'

/-- Where the test on the target says yes and each copy has a main row, each kept old message has
one. -/
theorem keptOld_rows {St : Statement} {old : SingleRows} {T : SwitchTarget}
    (hc : switchTargetCheck St old T = true) (hp : ∀ k ∈ T.kept.toList, 0 < k.shape.mainRows) :
    ∀ o ∈ (switchKept old).toList, 0 < (St.oracles.getD o default).shape.mainRows := by
  have TF := (targetOk_means St old T).1 (by rw [targetOk_eq]; exact hc)
  intro o ho
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem ho
  have ha' : a < (switchKept old).size := by simpa using ha
  have hk : a < T.kept.size := by
    rw [TF.keptCount]
    exact ha'
  have hmem : ((switchKept old)[a], T.kept[a]) ∈ (switchKept old).zip T.kept :=
    Array.mem_iff_getElem.2 ⟨a, by simp only [Array.size_zip]; omega, by simp⟩
  have h1 : T.kept[a].shape.mainRows =
      (St.oracles.getD (switchKept old)[a] default).shape.mainRows := (TF.keptShapes _ hmem).rows
  have h2 : 0 < T.kept[a].shape.mainRows := hp _ (by simp)
  rw [h1] at h2
  simpa using h2

theorem keptOld_bits {St : Statement} {old : SingleRows} {T : SwitchTarget}
    (hp : ∀ o ∈ (switchKept old).toList, 0 < (St.oracles.getD o default).shape.mainRows)
    (hcode : ∀ o ∈ (switchKept old).toList, (St.oracles.getD o default).shape.code = old.code)
    (hb : ∀ s ∈ (sizesAt St old T).kept,
      ceilLog2 s.mainRows + (St.codes.base.getD old.code default).logEll ≤ 63) :
    ∀ o ∈ (switchKept old).toList, St.tableBits o .main ≤ 63 := by
  intro o ho
  have hmem : (St.oracles.getD o default).shape ∈ (sizesAt St old T).kept := by
    show _ ∈ (switchKept old).toList.map _
    exact List.mem_map.2 ⟨o, ho, rfl⟩
  rw [tableBits_main (hp o ho), hcode o ho]
  exact hb _ hmem

/-- **`TablesFit.stored`, from four other clauses.** -/
theorem tables_stored {St : Statement} (h : SampleGoodS St) {old : SingleRows} {T : SwitchTarget}
    (hc : switchTargetCheck St old T = true) (hp : ∀ k ∈ T.kept.toList, 0 < k.shape.mainRows)
    (hcode : ∀ o ∈ (switchKept old).toList, (St.oracles.getD o default).shape.code = old.code)
    (hb : ∀ s ∈ (sizesAt St old T).kept,
      ceilLog2 s.mainRows + (St.codes.base.getD old.code default).logEll ≤ 63) :
    ∀ o ∈ (switchKept old).toList, ∀ r ∈ (St.oracles.getD o default).sampleRows.toList,
      (∀ t ∈ r.terms.toList, t.v.pairs.length = St.tableBits o .main ∧ Own.InOrder t.v) ∧
        ∀ u ∈ r.units.toList, u.index < 2 ^ St.tableBits o .main :=
  fun o ho => stored_tables h (keptOld_bare hc o ho) (keptOld_rows hc hp o ho)
    (keptOld_bits (keptOld_rows hc hp) hcode hb o ho)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

theorem link_goodS_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) : SampleGoodS (frontAt s L Q).st :=
  fun o x hx hs => (sw_link hS hR O hF hpl h23 hP hn hr).1.good o x hx hs

/-- **`TablesFit.stored` at a reached state, from four other clauses.** -/
theorem link_tables_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup)
    (check : switchTargetCheck (frontAt s L Q).st (frontAt s L Q).f.rows (frontAt s L Q).T = true)
    (keptPos : ∀ k ∈ (frontAt s L Q).T.kept.toList, 0 < k.shape.mainRows)
    (keptCode : ∀ o ∈ (switchKept (frontAt s L Q).f.rows).toList,
      ((frontAt s L Q).st.oracles.getD o default).shape.code = (frontAt s L Q).f.rows.code)
    (bitsKept : ∀ t ∈ (sizesAt (frontAt s L Q).st (frontAt s L Q).f.rows (frontAt s L Q).T).kept,
      ceilLog2 t.mainRows +
        ((frontAt s L Q).st.codes.base.getD (frontAt s L Q).f.rows.code default).logEll ≤ 63) :
    ∀ o ∈ (switchKept (frontAt s L Q).f.rows).toList,
      ∀ r ∈ ((frontAt s L Q).st.oracles.getD o default).sampleRows.toList,
        (∀ t ∈ r.terms.toList,
          t.v.pairs.length = (frontAt s L Q).st.tableBits o .main ∧ Own.InOrder t.v) ∧
          ∀ u ∈ r.units.toList, u.index < 2 ^ (frontAt s L Q).st.tableBits o .main :=
  tables_stored (link_goodS_reached hS hR O hF hpl h23 hP hn hr L Q) check keptPos keptCode bitsKept

end

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.padFold_index
#print axioms VerifiableInference.Desc.K2.Honest.Returns.form_units
#print axioms VerifiableInference.Desc.K2.Honest.Returns.tableBits_main
#print axioms VerifiableInference.Desc.K2.Honest.Returns.stored_is_formS
#print axioms VerifiableInference.Desc.K2.Honest.Returns.stored_tables
#print axioms VerifiableInference.Desc.K2.Honest.Returns.keptOld_rows
#print axioms VerifiableInference.Desc.K2.Honest.Returns.keptOld_bits
#print axioms VerifiableInference.Desc.K2.Honest.Returns.tables_stored
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_goodS_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_tables_reached
