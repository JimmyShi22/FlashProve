-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyMemberAtSeat.lean: at the full size: ONE STATEMENT INSIDE THE PROMISE OF THE KEY FILE's SECOND BORDER (On₁' … 1: row 1.1's guard), IN SCOPE, AT THE SEAT's OWN DESCRIPTION AND AT THE WRITTEN LETTERS OF The21AtName, FROM ONE BOOL ON A VIEW. A JOINING OF THEOREMS FROM OTHER FILES: every public premise of `on₁'_of_yes` (KeyFillYes.lean) is CALLED.
Main names.
  `first_blocksOk` · `send10_planOk` · `plan10`: the first block's own test on the plan, out of the description's.
  `public10_in_scope`: the three public premises on the first sending [two by the kernel at the written key].
  `cond10_in_scope`: the sending kind's one Boolean at the radius 6130.
  `yOf_cell'`: what is read off ANY strings of the first frame is their stored table.
  `member_yes_written`: THE THEOREM: in scope, under the description's three tests, «its data are D» and «D is the written data»: for every typed record r, every two rounds and columns, AT THE VERY (a, n) THAT the first held block's step at (keyInstanceOfOutOfDomainSample r, the start) RETURNS, and every stored table of code words: ∃ y', On₁' X N P ‹the data› (baseAt X decN recBack) atSix (readAt tab) collN 1 (a, y'): over `on₁'_of_yes` (KeyFillYes.lean) · `member_at_written`: its corollary from ONE BOOL (the step's isOk), for a ride.
  `member_yes_key`: the same at an instance x that a file holds · `member_yes_honest`: and at the table that the format's encoder makes, whatever its messages and tails (`tab_honestTab`): no premise on the stored side is left.
  `member_at_zero`: the same with the stored table chosen: the zero message's code words (`zero_words`): no premise on the stored side is left: the FORM is not empty.
  `keyOkB` · `keyOkB_of_four` (from the four terms as a file of evaluations rides them) · `x_is_instK` · `member_at_key`: the same at an instance x that a file holds: where its key fits the shape and passes four tests with code, x IS a typed record's instance (`keyOf_recOfKey`, called): so a ride of the Bool at a stored key pays the theorem's premise.
WHO PAYS WHAT: the start and the two lookups: `hl_in_scope` · `id_full` · the key fits: `fits_in_scope` (KeyPublicAtSeat.lean) · the two ties and the first two seats: `five_in_scope` · `codes_full` · `idx_shape_full` · `n01_scope` · the third seat: `n2_scope` with `rounds_in_scope` · the frame's three depths: `holds0` | `holds1` | `holds5` · the record: `recBack_instK` · no collision: `notColl_words` (`not_coll_words`).
OBJECT: `Key.descriptionFromSource X N P` in scope; `On₁'` (KeyTablesR.lean) · USER: KeyASideAll.lean (public10_in_scope), RowScope.lean (lengths_full) · LETTERS: tab.
Limits. IN FRONT OF THE CONCLUSION STAND, BESIDE SCOPE AND THE SEAT's OWN FACTS: (1) THE ONE BOOL; (2) «the description's data are the written data» (a theorem in other files over the key file's door with its second test: not in the build on which this file was written); (3) «the stored table is a table of code words». The state a is the first block's own; the oracles y' are fitted code words, built by the filling, not a run's. AT THE SECOND BORDER ALONE. A member of a promise makes no law count. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyNoCollAtWords
import Johnson.Top.Fire.Code.KeyRoundsAtSeat
import Johnson.Top.Fire.Code.KeyFillYesOne
import Johnson.RunOne.KeySendGood
import Johnson.RunOne.KeySeatScopeW2
import OnBytes.Slice.Honest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open scoped ENNReal
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)
open Johnson.RunOne.KeyRows1 (RecStays SendYes₀ sendYes₀ Public10)
open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece Sealed shapeAt shapesOf sampledAt errPort seedMaps seedEntry cond_parts)
open Johnson.Pack (portOmZ)
open VerifiableInference.Desc.Key.Fill (six)
open Johnson.RunOne.KeyRows23 (baseK kreadFam numSix atSix holdsB)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ n₁ slots₁ ties₁ tiesA shape₁' Sent0 sent0_of front0 shape_send0 pinned_behind0 roundsFit_noDigest')
open Johnson.Pack (aOf)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Johnson.G (writtenKFull)
open VerifiableInference.Desc.K1 (planOkOwn)
open Johnson.RunOne.KeyRows1 (start_shape start_order)

/-- The first chain's blocks pass their own tests on the plan. -/
theorem first_blocksOk (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hp : (Fk X N P).planOk = true) : blocksOk (Fk X N P).first.blocksInOrder = true := by
  have h := hp
  simp only [FileDescription.planOk, FileDescription.planOkCore, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.2

theorem send10_planOk (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hp : (Fk X N P).planOk = true) : (send10 X).planOk = true := by
  have hb := first_blocksOk X N P hp
  rw [q₁] at hb
  have h2 := List.all_eq_true.1 hb c₁ List.mem_cons_self
  have h3 : c₁.planOk = true := (Bool.and_eq_true_iff.1 h2).1
  rw [first_is X N P c₁ k₁ q₁] at h3
  exact (Bool.and_eq_true_iff.1 h3).1

theorem plan10 (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hp : (Fk X N P).planOk = true) : planOkOwn (par10 X) = true :=
  Johnson.RunOne.KeySendGood.planOwn_idxAt (oneAt X) pieces _ (send10_planOk X N P c₁ k₁ q₁ hp)

theorem sampled_full : keyFull.once.input.shape.answers ≠ 0 := by decide +kernel

theorem lay_full : ((layTrees keyFull.codes #[keyFull.once.input]).all fun lay => lay.shapes.size == 1 && lay.tree.getD 0 0 == 0 && lay.part.getD 0 0 == 0) = true := by
  decide +kernel

/-- The layout is made: so `lay_full` is no empty truth. -/
theorem lay_made : (layTrees keyFull.codes #[keyFull.once.input]).isSome = true := by decide +kernel

theorem lengths_full : Johnson.Top.H.csKey.lengthsOk = true := by decide +kernel

theorem meets_idx : Johnson.Pack.meetsB Johnson.Top.H.csKey Johnson.Top.H.shIdx 6130 = true := by decide +kernel

/-- What is read off ANY strings of the first frame is their stored table. -/
theorem yOf_cell' (D : WholeD) (y₀ : (fr₁ (D.at frS.P.T.a)).E.Str) : yOf (strsOf (fr₁ (D.at frS.P.T.a)) y₀).cell = y₀.1 := by
  funext p
  show ((cellAt (fr₁ (D.at frS.P.T.a)) y₀ p.val).getD (0, [])) = y₀.1 p
  unfold cellAt
  rw [dif_pos p.isLt]
  rfl

/-- A key with these sizes and words is the key written of a typed record, at any three numbers that are the shape's. -/
theorem rec_of_key (sh : OnBytes.Params.IndexShape) (key : OnBytes.TableKey) (hf : key.fits sh = true)
    (hz : (key.seeds.all fun x => !OnBytes.isZeroE x.beta) = true) (hr : ∀ a ∈ key.record, okE a = true)
    (hs : ∀ x ∈ key.seeds, okE x.beta = true ∧ ∀ a ∈ x.z, okE a = true) :
    ∀ (v lg s : ℕ), sh.v = v → sh.cubeBits = lg → sh.answers = s →
      ∃ r : RecP NZ v lg s, key = { keyOf (fun β : NZ => β.val) r with item := key.item } := by
  intro v lg s hv hc ha
  subst hv hc ha
  exact ⟨recOfKey sh key, keyOf_recOfKey sh key hf hz hr hs⟩

/-- **Four tests on a key, with code**: its item is 0; no seed's factor is the program's 0; every word of its record, of its seeds' factors and of their points is below the prime. -/
def keyOkB (k : OnBytes.TableKey) : Bool :=
  k.item == 0 && (k.seeds.all fun x => !OnBytes.isZeroE x.beta) && k.record.toList.all okE && k.seeds.all fun x => okE x.beta && x.z.all okE

/-- **The four tests as a file of evaluations rides them, term by term, give `keyOkB`**: the second there stands in the array's own form. -/
theorem keyOkB_of_four (k : OnBytes.TableKey) (K1 : (k.seeds.all fun s => !OnBytes.isZeroE s.beta) = true) (K2 : k.record.all okE = true)
    (K3 : (k.seeds.all fun s => okE s.beta && s.z.all okE) = true) (K4 : k.item = 0) : keyOkB k = true := by
  have K2' : k.record.toList.all okE = true := by
    rw [Array.all_toList]
    exact K2
  unfold keyOkB
  rw [K4, K1, K2', K3]
  rfl

/-- The table whose every symbol holds no word is the table of the zero message's code words. -/
theorem zero_words : ∀ (a : DN.ix.Row) (x : DN.toDec.Pos), DN.tab (fun _ => ((0 : ℕ), ([] : List UInt64))) a x = DN.ix.G.mulVec ((fun _ _ => 0 : DN.ix.Row → DN.toDec.Co → GE) a) x := by
  intro a x
  have e : DN.ix.G.mulVec ((fun _ _ => 0 : DN.ix.Row → DN.toDec.Co → GE) a) = 0 := Matrix.mulVec_zero _
  rw [e]
  show algebraMap GF GE (toF (([] : List UInt64).getD _ 0)) = 0
  simp [toF]

section
variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
variable {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol X₀) {cfg : ByteArray}
  {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
include hZ hP hm hX hp q₁

/-- **The three public premises on the first sending.** -/
theorem public10_in_scope : Public10 (oneAt X) pieces (groupsTold X.Y.told.1 0 (rootsAt X.Y.D.1 0)) := by
  obtain ⟨-, -, -, hi, hc⟩ := five_in_scope hZ hP hm hX hp
  refine ⟨plan10 X N P c₁ k₁ q₁ hp, ?_, ?_⟩
  · show (oneAt X).indexMasks.shape.answers ≠ 0
    rw [show (oneAt X).indexMasks = keyFull.once.input from hi]
    exact sampled_full
  · intro lay hl
    rw [show (oneAt X).codes = keyFull.codes from hc, show (oneAt X).indexMasks = keyFull.once.input from hi] at hl
    have h := lay_full
    rw [hl] at h
    simpa [and_assoc] using h

/-- **The sending kind's one Boolean at the radius 6130.** -/
theorem cond10_in_scope : condPort (par10 X) (fun _ => 6130) = true := by
  obtain ⟨-, -, -, hi, hc⟩ := five_in_scope hZ hP hm hX hp
  have tC : (par10 X).codes = Johnson.Top.H.csKey := (par10_codes X).trans (hc.trans Johnson.RunOne.KeyLetters.codes_full)
  refine Johnson.RunOne.KeySendGood.cond_of (par10 X) _ (plan10 X N P c₁ k₁ q₁ hp) (by rw [tC]; exact lengths_full) fun k _ => ?_
  have hk : shapeAt (par10 X) k = Johnson.Top.H.shIdx := by
    obtain ⟨k, hk⟩ := k
    have h0 : k = 0 := by
      have : k < 1 := hk
      omega
    subst h0
    show (oneAt X).indexMasks.shape = _
    rw [show (oneAt X).indexMasks = keyFull.once.input from hi]
    exact Johnson.RunOne.KeyLetters.idx_shape_full
  rw [tC, hk]
  exact meets_idx

omit q₁ in
/-- **An instance whose key fits and passes the four tests IS a typed record's**: `keyOf_recOfKey`, called. -/
theorem x_is_instK (x : Xi) (hf : x.key.fits (oneAt X).lin.fold.index = true) (hB : keyOkB x.key = true) :
    ∃ r : RecFull, VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r = x := by
  rw [(one_full hZ hP hm hX hp).2.1] at hf
  simp only [keyOkB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hB
  obtain ⟨⟨⟨h0, hz⟩, hr⟩, hs⟩ := hB
  obtain ⟨r, e⟩ := rec_of_key _ x.key hf (List.all_eq_true.2 hz) (fun a ha => hr a (Array.mem_def.1 ha)) hs
    frS.P.v 29 1 index_full.1 index_full.2.2 index_full.2.1
  rw [h0] at e
  refine ⟨r, ?_⟩
  cases x with
  | mk k => exact congrArg _ e.symm

/-- **ONE STATEMENT INSIDE On₁' 1, IN SCOPE, AT THE WRITTEN LETTERS, AT THE VERY STATE THAT THE FIRST HELD BLOCK's STEP RETURNS.** D: the record's data; they stand at the frame's depth, as at the seat. -/
theorem member_yes_written (hw : (Fk X N P).wantedOk = true) (D : WholeD) (hD : (Fk X N P).data "key file" = .ok (D.at frS.P.T.a))
    (hpin : D.at frS.P.T.a = writtenKFull)
    (tab : MsgN → ℕ → ℕ → OnBytes.F) (r : RecFull) (r₁ r₂ : _root_.Fmt.RoundView) (cols : List OpenedColumn)
    (a : Xi × FirstState) (n : ℕ)
    (hstep : (held c₁ : Block (Xi × FirstState) Claim).step 0 ((VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r), (Fk X N P).start₁ (VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r)) [r₁, r₂] cols = .ok (a, n))
    (y₀ : (fr₁ (D.at frS.P.T.a)).E.Str) (M : DN.ix.Row → DN.toDec.Co → GE) (hf : ∀ a x, DN.tab y₀.1 a x = DN.ix.G.mulVec (M a) x) :
    ∃ y' : (fr₁ (D.at frS.P.T.a)).E.Str, y'.1 = y₀.1 ∧ On₁' X N P (D.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN 1 (a, y') := by
  obtain ⟨-, hr, hl, hi, hc⟩ := five_in_scope hZ hP hm hX hp
  obtain ⟨x₀, x₁, h2⟩ := hl_in_scope hZ hP hm hX hp
  have tC : (oneAt X).codes = Johnson.Top.H.csKey := hc.trans Johnson.RunOne.KeyLetters.codes_full
  obtain ⟨n0, n1⟩ := Johnson.RunOne.KeyLetters.n01_scope X N P hi hc hr "" ""
  have hD' : (Fk X N P).data "key file" = .ok writtenKFull := by rw [hD, hpin]
  have f0 : holdsB (fr₁ (D.at frS.P.T.a)) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true := by
    rw [hpin]
    unfold holdsB
    exact Johnson.RunOne.KeyLetters.holds0
  have f1 : holdsB (fr₁ (D.at frS.P.T.a)) 1 (aOf Johnson.Top.H.csKey Johnson.Top.H.shMul) = true := by
    rw [hpin]
    unfold holdsB
    exact Johnson.RunOne.KeyLetters.holds1
  have f2 : holdsB (fr₁ (D.at frS.P.T.a)) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true := by
    rw [hpin]
    unfold holdsB
    exact Johnson.RunOne.KeyLetters.holds5
  have Pb := public10_in_scope hZ hP hm hX hp c₁ k₁ q₁
  haveI : Inhabited MsgN := ⟨fun _ => 0⟩
  exact on₁'_of_yes X N P (D.at frS.P.T.a) c₁ k₁ decN recBack tab collN q₁ Pb (fun _ => 6130)
    (cond10_in_scope hZ hP hm hX hp c₁ k₁ q₁) (VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r)
    (start_shape (oneAt X) (by rw [h2]; rfl) (by rw [show (oneAt X).ranges = keyFull.ranges.x from hr]; exact id_full)) (start_order _)
    (fits_in_scope hZ hP hm hX hp r) a r₁ r₂ cols n hstep ⟨0, Nat.zero_lt_one⟩ Pb.sampled rfl ((par10_codes X).trans tC)
    (by
      show (oneAt X).indexMasks.shape = _
      rw [show (oneAt X).indexMasks = keyFull.once.input from hi]
      exact Johnson.RunOne.KeyLetters.idx_shape_full)
    "" "" "" n0 n1
    (Johnson.RunOne.KeyLetters.n2_scope X N P tC hl hp hD' (rounds_in_scope hZ hP hm hX hp hw).1 "")
    f0 f1 f2 y₀ r (recBack_instK r) (fun y y' r h => (cellOnly_collN y y' r h).1)
    (by
      unfold collN
      rw [yOf_cell']
      exact notColl_words y₀.1 M hf r.1)

/-- **The same from ONE BOOL ON A VIEW**: the step's yes: its corollary, for a ride. -/
theorem member_at_written (hw : (Fk X N P).wantedOk = true) (D : WholeD) (hD : (Fk X N P).data "key file" = .ok (D.at frS.P.T.a))
    (hpin : D.at frS.P.T.a = writtenKFull)
    (tab : MsgN → ℕ → ℕ → OnBytes.F) (r : RecFull) (r₁ r₂ : _root_.Fmt.RoundView) (cols : List OpenedColumn)
    (hok : ((held c₁ : Block (Xi × FirstState) Claim).step 0 ((VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r), (Fk X N P).start₁ (VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r)) [r₁, r₂] cols).isOk = true)
    (y₀ : (fr₁ (D.at frS.P.T.a)).E.Str) (M : DN.ix.Row → DN.toDec.Co → GE) (hf : ∀ a x, DN.tab y₀.1 a x = DN.ix.G.mulVec (M a) x) :
    ∃ (a : Xi × FirstState) (y' : (fr₁ (D.at frS.P.T.a)).E.Str), y'.1 = y₀.1 ∧ On₁' X N P (D.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN 1 (a, y') := by
  cases hs : (held c₁ : Block (Xi × FirstState) Claim).step 0 ((VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r), (Fk X N P).start₁ (VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r)) [r₁, r₂] cols with
  | error e =>
    rw [hs] at hok
    cases hok
  | ok v =>
    obtain ⟨a, n⟩ := v
    obtain ⟨y', h⟩ := member_yes_written hZ hP hm hX hp c₁ k₁ q₁ hw D hD hpin tab r r₁ r₂ cols a n hs y₀ M hf
    exact ⟨a, y', h⟩

/-- **The same with the stored table CHOSEN: the zero message's code words**: no premise on the stored side is left. It shows that the FORM is not empty; the table that a row should name is an honest commitment's, which `member_at_written` covers at its M. -/
theorem member_at_zero (hw : (Fk X N P).wantedOk = true) (D : WholeD) (hD : (Fk X N P).data "key file" = .ok (D.at frS.P.T.a))
    (hpin : D.at frS.P.T.a = writtenKFull)
    (tab : MsgN → ℕ → ℕ → OnBytes.F) (r : RecFull) (r₁ r₂ : _root_.Fmt.RoundView) (cols : List OpenedColumn)
    (hok : ((held c₁ : Block (Xi × FirstState) Claim).step 0
      (VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r, (Fk X N P).start₁ (VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r)) [r₁, r₂] cols).isOk = true) :
    ∃ (a : Xi × FirstState) (y' : (fr₁ (D.at frS.P.T.a)).E.Str),
      On₁' X N P (D.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN 1 (a, y') := by
  obtain ⟨a, y', -, h⟩ := member_at_written hZ hP hm hX hp c₁ k₁ q₁ hw D hD hpin tab r r₁ r₂ cols hok
    ((fun _ => (0, []), fun _ => []) : (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (fun _ _ => 0) zero_words
  exact ⟨a, y', h⟩

/-- **The same AT AN INSTANCE x THAT A FILE HOLDS**: its key fits and passes the four tests; the Bool stands at x. -/
theorem member_at_key (hw : (Fk X N P).wantedOk = true) (D : WholeD) (hD : (Fk X N P).data "key file" = .ok (D.at frS.P.T.a))
    (hpin : D.at frS.P.T.a = writtenKFull)
    (tab : MsgN → ℕ → ℕ → OnBytes.F) (x : Xi) (hf : x.key.fits (oneAt X).lin.fold.index = true) (hB : keyOkB x.key = true)
    (r₁ r₂ : _root_.Fmt.RoundView) (cols : List OpenedColumn)
    (hok : ((held c₁ : Block (Xi × FirstState) Claim).step 0 (x, (Fk X N P).start₁ x) [r₁, r₂] cols).isOk = true)
    (y₀ : (fr₁ (D.at frS.P.T.a)).E.Str) (M : DN.ix.Row → DN.toDec.Co → GE) (hw' : ∀ a j, DN.tab y₀.1 a j = DN.ix.G.mulVec (M a) j) :
    ∃ (a : Xi × FirstState) (y' : (fr₁ (D.at frS.P.T.a)).E.Str), y'.1 = y₀.1 ∧
      On₁' X N P (D.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN 1 (a, y') := by
  obtain ⟨r, rfl⟩ := x_is_instK hZ hP hm hX hp x hf hB
  exact member_at_written hZ hP hm hX hp c₁ k₁ q₁ hw D hD hpin tab r r₁ r₂ cols hok y₀ M hw'

/-- **The same with the stored table chosen**: in front stand scope, the seat's facts, the tests on x's key, and THE ONE BOOL. -/
theorem member_at_key_zero (hw : (Fk X N P).wantedOk = true) (D : WholeD) (hD : (Fk X N P).data "key file" = .ok (D.at frS.P.T.a))
    (hpin : D.at frS.P.T.a = writtenKFull)
    (tab : MsgN → ℕ → ℕ → OnBytes.F) (x : Xi) (hf : x.key.fits (oneAt X).lin.fold.index = true) (hB : keyOkB x.key = true)
    (r₁ r₂ : _root_.Fmt.RoundView) (cols : List OpenedColumn)
    (hok : ((held c₁ : Block (Xi × FirstState) Claim).step 0 (x, (Fk X N P).start₁ x) [r₁, r₂] cols).isOk = true) :
    ∃ (a : Xi × FirstState) (y' : (fr₁ (D.at frS.P.T.a)).E.Str),
      On₁' X N P (D.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN 1 (a, y') := by
  obtain ⟨r, rfl⟩ := x_is_instK hZ hP hm hX hp x hf hB
  exact member_at_zero hZ hP hm hX hp c₁ k₁ q₁ hw D hD hpin tab r r₁ r₂ cols hok

/-- **THE CHAIR's FORM, AT AN INSTANCE x THAT A FILE HOLDS**: the step's own value a; every stored table of code words. -/
theorem member_yes_key (hw : (Fk X N P).wantedOk = true) (D : WholeD) (hD : (Fk X N P).data "key file" = .ok (D.at frS.P.T.a))
    (hpin : D.at frS.P.T.a = writtenKFull)
    (tab : MsgN → ℕ → ℕ → OnBytes.F) (x : Xi) (hf : x.key.fits (oneAt X).lin.fold.index = true) (hB : keyOkB x.key = true)
    (r₁ r₂ : _root_.Fmt.RoundView) (cols : List OpenedColumn) (a : Xi × FirstState) (n : ℕ)
    (hstep : (held c₁ : Block (Xi × FirstState) Claim).step 0 (x, (Fk X N P).start₁ x) [r₁, r₂] cols = .ok (a, n))
    (y₀ : (fr₁ (D.at frS.P.T.a)).E.Str) (M : DN.ix.Row → DN.toDec.Co → GE) (hw' : ∀ a j, DN.tab y₀.1 a j = DN.ix.G.mulVec (M a) j) :
    ∃ y' : (fr₁ (D.at frS.P.T.a)).E.Str, y'.1 = y₀.1 ∧ On₁' X N P (D.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN 1 (a, y') := by
  obtain ⟨r, rfl⟩ := x_is_instK hZ hP hm hX hp x hf hB
  exact member_yes_written hZ hP hm hX hp c₁ k₁ q₁ hw D hD hpin tab r r₁ r₂ cols a n hstep y₀ M hw'

/-- **THE SAME AT THE TABLE THAT THE FORMAT's ENCODER MAKES**, whatever its messages and tails: it IS a table of code words (`tab_honestTab`, OnBytes/Slice/Honest.lean): no premise on the stored side is left. -/
theorem member_yes_honest (hw : (Fk X N P).wantedOk = true) (D : WholeD) (hD : (Fk X N P).data "key file" = .ok (D.at frS.P.T.a))
    (hpin : D.at frS.P.T.a = writtenKFull)
    (tab : MsgN → ℕ → ℕ → OnBytes.F) (x : Xi) (hf : x.key.fits (oneAt X).lin.fold.index = true) (hB : keyOkB x.key = true)
    (r₁ r₂ : _root_.Fmt.RoundView) (cols : List OpenedColumn) (a : Xi × FirstState) (n : ℕ)
    (hstep : (held c₁ : Block (Xi × FirstState) Claim).step 0 (x, (Fk X N P).start₁ x) [r₁, r₂] cols = .ok (a, n)) (msg tl : ℕ → List UInt64) :
    ∃ y' : (fr₁ (D.at frS.P.T.a)).E.Str, y'.1 = honestTab frS msg tl ∧ On₁' X N P (D.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN 1 (a, y') :=
  member_yes_key hZ hP hm hX hp c₁ k₁ q₁ hw D hD hpin tab x hf hB r₁ r₂ cols a n hstep
    ((honestTab frS msg tl, fun _ => []) : (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (honestPolys frS msg tl) (tab_honestTab frS msg tl)

end

end LPFD

#print axioms LPFD.public10_in_scope
#print axioms LPFD.cond10_in_scope
#print axioms LPFD.yOf_cell'
#print axioms LPFD.lay_made
#print axioms LPFD.member_yes_written
#print axioms LPFD.member_at_written
#print axioms LPFD.member_yes_key
#print axioms LPFD.member_yes_honest
#print axioms LPFD.zero_words
#print axioms LPFD.rec_of_key
#print axioms LPFD.keyOkB_of_four
#print axioms LPFD.x_is_instK
#print axioms LPFD.member_at_key
#print axioms LPFD.member_at_key_zero
#print axioms LPFD.member_at_zero
