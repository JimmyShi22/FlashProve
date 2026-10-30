-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeShape.lean: the closing of a segment (K10): a test on shapes and counts alone under
which the shared text that makes a segment's group's rows anew (`groupRowsOf`, Honest/K2/Closing.lean) returns. It reads no
coin, no main row and no challenge, and it leaves out the one test of that text that costs time to evaluate
(`Sizes.roomy`), which stands as a premise.

  `msgOk`           a message's shape fits and its carried run has the count that its laying asks
  `rowsS`, `membersS`, `segS`, `lightS`, `groupS`   the tests, step by step as the text goes, and the members they name
  `rowsCore_ok`, `segmentLeft_ok`, `closingFrom_ok`   the text's steps return where these tests say yes
  `groupRows_ok`    the text returns, with these members, at every main row, list of challenges and coins of these counts
  `groupRows_count` what the text returns has as many members as rows

Limits. One way alone: where the tests say no, nothing is said. Nothing on what the rows hold.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentAlike
import Johnson.Desc.ProofFile.Honest.K2.Law.Room
import Johnson.Desc.ProofFile.Honest.K2.Law.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open ProofFile.Honest.K2 (FreshTable SegmentPub GroupRows Stretch closingFrom groupRowsOf groupFits segmentLeft segmentGroupRows
  challengesOr0 zeroLeft messageRows laidDue rideAs ShapeFits messageRows_returns)
open ProofFile.Honest.K2.Law (Laid rowsCore inFirstOf laterOf inFirst_same later_same map_fst_same segmentRows_eq)
open VerifiableInference.Desc.K2.Honest (GroupMember Left zeroG groupLayout)

/-- A message's shape fits and its carried run has the count that its laying asks. -/
def msgOk (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (fold : Option Nat) (d? : Option Due) : Bool :=
  VerifiableInference.Desc.Own.sentShapeFits codes s &&
    decide ((K1.stepsOf codes s (rideAs s fold)).pad ≤ (codes.base.getD s.code default).ell) &&
    (fold.all fun n => K1.rideFits codes s ⟨n, OnBytes.ceilLog2 s.maskRows⟩) &&
    d? == some (laidDue codes s fold)

/-- The shapes of a segment's members in its first sending. -/
def firstShapes (S : SegmentPub) : List OnBytes.OracleShape :=
  (inFirstOf S none fun _ _ _ => zeroG).map (·.1)

/-- The shapes of a segment's members in its later sendings. -/
def laterShapes (S : SegmentPub) (ps : Bool) : List OnBytes.OracleShape :=
  (laterOf S ps fun _ _ _ => zeroG).1.map (·.1)

/-- A segment's marks "kept". -/
def flagsS (S : SegmentPub) (ps : Bool) : List Bool :=
  (if ps then false :: S.sizes.target.kept.toList.map (·.keptAgain) else []) ++ S.ownKept

/-- A segment's members. -/
def membersS (S : SegmentPub) (ps : Bool) : List GroupMember :=
  ((firstShapes S ++ laterShapes S ps).zip (flagsS S ps)).map fun x => ⟨x.1, x.2⟩

/-- **The tests of `segmentGroupRows` on shapes and counts**, but for `Sizes.roomy`. -/
def rowsS (S : SegmentPub) (ps : Bool) (prevKept : List OnBytes.OracleShape) (ds : List Due) (base : Nat)
    (withFresh : Bool) : Bool :=
  let first := S.sent.headD #[]
  let freshNo := first.size - 1
  let skip := if withFresh then 1 else 0
  !first.isEmpty && !(ps && S.sizes.kept.length != S.sizes.target.kept.size) &&
    !(ps && S.sizes.kept != prevKept) &&
    (flagsS S ps).length == (firstShapes S).length + (laterShapes S ps).length &&
    ((firstShapes S).zipIdx.all fun x => msgOk S.sizes.codes x.1 none ds[base + x.2]?) &&
    (!withFresh || msgOk S.sizes.codes (first.getD freshNo default).shape (some S.foldVars) ds[base + freshNo]?) &&
    ((laterShapes S ps).zipIdx.all fun x => msgOk S.sizes.codes x.1 none ds[base + freshNo + skip + x.2]?)

/-- One segment's step. -/
def segS (S : SegmentPub) (prev : Option (List OnBytes.OracleShape)) (ds : List Due) (base : Nat) :
    Option (List OnBytes.OracleShape) :=
  let M := membersS S prev.isSome
  let vars := (groupLayout S.sizes.codes S.sizes.code S.sizes.maskCode M).k
  if rowsS S prev.isSome (prev.getD []) ds base true && vars == S.foldVars && S.gamma.length == vars &&
      groupFits S.sizes.codes S.sizes.code S.sizes.maskCode M
        (((S.sent.headD #[]).back?.map (·.shape)).getD default) then
    some ((M.filter (·.kept)).map (·.shape))
  else none

/-- The steps from a segment on. -/
def lightS (ds : List Due) : List SegmentPub → Nat → Option (List OnBytes.OracleShape) →
    Option (Option (List OnBytes.OracleShape) × Nat)
  | [], base, prev => some (prev, base)
  | S :: rest, base, prev =>
    (segS S prev ds base).bind fun W => lightS ds rest (base + S.messages) (some W)

/-- **The test on the group's rows.** -/
def groupS (segs : List SegmentPub) (ds : List Due) : Option (List GroupMember) :=
  match segs.getLast? with
  | none => none
  | some S =>
    (lightS ds segs.dropLast 0 none).bind fun y =>
      if rowsS S y.1.isSome (y.1.getD []) ds y.2 false then some (membersS S y.1.isSome) else none

/-- What the counts say of the carried stretches. -/
def DuesAt (ds : List Due) (k : Nat → Except String Stretch) : Prop :=
  ∀ n d, ds[n]? = some d → ∃ st, k n = .ok st ∧ st.due = d

/-- Carried coins have their counts. -/
theorem carried_dues : ∀ (ds : List (String × Due)) (ca : CsAll ds), DuesAt (ds.map (·.2)) (Stretch.carried ds ca)
  | [], _, n, d, h => by simp at h
  | x :: ds, ca, 0, d, h => by
    obtain rfl : x.2 = d := by simpa using h
    exact ⟨_, rfl, rfl⟩
  | x :: ds, ca, n + 1, d, h => by
    have h' : (ds.map (·.2))[n]? = some d := by simpa using h
    exact carried_dues ds ca.2 n d h'

theorem msg_returns (table : FreshTable) {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {fold : Option Nat}
    (data : Nat → Nat → Cb.Gl.E) {ds : List Due} {k : Nat → Except String Stretch} (hk : DuesAt ds k) {n : Nat}
    (h : msgOk codes s fold ds[n]? = true) : ∃ R, (k n).bind (messageRows table codes s fold data) = .ok R := by
  unfold msgOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨st, e, ed⟩ := hk n _ h4
  have H : ShapeFits codes s fold := ⟨h1, h2, fun m hm => by
    subst hm
    exact h3⟩
  obtain ⟨R, hR⟩ := messageRows_returns table data H ed
  exact ⟨R, by rw [e]; exact hR⟩

theorem mem_shapes {A : List Laid} {A' : List OnBytes.OracleShape} (hA : A.map (·.1) = A')
    {x : Laid × Nat} (hx : x ∈ A.zipIdx) : (x.1.1, x.2) ∈ A'.zipIdx := by
  subst hA
  rw [List.zipIdx_map]
  exact List.mem_map.2 ⟨x, hx, rfl⟩

theorem guard_pass {α : Type} {c : Prop} [Decidable c] {e : String} {f : PUnit → Except String α} (h : ¬ c) :
    (if c then (throw e : Except String PUnit) >>= f else pure PUnit.unit >>= f) = f PUnit.unit := by
  rw [if_neg h]
  rfl

theorem ok_then {α β : Type} {x : Except String α} {f : α → Except String β} {a : α} {P : β → Prop}
    (h : x = .ok a) (hf : ∃ R, f a = .ok R ∧ P R) : ∃ R, x >>= f = .ok R ∧ P R := by
  subst h
  exact hf

/-- **Where the tests on shapes say yes, `rowsCore` returns, with these members.** -/
theorem rowsCore_ok (table : FreshTable) {S : SegmentPub} {ps : Bool} {prevKept : List OnBytes.OracleShape}
    {A : List Laid} {B : List Laid × Nat} {ds : List Due} {k : Nat → Except String Stretch} {base : Nat}
    {withFresh : Bool} (hA : A.map (·.1) = firstShapes S) (hB : B.1.map (·.1) = laterShapes S ps)
    (hk : DuesAt ds k) (hroom : ps = true → S.sizes.roomy = true)
    (h : rowsS S ps prevKept ds base withFresh = true) :
    ∃ R, rowsCore table S ps prevKept A B k base withFresh = .ok R ∧ R.members = membersS S ps := by
  unfold rowsS at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩ := h
  have lA : A.length = (firstShapes S).length := by rw [← hA, List.length_map]
  have lB : B.1.length = (laterShapes S ps).length := by rw [← hB, List.length_map]
  have hflags : (if ps = true then false :: S.sizes.target.kept.toList.map (·.keptAgain) else []) ++ S.ownKept =
      flagsS S ps := rfl
  unfold rowsCore
  dsimp only
  rw [guard_pass (fun c => by rw [c] at g1; cases g1), guard_pass (fun c => by rw [c] at g2; cases g2),
    guard_pass (fun c => by rw [c] at g3; cases g3),
    guard_pass (fun c => by
      have := hroom (Bool.and_eq_true _ _ ▸ c).1
      simp [this] at c)]
  rw [hflags, lA, lB, guard_pass (fun c => bne_iff_ne.1 c (eq_of_beq g4))]
  obtain ⟨r0, e0⟩ := ProofFile.Honest.K2.Reads.mapM_of_all
    (fun x : Laid × Nat => (k (base + x.2)).bind (messageRows table S.sizes.codes x.1.1 none x.1.2)) A.zipIdx
    fun x hx => msg_returns table _ hk (List.all_eq_true.1 g5 _ (mem_shapes hA hx))
  refine ok_then e0 ?_
  obtain ⟨r1, e1⟩ := ProofFile.Honest.K2.Reads.mapM_of_all
    (fun x : Laid × Nat => (k (base + ((S.sent.headD #[]).size - 1) + (if withFresh = true then 1 else 0) + x.2)).bind
      (messageRows table S.sizes.codes x.1.1 none x.1.2)) B.1.zipIdx
    fun x hx => by
      have hm : msgOk S.sizes.codes x.1.1 none
          ds[base + ((S.sent.headD #[]).size - 1) + (if withFresh = true then 1 else 0) + x.2]? = true :=
        List.all_eq_true.1 g7 (x.1.1, x.2) (mem_shapes hB hx)
      exact msg_returns table x.1.2 hk hm
  have tail : ((((A ++ B.1).map (fun y : Laid => y.1)).zip (flagsS S ps)).map
      fun x : OnBytes.OracleShape × Bool => GroupMember.mk x.1 x.2) = membersS S ps := by
    rw [List.map_append, hA, hB]
    rfl
  cases withFresh with
  | false =>
    rw [if_neg (by simp)]
    first
      | exact ok_then e1 ⟨_, rfl, tail⟩
      | exact ok_then (a := none) rfl (ok_then e1 ⟨_, rfl, tail⟩)
  | true =>
    have g6' : msgOk S.sizes.codes ((S.sent.headD #[]).getD ((S.sent.headD #[]).size - 1) default).shape
        (some S.foldVars) ds[base + ((S.sent.headD #[]).size - 1)]? = true := g6
    obtain ⟨R, hR⟩ := msg_returns table (fun _ _ => zeroG) hk g6'
    rw [if_pos rfl]
    exact ok_then (a := some R) (by rw [hR]; rfl) (ok_then e1 ⟨_, rfl, tail⟩)

/-- `segmentGroupRows` at any main rows, with the members that the tests name. -/
theorem segmentRows_ok (table : FreshTable) {S : SegmentPub} {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} (own : Nat → Nat → Nat → Cb.Gl.E) {ds : List Due}
    {k : Nat → Except String Stretch} {base : Nat} {withFresh : Bool} (hk : DuesAt ds k)
    (hroom : prev.isSome = true → S.sizes.roomy = true)
    (h : rowsS S prev.isSome prevKept ds base withFresh = true) :
    ∃ R, segmentGroupRows table S prev prevKept own k base withFresh = .ok R ∧ R.members = membersS S prev.isSome := by
  rw [segmentRows_eq]
  exact rowsCore_ok table (map_fst_same (inFirst_same S prev none own _))
    (map_fst_same (later_same S _ own _)) hk hroom h

/-- **One segment's step returns where its test says yes.** -/
theorem segmentLeft_ok (table : FreshTable) {S : SegmentPub} {prev : Option (Left × List OnBytes.OracleShape)}
    (own : Nat → Nat → Nat → Cb.Gl.E) (heard : List Fmt.Drawn) {ds : List Due} {k : Nat → Except String Stretch}
    {base : Nat} (hk : DuesAt ds k) (hroom : prev.isSome = true → S.sizes.roomy = true)
    {W' : List OnBytes.OracleShape} (h : segS S (prev.map (·.2)) ds base = some W') :
    ∃ W, segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) own heard k base = .ok W ∧ W.2 = W' := by
  have q1 : (prev.map (·.2)).isSome = prev.isSome := by cases prev <;> rfl
  have q2 : (prev.map (·.1)).isSome = prev.isSome := by cases prev <;> rfl
  unfold segS at h
  dsimp only at h
  split at h
  · rename_i hc
    have hW := Option.some.inj h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
    rw [q1] at c1 c2 c3 c4 hW
    obtain ⟨R, hR, hm⟩ := segmentRows_ok table (prev := prev.map (·.1)) own hk (by rw [q2]; exact hroom)
      (by rw [q2]; exact c1)
    rw [q2] at hm
    have hγ : (challengesOr0 heard S.gamma).length = S.gamma.length := by
      simp [ProofFile.Honest.K2.challengesOr0]
    unfold segmentLeft
    dsimp only
    refine ok_then hR ?_
    rw [hm, hγ, guard_pass (fun c => by
      rw [Bool.or_eq_true] at c
      rcases c with c | c
      · exact bne_iff_ne.1 c c2
      · exact bne_iff_ne.1 c c3), guard_pass (fun c => by rw [c4] at c; cases c)]
    exact ⟨_, rfl, hW⟩
  · cases h

/-- The steps from a segment on return where their test says yes. -/
theorem closingFrom_ok (table : FreshTable) (own : Nat → Nat → Nat → Nat → Cb.Gl.E) (heard : List Fmt.Drawn)
    {ds : List Due} {k : Nat → Except String Stretch} (hk : DuesAt ds k) :
    ∀ (segs : List SegmentPub) (j base : Nat) (prev : Option (Left × List OnBytes.OracleShape))
      {y : Option (List OnBytes.OracleShape) × Nat},
      (∀ i S, segs[i]? = some S → (i ≠ 0 ∨ prev.isSome = true) → S.sizes.roomy = true) →
      lightS ds segs base (prev.map (·.2)) = some y →
      ∃ x, closingFrom table own heard k segs j base prev = .ok x ∧ x.1.map (·.2) = y.1 ∧ x.2 = y.2
  | [], _, _, _, y, _, h => by
    obtain rfl := Option.some.inj h
    exact ⟨_, rfl, rfl, rfl⟩
  | S :: rest, j, base, prev, y, hr, h => by
    obtain ⟨W', hW, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨W, e, eW⟩ := segmentLeft_ok table (own j) heard hk (fun c => hr 0 S rfl (Or.inr c)) hW
    subst eW
    obtain ⟨x, hx, x1, x2⟩ := closingFrom_ok table own heard hk rest (j + 1) (base + S.messages) (some W)
      (fun i S' hi _ => hr (i + 1) S' (by simpa using hi) (Or.inl (by omega))) h2
    refine ⟨x, ?_, x1, x2⟩
    show (segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard k base).bind _ = _
    rw [e]
    exact hx

/-- **The shared text returns, with the members that the test names.** -/
theorem groupRows_ok (table : FreshTable) {segs : List SegmentPub} (own : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (heard : List Fmt.Drawn) {ds : List Due} {k : Nat → Except String Stretch} (hk : DuesAt ds k)
    (hr : ∀ i S, segs[i]? = some S → i ≠ 0 → S.sizes.roomy = true) {ms : List GroupMember}
    (h : groupS segs ds = some ms) :
    ∃ R, groupRowsOf table segs own heard k = .ok R ∧ R.members = ms := by
  unfold groupS at h
  unfold groupRowsOf
  cases e : segs.getLast? with
  | none =>
    rw [e] at h
    cases h
  | some S =>
    rw [e] at h
    obtain ⟨y, hy, h2⟩ := Option.bind_eq_some_iff.1 h
    split at h2
    · rename_i hc
      have hms := Option.some.inj h2
      have hdl : ∀ (i : Nat) (S' : SegmentPub), segs.dropLast[i]? = some S' → segs[i]? = some S' := by
        intro i S' hi
        rw [List.getElem?_dropLast] at hi
        split at hi
        · exact hi
        · cases hi
      obtain ⟨x, hx, x1, x2⟩ := closingFrom_ok table own heard hk segs.dropLast 0 0 none
        (fun i S' hi c => hr i S' (hdl i S' hi) (by simpa using c)) hy
      have q : (x.1.map (·.1)).isSome = y.1.isSome := by
        rw [← x1]
        cases x.1 <;> rfl
      have g : (x.1.map (·.2)).getD [] = y.1.getD [] := by rw [x1]
      have hrs : y.1.isSome = true → S.sizes.roomy = true := by
        intro c
        have hne : segs.dropLast ≠ [] := by
          intro c0
          rw [c0] at hy
          have := Option.some.inj hy
          subst this
          cases c
        have hlen : 1 < segs.length := by
          have : segs.dropLast.length ≠ 0 := fun c0 => hne (List.length_eq_zero_iff.1 c0)
          rw [List.length_dropLast] at this
          omega
        refine hr (segs.length - 1) S ?_ (by omega)
        rw [← List.getLast?_eq_getElem?]
        exact e
      obtain ⟨R, hR, hm⟩ := segmentRows_ok table (prev := x.1.map (·.1)) (prevKept := (x.1.map (·.2)).getD [])
        (own (segs.length - 1)) (base := x.2) (withFresh := false) hk (by rw [q]; exact hrs)
        (by rw [q, g, x2]; exact hc)
      refine ⟨R, ?_, by rw [hm, q]; exact hms⟩
      show (closingFrom table own heard k segs.dropLast 0 0 none).bind _ = _
      rw [hx]
      exact hR
    · cases h2

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β} (h : x >>= f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem guard_ok {α : Type} {c : Prop} [Decidable c] {e : String} {f : PUnit → Except String α} {b : α}
    (h : (if c then (throw e : Except String PUnit) >>= f else pure PUnit.unit >>= f) = .ok b) :
    ¬ c ∧ f PUnit.unit = .ok b := by
  by_cases hc : c
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

theorem eq_of_not_bne {a b : Nat} (h : ¬ (a != b) = true) : a = b := by
  simpa using h

/-- What `segmentGroupRows` returns has as many rows as members. -/
theorem rowsCore_count {table : FreshTable} {S : SegmentPub} {ps : Bool} {prevKept : List OnBytes.OracleShape}
    {A : List ProofFile.Honest.K2.Law.Laid} {B : List ProofFile.Honest.K2.Law.Laid × Nat} {k : Nat → Except String Stretch}
    {base : Nat} {R : GroupRows} (h : rowsCore table S ps prevKept A B k base false = .ok R) :
    R.rows.length = R.members.length := by
  unfold rowsCore at h
  dsimp only at h
  obtain ⟨-, h⟩ := guard_ok h
  obtain ⟨-, h⟩ := guard_ok h
  obtain ⟨-, h⟩ := guard_ok h
  obtain ⟨-, h⟩ := guard_ok h
  obtain ⟨hc, h⟩ := guard_ok h
  have hc' := eq_of_not_bne hc
  obtain ⟨r0, e0, h⟩ := bind_ok h
  obtain ⟨u, -, h⟩ := bind_ok h
  obtain ⟨r1, e1, h⟩ := bind_ok h
  have h' := Except.ok.inj h
  subst h'
  have l0 := ProofFile.Honest.K2.Reads.mapM_length _ _ _ e0
  have l1 := ProofFile.Honest.K2.Reads.mapM_length _ _ _ e1
  rw [List.length_zipIdx] at l0 l1
  simp only [List.length_append, List.length_map, List.length_zip] at hc' ⊢
  omega

/-- What the shared text returns has as many rows as members. -/
theorem groupRows_count {table : FreshTable} {segs : List SegmentPub} {own : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard : List Fmt.Drawn} {k : Nat → Except String Stretch} {R : GroupRows}
    (h : groupRowsOf table segs own heard k = .ok R) : R.rows.length = R.members.length := by
  unfold groupRowsOf at h
  cases e : segs.getLast? with
  | none =>
    rw [e] at h
    cases h
  | some S =>
    rw [e] at h
    obtain ⟨x, -, h⟩ := bind_ok h
    rw [ProofFile.Honest.K2.Law.segmentRows_eq] at h
    exact rowsCore_count h

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.msgOk
#print axioms ProofFile.Honest.K10.membersS
#print axioms ProofFile.Honest.K10.rowsS
#print axioms ProofFile.Honest.K10.segS
#print axioms ProofFile.Honest.K10.lightS
#print axioms ProofFile.Honest.K10.groupS
#print axioms ProofFile.Honest.K10.carried_dues
#print axioms ProofFile.Honest.K10.msg_returns
#print axioms ProofFile.Honest.K10.mem_shapes
#print axioms ProofFile.Honest.K10.guard_pass
#print axioms ProofFile.Honest.K10.ok_then
#print axioms ProofFile.Honest.K10.rowsCore_ok
#print axioms ProofFile.Honest.K10.segmentRows_ok
#print axioms ProofFile.Honest.K10.segmentLeft_ok
#print axioms ProofFile.Honest.K10.closingFrom_ok
#print axioms ProofFile.Honest.K10.groupRows_ok
#print axioms ProofFile.Honest.K10.bind_ok
#print axioms ProofFile.Honest.K10.guard_ok
#print axioms ProofFile.Honest.K10.eq_of_not_bne
#print axioms ProofFile.Honest.K10.rowsCore_count
#print axioms ProofFile.Honest.K10.groupRows_count
