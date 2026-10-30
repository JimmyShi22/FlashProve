-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FirstOkLaw.lean: gpOk = true gives what the law of the proximity test (the kind
K12) asks at its first stage of the plan and of the record, so that the test
Johnson/Desc/K12/Law/FirstOk.lean is no transcription.

Statements and proofs. No definition of Johnson/Desc/K12/Law/FirstOk.lean is turned here.
Main names:
  `sg`: the place's stage in the library's form (g := k - h).
  `Good`, `good_of_ok`: the clauses that the law spends, as propositions; ok (gpL ...) = true gives
    them.
  `Made`, `made_of`: what gpOf has made: each member's and the mask's seat (Part1P), in the layout's
    order; the mask's entering; the trees' places; the declared openings.
  `mbOf`, `gpG`, `gpP`: the typed group and its public data, made of the plain data: the index type
    is Fin (the number of members); each member's format is the stage's two codes, its own tree's
    depth and its rows; the seats go by numbers (Site.byNo) from the blocks' first rows on.
  `gp_pub`, `gp_lay`, `gp_parts`: GpData.Pub, GpData.LayG, PartsP.
  `recvP_opened`, `entered_of_case`: the two arms of MaskCase are what `entered` computes (what is
    received does not hang on the columns that are left).
  `exists_map`, `opensOf_cut`: for OpensAre: a source for each tree, off the declared openings in
    turn.
  `cutS_first`: the frame's cut for the first switch is the two declared rounds at which
    fixed_switch speaks at j = 0.
  `gpOk_inv`, `first_at`: the two halves of first_of_ok, with the plain data D in front.
  `first_of_ok`: gpOk p t = true, at the record t behind the batching, gives P.Pub p.nums.firstTree;
    a src with OpensAre at the tie's own cut (so its keys); row.kept = #[]; P.LayG L; and PartsP P
    st book id in whichever arm of MaskCase the place takes, at the place's own stage.
  `first_fixed_cut`: with fixedOk, every tree off which the first stage's words are read has a
    source fixed in front of the stage's first draw, at the tie's own cut.
Limits: No soundness is claimed, and nothing is said on hiding. The law of the proximity test is not
proved here.
Letters that stay: rad (the members' radii: no clause reads them); dM i and dF (the written rounds
that sent the trees), under the premise that a written tree has as many positions as the book's
tree. A premise from elsewhere: a.h ≤ a.k (a clause of pubOk, Johnson/Desc/K12/Law/PubOk.lean).
Clauses of gpOk that no theorem here spends: codeM, codeZ, f:codeZ (the record's codes at the
shapes' numbers are the stage's: the typed group takes the stage's codes by definition in mbOf;
these three clauses are what makes that honest, and no theorem reads them); sizes; f:short;
f:zshort; f:no member; opens.n. The clauses opens.a and opens.W are spent in
Johnson/Desc/K12/Law/FirstCutLaw.lean and Johnson/Desc/K12/Law/ViewWide.lean.
Owed by whoever makes the plan, and said by no clause here: where all keys are equal, the first
component of OpensAre holds for any order of the trees; the declared order against the book's is
then held by depth and width alone (opens.a, opens.W). At a place where two opened trees had one
key, one depth and one width, nothing in the block would tell a swapped plan.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.FirstSrc
import Johnson.Desc.K12.Law.FirstOk

set_option autoImplicit false
namespace H2K.First
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw

/-- The place's stage in the library's form: g := k - h. -/
def sg (a : Fmt.M1.Stage) : Sg := ⟨a.C, a.Z, a.h, a.k - a.h, a.t⟩

/-- What the clauses say, as propositions. -/
structure Good (F : ℕ) (a : Fmt.M1.Stage) (row : GroupRow) (D : Plain) : Prop where
  short : ∀ i : Fin D.mems.length, (D.mems.get i).tsh.logN ≤ a.C.a
  long : ∀ i : Fin D.mems.length, 0 < (D.mems.get i).sh.mainRows → (D.mems.get i).tsh.logN = a.C.a
  zshort : ∀ i : Fin D.mems.length, 0 < (D.mems.get i).sh.maskRows → a.Z.a ≤ (D.mems.get i).tsh.logN
  deg : ∀ i : Fin D.mems.length, (D.mems.get i).sh.mainDeg = 1 ∨ (D.mems.get i).sh.mainDeg = 3
  roomM : ∀ i : Fin D.mems.length, oM D.L i + (D.mems.get i).sh.mainRows ≤ 2 ^ kk a
  roomZ : ∀ i : Fin D.mems.length, oZ D.L i + (D.mems.get i).sh.maskRows ≤ 2 ^ a.h
  firstM : ∀ i : Fin D.mems.length, 0 < (D.mems.get i).sh.mainRows →
    (D.L.mainFirst.getD i none).isSome = true
  firstZ : ∀ i : Fin D.mems.length, 0 < (D.mems.get i).sh.maskRows →
    (D.L.maskFirst.getD i none).isSome = true
  apartM : ∀ i j : Fin D.mems.length, i ≠ j →
    oM D.L i + (D.mems.get i).sh.mainRows ≤ oM D.L j ∨ oM D.L j + (D.mems.get j).sh.mainRows ≤ oM
        D.L i
  apartZ : ∀ i j : Fin D.mems.length, i ≠ j →
    oZ D.L i + (D.mems.get i).sh.maskRows ≤ oZ D.L j ∨ oZ D.L j + (D.mems.get j).sh.maskRows ≤ oZ
        D.L i
  kept : ∀ w, D.L.kept.getD w false = false
  fMain : D.fresh.sh.mainRows = 0
  fMask : D.fresh.sh.maskRows = 2 ^ a.h
  keys : D.opens.map (·.1.tree - F) = D.ts.map (keyAt F D.book)
  rowKept : row.kept = #[]

theorem mem_zipIdx_get {α : Type} (l : List α) (i : Fin l.length) : (l.get i, i.val) ∈ l.zipIdx :=
    by
  rw [List.mem_zipIdx_iff_getElem?]
  simp

theorem apart_of (first : ℕ → ℕ) (rows : Seat1 → ℕ) (ms : List Seat1)
    (h : apartB first rows ms = true) (i j : Fin ms.length) (hij : i ≠ j) :
    first i + rows (ms.get i) ≤ first j ∨ first j + rows (ms.get j) ≤ first i := by
  unfold apartB at h
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h _ (mem_zipIdx_get ms i)) _ (mem_zipIdx_get ms
      j)
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
  rcases h1 with (h1 | h1) | h1
  · exact absurd (Fin.ext h1) hij
  · exact Or.inl h1
  · exact Or.inr h1

theorem memL_all (K : Codes) (a : Fmt.M1.Stage) (L : GroupLayout) (w : ℕ) (m : Seat1)
    (h : (memL K a L w m).all (·.2) = true) :
    m.tsh.logN ≤ a.C.a ∧ (0 < m.sh.mainRows → m.tsh.logN = a.C.a) ∧
      (0 < m.sh.maskRows → a.Z.a ≤ m.tsh.logN) ∧ (m.sh.mainDeg = 1 ∨ m.sh.mainDeg = 3) ∧
      oM L w + m.sh.mainRows ≤ 2 ^ kk a ∧ oZ L w + m.sh.maskRows ≤ 2 ^ a.h ∧
      (m.sh.mainRows = 0 ∨ (L.mainFirst.getD w none).isSome = true) ∧
      (m.sh.maskRows = 0 ∨ (L.maskFirst.getD w none).isSome = true) := by
  unfold memL at h
  rw [List.all_map] at h
  simp only [Function.comp_def, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

theorem good_of_ok (p : P12) (a : Fmt.M1.Stage) (row : GroupRow) (D : Plain)
    (h : ok (gpL p a row D) = true) : Good p.nums.firstTree a row D := by
  unfold ok gpL at h
  dsimp only at h
  rw [List.all_append, Bool.and_eq_true, List.all_flatMap] at h
  obtain ⟨hm, ht⟩ := h
  have hm' := fun i : Fin D.mems.length =>
    memL_all _ _ _ _ _ (List.all_eq_true.1 hm (D.mems.get i, i.val) (mem_zipIdx_get D.mems i))
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at ht
  obtain ⟨t1, t2, t3, _, t5, t6, _, _, _, _, _, t12, _, _, t15⟩ := ht
  refine ⟨fun i => (hm' i).1, fun i => (hm' i).2.1, fun i => (hm' i).2.2.1,
    fun i => (hm' i).2.2.2.1, fun i => (hm' i).2.2.2.2.1, fun i => (hm' i).2.2.2.2.2.1,
    fun i h0 => ((hm' i).2.2.2.2.2.2.1).resolve_left (Nat.pos_iff_ne_zero.1 h0),
    fun i h0 => ((hm' i).2.2.2.2.2.2.2).resolve_left (Nat.pos_iff_ne_zero.1 h0),
    apart_of _ _ _ t1, apart_of _ _ _ t2, fun w => ?_, t5, t6, t12, ?_⟩
  · by_cases hw : w < D.L.kept.size
    · have := Array.all_eq_true.1 t3 w hw
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw]
      simpa using this
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
  · exact Array.isEmpty_iff.1 t15

/-! ## What gpOf has made -/

theorem seatOf_inv (st : Statement) (book : TreeBook) (id : ℕ) (m : Seat1)
    (h : seatOf st book id = some m) : m.id = id ∧
    Part1P st book id m.sh m.num m.tsh m.t m.part := by
  unfold seatOf at h
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨T, hT, h⟩ := Option.map_eq_some_iff.1 h
  subst h
  exact ⟨rfl, ⟨x, hx, rfl⟩, hq, T, hT, rfl, rfl⟩

/-- What gpOf has made: the mask and what lies behind its entering; each member's seat, in the
layout's order; the mask's seat; the trees' places; the declared openings. -/
structure Made (p : P12) (t : T12) (a : Fmt.M1.Stage) (L : GroupLayout) (D : Plain) : Prop where
  lay : D.L = L
  ent : ∃ cu, stageAt p 0 a = some cu ∧ entered p t cu L = some (D.fresh.id, D.st, D.book)
  size : L.members.size = D.mems.length
  mem : ∀ i : Fin D.mems.length, L.members[i.val]? = some (D.mems.get i).id ∧
    Part1P D.st D.book (D.mems.get i).id (D.mems.get i).sh (D.mems.get i).num (D.mems.get i).tsh
      (D.mems.get i).t (D.mems.get i).part
  fresh : Part1P D.st D.book D.fresh.id D.fresh.sh D.fresh.num D.fresh.tsh D.fresh.t D.fresh.part
  ts : D.ts = Fmt.listOf ((D.mems.map (·.t)) ++ [D.fresh.t])
  opens : D.opens = opensOf p a.k

theorem made_of (p : P12) (t : T12) (a : Fmt.M1.Stage) (L : GroupLayout) (D : Plain)
    (h : gpOf p t a L = some D) : Made p t a L D := by
  unfold gpOf at h
  obtain ⟨cu, hcu, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨id, st, book⟩, he, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ms, hms, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨f, hf, h⟩ := Option.map_eq_some_iff.1 h
  subst h
  obtain ⟨f1, f2⟩ := seatOf_inv _ _ _ _ hf
  obtain ⟨z1, z2⟩ := list_mapM_inv _ _ _ hms
  have hsz : L.members.size = ms.length := by rw [z1, Array.length_toList]
  refine ⟨rfl, ⟨cu, hcu, by rw [he, f1]⟩, hsz, fun i => ?_, by rw [f1]; exact f2, rfl, rfl⟩
  have hi : i.val < L.members.toList.length := by rw [← z1]; exact i.isLt
  have e := z2 i.val hi
  have e' : seatOf st book L.members.toList[i.val] = some (ms.get i) := by
    rw [e, List.getElem?_eq_getElem i.isLt]
    rfl
  obtain ⟨g1, g2⟩ := seatOf_inv _ _ _ _ e'
  refine ⟨?_, by rw [g1]; exact g2⟩
  rw [g1, ← Array.getElem?_toList, List.getElem?_eq_getElem hi]

/-! ## The typed group and what is public of it, made of the plain data -/

/-- A member's format: the stage's two codes; its own tree's depth; its rows. rad: its radius (a
letter: no clause reads it). -/
def mbOf (a : Fmt.M1.Stage) (rad : ℕ) (m : Seat1) : Mb :=
  ⟨a.C, a.Z, m.tsh.logN, m.sh.mainRows, m.sh.maskRows, rad⟩

section
variable {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain}

/-- The group: the layout's members, by their numbers in the layout; seats by numbers, from the
blocks' first rows on. -/
def gpG (h : Good F a row D) (rad : ℕ → ℕ) : Gp (sg a) where
  ι := Fin D.mems.length
  mb := fun i => mbOf a (rad i.val) (D.mems.get i)
  seat := fun i => Site.byNo (sg a) (mbOf a (rad i.val) (D.mems.get i)) (oM D.L i.val) (oZ D.L
      i.val)
    (h.short i) (fun h0 => ⟨rfl, h.long i h0⟩) (fun h0 => ⟨rfl, h.zshort i h0⟩)

/-- What is public of the group. dM i, dF: the written rounds that sent member i's tree and the
mask's: letters. -/
def gpP (h : Good F a row D) (rad : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD) :
    GpData (gpG h rad) where
  n := D.mems.length
  ix := fun i => i.val
  id := fun i => (D.mems.get i).id
  sh := fun i => (D.mems.get i).sh
  num := fun i => (D.mems.get i).num
  tsh := fun i => (D.mems.get i).tsh
  tp := fun i => (D.mems.get i).t
  part := fun i => (D.mems.get i).part
  oM := fun i => oM D.L i.val
  oZ := fun i => oZ D.L i.val
  lay := fun i => ⟨(D.mems.get i).sh.mainDeg == 1, skM (D.mems.get i).tsh (D.mems.get i).part,
    skZ (D.mems.get i).tsh (D.mems.get i).part⟩
  d := dM
  fsh := D.fresh.sh
  fnum := D.fresh.num
  ftsh := D.fresh.tsh
  ft := D.fresh.t
  fpart := D.fresh.part
  aF := D.fresh.tsh.logN
  oF := skZ D.fresh.tsh D.fresh.part
  dF := dF
  ts := D.ts
  key := keyAt F D.book
  log := logAt D.book

theorem keyAt_of {st : Statement} {book : TreeBook} {o num t p : ℕ} {sh : OracleShape}
    {tsh : TreeShape} (h : Part1P st book o sh num tsh t p) :
    keyAt F book t = num - F ∧ logAt book t = tsh.logN := by
  obtain ⟨T, hT, e1, e2⟩ := h.tree
  unfold keyAt logAt
  rw [hT, ← e1, ← e2]
  exact ⟨rfl, rfl⟩

/-- gpOk's clauses give GpData.Pub. The two premises on the letters dM, dF (a written tree has as
many positions as the book's tree) are the reading's. -/
theorem gp_pub {p : P12} {t : T12} {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D)
    (rad : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD)
    (hd : ∀ i, PQ.posN (dM i).tree = 2 ^ (D.mems.get i).tsh.logN)
    (hdF : PQ.posN dF.tree = 2 ^ D.fresh.tsh.logN) : (gpP h rad dM dF).Pub F where
  numbered :=
    { pM := fun _ _ => rfl
      pZ := fun _ _ => rfl
      roomM := fun i => h.roomM i
      roomZ := fun i => h.roomZ i
      apartM := fun i j hij => h.apartM i j hij
      apartZ := fun i j hij => h.apartZ i j hij }
  ixLt := fun i => i.isLt
  ixInj := fun _ _ e => Fin.ext e
  ixSur := fun w hw => ⟨⟨w, hw⟩, rfl⟩
  mainRows := fun _ => rfl
  maskRows := fun _ => rfl
  deg := fun i => by
    show (D.mems.get i).sh.mainDeg = if ((D.mems.get i).sh.mainDeg == 1) = true then 1 else 3
    rcases h.deg i with e | e <;> rw [e] <;> rfl
  depth := fun _ => rfl
  skipM := fun _ => rfl
  skipZ := fun _ => rfl
  posN := hd
  fMain := h.fMain
  fMask := h.fMask
  fDepth := rfl
  fSkip := rfl
  fPosN := hdF
  incr := by
    show D.ts.Pairwise (· < ·)
    rw [hm.ts]
    exact Fmt.listOf_incr _
  mem := fun z => by
    show z ∈ D.ts ↔ (∃ i : Fin D.mems.length, (D.mems.get i).t = z) ∨ z = D.fresh.t
    rw [hm.ts, Fmt.listOf_mem, List.mem_append, List.mem_singleton, List.mem_map]
    refine or_congr ⟨?_, ?_⟩ Iff.rfl
    · rintro ⟨m, hmem, rfl⟩
      obtain ⟨i, rfl⟩ := List.get_of_mem hmem
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, List.get_mem _ i, rfl⟩
  keyOf := fun i => (keyAt_of (hm.mem i).2).1
  logOf := fun i => (keyAt_of (F := F) (hm.mem i).2).2
  fKey := (keyAt_of hm.fresh).1
  fLog := (keyAt_of (F := F) hm.fresh).2

/-- … and GpData.LayG at the layout behind the batching. -/
theorem gp_lay {p : P12} {t : T12} {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D)
    (rad : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD) : (gpP h rad dM dF).LayG L where
  size := hm.size
  members := fun i => (hm.mem i).1
  kept := fun w => by rw [← hm.lay]; exact h.kept w
  mainFirst := fun i h0 => by
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (h.firstM i h0)
    rw [← hm.lay]
    show D.L.mainFirst.getD i.val none = some ((D.L.mainFirst.getD i.val none).getD 0)
    rw [hf]
    rfl
  maskFirst := fun i h0 => by
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (h.firstZ i h0)
    rw [← hm.lay]
    show D.L.maskFirst.getD i.val none = some ((D.L.maskFirst.getD i.val none).getD 0)
    rw [hf]
    rfl

/-- … and PartsP at the statement and the book behind the mask's entering. -/
theorem gp_parts {p : P12} {t : T12} {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D)
    (rad : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD) :
    PartsP (gpP h rad dM dF) D.st D.book D.fresh.id :=
  ⟨fun i => (hm.mem i).2, hm.fresh⟩

end

/-! ## The mask's entering, the declared openings, and the whole -/

/-- What is received does not hang on the columns that are left. -/
theorem recvP_opened (F : ℕ) (st : Statement) (bk : TreeBook) (roots : ℕ)
    (op op' : List (ℕ × ℕ × List UInt64)) (sent : Array OracleNotice) (ids : Array ℕ)
    (d1 : _root_.Desc.Plain.DState Unit)
    (h : Ground.recvP F ⟨st, bk, roots, op, ()⟩ sent = some (ids, d1)) :
    ∃ d2, Ground.recvP F ⟨st, bk, roots, op', ()⟩ sent = some (ids, d2) ∧ d2.st = d1.st ∧
      d2.book = d1.book := by
  unfold Ground.recvP at h ⊢
  dsimp only at h ⊢
  split at h
  · rename_i hc
    rw [if_pos hc]
    obtain ⟨lay, hl, e⟩ := Option.map_eq_some_iff.1 h
    rw [hl]
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact ⟨_, rfl, rfl, rfl⟩
  · cases h

/-- MaskCase's two arms are what "entered" computes. -/
theorem entered_of_case (p : P12) (t : T12) (cu : IoppStage) (L : GroupLayout) (id : ℕ)
    (st : Statement) (book : TreeBook) (h : MaskCase p t (ioppFoldShape cu L) id st book) :
    entered p t cu L = some (id, st, book) := by
  unfold entered
  rcases h with ⟨hm, rfl, rfl⟩ | ⟨hm, opened, ids, d1, hr, hi, rfl, rfl⟩
  · rw [hm]
  · rw [hm]
    obtain ⟨d2, h2, e1, e2⟩ := recvP_opened _ _ _ _ _ [] _ _ _ hr
    show (Ground.recvP _ _ _).bind _ = _
    rw [h2]
    show (ids[0]?).map _ = _
    rw [hi, e1, e2]
    rfl

/-- A list as long as a list without repeats is that list's image under some function. -/
theorem exists_map {α : Type} [Inhabited α] : ∀ (ts : List ℕ) (xs : List α), ts.Nodup →
    xs.length = ts.length → ∃ f : ℕ → α, xs = ts.map f
  | [], [], _, _ => ⟨fun _ => default, rfl⟩
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | t :: ts, x :: xs, hn, h => by
    obtain ⟨h1, h2⟩ := List.nodup_cons.1 hn
    obtain ⟨f, hf⟩ := exists_map ts xs h2 (by simpa using h)
    refine ⟨fun z => if z = t then x else f z, ?_⟩
    rw [List.map_cons, if_pos rfl, hf]
    congr 1
    refine List.map_congr_left fun z hz => ?_
    have hne : z ≠ t := fun e => h1 (by rw [← e]; exact hz)
    rw [if_neg hne]

/-- The frame's cut for the first switch, off the place's laid rounds, is the two declared rounds at
which FixedLaw.lean's fixed_switch speaks (j = 0), where each declared round has its list of oracle
messages. -/
theorem cutS_first (rds : List Fmt.DeclaredRound) (os : List (List VerifiableInference.Desc.Oracle))
    (stages : List Fmt.M1.Stage) (k : ℕ) (h : rds.length ≤ os.length) :
    cutS ((rds.zip os).drop 1) k =
      (rds.drop (H2K.FixedBefore.foldStart 1 stages 0 + 1 + k)).take 2 := by
  unfold cutS H2K.FixedBefore.foldStart
  rw [List.drop_drop, List.map_take, List.map_drop, List.map_fst_zip h]
  congr 2
  simp
  omega

/-- The declared openings of the frame's cut are opensOf's. -/
theorem opensOf_cut (p : P12) (k : ℕ) :
    (cutS ((((H2U.roundsOfNums p.nums).getD []).zip p.oracles).drop 1) k).flatMap (·.opens) =
      opensOf p k := by
  unfold cutS opensOf
  rw [List.flatMap_map]

/-- What gpOk's yes holds: the plain data are made, and every clause says yes. -/
theorem gpOk_inv (p : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (row : GroupRow) (L : GroupLayout) (hs : p.nums.stages = a :: rest)
    (hp : t.pass = .claim row L) (hok : gpOk p t = true) :
    ∃ D, gpOf p t a L = some D ∧ ok (gpL p a row D) = true := by
  unfold gpOk gpAll at hok
  rw [hs, hp] at hok
  dsimp only at hok
  cases hD : gpOf p t a L with
  | none =>
    rw [hD] at hok
    cases hok
  | some D =>
    rw [hD] at hok
    exact ⟨D, rfl, hok⟩

/-- The clauses' yes at the plain data D gives what the law's top asks that is public or the
record's, at the first stage. t: the record behind the batching (row, L pass). The typed group and
its public data are made of the plain data that gpOf makes by code. letters: rad (the members'
radii: no clause reads them) · dM, dF (the written rounds that sent the trees), with the reading's
two premises on them. a.h ≤ a.k is pubOk's clause "h ≤ k". -/
theorem first_at (p : P12) (t : T12) (a : Fmt.M1.Stage) (row : GroupRow) (L : GroupLayout)
    (D : Plain) (hD : gpOf p t a L = some D) (hok : ok (gpL p a row D) = true) (hhk : a.h ≤ a.k)
    (rad : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD)
    (hd : ∀ i, PQ.posN (dM i).tree = 2 ^ (D.mems.get i).tsh.logN)
    (hdF : PQ.posN dF.tree = 2 ^ D.fresh.tsh.logN) :
    (gpP (good_of_ok p a row D hok) rad dM dF).Pub p.nums.firstTree ∧
    (∃ src, OpensAre p.nums.firstTree
      (cutS ((((H2U.roundsOfNums p.nums).getD []).zip p.oracles).drop 1)
        ((sg a).h + (sg a).g)) (gpP (good_of_ok p a row D hok) rad dM dF) src) ∧
    row.kept = #[] ∧ (gpP (good_of_ok p a row D hok) rad dM dF).LayG L ∧
    ∀ (cu : IoppStage) (id : ℕ) (st : Statement) (book : TreeBook), stageAt p 0 a = some cu →
      MaskCase p t (ioppFoldShape cu L) id st book →
      PartsP (gpP (good_of_ok p a row D hok) rad dM dF) st book id := by
  have h := good_of_ok p a row D hok
  have hm := made_of p t a L D hD
  refine ⟨gp_pub h hm rad dM dF hd hdF, ?_, h.rowKept, gp_lay h hm rad dM dF,
    fun cu id st book hcu hc => ?_⟩
  · have hk : (sg a).h + (sg a).g = a.k := by
      show a.h + (a.k - a.h) = a.k
      omega
    have hinc : D.ts.Pairwise (· < ·) := by
      rw [hm.ts]
      exact Fmt.listOf_incr _
    have hlen : (D.opens.map (·.2)).length = D.ts.length := by
      have := congrArg List.length h.keys
      simpa using this
    obtain ⟨src, hsrc⟩ := exists_map D.ts (D.opens.map (·.2))
      (hinc.imp fun hlt => Nat.ne_of_lt hlt) hlen
    refine ⟨src, ?_⟩
    unfold OpensAre
    rw [hk, opensOf_cut, ← hm.opens]
    show D.opens.map (fun o => (o.1.tree - p.nums.firstTree, o.2)) =
      D.ts.map fun z => (keyAt p.nums.firstTree D.book z, src z)
    have e1 : D.opens.map (fun o => (o.1.tree - p.nums.firstTree, o.2)) =
        (D.opens.map (·.1.tree - p.nums.firstTree)).zip (D.opens.map (·.2)) := by
      rw [List.zip_map']
    have e2 : (D.ts.map fun z => (keyAt p.nums.firstTree D.book z, src z)) =
        (D.ts.map (keyAt p.nums.firstTree D.book)).zip (D.ts.map src) := by
      rw [List.zip_map']
    rw [e1, e2, h.keys, hsrc]
  · obtain ⟨cu', hcu', he⟩ := hm.ent
    obtain rfl : cu' = cu := Option.some.inj (hcu'.symm.trans hcu)
    have e := (entered_of_case p t cu' L id st book hc).symm.trans he
    obtain ⟨rfl, e'⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
    exact gp_parts h hm rad dM dF

/-- The same from gpOk p t = true: out of the two above. -/
theorem first_of_ok (p : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (row : GroupRow) (L : GroupLayout) (hs : p.nums.stages = a :: rest)
    (hp : t.pass = .claim row L) (hok : gpOk p t = true) (hhk : a.h ≤ a.k) (rad : ℕ → ℕ) :
    ∃ (D : Plain) (h : Good p.nums.firstTree a row D),
      ∀ (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD),
        (∀ i, PQ.posN (dM i).tree = 2 ^ (D.mems.get i).tsh.logN) →
        PQ.posN dF.tree = 2 ^ D.fresh.tsh.logN →
        (gpP h rad dM dF).Pub p.nums.firstTree ∧
        (∃ src, OpensAre p.nums.firstTree
          (cutS ((((H2U.roundsOfNums p.nums).getD []).zip p.oracles).drop 1)
            ((sg a).h + (sg a).g)) (gpP h rad dM dF) src) ∧
        row.kept = #[] ∧ (gpP h rad dM dF).LayG L ∧
        ∀ (cu : IoppStage) (id : ℕ) (st : Statement) (book : TreeBook), stageAt p 0 a = some cu →
          MaskCase p t (ioppFoldShape cu L) id st book → PartsP (gpP h rad dM dF) st book id := by
  obtain ⟨D, hD, hk⟩ := gpOk_inv p t a rest row L hs hp hok
  exact ⟨D, good_of_ok p a row D hk, fun dM dF hd hdF =>
    first_at p t a row L D hD hk hhk rad dM dF hd hdF⟩

/-- The two cuts held together: OpensAre at the tie's own cut (the frame's cutS of the place's laid
rounds) gives, under fixedOk, that every tree off which the first stage's words are read has a
source that is fixed in front of the stage's first draw. (src t: the source that the plan declares
at t's rank among the opened trees: nothing here ties it to the tree at the book's place t but rank,
key, depth and width; FirstCut.lean's labelsOk adds the label uncut.) -/
theorem first_fixed_cut (p : P12) (hfx : H2K.FixedBefore.fixedOk p = true)
    (rds : List Fmt.DeclaredRound) (hr : H2U.roundsOfNums p.nums = some rds) (a b : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hs : p.nums.stages = a :: b :: rest)
    (hlen : rds.length ≤ p.oracles.length) {s : Sg} {G : Gp s} (P : GpData G)
    (src : ℕ → Fmt.TreeSource)
    (hO : OpensAre p.nums.firstTree
      (cutS ((((H2U.roundsOfNums p.nums).getD []).zip p.oracles).drop 1) a.k) P src) :
    ∀ t ∈ P.ts, ∀ sh : Fmt.Shape, H2K.FixedBefore.Fixed p.place.chain p.before p.nums rds
      (H2K.FixedBefore.foldStart 1 p.nums.stages 0 + 1) (sh, src t) := by
  rw [hr, Option.getD_some, cutS_first rds _ p.nums.stages a.k hlen] at hO
  exact first_fixed p hfx rds hr a (by rw [hs]; simp) (by rw [hs]; rfl) P src hO

end H2K.First
