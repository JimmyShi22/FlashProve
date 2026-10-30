-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-

Johnson/RunOne/KeyThree.lean: THE KEY FILE's FIRST CHAIN AT THE FROZEN F_K: rng.0.rows: THE EIGHTH OF THE TEN: ITS LAW «Keeps» (border 14 → 15) FROM ONE NAMED FACT ON THE GROUND's addRowsP.
  RowsGround s d'   WHAT THE GROUND's addRowsP s.d s.grp s.base.rows.flatten = some d' IS ASKED TO GIVE: the tables' sizes, the oracle messages and the codes are not turned · the ranges' group behind is the group in front with the rows laid behind its own, its test not begun as before
  RowsYes           rng.0.rows' yes: the state behind is the state in front with d := d', RowsGround, and just as many lists of rows as lookups: OWED BY WHOEVER HAS THE GROUND's LAW
  (Where this and lean/THEOREM.md differ, the page holds.)
  ReadsO G          a premise on the reading: of the chain's state it reads the statement's oracle messages, the book and the codes alone (the book and the codes are let in, on a reader's word: a reading that finds a tenant's message by the book could not meet the elder form)
  facts_14 · rides_14 · sh_14_15 · keeps_rngRows   **PROVED** from these
Nothing on soundness.
-/
import Johnson.RunOne.KeyTenKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction)

section
variable {S : Type} (K : KPlan) (X : KReaders S)

theorem groupB_some (s : S) (ir : Bool) (n : Nat) (h : groupB X s ir n = true) :
    ∃ g Gr, X.grpB s = some g ∧ (X.st s).groups[g]? = some Gr ∧ Gr.inRun = ir ∧ Gr.rows.size = n := by
  unfold groupB at h
  cases hg : X.grpB s with
  | none => rw [hg] at h; cases h
  | some g =>
    rw [hg] at h
    cases hG : (X.st s).groups[g]? with
    | none => simp [hG] at h
    | some Gr =>
      simp [hG] at h
      exact ⟨g, Gr, rfl, hG, h.1, h.2⟩

theorem groupB_of (s : S) (ir : Bool) (n g : Nat) (Gr : OnBytes.Group) (hg : X.grpB s = some g) (hG : (X.st s).groups[g]? = some Gr) (h1 : Gr.inRun = ir) (h2 : Gr.rows.size = n) :
    groupB X s ir n = true := by
  unfold groupB
  simp [hg, hG, h1, h2]

theorem sentB_some (s : S) (k o : Nat) (x : OnBytes.Oracle) (h : sentB K X s k = true) (ho : K.orc k = some o) (hx : (X.st s).oracles[o]? = some x) :
    x.sampled = true ∧ x.sampleRows.size ≠ 0 := by
  unfold sentB at h
  simp [ho, hx] at h
  exact ⟨h.1, fun h0 => h.2 (Array.eq_empty_of_size_eq_zero h0)⟩

theorem doneB_rows (n d : Nat) (s : S) (h : doneB K X n d s = true) (l : Nat) (hl : l < n) (hd : l < d) : ∃ rs, X.rowsAt s l = some rs ∧ rs ≠ [] := by
  unfold doneB at h
  have h1 := List.all_eq_true.1 h l (List.mem_range.2 hl)
  rw [if_pos hd] at h1
  have h2 := (Bool.and_eq_true_iff.1 h1).1
  cases hr : X.rowsAt s l with
  | none => rw [hr] at h2; cases h2
  | some rs =>
    rw [hr] at h2
    refine ⟨rs, rfl, ?_⟩
    intro h0
    subst h0
    cases h2

theorem sentB_congr (s s' : S) (k : Nat) (h : (X.st s').oracles = (X.st s).oracles) : sentB K X s' k = sentB K X s k := by
  unfold sentB; rw [h]

end

end VerifiableInference.Desc.Key

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup)
open VerifiableInference.Desc.Key (Xi)
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction)

/-- Whether a table is there, and its bits, hang on the codes and on the messages' shapes alone. -/
theorem hasBits_of (A B : Statement) (hc : B.codes = A.codes) (ho : ∀ o : Nat, (B.oracles[o]?).map (·.shape) = (A.oracles[o]?).map (·.shape)) (o : Nat) (part : Part) :
    B.has o part = A.has o part ∧ B.tableBits o part = A.tableBits o part := by
  have q := ho o
  unfold Statement.has Statement.tableBits Statement.rowBits Statement.placeBits
  rw [hc]
  cases hA : A.oracles[o]? with
  | none =>
    rw [hA] at q
    cases hB : B.oracles[o]? with
    | none => exact ⟨rfl, rfl⟩
    | some x => rw [hB] at q; cases q
  | some x =>
    rw [hA] at q
    cases hB : B.oracles[o]? with
    | none => rw [hB] at q; cases q
    | some x' =>
      rw [hB] at q
      have e : x'.shape = x.shape := Option.some.inj q
      simp only [e]
      exact ⟨trivial, trivial⟩

/-- The fence on a row's content (Means.RowIn) reads the statement through these two alone. -/
theorem rowIn_of (A B : Statement) (h : ∀ o part, B.has o part = A.has o part ∧ B.tableBits o part = A.tableBits o part) (Gr : Group) (r : Row) (hr : Means.RowIn A Gr r) : Means.RowIn B Gr r := by
  have hp : ∀ o part v i, Blk.placeOk B Gr o part v i = Blk.placeOk A Gr o part v i := fun o part v i => by
    unfold Blk.placeOk; rw [(h o part).1, (h o part).2]
  refine ⟨fun t ht => ?_, fun u hu => ?_, fun w hw => ?_, fun f hf => ?_⟩
  · rw [hp]; exact hr.terms t ht
  · rw [hp, (h _ _).2]; exact hr.units u hu
  · rw [hp, (h _ _).2]; exact hr.runs w hw
  · rw [hp, (h _ _).2]; exact hr.forms f hf

/-- **SampleIn rides** where the codes, and of every message its shape and its sample rows, stay. -/
theorem sampleIn_of (A B : Statement) (hc : B.codes = A.codes) (ho : ∀ o : Nat, (B.oracles[o]?).map (fun x => (x.shape, x.sampleRows)) = (A.oracles[o]?).map fun x => (x.shape, x.sampleRows))
    (o : Nat) (h : KeyRows23.SampleIn A o) : KeyRows23.SampleIn B o := by
  intro y' hy' r hr
  have q := ho o
  rw [hy'] at q
  cases hA : A.oracles[o]? with
  | none => rw [hA] at q; cases q
  | some y =>
    rw [hA] at q
    have e : (y'.shape, y'.sampleRows) = (y.shape, y.sampleRows) := Option.some.inj q
    have e2 : y'.sampleRows = y.sampleRows := congrArg Prod.snd e
    refine rowIn_of A B (hasBits_of A B hc fun o' => ?_) _ r (h y hA r (e2 ▸ hr))
    have q' := congrArg (Option.map Prod.fst) (ho o')
    simpa [Option.map_map, Function.comp_def] using q'

/-- The state with another statement's part. -/
def withD (s : FirstState) (d' : PlainState) : FirstState := { s with d := d' }

/-- **What the ground's addRowsP is asked to give.** -/
structure RowsGround (s : FirstState) (d' : PlainState) : Prop where
  tables : SameTables d'.st s.d.st
  oracles : d'.st.oracles = s.d.st.oracles
  codes : d'.st.codes = s.d.st.codes
  book : d'.book = s.d.book
  gsize : d'.st.groups.size = s.d.st.groups.size
  order : Means.InOrder s.d.st → Means.InOrder d'.st
  group : ∀ Gr, s.d.st.groups[s.grp]? = some Gr → ∃ Gr', d'.st.groups[s.grp]? = some Gr' ∧ Gr'.rows.toList = Gr.rows.toList ++ s.base.rows.flatten ∧ Gr'.inRun = Gr.inRun ∧ Gr'.members = Gr.members
  /-- the count of roots is not turned -/
  roots : d'.roots = s.d.roots

/-- **rng.0.rows' yes.** -/
def RowsYes (b : Block FirstState Claim) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ d', s' = withD s d' ∧ RowsGround s d' ∧ s.base.rows.length = 2

section
variable {Cells M Smp Rec : Type} (G : Reading (Xi × FirstState) Cells M Smp Rec) (one : OneTime)

/-- **A premise on the reading**: of the chain's state it reads the statement's oracle messages alone. -/
def ReadsO : Prop := ∀ (p : Xi) (s s' : FirstState), s'.d.st.oracles = s.d.st.oracles → s'.d.book = s.d.book → s'.d.st.codes = s.d.st.codes → SamePins G (p, s) (p, s')

variable (s : FirstState) (d' : PlainState)

/-- What the book-keeping in front of rng.0.rows says, taken apart. -/
theorem c_14_parts (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 14 s = true) :
    sentB (plan₁ one) (readers₁ one) s 0 = true ∧ sentB (plan₁ one) (readers₁ one) s 1 = true ∧ ((book₁ one).ledger s).isNone = true ∧ (!(book₁ one).heard s) = true ∧ doneB (plan₁ one) (readers₁ one) 2 2 s = true ∧ groupB (readers₁ one) s false 0 = true ∧ ((readers₁ one).pile s).isNone = true ∧ (!sentB (plan₁ one) (readers₁ one) s 2) = true := by
  have h' : (sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 && ((book₁ one).ledger s).isNone && !(book₁ one).heard s && doneB (plan₁ one) (readers₁ one) 2 2 s && (groupB (readers₁ one) s false 0 && ((readers₁ one).pile s).isNone && !sentB (plan₁ one) (readers₁ one) s 2)) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, ⟨f, g⟩, i⟩ := h'
  exact ⟨a, b, c, d, e, f, g, i⟩

theorem grp_eq (g : Nat) (h : (readers₁ one).grpB s = some g) : g = s.grp := by
  have h' : (if s.grp == noId then none else some s.grp) = some g := h
  split at h'
  · cases h'
  · exact (Option.some.inj h').symm

/-- **KeyLaws.RowsLaidFacts around rng.0.rows.** -/
theorem facts_14 (H : RowsGround s d') (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 14 s = true) : RowsLaidFacts (plan₁ one) (readers₁ one) 2 s (withD s d') := by
  obtain ⟨_, b, _, _, e, f, _, _⟩ := c_14_parts one s h
  obtain ⟨g₀, G₀, hg₀, hG₀, _, _⟩ := groupB_some (readers₁ one) s false 0 f
  have eg := grp_eq one s g₀ hg₀
  subst eg
  obtain ⟨Gr', hGr', hrows, _, _⟩ := H.group G₀ hG₀
  refine ⟨H.tables, fun o _ => ?_, fun l hl => doneB_rows (plan₁ one) (readers₁ one) 2 2 s e l hl hl, ?_, fun o x ho hx => sentB_some (plan₁ one) (readers₁ one) s 1 o x b ho hx⟩
  · show d'.st.oracles[o]? = s.d.st.oracles[o]?
    rw [H.oracles]
  · intro l rs g Gr _ hrs hg hG r hr
    have eg' := grp_eq one s g hg
    subst eg'
    have e2 : Gr = Gr' := Option.some.inj ((show d'.st.groups[s.grp]? = some Gr from hG).symm.trans hGr')
    subst e2
    rw [hrows]
    exact List.mem_append_right _ (List.mem_flatten.2 ⟨rs, List.mem_of_getElem? (show s.base.rows[l]? = some rs from hrs), hr⟩)

/-- The table's row at rng.0.rows, by its three lists. -/
def row14 : KRow := { ins := (List.range 2).map KItem.rows ++ [.srow 1], outs := [.grows], ctx := [.pin 1] }

/-- **KeyQuiet.Rides around rng.0.rows**, at what rides. -/
theorem rides_14 (hG : ReadsO G) (H : RowsGround s d') (p : Xi) : Rides G (readers₁ one) ((open₁ 2 14).filter fun i => !row14.ins.contains i) p s (withD s d') :=
  { marked := rfl, pins := hG p s (withD s d') H.oracles H.book H.codes
    stmt := fun _ => ⟨H.tables, fun o x' h => ⟨x', (show s.d.st.oracles[o]? = some x' from H.oracles ▸ h), rfl, rfl⟩⟩
    rows := fun _ _ => rfl, keys := fun _ _ => rfl, pile := fun _ => rfl
    grp := fun h => absurd h (by decide) }

/-- **The book-keeping's step across rng.0.rows.** -/
theorem c_14_15 (H : RowsGround s d') (h2 : s.base.rows.length = 2) (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 14 s = true) : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 15 (withD s d') = true := by
  obtain ⟨a, b, c, d, e, f, g, i⟩ := c_14_parts one s h
  obtain ⟨g₀, G₀, hg₀, hG₀, hir, hsz⟩ := groupB_some (readers₁ one) s false 0 f
  have eg := grp_eq one s g₀ hg₀
  subst eg
  obtain ⟨Gr', hGr', hrows, hir', _⟩ := H.group G₀ hG₀
  obtain ⟨r₀, hr₀, hne⟩ := doneB_rows (plan₁ one) (readers₁ one) 2 2 s e 0 (by decide) (by decide)
  have hcount : Gr'.rows.size = rowsCount (readers₁ one) 2 s := by
    show Gr'.rows.toList.length = _
    rw [hrows, List.length_append]
    have z : G₀.rows.toList.length = 0 := hsz
    rw [z]
    match hb : s.base.rows, h2 with
    | [x₀, x₁], _ =>
      have q : rowsCount (readers₁ one) 2 s = x₀.length + x₁.length := by
        simp [rowsCount, readers₁, KeyReaders.readers, hb, List.range_succ]
      rw [q]
      simp
  have hpos : (rowsCount (readers₁ one) 2 s != 0) = true := by
    match hb : s.base.rows, h2 with
    | [x₀, x₁], _ =>
      have q : rowsCount (readers₁ one) 2 s = x₀.length + x₁.length := by
        simp [rowsCount, readers₁, KeyReaders.readers, hb, List.range_succ]
      have e0 : r₀ = x₀ := by
        have : s.base.rows[0]? = some r₀ := hr₀
        rw [hb] at this
        exact (Option.some.inj this).symm
      subst e0
      rw [q]
      have hz : r₀.length ≠ 0 := fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
      have hp : r₀.length + x₁.length ≠ 0 := by omega
      exact bne_iff_ne.2 hp
  have hgB : groupB (readers₁ one) (withD s d') false (rowsCount (readers₁ one) 2 s) = true :=
    groupB_of (readers₁ one) (withD s d') false _ s.grp Gr' hg₀ hGr' (hir'.trans hir) hcount
  have a' : sentB (plan₁ one) (readers₁ one) (withD s d') 0 = true := (sentB_congr (plan₁ one) (readers₁ one) s (withD s d') 0 H.oracles).trans a
  have b' : sentB (plan₁ one) (readers₁ one) (withD s d') 1 = true := (sentB_congr (plan₁ one) (readers₁ one) s (withD s d') 1 H.oracles).trans b
  have i' : (!sentB (plan₁ one) (readers₁ one) (withD s d') 2) = true := by rw [sentB_congr (plan₁ one) (readers₁ one) s (withD s d') 2 H.oracles]; exact i
  show (sentB (plan₁ one) (readers₁ one) (withD s d') 0 && sentB (plan₁ one) (readers₁ one) (withD s d') 1 && ((book₁ one).ledger s).isNone && !(book₁ one).heard s && doneB (plan₁ one) (readers₁ one) 2 2 s &&
    (groupB (readers₁ one) (withD s d') false (rowsCount (readers₁ one) 2 s) && rowsCount (readers₁ one) 2 s != 0 && ((readers₁ one).pile s).isNone && !sentB (plan₁ one) (readers₁ one) (withD s d') 2)) = true
  rw [a', b', c, d, e, hgB, hpos, g, i']; rfl

/-- The ties' step across rng.0.rows. -/
theorem tA_14_15 (H : RowsGround s d') (h : tiesA one 14 s = true) : tiesA one 15 (withD s d') = true := by
  have h' : ((lookupsOf one).length == 2 && one.ranges.messageId == 1 && decide (s.d.st.codes = one.codes) && s.idx == 0 && ((s.d.st.groups[s.grp]?).any (fun G => G.members.toList == [1]) && s.rider == some 2 && (s.d.st.oracles[2]?).any fun x => !x.sampled && !x.spentAsMask)) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, ⟨e, f⟩, g⟩ := h'
  have e' : (d'.st.groups[s.grp]?).any (fun G => G.members.toList == [1]) = true := by
    cases hG : s.d.st.groups[s.grp]? with
    | none => rw [hG] at e; cases e
    | some Gr =>
      rw [hG] at e
      obtain ⟨Gr', hGr', _, _, hm⟩ := H.group Gr hG
      rw [hGr']
      show (Gr'.members.toList == [1]) = true
      rw [hm]
      exact e
  show ((lookupsOf one).length == 2 && one.ranges.messageId == 1 && decide (d'.st.codes = one.codes) && s.idx == 0 && ((d'.st.groups[s.grp]?).any (fun G => G.members.toList == [1]) && s.rider == some 2 && (d'.st.oracles[2]?).any fun x => !x.sampled && !x.spentAsMask)) = true
  rw [H.codes, H.oracles, a, b, c, d, e', f, g]; rfl

theorem sz_14_15 (H : RowsGround s d') : sizesB one 15 (withD s d') = sizesB one 14 s := by
  show (d'.st.oracles.size == 3 && d'.st.groups.size == 1 && d'.book.trees.size == 2 && d'.book.place.size == d'.st.oracles.size && true && true && true && true) = (s.d.st.oracles.size == 3 && s.d.st.groups.size == 1 && s.d.book.trees.size == 2 && s.d.book.place.size == s.d.st.oracles.size && true && true && true && true)
  rw [H.oracles, H.gsize, H.book]

theorem t_14_15 (H : RowsGround s d') (h : ties₁ one 14 s = true) : ties₁ one 15 (withD s d') = true := by
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.1 (show (tiesA one 14 s && moreB 14 s && sizesB one 14 s) = true from h)
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h12
  exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨tA_14_15 one s d' H h1, (show moreB 15 (withD s d') = moreB 14 s from by unfold moreB; rw [show (withD s d').d.book = s.d.book from H.book, show (withD s d').d.roots = s.d.roots from H.roots]; rfl).trans h2⟩, (sz_14_15 one s d' H).trans h3⟩

theorem sh_14_15 (H : RowsGround s d') (h2 : s.base.rows.length = 2) (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 14 s = true) : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 15 (withD s d') = true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 14 15 s (withD s d') (t_14_15 one s d' H) (c_14_15 one s d' H h2) h

end

section
variable {XI Cells M Smp Rec W : Type} {C : CK} (F : FileDescription XI) (Fr : Frame) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where)
  (one : OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)

/-- Border 14 → 15, where the number of lookups is given. -/
theorem keeps_rngRows_two (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hb : RowsYes b)
    (hn : n₁ one = 2) (hbase : ∀ j ∈ pinned (open₁ 2 14), (at_ j).1 < pc.base) (hcoll : CollCell coll) (hG : ReadsO G) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 14) (on₁ F Fr G at_ one R coll 15) (L₁ F Fr G at_ one R 14) (L₁ F Fr G at_ one R 15) pc.err := by
  have key := rngRows_keeps F Fr G at_ (plan₁ one) R (readers₁ one) (fun _ _ _ => False) (formsAt (plan₁ one) R k3At₁ one.ranges) (worthAt (plan₁ one) R k3At₁ one.ranges one.codes)
    (fun _ _ _ _ _ => False) pc (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 14) (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 15) (free₁ F G at_ one R coll 14) (free₁ F G at_ one R coll 15) 2 row14 rfl rfl rfl (open₁ 2 14) (by decide) (by decide) (by decide) hbase (fun _ => rfl)
    (fun a rs gs a' h hs => by
      obtain ⟨e, hd⟩ := hheld a rs gs a' h
      obtain ⟨d', e', H, h2⟩ := hb _ rs gs _ hd
      obtain ⟨p, s⟩ := a
      obtain ⟨p', s'⟩ := a'
      have e1 : p' = p := e
      have e2 : s' = withD s d' := e'
      subst e1
      subst e2
      exact ⟨rfl, rides_14 G one s d' hG H p', facts_14 one s d' H ((shape₁_iff _ _ _ _ _ _ _).1 hs).2, sh_14_15 one s d' H h2 hs,
        fun y y' Hy hf => free₁_step F G at_ one R coll 14 15 p' s (withD s d') y y' (hG p' s (withD s d') H.oracles H.book H.codes) hcoll Hy H.book (by decide) (by omega) (fun h18 => absurd h18 (by decide))
          (fun o => sampleIn_of s.d.st d'.st H.codes (fun o' => by rw [H.oracles]) o) H.order hf⟩)
  have ho : stepOpen (open₁ 2 14) row14 = open₁ 2 15 := by decide
  rw [ho] at key
  unfold on₁ L₁ R₁
  rw [hn]
  exact key

/-- **Border 14 → 15: rng.0.rows.** -/
theorem keeps_rngRows (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hb : RowsYes b)
    (hbase : ∀ j ∈ pinned (open₁ 2 14), (at_ j).1 < pc.base) (hcoll : CollCell coll) (hG : ReadsO G) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 14) (on₁ F Fr G at_ one R coll 15) (L₁ F Fr G at_ one R 14) (L₁ F Fr G at_ one R 15) pc.err := by
  intro a ha
  exact keeps_rngRows_two F Fr G at_ one R coll pc b hheld hb (on₁_two F Fr G at_ one R coll 14 a ha) hbase hcoll hG a ha

end

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.facts_14
#print axioms Johnson.RunOne.KeyRows1.sh_14_15
#print axioms Johnson.RunOne.KeyRows1.keeps_rngRows
