-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/MadeRows.lean: THE FIVE SORTS OF ROWS THAT A CODE SWITCH BETWEEN TWO
SEGMENTS LAYS, EACH WITH PARTS THAT FIT; SO EVERY MADE ROW PASSES THE GROUND's WHOLE TEST ON A NEW
OPEN ROW: its seven clauses on the row's make (`makeClauses`, Returns/RowFit.lean) and its one on
values (`padClause`, Inner/PadsWords.lean). Statements and proofs.

  `kind_fold`, `kind_restE`, `kind_restF`, `kind_addKept`   building a row keeps its kind
  `lift_room`       two inequalities between the sizes, behind the program's test on the target
  `fits_message`    the generator's message tensor, as a form
  `fit_lift`, `old_bits`   a form on the old main row's message, carried to g; that message's index
                    bits
  `place_vars`, `fit_foldKept`, `carried_eq`   tools for the mask rows and the carried row
  `fit_main`, `fit_keptGen`, `fit_mask`, `fit_sample`, `fit_carried`   the five sorts
  `madeRows_make`   every made row passes the seven clauses
  `valueClause_eq`, `madeRows_pass`   the clause on values under its two names; every made row
                    passes `rowL`

Limits. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.MadeFit
import Johnson.Desc.K2.Honest.Inner.PadsWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Slice (genMain genMask messageTensor symAtB)
open Johnson.Prover.Send (Rows)
open H2K.Lift (genKept keptFrom keptForm)
open VerifiableInference.Desc.First.K2Hands (placeOf carriedOf formOn sampleRow samplesOf)
open VerifiableInference.Desc.Ground (rowL ok)

/-- A loop whose steps keep a row's kind keeps it. -/
theorem kind_fold {α : Type} (f : OnBytes.Row → α → OnBytes.Row)
    (hf : ∀ r a, (f r a).kind = r.kind) : ∀ (l : List α) (r : OnBytes.Row),
    (l.foldl f r).kind = r.kind
  | [], _ => rfl
  | a :: l, r => by rw [List.foldl_cons, kind_fold f hf l, hf]

theorem kind_restE (r : OnBytes.Row) (g : Nat) (part : Part) (l : List SwitchPiece)
    (coeff : Array E) : (switchAddRestE r g part l coeff).kind = r.kind :=
  kind_fold (fun (r : OnBytes.Row) (p : SwitchPiece) =>
    r.addRun g part p.first p.step (.own (coeff.extract p.start p.stop))) (fun _ _ => rfl) l r

theorem kind_restF (r : OnBytes.Row) (g : Nat) (part : Part) (l : List SwitchPiece)
    (coeff : Array F) : (switchAddRestF r g part l coeff).kind = r.kind :=
  kind_fold (fun (r : OnBytes.Row) (p : SwitchPiece) =>
    r.addRun g part p.first p.step (.stretch coeff p.start (p.stop - p.start))) (fun _ _ => rfl) l r

theorem kind_addKept (Fr : SwitchFrame) (r : OnBytes.Row) (k : KeptPlace) (c : Form) :
    (Fr.addKept r k c).kind = r.kind :=
  kind_fold (fun (r : OnBytes.Row) (p : PadPlace × Nat) =>
    (r.addUnit k.anew .main p.1.index (negE (c.entry p.1.index))).addUnit Fr.g Fr.restPart
      (Fr.places.get (k.oldPadAt + p.2)) (c.entry p.1.index)) (fun _ _ => rfl) k.pad.zipIdx
    (r.addForm k.anew c)

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows} {G : Group}

/-- Two inequalities between the sizes. -/
theorem lift_room (A : AtSwitch S old T g anew W V) :
    T.main.bits ≤ (S.codes.base.getD old.code default).logEll ∧
      (S.codes.base.getD old.code default).logEll + (switchRowBits T .main - T.main.bits) ≤
        switchRowBits T .main + (S.codes.base.getD T.shape.code default).logEll := by
  have F := A.target
  obtain ⟨_, _, hM⟩ := SwitchPlaces.of_check A.check
  rw [F.mainPart] at hM
  have hpow : 2 ^ (S.codes.base.getD old.code default).logEll =
      (S.codes.base.getD old.code default).ell := F.power.2
  have hb : T.main.bits ≤ (S.codes.base.getD old.code default).logEll :=
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (by rw [hpow]; exact F.mainSmall)
  have hR : T.main.bits ≤ switchRowBits T .main :=
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (by unfold RowCut.Fits at hM; omega)
  have hn : (S.codes.base.getD old.code default).logEll ≤
      (S.codes.base.getD T.shape.code default).logEll + T.main.bits :=
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (by
      rw [hpow, Nat.pow_add]
      exact Nat.le_trans F.mainRoom
        (Nat.mul_le_mul_right _ (SwitchPlaces.le_two_pow_ceilLog2' _)))
  exact ⟨hb, by omega⟩

/-- The generator's message tensor, as a form. -/
theorem fits_message (c : OnBytes.Code) (x : Nat) (hpow : c.ell = 2 ^ c.logEll)
    (h63 : c.logEll ≤ 63) : Own.formFits (Form.ofTensor (messageTensor c x)) c.logEll = true := by
  have hv : (messageTensor c x).pairs.length = c.logEll :=
    OnBytes.Slice.vars_messageTensor c x hpow
  refine (Own.formFits_iff _ _).2 ⟨fun v hv' => ?_, fun e he => absurd he List.not_mem_nil⟩
  have e : v = messageTensor c x := List.mem_singleton.1 hv'
  rw [e]
  exact ⟨hv, inOrder_plain _ rfl (by rw [hv]; exact h63)⟩

/-- **A form on the old main row's message, carried to g.** -/
theorem fit_lift (A : AtSwitch S old T g anew W V) (M : MakeFits S old T g anew G) (c : Form)
    (hc : Own.formFits c (S.codes.base.getD old.code default).logEll = true) :
    PartsFit S G (({} : OnBytes.Row).addForm g
      (switchLift c (S.codes.base.getD old.code default).logEll T.main (switchRowBits T .main)
        (switchRowBits T .main + (S.codes.base.getD T.shape.code default).logEll))) := by
  obtain ⟨hb, hv⟩ := lift_room A
  refine partsFit_empty.addForm _ _ (place_of M.gIn (size_g A) 0 (Nat.two_pow_pos _)) ?_
  rw [(bits_of_size (size_g A)).1]
  exact formFits_lift c _ T.main _ _ hc hb hv M.bitsG

/-- The old main code's message has at most 63 index bits. -/
theorem old_bits (A : AtSwitch S old T g anew W V) (M : MakeFits S old T g anew G) :
    (S.codes.base.getD old.code default).logEll ≤ 63 := by
  have := (lift_room A).2
  have := M.bitsG
  omega

/-- **The main row's generator row.** -/
theorem fit_main (A : AtSwitch S old T g anew W V) (M : MakeFits S old T g anew G)
    {Fr : SwitchFrame} (hFr : switchFrame S old T g anew = some Fr) (x : Nat) (t : E) :
    PartsFit S G (genMain Fr x t) := by
  have I := frameIs hFr
  have hT := (VerifiableInference.Desc.First.K2Hands.frame_more S old T g anew Fr hFr).1
  unfold genMain
  rw [hT, I.gIs, I.restPart, A.restMain, I.places, I.parts, I.code, I.mainCut, I.rowBits,
    I.tableBits]
  exact (fit_stretchF A M
    (fit_lift A M _ (fits_message _ x A.target.power.2.symm (old_bits A M))) _ _ _
    (by rw [OnBytes.Slice.size_generatorTail]) (mainTail_fits A)).dress _ _

/-- **A kept row's generator row.** -/
theorem fit_keptGen (A : AtSwitch S old T g anew W V) (M : MakeFits S old T g anew G)
    {Fr : SwitchFrame} (hFr : switchFrame S old T g anew = some Fr) (a : Nat) (k : KeptPlace)
    (hk : Fr.kept[a]? = some k) (b : Nat) (hb : b < k.rows) (x : Nat) (t : E) :
    PartsFit S G (genKept Fr k b (((Fr.kept.take a).map (·.rows)).sum + b) x t) := by
  have I := frameIs hFr
  obtain ⟨s, _, hs, _, _, _, _, _, e5, _, _⟩ := kept_at hFr a k hk
  have hT := VerifiableInference.Desc.First.K2Hands.tailPieces_of_frame S old T g anew Fr hFr a k hk
    (rows_count A hFr) b hb
  have hT' : Fr.keptTail.getD (((Fr.kept.take a).map (·.rows)).sum + b) [] =
      switchPieces Fr.places
        (Fr.parts.keptTailAt.getD (((Fr.kept.take a).map (·.rows)).sum + b) 0) Fr.code.r := hT
  have h63 := M.bitsKept s (List.mem_of_getElem? hs)
  have hform : Own.formFits (keptForm Fr k b x)
      (k.rowBits + (S.codes.base.getD old.code default).logEll) = true := by
    unfold keptForm
    rw [I.code, Nat.add_comm]
    exact formFits_insert _ _ 0 k.rowBits b
      (fits_message _ x A.target.power.2.symm (old_bits A M)) (Nat.zero_le _)
      (by rw [e5]; omega)
  have hbase := fit_addKept A M hFr a k hk partsFit_empty (keptForm Fr k b x) hform
  unfold genKept
  rw [hT', I.gIs, I.restPart, A.restMain, I.places, I.parts, I.code]
  exact (fit_stretchF A M hbase _ _ _ (by rw [OnBytes.Slice.size_generatorTail])
    (keptTail_fits A _ (keptNo_lt A hFr a k hk b hb))).dress _ _

/-- **A stored sample row, carried over.** -/
theorem fit_sample (A : AtSwitch S old T g anew W V) (M : MakeFits S old T g anew G)
    {Fr : SwitchFrame} (hFr : switchFrame S old T g anew = some Fr) (a : Nat) (k : KeptPlace)
    (hk : Fr.kept[a]? = some k) (sample : OnBytes.Row) (hm : sample ∈ samplesOf S k) :
    PartsFit S G (sampleRow Fr k sample) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, e6, _⟩ := kept_at hFr a k hk
  have hin := List.mem_of_getElem? e6
  have hst := A.fits.stored k.old hin sample hm
  obtain ⟨h1, h2⟩ := M.stored k.old hin sample hm
  have hb := (bits_of_size (size_old A hFr a k hk)).1
  rw [hb] at h1 h2
  exact (fit_addKept A M hFr a k hk partsFit_empty (formOn sample)
    (formFits_on sample _ (Array.eq_empty_of_size_eq_zero hst.1)
      (Array.eq_empty_of_size_eq_zero hst.2) h1 h2)).aim _

/-- A tensor with as many variables as a main table has index bits fits its place. -/
theorem place_vars {S : Statement} {G : Group} {o n vars : Nat}
    (hc : G.members.contains o = true) (hs : OnBytes.Means.tableSize S o .main = 2 ^ n)
    (hv : vars = n) : Own.placeFits S G o .main vars 0 = true := by
  obtain ⟨h1, h2⟩ := bits_of_size hs
  unfold Own.placeFits
  rw [hc, h2, h1, hv, decide_eq_true (Nat.two_pow_pos n)]
  simp

/-- **A mask row's generator row.** -/
theorem fit_mask (A : AtSwitch S old T g anew W V) (M : MakeFits S old T g anew G)
    {Fr : SwitchFrame} (hFr : switchFrame S old T g anew = some Fr)
    (hlog : (S.codes.mask.getD old.maskCode default).logN ≤ 32) (j : Nat) (hj : j < 2) (x : Nat)
    (t : E) : PartsFit S G (genMask Fr x j t) := by
  have I := frameIs hFr
  obtain ⟨xo, hxo, hxs⟩ := Option.map_eq_some_iff.1 A.seated.carrying
  have Mk := VerifiableInference.Desc.First.K2Hands.maskAt_of_check S old T g anew Fr hFr A.check
    xo hxo hxs (by rw [I.zk]; exact hlog) j hj
  have hrb := restBits_eq A hFr
  have inner : PartsFit S G (match Fr.box.getD j none with
      | some b =>
        ({} : OnBytes.Row).add Fr.g Fr.restPart
          (switchOnBox b (messageTensor Fr.zk (shortPosition Fr.zk.logN x)) Fr.zk.logEll
            Fr.restBits)
      | none =>
        switchAddRestF {} Fr.g Fr.restPart (Fr.maskMessage.getD j [])
          (generatorMessage Fr.zk (shortPosition Fr.zk.logN x))) := by
    split
    · rename_i b hb
      obtain ⟨_, hpow, hle, _⟩ := Mk.box b hb
      have h63 := M.bitsG
      have hv : (messageTensor Fr.zk (shortPosition Fr.zk.logN x)).pairs.length = Fr.zk.logEll :=
        OnBytes.Slice.vars_messageTensor _ _ hpow
      have s1 := inOrder_insert _ (inOrder_plain _ rfl (by rw [hv]; omega)) 0 b.shift
        (b.start % 2 ^ b.shift) (Nat.zero_le _) (by rw [hv]; omega)
      have s2 := inOrder_insert _ s1.2 (b.shift + Fr.zk.logEll)
        (Fr.restBits - b.shift - Fr.zk.logEll) (b.start / 2 ^ (b.shift + Fr.zk.logEll))
        (by rw [s1.1, hv]; omega) (by rw [s1.1, hv]; omega)
      rw [I.gIs, I.restPart, A.restMain]
      refine partsFit_empty.add _ _ _ ((Own.tensorInOrder_iff _).2 s2.2)
        (place_vars M.gIn (size_g A) ?_)
      show (switchOnBox b _ _ _).pairs.length = _
      unfold switchOnBox
      rw [s2.1, s1.1, hv, ← hrb]
      omega
    · rename_i hb
      rw [Mk.msg hb, I.gIs, I.restPart, A.restMain, I.places, I.parts, I.zk]
      exact fit_stretchF A M partsFit_empty _ _ _
        (by rw [OnBytes.Slice.size_generatorMessage]) (mask_fits A j hj).1
  unfold genMask
  rw [Mk.tail]
  have outer := fun (r : OnBytes.Row) (h : PartsFit S G r) =>
    fit_stretchF A M h ((switchParts S old).maskTailAt.getD j 0)
      (S.codes.mask.getD old.maskCode default).r
      (generatorTail (S.codes.mask.getD old.maskCode default)
        (shortPosition (S.codes.mask.getD old.maskCode default).logN x))
      (by rw [OnBytes.Slice.size_generatorTail]) (mask_fits A j hj).2
  have h := outer _ inner
  rw [← I.zk, ← I.parts, ← I.places] at h
  have hg : Fr.g = g := I.gIs
  have hp : Fr.restPart = .main := by rw [I.restPart, A.restMain]
  rw [← hg, ← hp] at h
  exact h.dress _ _

/-- Forms on kept members' tables, carried over one after the other. -/
theorem fit_foldKept (A : AtSwitch S old T g anew W V) (M : MakeFits S old T g anew G)
    {Fr : SwitchFrame} (hFr : switchFrame S old T g anew = some Fr) :
    ∀ (l : List (KeptForm × KeptPlace)) (r : OnBytes.Row), PartsFit S G r →
      (∀ x ∈ l, ∃ a : Nat, Fr.kept[a]? = some x.2 ∧ Own.formFits x.1.c
        (x.2.rowBits + (S.codes.base.getD old.code default).logEll) = true) →
      PartsFit S G (l.foldl (fun (r : OnBytes.Row) x => Fr.addKept r x.2 x.1.c) r)
  | [], _, h, _ => h
  | x :: l, r, h, hl => by
    obtain ⟨a, hk, hc⟩ := hl x (List.mem_cons_self ..)
    rw [List.foldl_cons]
    exact fit_foldKept A M hFr l _ (fit_addKept A M hFr a x.2 hk h x.1.c hc)
      fun y hy => hl y (List.mem_cons_of_mem _ hy)

/-- The carried row, written out at two mask rows. -/
theorem carried_eq (A : AtSwitch S old T g anew W V) (Fr : SwitchFrame) (ks : List KeptPlace) :
    carriedOf Fr old ks =
      { switchAddRestE (switchAddRestE
        ((old.kept.toList.zip ks).foldl (fun (r : OnBytes.Row) x => Fr.addKept r x.2 x.1.c)
          (({} : OnBytes.Row).addForm Fr.g
            (switchLift old.c Fr.code.logEll Fr.mainCut Fr.rowBits Fr.tableBits)))
        Fr.g Fr.restPart
        (switchPieces Fr.places (Fr.parts.maskAt.getD 0 0) (old.d.getD 0 #[]).size)
        (old.d.getD 0 #[]))
        Fr.g Fr.restPart
        (switchPieces Fr.places (Fr.parts.maskAt.getD 1 0) (old.d.getD 1 #[]).size)
        (old.d.getD 1 #[]) with target := old.target } := by
  unfold carriedOf
  rw [A.target.masks]
  rfl

/-- **The carried row.** -/
theorem fit_carried (A : AtSwitch S old T g anew W V) (M : MakeFits S old T g anew G)
    {Fr : SwitchFrame} (hFr : switchFrame S old T g anew = some Fr) (ks : List KeptPlace)
    (hks : old.kept.toList.mapM (placeOf Fr) = some ks) :
    PartsFit S G (carriedOf Fr old ks) ∧ (carriedOf Fr old ks).kind ≠ .sample := by
  have I := frameIs hFr
  obtain ⟨_, hmem⟩ := Lists.mapM_mem _ _ _ hks
  have f0 := (mask_fits A 0 (by omega)).1
  have f1 := (mask_fits A 1 (by omega)).1
  have d0 := A.fits.d0
  have d1 := A.fits.d1
  have hbase := fit_foldKept A M hFr (old.kept.toList.zip ks) _ (fit_lift A M old.c M.claimMain)
    (by
      intro x hx
      obtain ⟨ho, a, hk⟩ := place_at x.1 x.2 (hmem x hx)
      refine ⟨a, hk, ?_⟩
      have h := M.claimKept x.1 (List.of_mem_zip hx).1
      rw [← ho, (bits_of_size (size_old A hFr a x.2 hk)).1] at h
      exact h)
  have h := fit_stretchE A M (fit_stretchE A M hbase ((switchParts S old).maskAt.getD 0 0)
    (old.d.getD 0 #[]) (by omega)) ((switchParts S old).maskAt.getD 1 0) (old.d.getD 1 #[])
    (by omega)
  rw [carried_eq A Fr ks]
  constructor
  · rw [I.gIs, I.restPart, A.restMain, I.places, I.parts, I.code, I.mainCut, I.rowBits,
      I.tableBits]
    exact h.aim _
  · show (switchAddRestE _ _ _ _ _).kind ≠ .sample
    rw [kind_restE, kind_restE,
      kind_fold (fun (r : OnBytes.Row) (x : KeptForm × KeptPlace) => Fr.addKept r x.2 x.1.c)
        (fun r x => kind_addKept Fr r x.2 x.1.c)]
    exact fun e => by cases e

/-- **Every made row passes the seven clauses on a row's make.** -/
theorem madeRows_make (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) (pos : Positions) (y : Array E) (rows : List OnBytes.Row)
    (check : switchTargetCheck S old T = true) (restMain : T.rest.part = .main)
    (fits : OldFits S old) (keptPos : ∀ k ∈ T.kept.toList, 0 < k.shape.mainRows)
    (seated : SeatedAt S old T g anew) (lengths : S.codes.lengthsOk = true)
    (hlogZ : (S.codes.mask.getD old.maskCode default).logN ≤ 32)
    (hrows : Own.swRows S old T g anew pos y = some rows)
    (grp : Nat) (G : Group) (hG : S.groups[grp]? = some G) (hrun : G.inRun = false)
    (M : MakeFits S old T g anew G) : ∀ r ∈ rows, makeClauses S grp r = true := by
  intro r hr
  have A := atPublic check restMain fits keptPos seated lengths
  obtain ⟨Fr, carried, L⟩ := VerifiableInference.Desc.First.K2Hands.laid_of
    (show switchRows S old T g anew pos y = some rows from hrows)
  have hFr := L.frame
  have hm := A.target.masks
  rw [L.rows, List.cons_append, List.mem_cons, List.mem_append] at hr
  rcases hr with hr | hr | hr
  · obtain ⟨ks, hks, hc⟩ :=
      (VerifiableInference.Desc.First.K2Hands.switchCarried_iff Fr old carried).1 L.claim
    obtain ⟨h1, h2⟩ := fit_carried A M hFr ks hks
    rw [hr, hc]
    exact makeClauses_of hG hrun h2 h1
  · obtain ⟨k, hk, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨sample, hsm, rfl⟩ := List.mem_map.1 hr
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 hk
    refine makeClauses_of hG hrun ?_ (fit_sample A M hFr a k ha sample hsm)
    show (Fr.addKept {} k (formOn sample)).kind ≠ .sample
    rw [kind_addKept]
    exact fun e => by cases e
  · obtain ⟨x, _, hr⟩ := List.mem_flatMap.1 hr
    rw [H2K.Lift.switchGenerators_all, List.cons_append, List.mem_cons, List.mem_append] at hr
    rcases hr with hr | hr | hr
    · rw [hr]
      exact makeClauses_of hG hrun (fun e => by cases e) (fit_main A M hFr x _)
    · obtain ⟨a, k, b, hk, hb, hr⟩ := mem_keptFrom Fr x _ r Fr.kept 0 hr
      rw [hr]
      simp only [Nat.zero_add]
      exact makeClauses_of hG hrun (fun e => by cases e) (fit_keptGen A M hFr a k hk b hb x _)
    · obtain ⟨jj, hjj, hr⟩ := List.mem_map.1 hr
      have hj2 : jj < 2 := by
        have := List.mem_range.1 hjj
        omega
      rw [← hr]
      exact makeClauses_of hG hrun (fun e => by cases e) (fit_mask A M hFr hlogZ jj hj2 x _)

/-- The clause on values, under its two names. -/
theorem valueClause_eq (S : Statement) (grp : Nat) (row : OnBytes.Row) :
    valueClause S grp row = padClause S grp row := by
  unfold valueClause ok
  show (padClause S grp row && true) = _
  rw [Bool.and_true]

/-- **Every made row passes the ground's whole test on a new open row.** -/
theorem madeRows_pass (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) (pos : Positions) (y : Array E) (rows : List OnBytes.Row)
    (check : switchTargetCheck S old T = true) (restMain : T.rest.part = .main)
    (fits : OldFits S old) (keptPos : ∀ k ∈ T.kept.toList, 0 < k.shape.mainRows)
    (seated : SeatedAt S old T g anew) (lengths : S.codes.lengthsOk = true)
    (hlogC : (S.codes.base.getD old.code default).logN ≤ 32)
    (hlogZ : (S.codes.mask.getD old.maskCode default).logN ≤ 32)
    (hx : ∀ x ∈ pos.all.toList, x < 2 ^ (S.codes.base.getD old.code default).logN)
    (hrows : Own.swRows S old T g anew pos y = some rows)
    (stored : PadsStored S T g anew) (grp : Nat) (G : Group) (hG : S.groups[grp]? = some G)
    (hrun : G.inRun = false) (M : MakeFits S old T g anew G)
    (hmem : ∀ o ∈ G.members.toList, o = g ∨ ∃ a k, T.kept[a]? = some k ∧ o = anew.getD a noId) :
    ∀ r ∈ rows, ok (rowL S grp r) = true := by
  intro r hr
  rw [rowL_cut, valueClause_eq,
    madeRows_make S old T g anew pos y rows check restMain fits keptPos seated lengths hlogZ hrows
      grp G hG hrun M r hr,
    padClause_made S old T g anew pos y rows check restMain fits keptPos seated lengths hlogC hlogZ
      hx hrows stored grp G hG hmem r hr]
  rfl

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.madeRows_make
#print axioms VerifiableInference.Desc.K2.Honest.Returns.madeRows_pass
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fit_main
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fit_keptGen
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fit_sample
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fit_mask
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fit_carried
