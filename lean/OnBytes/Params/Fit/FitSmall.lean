-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/FitSmall.lean: every routine of OnBytes/Params/Planner.lean that plans a block
keeps the property Small of entries (FitCalc.lean in this folder), under caps on the setting and on
the routine's own arguments.

Main names (each says Keeps s Small of the routine named; S : SetCap s where it is written):
  without a cap: keeps_bat, keeps_batSigma, keeps_split, keeps_pscRounds, keeps_psc, keeps_line,
    keeps_shift, keeps_lkp, keeps_treeLevels, keeps_productTree, keeps_batt, keeps_foldFrom,
    keeps_foldRounds, keeps_seal; general in the property: keeps_analysis, keeps_listOfGroups,
    keeps_sampleErrors, keeps_listed, keeps_table, keeps_positions S.
  for a round of one's own: keeps_elems, keeps_one, keeps_poss, keeps_silent, with nf_… for the 28
    names that the planner writes.
  keeps_zero, keeps_join: the variables are at most 2 ^ 40.
  keeps_lookup S x: no cap on x: the routine's own tests bound mu and d.
  keeps_rng S columns: columns * 276 ≤ 2 ^ 45. 276 bounds the combinations of a smallness test
    under SetCap (256 for the target, 20 for the instances: combinations_le); 2 ^ 45 is the cap of
    Small on the matrix entries that a round draws.
  keeps_send S: every cube has at most 2 ^ 32 variables; at most two roots.
  keeps_fold: at most two roots. keeps_loc S: logN ≤ 64 of the group. keeps_base S: both.
    keeps_cs S: these and the cube. StageOk x: logN ≤ 64 and the cube, asked of every stage (the
    routine reads the cube of the second and later ones); keeps_stages S, keeps_iopp S.
  TableOk T, LinOk x; keeps_record, keeps_linFirst S, keeps_linShared S, keeps_link S.
Limits: of a routine that refuses nothing is said. That the caps hold at the sizes which the planner
derives from public files is not said here (SetCapOf.lean, FitCaps.lean, KeyCaps.lean in this
folder). No value of SetCap, TableOk, LinOk or StageOk is shown here.
The program does not import this file.

-/
import OnBytes.Params.Fit.FitCalc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-! ## The names -/

theorem nf_send_seed : NameOk "SEND seed" := ⟨by decide +kernel, by decide⟩
theorem nf_send_answer : NameOk "SEND answer" := ⟨by decide +kernel, by decide⟩
theorem nf_bat : NameOk "BAT" := ⟨by decide +kernel, by decide⟩
theorem nf_bat_sigma : NameOk "BAT-sigma" := ⟨by decide +kernel, by decide⟩
theorem nf_split : NameOk "SPLIT" := ⟨by decide +kernel, by decide⟩
theorem nf_psc_round : NameOk "PSC round" := ⟨by decide +kernel, by decide⟩
theorem nf_psc_epsilon : NameOk "PSC epsilon" := ⟨by decide +kernel, by decide⟩
theorem nf_psc_y : NameOk "PSC Y" := ⟨by decide +kernel, by decide⟩
theorem nf_psc_values : NameOk "PSC values" := ⟨by decide +kernel, by decide⟩
theorem nf_zero : NameOk "ZERO" := ⟨by decide +kernel, by decide⟩
theorem nf_line : NameOk "LINE" := ⟨by decide +kernel, by decide⟩
theorem nf_lkp_shift : NameOk "LKP shift" := ⟨by decide +kernel, by decide⟩
theorem nf_join : NameOk "JOIN" := ⟨by decide +kernel, by decide⟩
theorem nf_lkp : NameOk "LKP" := ⟨by decide +kernel, by decide⟩
theorem nf_rng : NameOk "RNG" := ⟨by decide +kernel, by decide⟩
theorem nf_fold_round : NameOk "FOLD round" := ⟨by decide +kernel, by decide⟩
theorem nf_fold_epsilon : NameOk "FOLD epsilon" := ⟨by decide +kernel, by decide⟩
theorem nf_loc : NameOk "LOC" := ⟨by decide +kernel, by decide⟩
theorem nf_cs : NameOk "CS" := ⟨by decide +kernel, by decide⟩
theorem nf_base_lambda : NameOk "BASE lambda" := ⟨by decide +kernel, by decide⟩
theorem nf_base : NameOk "BASE" := ⟨by decide +kernel, by decide⟩
theorem nf_record : NameOk "RECORD" := ⟨by decide +kernel, by decide⟩
theorem nf_seal : NameOk "SEAL" := ⟨by decide +kernel, by decide⟩
theorem nf_lin_point : NameOk "LIN point" := ⟨by decide +kernel, by decide⟩
theorem nf_lin_zeta : NameOk "LIN zeta" := ⟨by decide +kernel, by decide⟩
theorem nf_link_point : NameOk "LINK point" := ⟨by decide +kernel, by decide⟩
theorem nf_link : NameOk "LINK" := ⟨by decide +kernel, by decide⟩
theorem nf_link_phi : NameOk "LINK phi" := ⟨by decide +kernel, by decide⟩

/-! ## Small at an entry -/

/-- Small of the entry that close writes, from its name, the open roots and its draws. -/
theorem small_said {name : String} (hn : NameOk name) {m : Nat} (hm : m ≤ 2)
    {d : Draws} (h1 : d.logN ≤ 64) (h2 : d.poss ≤ 2 ^ 40) (h3 : d.drawE ≤ 2 ^ 40)
    (h4 : d.drawNZ ≤ 2 ^ 40) (h5 : d.trits ≤ 2 ^ 45) (work msg answers : Nat) : Small
      { name, work := work, msg := msg, roots := m, answers := answers, drawE := d.drawE,
        drawNZ := d.drawNZ, poss := d.poss, logN := d.logN, trits := d.trits, rows := d.rows } :=
  ⟨hn, hm, h1, h2, h3, h4, h5⟩

/-- Small of a silent round's entry. -/
theorem small_silent {name : String} (hn : NameOk name) (msg answers : Nat) :
    Small { name, msg := msg, answers := answers } :=
  ⟨hn, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

section
variable {s : Setting} {m : Nat}

/-- close, with draws of elements alone, at most 2 ^ 40. -/
theorem keeps_elems {name : String} (hn : NameOk name) (hm : m ≤ 2) (why : ErrorKind)
    (error : Bound) (d : Draws) (h0 : d.logN = 0 ∧ d.poss = 0 ∧ d.trits = 0)
    (h3 : d.drawE ≤ 2 ^ 40) (h4 : d.drawNZ ≤ 2 ^ 40) :
    KeepsAt s Small m 0 (close name why error d) :=
  keeps_close name why error d (small_said hn hm (by rw [h0.1]; exact Nat.zero_le _)
    (by rw [h0.2.1]; exact Nat.zero_le _) h3 h4 (by rw [h0.2.2]; exact Nat.zero_le _))

/-- close, with at most one element drawn. -/
theorem keeps_one {name : String} (hn : NameOk name) (hm : m ≤ 2) (why : ErrorKind)
    (error : Bound) (d : Draws) (h0 : d.logN = 0 ∧ d.poss = 0 ∧ d.trits = 0)
    (h3 : d.drawE ≤ 1) (h4 : d.drawNZ ≤ 1) : KeepsAt s Small m 0 (close name why error d) :=
  keeps_elems hn hm why error d h0 (h3.trans (by norm_num)) (h4.trans (by norm_num))

/-- close, with positions. -/
theorem keeps_poss {name : String} (hn : NameOk name) (hm : m ≤ 2) (why : ErrorKind)
    (error : Bound) (d : Draws) (h1 : d.logN ≤ 64) (h2 : d.poss ≤ 2 ^ 40) (h3 : d.drawE ≤ 1)
    (h4 : d.drawNZ = 0) (h5 : d.trits = 0) : KeepsAt s Small m 0 (close name why error d) :=
  keeps_close name why error d (small_said hn hm h1 h2 (h3.trans (by norm_num))
    (by rw [h4]; exact Nat.zero_le _) (by rw [h5]; exact Nat.zero_le _))

theorem keeps_silent {name : String} (hn : NameOk name) :
    KeepsAt s Small m 0 (closeNone name) := keeps_closeNone name (small_silent hn)

/-! ## Routines that add no round: for every property -/

variable {Q : Fmt.Entry → Prop}

theorem keeps_analysis (g : GroupSize) : KeepsAt s Q m m (planAnalysis g) :=
  keeps_bind keeps_setting fun _ _ => keeps_bind (keeps_needs _ _) fun _ _ => keeps_pure trivial

theorem keeps_listOfGroups : ∀ gs : List GroupSize, KeepsAt s Q m m (listOfGroups gs)
  | [] => keeps_pure trivial
  | g :: gs => keeps_bind (keeps_analysis g) fun _ _ =>
      keeps_bind (keeps_listOfGroups gs) fun _ _ => keeps_pure trivial

theorem keeps_sampleErrors (s' : Setting) :
    ∀ (o : List SampleSize) (e : Bound), KeepsAt s Q m m (sampleErrors s' o e)
  | [], _ => keeps_pure trivial
  | x :: xs, _ => keeps_bind (keeps_listOfGroups x.groups) fun _ _ => keeps_sampleErrors s' xs _

theorem keeps_listed (logN t : Nat) : KeepsAt s Q m m (planListed logN t) :=
  keeps_bind keeps_setting fun _ _ => (keeps_needs _ _).any

theorem keeps_table (T : TableSize) : KeepsAt s Q m m (planTable T) :=
  keeps_bind keeps_setting fun _ _ => keeps_bind (keeps_needs _ _) fun _ _ => keeps_pure trivial

/-- The number of positions is at most 2 ^ 32: by SetCap.pos. -/
theorem keeps_positions (S : SetCap s) (agree extra : Bound) :
    KeepsAt s Q m m (planPositions agree extra) (· ≤ 2 ^ 32) :=
  keeps_bind keeps_setting fun a ha => keeps_bind keeps_scope fun c _ =>
    keeps_pure (by rw [ha]; exact S.pos c agree extra)

end

section
variable {s : Setting}

/-! ## Sending, batching, splitting -/

theorem cube_le (B : Nat) : ∀ (o : List SampleSize) (c : Nat), c ≤ B →
    (∀ x ∈ o, x.cubeBits ≤ B) → o.foldl (fun c x => max c x.cubeBits) c ≤ B
  | [], _, h, _ => h
  | a :: t, c, h, ho => cube_le B t (max c a.cubeBits) (max_le h (ho a List.mem_cons_self))
      fun x hx => ho x (List.mem_cons_of_mem _ hx)

/-- samples * (cube + 1) is small. -/
theorem seed_le (S : SetCap s) {cube : Nat} (h : cube ≤ 2 ^ 32) :
    s.samples * (cube + 1) ≤ 2 ^ 40 :=
  (Nat.mul_le_mul S.samples (Nat.succ_le_succ h)).trans (by norm_num)

theorem samples_le (S : SetCap s) : s.samples ≤ 2 ^ 40 := S.samples.trans (by norm_num)

theorem keeps_send (S : SetCap s) (o : List SampleSize) (roots : Nat) (answerRound : Bool)
    (ho : ∀ x ∈ o, x.cubeBits ≤ 2 ^ 32) (hr : roots ≤ 2) :
    Keeps s Small (planSend o roots answerRound) := by
  unfold planSend
  refine keeps_bind keeps_setting fun s' hs' => ?_
  subst hs'
  refine keeps_bind (keeps_roots roots) fun _ _ => ?_
  refine keeps_bind (keeps_sampleErrors _ _ _) fun e _ => ?_
  refine keeps_bind (keeps_elems nf_send_seed (by omega) _ _ _ ⟨rfl, rfl, rfl⟩
    (seed_le S (cube_le _ o 0 (Nat.zero_le _) ho)) (samples_le S)) fun _ _ => ?_
  refine keeps_bind (keeps_answers _) fun _ _ => ?_
  exact keeps_ite (fun _ => keeps_silent nf_send_answer) fun _ => keeps_pure trivial

theorem keeps_bat (groups : List GroupSize) (rows : Nat) : Keeps s Small (planBat groups rows) :=
  keeps_bind keeps_setting fun _ _ => keeps_bind (keeps_listOfGroups groups) fun _ _ =>
    keeps_one nf_bat (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ (Nat.le_refl _) (Nat.zero_le _)

theorem keeps_batSigma (rows : Nat) : Keeps s Small (planBatSigma rows) :=
  keeps_bind keeps_setting fun _ _ =>
    keeps_one nf_bat_sigma (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ (Nat.le_refl _) (Nat.zero_le _)

theorem keeps_split : Keeps s Small planSplit :=
  keeps_bind (keeps_scalars 1) fun _ _ => keeps_silent nf_split

/-! ## Sumchecks, product trees, lookups -/

theorem keeps_pscRounds (s' : Setting) : ∀ l : List Nat, Keeps s Small (planPscRounds s' l)
  | [] => keeps_pure trivial
  | g :: gs => keeps_bind (keeps_scalars (g - 1)) fun _ _ =>
      keeps_bind (keeps_one nf_psc_round (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ (Nat.le_refl _)
        (Nat.zero_le _)) fun _ _ => keeps_pscRounds s' gs

theorem keeps_psc (x : PscSize) : Keeps s Small (planPsc x) := by
  unfold planPsc
  refine keeps_bind keeps_setting fun s' _ => keeps_bind (keeps_scalars 1) fun _ _ => ?_
  refine keeps_bind (keeps_one nf_psc_epsilon (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩
    (Nat.le_refl _) (Nat.zero_le _)) fun _ _ => ?_
  refine keeps_bind (keeps_pscRounds s' x.degree) fun _ _ => ?_
  refine keeps_ite (fun _ => ?_) fun _ => keeps_pure trivial
  refine keeps_bind (keeps_scalars _) fun _ _ => ?_
  refine keeps_bind (keeps_one nf_psc_y (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ (Nat.le_refl _)
    (Nat.le_refl _)) fun _ _ => ?_
  exact keeps_bind (keeps_scalars _) fun _ _ => keeps_silent nf_psc_values

theorem keeps_zero (v : Nat) (hv : v ≤ 2 ^ 40) : Keeps s Small (planZero v) :=
  keeps_bind keeps_setting fun _ _ =>
    keeps_elems nf_zero (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ hv (Nat.zero_le _)

theorem keeps_line : Keeps s Small planLine :=
  keeps_bind keeps_setting fun _ _ =>
    keeps_one nf_line (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ (Nat.le_refl _) (Nat.zero_le _)

theorem keeps_shift (n : Nat) : Keeps s Small (planShift n) :=
  keeps_bind keeps_setting fun _ _ =>
    keeps_one nf_lkp_shift (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ (Nat.le_refl _) (Nat.zero_le _)

theorem keeps_join (v : Nat) (hv : v ≤ 2 ^ 40) : Keeps s Small (planJoin v) :=
  keeps_bind keeps_setting fun _ _ =>
    keeps_elems nf_join (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ hv (Nat.zero_le _)

theorem keeps_lkp (k : Nat) : Keeps s Small (planLkp k) :=
  keeps_bind keeps_setting fun _ _ =>
    keeps_one nf_lkp (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ (Nat.le_refl _) (Nat.zero_le _)

theorem keeps_treeLevels (more : Nat) : ∀ fuel l, Keeps s Small (planTreeLevels more fuel l)
  | 0, _ => keeps_pure trivial
  | fuel + 1, l => keeps_bind (keeps_psc _) fun _ _ => keeps_bind keeps_line fun _ _ =>
      keeps_treeLevels more fuel (l + 1)

theorem keeps_productTree (levels more : Nat) : Keeps s Small (planProductTree levels more) :=
  keeps_treeLevels more levels 0

theorem keeps_batt (rows kCol : Nat) : Keeps s Small (planBatt rows kCol) :=
  keeps_bind (keeps_batSigma rows) fun _ _ => keeps_psc _

/-- From the lookup's own test: d is below 64. -/
theorem d_lt {p d w : Nat} (hp : p < 2 ^ 64) (hw : 2 ≤ w) (h : 2 ^ d * (2 ^ w - 1) < p) :
    d < 64 := by
  by_contra hd
  have h1 : 2 ^ 64 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have h3 : 1 ≤ 2 ^ w - 1 := by
    have : (4 : Nat) ≤ 2 ^ w := h2
    omega
  have h4 : 2 ^ d * 1 ≤ 2 ^ d * (2 ^ w - 1) := Nat.mul_le_mul_left _ h3
  omega

theorem keeps_lookup (S : SetCap s) (x : LookupSize) : Keeps s Small (planLookup x) := by
  unfold planLookup
  refine keeps_bind keeps_setting fun s' hs' => ?_
  subst hs'
  refine keeps_bind (keeps_needs _ _) fun _ h1 => keeps_bind (keeps_needs _ _) fun _ h2 => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  have hd := d_lt S.p h1.1.2 h2.2
  have h70 : x.mu + x.d ≤ 2 ^ 40 := by
    have h6 := h1.1.1.2
    have : x.mu + x.d ≤ 70 := by omega
    exact this.trans (by norm_num)
  refine keeps_ite (fun _ => keeps_bind (keeps_shift _) fun _ _ => ?_) fun _ =>
    keeps_bind (R := fun _ => True) (keeps_pure trivial) fun _ _ => ?_
  all_goals
    refine keeps_bind (keeps_one nf_lkp (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ (Nat.le_refl _)
      (Nat.zero_le _)) fun _ _ => ?_
    refine keeps_bind (keeps_psc _) fun _ _ => ?_
    refine keeps_bind (keeps_times (keeps_psc _) _) fun _ _ => ?_
    refine keeps_bind (keeps_times (keeps_psc _) _) fun _ _ => ?_
    refine keeps_bind (keeps_join _ (h1.1.1.2.trans (by norm_num))) fun _ _ => ?_
    refine keeps_bind (keeps_forEach _ fun v _ => keeps_productTree v 0) fun _ _ => ?_
    refine keeps_bind (keeps_productTree _ _) fun _ _ => keeps_bind (keeps_psc _) fun _ _ => ?_
    exact keeps_bind (keeps_zero _ h70) fun _ _ => keeps_psc _

/-- The combinations of the smallness test are at most 276. -/
theorem combinations_le (S : SetCap s) (c : Scope) : rngCombinations s c ≤ 276 := by
  unfold rngCombinations
  have h1 := S.target
  have h2 := S.inst
  split <;> omega

theorem keeps_rng (S : SetCap s) (columns : Nat) (hc : columns * 276 ≤ 2 ^ 45) :
    Keeps s Small (planRng columns) := by
  unfold planRng
  refine keeps_bind keeps_setting fun s' hs' => keeps_bind keeps_scope fun c _ => ?_
  subst hs'
  refine keeps_bind (keeps_needs _ _) fun _ _ => ?_
  exact keeps_close _ _ _ _ (small_said nf_rng (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    (Nat.zero_le _) (Nat.zero_le _)
    ((Nat.mul_le_mul_left columns (combinations_le S c)).trans hc))

/-! ## Folding, positions, the proximity test -/

theorem keeps_foldFrom (s' : Setting) (g : GroupSize) (a : Analysis) :
    ∀ fuel j, Keeps s Small (planFoldFrom s' g a fuel j)
  | 0, _ => keeps_pure trivial
  | fuel + 1, j => keeps_bind (keeps_scalars 2) fun _ _ =>
      keeps_bind (keeps_one nf_fold_round (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ (Nat.le_refl _)
        (Nat.zero_le _)) fun _ _ => keeps_foldFrom s' g a fuel (j + 1)

theorem keeps_foldRounds (g : GroupSize) : Keeps s Small (planFoldRounds g) :=
  keeps_bind (keeps_analysis g) fun _ _ => keeps_bind keeps_setting fun _ _ =>
    keeps_foldFrom _ g _ g.k 1

theorem keeps_fold (g : GroupSize) (roots : Nat) (hr : roots ≤ 2) :
    Keeps s Small (planFold g roots) := by
  unfold planFold
  refine keeps_bind keeps_setting fun _ _ => keeps_bind (keeps_analysis g) fun _ _ => ?_
  refine keeps_bind (keeps_roots roots) fun _ _ => keeps_bind (keeps_scalars 1) fun _ _ => ?_
  exact keeps_bind (keeps_one nf_fold_epsilon (by omega) _ _ _ ⟨rfl, rfl, rfl⟩ (Nat.le_refl _)
    (Nat.zero_le _)) fun _ _ => keeps_foldRounds g

theorem le40 {t : Nat} (h : t ≤ 2 ^ 32) : t ≤ 2 ^ 40 := h.trans (by norm_num)

theorem keeps_loc (S : SetCap s) (g : GroupSize) (hg : g.main.logN ≤ 64) :
    Keeps s Small (planLoc g) := by
  unfold planLoc
  refine keeps_bind (keeps_analysis g) fun a _ => ?_
  refine keeps_bind (keeps_positions S _ _) fun t ht => keeps_bind (keeps_needs _ _) fun _ _ => ?_
  refine keeps_bind (keeps_poss nf_loc (Nat.zero_le _) _ _ _ hg (le40 ht) (Nat.zero_le _) rfl
    rfl) fun _ _ => ?_
  exact keeps_bind (keeps_listed _ _) fun _ _ => keeps_pure trivial

theorem csPositions_le (S : SetCap s) (c : Scope) (agree : Bound) (list oldRows symbols : Nat) :
    ∀ fuel t, t ≤ 2 ^ 32 → csPositions s c agree list oldRows symbols fuel t ≤ 2 ^ 32
  | 0, _, h => h
  | fuel + 1, t, _ => by
    unfold csPositions
    dsimp only
    split
    · exact S.pos _ _ _
    · exact csPositions_le S c agree list oldRows symbols fuel _ (S.pos _ _ _)

theorem keeps_cs (S : SetCap s) (source target : GroupSize) (cubeBits oldRows symbols roots : Nat)
    (hg : source.main.logN ≤ 64) (hc : cubeBits ≤ 2 ^ 32) (hr : roots ≤ 2) :
    Keeps s Small (planCs source target cubeBits oldRows symbols roots) := by
  unfold planCs
  refine keeps_bind keeps_setting fun s' hs' => ?_
  subst hs'
  refine keeps_bind (keeps_analysis source) fun a _ => ?_
  refine keeps_bind (keeps_analysis target) fun next _ => ?_
  refine keeps_bind (keeps_send S _ roots false (fun x hx => ?_) hr) fun _ _ => ?_
  · rw [List.mem_singleton.1 hx]
    exact hc
  refine keeps_bind keeps_scope fun c _ => keeps_bind (keeps_needs _ _) fun _ _ => ?_
  refine keeps_bind (keeps_poss nf_cs (Nat.zero_le _) _ _ _ hg
    (le40 (csPositions_le S c _ _ _ _ 64 0 (Nat.zero_le _))) (Nat.le_refl _) rfl rfl)
    fun _ _ => ?_
  exact keeps_bind (keeps_listed _ _) fun _ _ => keeps_pure trivial

theorem keeps_base (S : SetCap s) (g : GroupSize) (roots : Nat) (hg : g.main.logN ≤ 64)
    (hr : roots ≤ 2) : Keeps s Small (planBase g roots) := by
  unfold planBase
  refine keeps_bind keeps_setting fun _ _ => keeps_bind (keeps_analysis g) fun a _ => ?_
  refine keeps_bind (keeps_roots roots) fun _ _ => keeps_bind (keeps_scalars 1) fun _ _ => ?_
  refine keeps_bind (keeps_one nf_base_lambda (by omega) _ _ _ ⟨rfl, rfl, rfl⟩ (Nat.le_refl _)
    (Nat.zero_le _)) fun _ _ => ?_
  refine keeps_bind (keeps_scalars _) fun _ _ => ?_
  refine keeps_bind (keeps_positions S _ _) fun t ht => keeps_bind (keeps_needs _ _) fun _ _ => ?_
  refine keeps_bind (keeps_poss nf_base (Nat.zero_le _) _ _ _ hg (le40 ht) (Nat.zero_le _) rfl
    rfl) fun _ _ => ?_
  exact keeps_bind (keeps_listed _ _) fun _ _ => keeps_pure trivial

/-- What a proximity test asks of a stage. -/
def StageOk (x : StageSize) : Prop := x.g.main.logN ≤ 64 ∧ stageCubeBits x.g ≤ 2 ^ 32

theorem keeps_stages (S : SetCap s) (fm : Nat) (ride : Bool) (hf : fm ≤ 2) :
    ∀ (first : Bool) (st : List StageSize), (∀ x ∈ st, StageOk x) →
      Keeps s Small (planStages fm ride first st)
  | first, x :: y :: rest, h => by
    unfold planStages
    have hx := h x List.mem_cons_self
    have hy := h y (List.mem_cons_of_mem _ List.mem_cons_self)
    refine keeps_bind (keeps_fold x.g _ ?_) fun _ _ => ?_
    · split
      · exact hf
      · split <;> omega
    refine keeps_bind (keeps_cs S x.g y.g _ 1 _ 1 hx.1 hy.2 (by omega)) fun t _ => ?_
    refine keeps_bind (keeps_needs _ _) fun _ _ => ?_
    exact keeps_stages S fm ride hf false (y :: rest) fun z hz => h z (List.mem_cons_of_mem _ hz)
  | _, [x], h => by
    unfold planStages
    refine keeps_bind (keeps_base S x.g _ (h x List.mem_cons_self).1 ?_) fun t _ =>
      (keeps_needs _ _).any
    split <;> omega
  | _, [], _ => by
    unfold planStages
    exact keeps_refuse _

theorem keeps_iopp (S : SetCap s) (st : List StageSize) (rows fm : Nat) (ride : Bool)
    (hst : ∀ x ∈ st, StageOk x) (hf : fm ≤ 2) : Keeps s Small (planIopp st rows fm ride) :=
  keeps_bind (keeps_needs _ _) fun _ _ => keeps_bind (keeps_bat _ rows) fun _ _ =>
    keeps_stages S fm ride hf true st hst

/-! ## The committed table -/

/-- What is asked of the table's sizes. -/
structure TableOk (T : TableSize) : Prop where
  logN : T.code.logN ≤ 64
  v : T.v ≤ 2 ^ 32
  ell : clog2 T.code.ell ≤ 2 ^ 32
  answers : T.answers ≤ 4

/-- What is asked of the sizes of the test on the table. -/
structure LinOk (x : LinSize) : Prop where
  w : x.w.cubeBits ≤ 2 ^ 32
  u : x.u.cubeBits ≤ 2 ^ 32
  omega : x.omega.cubeBits ≤ 2 ^ 32
  besideW : ∀ y ∈ x.besideW, y.cubeBits ≤ 2 ^ 32
  besideOmega : ∀ y ∈ x.besideOmega, y.cubeBits ≤ 2 ^ 32
  kLo : x.kLo ≤ 2 ^ 32
  rowsLog : x.rowsLog ≤ 2 ^ 32
  rootsW : x.rootsW ≤ 2
  rootsU : x.rootsU ≤ 2
  rootsOmega : x.rootsOmega ≤ 2

theorem keeps_record (T : TableSize) (hT : TableOk T) : Keeps s Small (planRecord T) := by
  unfold planRecord
  refine keeps_bind keeps_setting fun _ _ => keeps_bind (keeps_table T) fun _ _ => ?_
  refine keeps_bind keeps_scope fun _ _ => keeps_push _ ?_
  exact ⟨nf_record, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    (Nat.mul_le_mul hT.answers (Nat.succ_le_succ hT.ell)).trans (by norm_num),
    hT.answers.trans (by norm_num), Nat.zero_le _⟩

theorem keeps_seal : Keeps s Small planSeal :=
  keeps_one nf_seal (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ (Nat.zero_le _) (Nat.zero_le _)

theorem cons_cube {a : SampleSize} {l : List SampleSize} (ha : a.cubeBits ≤ 2 ^ 32)
    (hl : ∀ y ∈ l, y.cubeBits ≤ 2 ^ 32) : ∀ y ∈ a :: l, y.cubeBits ≤ 2 ^ 32 := by
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact ha
  · exact hl y hy

theorem keeps_linFirst (S : SetCap s) (x : LinSize) (hx : LinOk x) :
    Keeps s Small (planLinFirst x) :=
  keeps_send S _ _ true (cons_cube hx.w hx.besideW) hx.rootsW

theorem keeps_linShared (S : SetCap s) (T : TableSize) (x : LinSize) (hT : TableOk T)
    (hx : LinOk x) : Keeps s Small (planLinShared T x) := by
  unfold planLinShared
  refine keeps_bind keeps_setting fun _ _ => keeps_bind (keeps_table T) fun A _ => ?_
  refine keeps_bind (keeps_elems nf_lin_point (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ ?_
    (Nat.zero_le _)) fun _ _ => ?_
  · exact (Nat.add_le_add hT.v hx.kLo).trans (by norm_num)
  refine keeps_bind (keeps_send S _ _ true (cons_cube hx.u fun _ h => absurd h (by simp))
    hx.rootsU) fun _ _ => ?_
  refine keeps_bind (keeps_positions S _ _) fun nu hnu => ?_
  refine keeps_bind (keeps_needs _ _) fun _ _ => ?_
  refine keeps_bind (keeps_poss nf_loc (Nat.zero_le _) _ _ _ hT.logN (le40 hnu) (Nat.zero_le _)
    rfl rfl) fun _ _ => ?_
  refine keeps_bind (keeps_listed _ _) fun _ _ => ?_
  refine keeps_bind (keeps_send S _ _ true (cons_cube hx.omega hx.besideOmega) hx.rootsOmega)
    fun _ _ => ?_
  exact keeps_bind (keeps_elems nf_lin_zeta (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩
    (le40 hx.rowsLog) (Nat.zero_le _)) fun _ _ => keeps_pure trivial

theorem keeps_link (S : SetCap s) (T : TableSize) (u : SampleSize) (hT : TableOk T)
    (hu : u.cubeBits ≤ 2 ^ 32) : Keeps s Small (planLink T u) := by
  unfold planLink
  refine keeps_bind keeps_setting fun s' hs' => ?_
  subst hs'
  refine keeps_bind (keeps_table T) fun A _ => ?_
  refine keeps_bind (keeps_elems nf_link_point (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ (le40 hT.v)
    (Nat.zero_le _)) fun _ _ => ?_
  refine keeps_bind (keeps_roots 1) fun _ _ => ?_
  refine keeps_bind (keeps_listOfGroups u.groups) fun l _ => ?_
  refine keeps_bind (keeps_elems nf_send_seed (by omega) _ _ _ ⟨rfl, rfl, rfl⟩ (seed_le S hu)
    (samples_le S)) fun _ _ => ?_
  refine keeps_bind (keeps_answers _) fun _ _ => ?_
  refine keeps_bind (keeps_silent nf_send_answer) fun _ _ => ?_
  refine keeps_bind (keeps_positions S _ _) fun n1 h1 => ?_
  refine keeps_bind (keeps_positions S _ _) fun n2 h2 => ?_
  refine keeps_bind (keeps_needs _ _) fun _ _ => ?_
  refine keeps_bind (keeps_poss nf_link (Nat.zero_le _) _ _ _ hT.logN
    ((Nat.add_le_add h1 h2).trans (by norm_num)) (Nat.zero_le _) rfl rfl) fun _ _ => ?_
  refine keeps_bind (keeps_listed _ _) fun _ _ => ?_
  exact keeps_bind (keeps_elems nf_link_phi (Nat.zero_le _) _ _ _ ⟨rfl, rfl, rfl⟩ (le40 hT.ell)
    (Nat.zero_le _)) fun _ _ => keeps_pure trivial

end

end OnBytes.Params

#print axioms OnBytes.Params.keeps_send
#print axioms OnBytes.Params.keeps_lookup
#print axioms OnBytes.Params.keeps_rng
#print axioms OnBytes.Params.keeps_iopp
#print axioms OnBytes.Params.keeps_linShared
#print axioms OnBytes.Params.keeps_link
