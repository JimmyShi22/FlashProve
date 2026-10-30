-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SampleOfSeed.lean: the converse of `sample_of_L` (SampleLaw.lean), at a shape
with one table: if the message's one sample row in the verifier's state is `Send.form`'s at a seed,
the test `sampleL` (SampleOk.lean) says yes. Statements and proofs.

Why. `sampleL` does not ask «the row is Send.form's at SOME seed»: the verifier's state keeps rows,
not seeds: it reads a seed BACK off the row (`seedOfRow`) and asks that `Send.form` at the seed read
back gives the row again. So «the sending made the row at a seed» gives the test's yes only by a law
on that reading back. Here it is, where the shape has rows of one kind: the point read back is the
seed's first `cube.bits` coordinates, to the word; the factor read back is (β · θ⁰ − e) + e in the
program's arithmetic on words: a canonical word that reads as β: and `Send.form` reads the factor
through products alone, whose words hang on the factors' readings alone. SO NOTHING IS ASKED OF β's
WORDS. Main names.
  `fold_units`: what adding single entries leaves of a row.
  `rowSame_self`: a row without runs and forms is «the same» as itself with another target.
  `backB`, `backB_ok`, `backB_read`, `backB_mul`: the factor read back: canonical; reads as β; gives
    the same products as β, to the word.
  `form_fields`: `Send.form`'s row, field by field. `pad_head`: the pad's first place at one answer.
  `form_back`: `Send.form` at the factor read back is `Send.form` at β.
  `seed_back`: at one table `seedOfRow` of that row is ⟨z.take bits, backB β e⟩.
  `sampleL_of_seed`: the twelve clauses.
  `shapeOkB`: the six facts on shape and codes, as one test with code. `hQ_of_seedAt`: what the
    seam's core asks of a member's sample, to the letter.
ROWS OF BOTH KINDS: `back_top` · `cube_both` · `front_long` · `take_snoc` ·
`seed_back₂` · `sampleL_of_back` · `sampleL_of_seed₂` · `hQ_of_seedAt₂`: there the cube has one
bit more than the longer table; where the main table is no shorter than the mask's the last
coordinate is read back by 1 − (1 − top) in the program's arithmetic: it comes back to the word
where its three words are below the field's size (`okE`): A PREMISE ON THE SEED; where the mask's
table is the longer
it is read off as it stands. (Of the factor nothing is asked, as at one table.)
`okE_getD` · `sampleL_of_seedA`: one form for every shape with one answer,
under «every coordinate of the seed's point is canonical».
WHERE THE ARM OF BOTH KINDS IS WANTED: none of the proof file's three members on the shared chain
has rows of both kinds; of the key file's six shapes two have (the lookups' multiplicities; V).
What it is not. That the row in the verifier's state IS `Send.form`'s
at a seed whose factor reads as a unit of the field is a premise: the sending block's law's. Four
clauses read shape and codes alone and are premises. A bridge: if the antecedent «sampleL's yes» in
`TupleAt` (TupleAt.lean) is one day turned into the four facts that its proof spends, this file
falls idle. No soundness is claimed. Nothing on hiding.
Cousins: `fold_units` has kin at one fixed part (OnBytes/Slice/BlkRecRow.lean:99, BlkLinRec.lean:55:
kind, terms and forms stay); here the part is the place's own and the single entries are written
out.
-/
import Johnson.Desc.K12.Law.SampleLaw

set_option autoImplicit false
namespace H2K.Pin
open OnBytes OnBytes.Params OnBytes.Slice Johnson.Pack
open H2K.First (Seat1)

/-! ## Tools -/

/-- What adding single entries leaves of a row. -/
theorem fold_units (o : Nat) (g : PadPlace → E) : ∀ (l : List PadPlace) (r : Row),
    (l.foldl (fun (r : Row) p => r.addUnit o p.part p.index (g p)) r) =
      { r with units := r.units ++ (l.map fun p => (⟨o, p.part, p.index, g p⟩ : Single)).toArray }
  | [], r => by simp
  | p :: l, r => by
    rw [List.foldl_cons, fold_units o g l]
    simp [Row.addUnit]

theorem zip_self_fst {α : Type} : ∀ (l : List α) (x : α × α), x ∈ l.zip l → x.1 = x.2
  | [], _, h => by simp at h
  | a :: l, x, h => by
    rw [List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact zip_self_fst l x h

/-- A row without runs and forms is «the same» as itself with another target. -/
theorem rowSame_self (a : Row) (tt : E) (h1 : a.runs.size = 0) (h2 : a.forms.size = 0) :
    rowSame a { a with target := tt } = true := by
  unfold rowSame tensorSame
  simp only [h1, h2, decide_true, beq_self_eq_true, Bool.and_true, Bool.true_and,
    Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [zip_self_fst _ x hx]
    simp
  · rw [zip_self_fst _ x hx]
    simp

/-- Every sum is canonical. (The text of `okE_addE`, Johnson/Desc/Kinds/Law/Lemma2a.lean:26, which
stands in another kind's files, over that kind's own files: not imported here; private. Its home is
the field's: OnBytes/Slice/ProgField.lean.) -/
private theorem okE_add' (a b : E) : okE (addE a b) = true := by
  rw [OnBytes.okE_triple, OnBytes.addE_triple]
  unfold Fmt.Fld.okE Fmt.Fld.addE
  simp [Fmt.Fld.ok_add]

/-- Every product is canonical. (The text of `okE_mulE`, Johnson/Desc/Kinds/Law/Lemma2b.lean:30: as
above.) -/
private theorem okE_mul' (a b : E) : okE (mulE a b) = true := by
  rw [OnBytes.okE_triple, OnBytes.mulE_triple]
  unfold Fmt.Fld.okE Fmt.Fld.mulE
  simp [Fmt.Fld.ok_add]

/-- The factor read back. -/
def backB (β e : E) : E := addE (subE (mulE β (thetaE 0)) e) e

theorem backB_ok (β e : E) : okE (backB β e) = true := okE_add' _ _

theorem backB_read (β e : E) : readE (backB β e) = readE β := by
  unfold backB
  rw [readE_add, readE_sub, readE_mul, readE_theta_zero]
  ring

/-- It gives the same products as β, to the word: nothing is asked of β's words. -/
theorem backB_mul (β e θ : E) : mulE (backB β e) θ = mulE β θ :=
  readE_inj _ _ (okE_mul' _ _) (okE_mul' _ _) (by rw [readE_mul, readE_mul, backB_read])

/-! ## Send.form's row -/

/-- The single entry that `Send.form` lays on a place of the pad, at the answer 0. -/
def unitAt (K : Codes) (s : OracleShape) (o : Nat) (seed : SampleSeed) (p : PadPlace) : Single :=
  ⟨o, p.part, p.index,
    subE (if p.answer == 0 then mulE seed.beta p.basis else zeroE)
      ((if p.part == .main then
          Tensor.eq (seed.z.take (Send.cube K s).mainBits)
            (Send.front seed.z (Send.cube K s) (Send.cube K s).mainBits false)
        else Tensor.eq (seed.z.take (Send.cube K s).maskBits)
            (Send.front seed.z (Send.cube K s) (Send.cube K s).maskBits true)).entry p.index)⟩

/-- **`Send.form`'s row, field by field.** -/
theorem form_fields (K : Codes) (s : OracleShape) (o : Nat) (seed : SampleSeed) (row0 : Row)
    (h : Send.form K s o seed 0 = some row0) :
    ∃ places, Send.pad K s = some places ∧ row0.kind = .sample ∧ row0.runs = #[] ∧
      row0.forms = #[] ∧ row0.units = (places.map (unitAt K s o seed)).toArray ∧
      row0.terms =
        (if (Send.cube K s).hasMain then
          #[(⟨o, .main, Tensor.eq (seed.z.take (Send.cube K s).mainBits)
            (Send.front seed.z (Send.cube K s) (Send.cube K s).mainBits false)⟩ : Term)]
          else #[]) ++
        (if (Send.cube K s).hasMask then
          #[(⟨o, .mask, Tensor.eq (seed.z.take (Send.cube K s).maskBits)
            (Send.front seed.z (Send.cube K s) (Send.cube K s).maskBits true)⟩ : Term)]
          else #[]) := by
  unfold Send.form at h
  cases hp : Send.pad K s with
  | none => simp [hp] at h
  | some places =>
    simp only [hp, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    rw [fold_units] at h
    subst h
    refine ⟨places, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
      cases (Send.cube K s).hasMain <;> cases (Send.cube K s).hasMask <;>
      simp [Row.add, unitAt]

/-- The pad's first place, at a shape with one answer. -/
theorem pad_head (K : Codes) (s : OracleShape) (places : List PadPlace)
    (h : Send.pad K s = some places) (h1 : s.answers = 1) :
    ∃ p ps, places = p :: ps ∧ p.answer = 0 ∧ p.basis = thetaE 0 ∧
      p.part = if (Send.cube K s).hasMask then .mask else .main := by
  unfold Send.pad at h
  dsimp only at h
  rw [h1] at h
  cases hM : (Send.cube K s).hasMask <;> cases hq : (s.mainDeg == 3) <;>
    simp only [hM, hq, Bool.or_true, Bool.or_false, if_true, Bool.false_eq_true, if_false] at h <;>
    split at h <;> first
      | (cases h; done)
      | (cases h; exact ⟨_, _, rfl, rfl, rfl, rfl⟩)

/-- `Send.form` at the factor read back is `Send.form` at β. -/
theorem form_back (K : Codes) (s : OracleShape) (o : Nat) (z : List E) (β e : E) (a : Nat) :
    Send.form K s o ⟨z, backB β e⟩ a = Send.form K s o ⟨z, β⟩ a := by
  unfold Send.form
  simp only [backB_mul]

/-! ## The seed read back, at one table -/

/-- With rows of one kind the cube's bits are that table's. -/
theorem cube_one (K : Codes) (s : OracleShape) :
    ((Send.cube K s).hasMain = true → (Send.cube K s).hasMask = false →
      (Send.cube K s).mainBits = (Send.cube K s).bits) ∧
    ((Send.cube K s).hasMain = false → (Send.cube K s).hasMask = true →
      (Send.cube K s).maskBits = (Send.cube K s).bits) := by
  unfold Send.cube
  dsimp only
  constructor <;> intro h1 h2 <;> simp [h1, h2]

/-- **At one table `seedOfRow` reads back the seed's first coordinates, to the word, and a factor
that is `backB` of the seed's.** -/
theorem seed_back (K : Codes) (s : OracleShape) (o : Nat) (seed : SampleSeed) (row0 : Row) (tt : E)
    (h : Send.form K s o seed 0 = some row0) (h1 : s.answers = 1)
    (hone : ((Send.cube K s).hasMain && (Send.cube K s).hasMask) = false)
    (hsome : ((Send.cube K s).hasMain || (Send.cube K s).hasMask) = true) :
    ∃ e, seedOfRow K s { row0 with target := tt } =
      some ⟨seed.z.take (Send.cube K s).bits, backB seed.beta e⟩ := by
  obtain ⟨places, hp, _, _, _, hu, ht⟩ := form_fields K s o seed row0 h
  obtain ⟨p, ps, rfl, pa, pb, pp⟩ := pad_head K s places hp h1
  obtain ⟨c1, c2⟩ := cube_one K s
  unfold seedOfRow
  simp only [hone, Bool.false_eq_true, if_false, hu, ht]
  cases hM : (Send.cube K s).hasMain <;> cases hZ : (Send.cube K s).hasMask <;>
    simp only [hM, hZ, Bool.and_self, Bool.or_self, Bool.and_true, Bool.and_false, Bool.or_true,
      Bool.or_false, Bool.true_eq_false, Bool.false_eq_true] at hone hsome
  · rw [hZ] at pp
    refine ⟨(Tensor.eq (seed.z.take (Send.cube K s).maskBits)
      (Send.front seed.z (Send.cube K s) (Send.cube K s).maskBits true)).entry p.index, ?_⟩
    simp [unitAt, pa, pb, pp, backB, ← c2 hM hZ, Tensor.eq, List.map_map, Function.comp_def]
  · rw [hZ] at pp
    refine ⟨(Tensor.eq (seed.z.take (Send.cube K s).mainBits)
      (Send.front seed.z (Send.cube K s) (Send.cube K s).mainBits false)).entry p.index, ?_⟩
    simp [unitAt, pa, pb, pp, backB, ← c1 hM hZ, Tensor.eq, List.map_map, Function.comp_def]

/-! ## The twelve clauses -/

/-- **If the message's one sample row is `Send.form`'s at a seed whose factor reads as a unit of
the field and whose point is long enough, the test `sampleL` says yes**: at a shape with rows of one
kind and one answer. hcase, hpM, hpZ: the three clauses that read shape and codes alone, as
`sampleL` writes them. -/
theorem sampleL_of_seed (K : Codes) (m : Seat1) (x : OnBytes.Oracle) (seed : SampleSeed)
    (row0 : Row) (tt : E) (β : GEˣ) (hs : x.sampled = true)
    (hform : Send.form K m.sh m.id seed 0 = some row0)
    (hrows : x.sampleRows.toList = [{ row0 with target := tt }])
    (hlen : bitsZ K m.sh ≤ seed.z.length) (hβ : (β : GE) = readE seed.beta)
    (h1 : m.sh.answers = 1)
    (hone : ¬ (0 < m.sh.mainRows ∧ 0 < m.sh.maskRows))
    (hsome : 0 < m.sh.mainRows ∨ 0 < m.sh.maskRows)
    (hcase : (0 < m.sh.maskRows ∨ m.sh.mainDeg = 3) ∨ (m.sh.maskRows = 0 ∧ m.sh.mainDeg = 1))
    (hpM : m.sh.mainRows = 0 ∨ 2 ^ ceilLog2 (mainB K m.sh).ell = (mainB K m.sh).ell)
    (hpZ : m.sh.maskRows = 0 ∨ 2 ^ ceilLog2 (maskB K m.sh).ell = (maskB K m.sh).ell) :
    ok (sampleL K m x) = true := by
  have cM : (Send.cube K m.sh).hasMain = decide (0 < m.sh.mainRows) := rfl
  have cZ : (Send.cube K m.sh).hasMask = decide (0 < m.sh.maskRows) := rfl
  have hone' : ((Send.cube K m.sh).hasMain && (Send.cube K m.sh).hasMask) = false := by
    rw [cM, cZ, Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    by_cases q : 0 < m.sh.mainRows
    · exact Or.inr fun z => hone ⟨q, z⟩
    · exact Or.inl q
  have hsome' : ((Send.cube K m.sh).hasMain || (Send.cube K m.sh).hasMask) = true := by
    rw [cM, cZ, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact hsome
  obtain ⟨e, hback⟩ := seed_back K m.sh m.id seed row0 tt hform h1 hone' hsome'
  obtain ⟨_, _, hk, hr, hf, _, _⟩ := form_fields K m.sh m.id seed row0 hform
  have hget : x.sampleRows.getD 0 default = { row0 with target := tt } := by
    rcases hx : x.sampleRows with ⟨l⟩
    rw [hx] at hrows
    have : l = [{ row0 with target := tt }] := hrows
    subst this
    rfl
  have hsize : x.sampleRows.size = 1 := by
    rw [← Array.length_toList, hrows]
    rfl
  have hfb : Send.form K m.sh m.id
      ⟨seed.z.take (Send.cube K m.sh).bits, backB seed.beta e⟩ 0 = some row0 := by
    rw [form_back, form_take]
    exact hform
  have hne : isZeroE (backB seed.beta e) = false := by
    cases hz : isZeroE (backB seed.beta e) with
    | false => rfl
    | true =>
      exfalso
      have := readE_of_isZeroE _ hz
      rw [backB_read, ← hβ] at this
      exact β.ne_zero this
  simp only [sampleL, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true, hget, hback]
  refine ⟨hs, hsize, h1, hk, rfl, ?_, ?_, ?_, backB_ok _ _, hcase, hpM, hpZ⟩
  · unfold formIs
    rw [hfb]
    exact rowSame_self row0 tt (by rw [hr]; rfl) (by rw [hf]; rfl)
  · rw [List.length_take, cube_bits]
    exact Nat.min_eq_left hlen
  · rw [hne]
    rfl

/-! ## Rows of both kinds -/

private theorem okE_sub' (a b : E) : okE (subE a b) = true := by
  rw [OnBytes.okE_triple, OnBytes.subE_triple]
  unfold Fmt.Fld.okE Fmt.Fld.subE
  simp [Fmt.Fld.ok_sub]

/-- The last coordinate comes back, where its words are canonical. -/
theorem back_top (x : E) (h : okE x = true) : subE oneE (subE oneE x) = x := by
  refine readE_inj _ _ (okE_sub' _ _) h ?_
  rw [readE_sub, readE_sub]
  ring

/-- With rows of both kinds the cube has one bit more than the longer table. -/
theorem cube_both (K : Codes) (s : OracleShape) (h1 : (Send.cube K s).hasMain = true)
    (h2 : (Send.cube K s).hasMask = true) :
    (Send.cube K s).bits = max (Send.cube K s).mainBits (Send.cube K s).maskBits + 1 := by
  unfold Send.cube at h1 h2 ⊢
  dsimp only at h1 h2 ⊢
  simp [h1, h2]

/-- The factor in front of the longer table's term: nothing is left to multiply. -/
theorem front_long (z : List E) (c : SampleCube) (mask : Bool) (n : ℕ)
    (hb : (c.hasMain && c.hasMask) = true) (hn : c.bits - 1 = n) :
    Send.front z c n mask =
      if mask then z.getD (c.bits - 1) zeroE else subE oneE (z.getD (c.bits - 1) zeroE) := by
  unfold Send.front
  rw [hb, hn]
  have e : (z.take n).drop n = [] := List.drop_eq_nil_of_le (by simp)
  simp [e]

theorem take_snoc (z : List E) (n : ℕ) (h : n < z.length) :
    z.take n ++ [z[n]?.getD zeroE] = z.take (n + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  rfl

/-- **With rows of both kinds `seedOfRow` reads back the seed's first coordinates, to the word,
where the last of them is canonical; and a factor that is `backB` of the seed's.** -/
theorem seed_back₂ (K : Codes) (s : OracleShape) (o : Nat) (seed : SampleSeed) (row0 : Row) (tt : E)
    (h : Send.form K s o seed 0 = some row0) (h1 : s.answers = 1)
    (hM : (Send.cube K s).hasMain = true) (hZ : (Send.cube K s).hasMask = true)
    (hlen : (Send.cube K s).bits ≤ seed.z.length)
    (hok : okE (seed.z.getD ((Send.cube K s).bits - 1) zeroE) = true) :
    ∃ e, seedOfRow K s { row0 with target := tt } =
      some ⟨seed.z.take (Send.cube K s).bits, backB seed.beta e⟩ := by
  obtain ⟨places, hp, _, _, _, hu, ht⟩ := form_fields K s o seed row0 h
  obtain ⟨p, ps, rfl, pa, pb, pp⟩ := pad_head K s places hp h1
  have hb := cube_both K s hM hZ
  have hand : ((Send.cube K s).hasMain && (Send.cube K s).hasMask) = true := by rw [hM, hZ]; rfl
  rw [hZ] at pp
  refine ⟨(Tensor.eq (seed.z.take (Send.cube K s).maskBits)
    (Send.front seed.z (Send.cube K s) (Send.cube K s).maskBits true)).entry p.index, ?_⟩
  unfold seedOfRow
  simp only [if_true, hu, ht, hM, hZ]
  by_cases q : (Send.cube K s).maskBits ≤ (Send.cube K s).mainBits
  · have hn : (Send.cube K s).bits - 1 = (Send.cube K s).mainBits := by
      rw [hb, Nat.max_eq_left q]
      rfl
    have hlt : (Send.cube K s).mainBits < seed.z.length := by omega
    have e1 : (Send.cube K s).bits = (Send.cube K s).mainBits + 1 := by omega
    have hok' : okE (seed.z[(Send.cube K s).mainBits]?.getD zeroE) = true := by
      rw [hn, List.getD_eq_getElem?_getD] at hok
      exact hok
    simp [unitAt, pa, pb, pp, backB, q, Tensor.eq, List.map_map, Function.comp_def,
      front_long seed.z (Send.cube K s) false _ hand hn]
    rw [hn, back_top _ hok', take_snoc _ _ hlt, ← e1]
  · have q' : (Send.cube K s).mainBits ≤ (Send.cube K s).maskBits := by omega
    have hn : (Send.cube K s).bits - 1 = (Send.cube K s).maskBits := by
      rw [hb, Nat.max_eq_right q']
      rfl
    have hlt : (Send.cube K s).maskBits < seed.z.length := by omega
    have e1 : (Send.cube K s).bits = (Send.cube K s).maskBits + 1 := by omega
    simp [unitAt, pa, pb, pp, backB, q, Tensor.eq, List.map_map, Function.comp_def,
      front_long seed.z (Send.cube K s) true _ hand hn]
    rw [hn, take_snoc _ _ hlt, ← e1]

/-- The twelve clauses from «the seed comes back»: what both tops spend. -/
theorem sampleL_of_back (K : Codes) (m : Seat1) (x : OnBytes.Oracle) (seed : SampleSeed)
    (row0 : Row) (tt : E) (β : GEˣ) (e : E) (hs : x.sampled = true)
    (hform : Send.form K m.sh m.id seed 0 = some row0)
    (hrows : x.sampleRows.toList = [{ row0 with target := tt }])
    (hlen : bitsZ K m.sh ≤ seed.z.length) (hβ : (β : GE) = readE seed.beta)
    (h1 : m.sh.answers = 1)
    (hback : seedOfRow K m.sh { row0 with target := tt } =
      some ⟨seed.z.take (Send.cube K m.sh).bits, backB seed.beta e⟩)
    (hcase : (0 < m.sh.maskRows ∨ m.sh.mainDeg = 3) ∨ (m.sh.maskRows = 0 ∧ m.sh.mainDeg = 1))
    (hpM : m.sh.mainRows = 0 ∨ 2 ^ ceilLog2 (mainB K m.sh).ell = (mainB K m.sh).ell)
    (hpZ : m.sh.maskRows = 0 ∨ 2 ^ ceilLog2 (maskB K m.sh).ell = (maskB K m.sh).ell) :
    ok (sampleL K m x) = true := by
  obtain ⟨_, _, hk, hr, hf, _, _⟩ := form_fields K m.sh m.id seed row0 hform
  have hget : x.sampleRows.getD 0 default = { row0 with target := tt } := by
    rcases hx : x.sampleRows with ⟨l⟩
    rw [hx] at hrows
    have : l = [{ row0 with target := tt }] := hrows
    subst this
    rfl
  have hsize : x.sampleRows.size = 1 := by
    rw [← Array.length_toList, hrows]
    rfl
  have hfb : Send.form K m.sh m.id
      ⟨seed.z.take (Send.cube K m.sh).bits, backB seed.beta e⟩ 0 = some row0 := by
    rw [form_back, form_take]
    exact hform
  have hne : isZeroE (backB seed.beta e) = false := by
    cases hz : isZeroE (backB seed.beta e) with
    | false => rfl
    | true =>
      exfalso
      have := readE_of_isZeroE _ hz
      rw [backB_read, ← hβ] at this
      exact β.ne_zero this
  simp only [sampleL, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true, hget, hback]
  refine ⟨hs, hsize, h1, hk, rfl, ?_, ?_, ?_, backB_ok _ _, hcase, hpM, hpZ⟩
  · unfold formIs
    rw [hfb]
    exact rowSame_self row0 tt (by rw [hr]; rfl) (by rw [hf]; rfl)
  · rw [List.length_take, cube_bits]
    exact Nat.min_eq_left hlen
  · rw [hne]
    rfl

/-- **The same at a shape with rows of BOTH kinds**, where the last of the coordinates that the
message's own cube uses is canonical (`okE`: its three words are below the field's size). The case
(CaseE) is then had: 0 < maskRows. -/
theorem sampleL_of_seed₂ (K : Codes) (m : Seat1) (x : OnBytes.Oracle) (seed : SampleSeed)
    (row0 : Row) (tt : E) (β : GEˣ) (hs : x.sampled = true)
    (hform : Send.form K m.sh m.id seed 0 = some row0)
    (hrows : x.sampleRows.toList = [{ row0 with target := tt }])
    (hlen : bitsZ K m.sh ≤ seed.z.length) (hβ : (β : GE) = readE seed.beta)
    (h1 : m.sh.answers = 1)
    (hboth : 0 < m.sh.mainRows ∧ 0 < m.sh.maskRows)
    (hok : okE (seed.z.getD (bitsZ K m.sh - 1) zeroE) = true)
    (hpM : 2 ^ ceilLog2 (mainB K m.sh).ell = (mainB K m.sh).ell)
    (hpZ : 2 ^ ceilLog2 (maskB K m.sh).ell = (maskB K m.sh).ell) :
    ok (sampleL K m x) = true := by
  have cM : (Send.cube K m.sh).hasMain = true := decide_eq_true hboth.1
  have cZ : (Send.cube K m.sh).hasMask = true := decide_eq_true hboth.2
  obtain ⟨e, hback⟩ := seed_back₂ K m.sh m.id seed row0 tt hform h1 cM cZ
    (by rw [cube_bits]; exact hlen) (by rw [cube_bits]; exact hok)
  exact sampleL_of_back K m x seed row0 tt β e hs hform hrows hlen hβ h1 hback
    (Or.inl (Or.inl hboth.2)) (Or.inr hpM) (Or.inr hpZ)

/-- Where every coordinate of a point is canonical, so is whatever `getD` reads of it. -/
theorem okE_getD (z : List E) (n : ℕ) (h : ∀ c ∈ z, okE c = true) :
    okE (z.getD n zeroE) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases e : z[n]? with
  | none => rfl
  | some c => exact h c (List.mem_of_getElem? e)

/-- **One form for every shape with one answer**: rows of one kind or of both: where every
coordinate of the seed's point is canonical (as the drawn elements of a round are). -/
theorem sampleL_of_seedA (K : Codes) (m : Seat1) (x : OnBytes.Oracle) (seed : SampleSeed)
    (row0 : Row) (tt : E) (β : GEˣ) (hs : x.sampled = true)
    (hform : Send.form K m.sh m.id seed 0 = some row0)
    (hrows : x.sampleRows.toList = [{ row0 with target := tt }])
    (hlen : bitsZ K m.sh ≤ seed.z.length) (hβ : (β : GE) = readE seed.beta)
    (hall : ∀ c ∈ seed.z, okE c = true) (h1 : m.sh.answers = 1)
    (hsome : 0 < m.sh.mainRows ∨ 0 < m.sh.maskRows)
    (hcase : (0 < m.sh.maskRows ∨ m.sh.mainDeg = 3) ∨ (m.sh.maskRows = 0 ∧ m.sh.mainDeg = 1))
    (hpM : m.sh.mainRows = 0 ∨ 2 ^ ceilLog2 (mainB K m.sh).ell = (mainB K m.sh).ell)
    (hpZ : m.sh.maskRows = 0 ∨ 2 ^ ceilLog2 (maskB K m.sh).ell = (maskB K m.sh).ell) :
    ok (sampleL K m x) = true := by
  by_cases hb : 0 < m.sh.mainRows ∧ 0 < m.sh.maskRows
  · exact sampleL_of_seed₂ K m x seed row0 tt β hs hform hrows hlen hβ h1 hb
      (okE_getD _ _ hall) (hpM.resolve_left (by omega)) (hpZ.resolve_left (by omega))
  · exact sampleL_of_seed K m x seed row0 tt β hs hform hrows hlen hβ h1 hb hsome hcase hpM hpZ

/-! ## In the letters of the seam's core -/

/-- **The six facts on shape and codes, as one test with code**: one answer · not rows of both kinds
· rows of some kind · the case · the message length of each code of which the shape has rows is a
power of two. The last three as `sampleL` writes them. -/
def shapeOkB (K : Codes) (s : OracleShape) : Bool :=
  s.answers == 1 && !(decide (0 < s.mainRows) && decide (0 < s.maskRows)) &&
    (decide (0 < s.mainRows) || decide (0 < s.maskRows)) &&
    decide ((0 < s.maskRows ∨ s.mainDeg = 3) ∨ (s.maskRows = 0 ∧ s.mainDeg = 1)) &&
    (s.mainRows == 0 || 2 ^ ceilLog2 (mainB K s).ell == (mainB K s).ell) &&
    (s.maskRows == 0 || 2 ^ ceilLog2 (maskB K s).ell == (maskB K s).ell)

/-- **What the seam's core asks of a member's sample (its second clause), to the letter**: from
«the message at the member's number is sampled and its one sample row is `Send.form`'s at a seed»
and the test on shape and codes. -/
theorem hQ_of_seedAt (K : Codes) (m : Seat1) (St : Statement)
    (h : ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : Row) (tt : E) (β : GEˣ),
      St.oracles[m.id]? = some x ∧ x.sampled = true ∧
      Send.form K m.sh m.id seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ K m.sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta)
    (hs : shapeOkB K m.sh = true) :
    ∃ o, St.oracles[m.id]? = some o ∧ ok (sampleL K m o) = true := by
  obtain ⟨x, seed, row0, tt, β, hx, h1, h2, h3, h4, h5⟩ := h
  simp only [shapeOkB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
    decide_eq_true_eq, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hs
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := hs
  exact ⟨x, hx, sampleL_of_seed K m x seed row0 tt β h1 h2 h3 h4 h5 a1
    (fun q => a2.elim (fun z => z q.1) fun z => z q.2) a3 a4 a5 a6⟩

/-- **The seam's core's second clause at a member with rows of both kinds, to the letter.** -/
theorem hQ_of_seedAt₂ (K : Codes) (m : Seat1) (St : Statement)
    (h : ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : Row) (tt : E) (β : GEˣ),
      St.oracles[m.id]? = some x ∧ x.sampled = true ∧
      Send.form K m.sh m.id seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ K m.sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
      okE (seed.z.getD (bitsZ K m.sh - 1) zeroE) = true)
    (h1 : m.sh.answers = 1) (hboth : 0 < m.sh.mainRows ∧ 0 < m.sh.maskRows)
    (hpM : 2 ^ ceilLog2 (mainB K m.sh).ell = (mainB K m.sh).ell)
    (hpZ : 2 ^ ceilLog2 (maskB K m.sh).ell = (maskB K m.sh).ell) :
    ∃ o, St.oracles[m.id]? = some o ∧ ok (sampleL K m o) = true := by
  obtain ⟨x, seed, row0, tt, β, hx, a1, a2, a3, a4, a5, a6⟩ := h
  exact ⟨x, hx, sampleL_of_seed₂ K m x seed row0 tt β a1 a2 a3 a4 a5 h1 hboth a6 hpM hpZ⟩

end H2K.Pin

#print axioms H2K.Pin.fold_units
#print axioms H2K.Pin.zip_self_fst
#print axioms H2K.Pin.rowSame_self
#print axioms H2K.Pin.backB_ok
#print axioms H2K.Pin.backB_read
#print axioms H2K.Pin.backB_mul
#print axioms H2K.Pin.form_fields
#print axioms H2K.Pin.pad_head
#print axioms H2K.Pin.form_back
#print axioms H2K.Pin.cube_one
#print axioms H2K.Pin.seed_back
#print axioms H2K.Pin.sampleL_of_seed
#print axioms H2K.Pin.hQ_of_seedAt
#print axioms H2K.Pin.back_top
#print axioms H2K.Pin.cube_both
#print axioms H2K.Pin.front_long
#print axioms H2K.Pin.take_snoc
#print axioms H2K.Pin.seed_back₂
#print axioms H2K.Pin.sampleL_of_back
#print axioms H2K.Pin.sampleL_of_seed₂
#print axioms H2K.Pin.hQ_of_seedAt₂
#print axioms H2K.Pin.okE_getD
#print axioms H2K.Pin.sampleL_of_seedA
