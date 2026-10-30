-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/SampleOfSeedBoth.lean: THE CONVERSE OF sample_of_L AT A SHAPE WITH BOTH TABLES, WITH THE
PREMISE ON THE TOP COORDINATE's WORDS ASKED ONLY WHERE IT IS NEEDED. Statements and proofs.

WHY. Johnson/Desc/K12/Law/SampleOfSeed.lean has: if a state's one sample row is Send.form's at a seed, the test H2K.Pin.sampleL accepts: at rows of one kind (sampleL_of_seed), at rows of both kinds under okE of the seed's top coordinate (sampleL_of_seed₂), at every shape under okE of every coordinate (sampleL_of_seedA). The carried invariants say nothing on the point's words. The message W of the full size has one main row and one mask row, and its main table is the larger. Here: where the main table is the larger NOTHING is asked of any word; the premise stays where the two tables have as many bits, and there it cannot fall.

HOW. Over that file: its form_fields, pad_head, backB, form_back, rowSame_self, back_top's user seed_back₂, cube_both, front_long and take_snoc are called; no second text of them. seedOfRow reads the top coordinate, where the main table is no shorter, as 1 − (1 − top) =: topB top. Where the main table is the larger, Send.form at topB top is Send.form at top (form_topB: the main's factor in front is 1 − top, the mask's a product that begins with top: both hang on top's reading alone: backB's own device, on the top). Where the two tables have as many bits, the mask's factor in front IS the top: there its words must be below the prime.

WHAT IS SAID.
  topB · topB_read · topB_sub · topB_mul · eq_pairs   tools · take_snocD · front_longD · bits_both   that file's take_snoc, front_long and cube_both in the letters used here, each by one call
  form_topB               where the main table is the larger: Send.form at the point read back is Send.form at the point
  seed_back_raw           what seedOfRow reads back at both tables, with nothing asked of any word
  **seed_back_any**       what the five clauses want: a point of the cube's length at which Send.form is Send.form at the seed's; htop asked at maskBits = mainBits alone (there: that file's seed_back₂)
  sampleL_of_backZ        the twelve clauses from that: that file's sampleL_of_back with the point read back as a letter
  sampleL_of_seed_both    the twelve clauses at both tables
  **sampleL_of_seed_all** sampleL_of_seed's statement with hone struck and one premise more
  example_met · example_evaluated   at a small shape with both tables of as many bits: all premises are met together; the test accepts there (by the kernel)
  top_needed · WithoutTop · withoutTop_is_all · withoutTop_is_theirs · without_top_false   there, with the prime itself as the top coordinate's first word, the test rejects: so sampleL_of_seed_all's statement without htop is false (that WithoutTop's ten premises are that theorem's other ten, and sampleL_of_seed's but hone, is held by Lean)
  top_idle                where the main table is the larger the test accepts at such a top: htop is not asked there

THE PREMISE htop. The words of coordinate number bits − 1 of the seed's point are below the prime: ASKED WHERE THE MESSAGE HAS BOTH TABLES AND THESE HAVE AS MANY BITS, AND NOWHERE ELSE. There it cannot fall: without_top_false.

What is not claimed. That any state's row is Send.form's. Nothing at another answer's number than 0. No soundness.

-/
import Johnson.Desc.K12.Law.SampleOfSeed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open OnBytes OnBytes.Params OnBytes.Slice Johnson.Pack H2K.Pin
open H2K.First (Seat1)

/-! ### Tools -/

private theorem okE_sub' (a b : E) : okE (subE a b) = true := by
  rw [okE_triple, subE_triple]
  simp only [Fmt.Fld.okE, Fmt.Fld.subE, Fmt.Fld.ok_sub, Bool.and_self]

private theorem okE_mul' (a b : E) : okE (mulE a b) = true := by
  rw [okE_triple, mulE_triple]
  simp only [Fmt.Fld.okE, Fmt.Fld.mulE, Fmt.Fld.ok_add, Bool.and_self]

/-- The top coordinate as it is read back where the main table is the larger. -/
def topB (t : E) : E := subE oneE (subE oneE t)

theorem topB_read (t : E) : readE (topB t) = readE t := by
  unfold topB
  rw [readE_sub, readE_sub, readE_one]
  ring

/-- It gives the same differences and products as t, to the word: nothing is asked of t's words. -/
theorem topB_sub (t : E) : subE oneE (topB t) = subE oneE t :=
  readE_inj _ _ (okE_sub' _ _) (okE_sub' _ _) (by rw [readE_sub, readE_sub, topB_read])

theorem topB_mul (t x : E) : mulE (topB t) x = mulE t x :=
  readE_inj _ _ (okE_mul' _ _) (okE_mul' _ _) (by rw [readE_mul, readE_mul, topB_read])

theorem eq_pairs (z : List E) (s : E) : (Tensor.eq z s).pairs.map (·.2) = z := by
  simp [Tensor.eq, List.map_map, Function.comp_def]

/-- H2K.Pin.take_snoc, with getD. -/
theorem take_snocD (z : List E) (n : Nat) (h : n < z.length) :
    z.take n ++ [z.getD n zeroE] = z.take (n + 1) := by
  rw [List.getD_eq_getElem?_getD]
  exact take_snoc z n h

/-- H2K.Pin.front_long, with the table's bits in the place of bits − 1. -/
theorem front_longD (z : List E) (c : SampleCube) (tb : Nat) (mask : Bool)
    (hc : (c.hasMain && c.hasMask) = true) (hb : c.bits - 1 = tb) :
    Send.front z c tb mask =
      if mask then z.getD tb zeroE else subE oneE (z.getD tb zeroE) := by
  rw [front_long z c mask tb hc hb, hb]

/-- **Where the main table is the larger, Send.form at the point read back is Send.form at the
point**: the main's factor in front is 1 − top; the mask's is a product that begins with top. -/
theorem form_topB (K : Codes) (s : OracleShape) (o : Nat) (z : List E) (β : E) (a : Nat)
    (hboth : ((Send.cube K s).hasMain && (Send.cube K s).hasMask) = true)
    (hn : (Send.cube K s).bits = (Send.cube K s).mainBits + 1)
    (hlt : (Send.cube K s).maskBits < (Send.cube K s).mainBits)
    (hl : (Send.cube K s).mainBits < z.length) :
    Send.form K s o ⟨z.take (Send.cube K s).mainBits ++
      [topB (z.getD (Send.cube K s).mainBits zeroE)], β⟩ a = Send.form K s o ⟨z, β⟩ a := by
  have hlen : (z.take (Send.cube K s).mainBits).length = (Send.cube K s).mainBits := by
    rw [List.length_take]
    omega
  have e1 : (z.take (Send.cube K s).mainBits ++
      [topB (z.getD (Send.cube K s).mainBits zeroE)]).take (Send.cube K s).mainBits =
      z.take (Send.cube K s).mainBits := by
    rw [List.take_append_of_le_length (by omega), List.take_take, Nat.min_self]
  have e2 : (z.take (Send.cube K s).mainBits ++
      [topB (z.getD (Send.cube K s).mainBits zeroE)]).take (Send.cube K s).maskBits =
      z.take (Send.cube K s).maskBits := by
    rw [List.take_append_of_le_length (by omega), List.take_take, Nat.min_eq_left (by omega)]
  have g : (z.take (Send.cube K s).mainBits ++
      [topB (z.getD (Send.cube K s).mainBits zeroE)]).getD (Send.cube K s).mainBits zeroE =
      topB (z.getD (Send.cube K s).mainBits zeroE) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
    rfl
  have f1 : Send.front (z.take (Send.cube K s).mainBits ++
      [topB (z.getD (Send.cube K s).mainBits zeroE)]) (Send.cube K s) (Send.cube K s).mainBits
      false = Send.front z (Send.cube K s) (Send.cube K s).mainBits false := by
    rw [front_longD _ _ _ false hboth (by omega), front_longD _ _ _ false hboth (by omega), g]
    simp only [Bool.false_eq_true, if_false]
    exact topB_sub _
  have f2 : Send.front (z.take (Send.cube K s).mainBits ++
      [topB (z.getD (Send.cube K s).mainBits zeroE)]) (Send.cube K s) (Send.cube K s).maskBits
      true = Send.front z (Send.cube K s) (Send.cube K s).maskBits true := by
    unfold Send.front
    rw [hboth, hn, Nat.add_sub_cancel, g, e1]
    simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true]
    cases hL : (z.take (Send.cube K s).mainBits).drop (Send.cube K s).maskBits with
    | nil =>
      exfalso
      have := congrArg List.length hL
      rw [List.length_drop, hlen] at this
      simp only [List.length_nil] at this
      omega
    | cons x L => rw [List.foldl_cons, List.foldl_cons, topB_mul]
  unfold Send.form
  simp only [e1, e2, f1, f2]

/-- The equality vector on the main table, as Send.form lays it. -/
def onMain (K : Codes) (s : OracleShape) (z : List E) : Tensor :=
  Tensor.eq (z.take (Send.cube K s).mainBits)
    (Send.front z (Send.cube K s) (Send.cube K s).mainBits false)

/-- The equality vector on the mask table, as Send.form lays it. -/
def onMask (K : Codes) (s : OracleShape) (z : List E) : Tensor :=
  Tensor.eq (z.take (Send.cube K s).maskBits)
    (Send.front z (Send.cube K s) (Send.cube K s).maskBits true)

/-! ### The seed read back, at both tables -/

/-- **What seedOfRow reads back at both tables, with nothing asked of any word**: the low coordinates
to the word; the top coordinate to the word if the mask's table is the larger, else as topB of it; a
factor that is backB of the seed's. -/
theorem seed_back_raw (K : Codes) (s : OracleShape) (o : Nat) (seed : SampleSeed) (row0 : Row)
    (tt : E) (h : Send.form K s o seed 0 = some row0) (h1 : s.answers = 1)
    (hboth : ((Send.cube K s).hasMain && (Send.cube K s).hasMask) = true)
    (hlen : (Send.cube K s).bits ≤ seed.z.length) :
    ∃ e, seedOfRow K s { row0 with target := tt } =
      some ⟨if (Send.cube K s).maskBits ≤ (Send.cube K s).mainBits then
          seed.z.take (Send.cube K s).mainBits ++
            [topB (seed.z.getD (Send.cube K s).mainBits zeroE)]
        else seed.z.take (Send.cube K s).bits, backB seed.beta e⟩ := by
  obtain ⟨places, hp, _, _, _, hu, ht⟩ := form_fields K s o seed row0 h
  obtain ⟨p, ps, rfl, pa, pb, pp⟩ := pad_head K s places hp h1
  have hMZ := hboth
  rw [Bool.and_eq_true] at hMZ
  obtain ⟨hM, hZ⟩ := hMZ
  have hb : (Send.cube K s).bits = if (Send.cube K s).hasMain && (Send.cube K s).hasMask
      then max (Send.cube K s).mainBits (Send.cube K s).maskBits + 1
      else (Send.cube K s).mainBits + (Send.cube K s).maskBits := rfl
  rw [hboth, if_pos rfl] at hb
  rw [hZ, if_pos rfl] at pp
  rw [hM, hZ, if_pos rfl, if_pos rfl] at ht
  obtain ⟨part, idx, ans, bas⟩ := p
  simp only at pa pb pp
  subst pa pb pp
  have u0 : row0.units[0]? = some ⟨o, .mask, idx,
      subE (mulE seed.beta (thetaE 0)) ((onMask K s seed.z).entry idx)⟩ := by
    rw [hu]
    rfl
  have t0 : row0.terms[0]? = some ⟨o, .main, onMain K s seed.z⟩ := by
    rw [ht]
    rfl
  have t1 : row0.terms[1]? = some ⟨o, .mask, onMask K s seed.z⟩ := by
    rw [ht]
    rfl
  have e : seedOfRow K s { row0 with target := tt } = seedOfRow K s row0 := rfl
  refine ⟨(onMask K s seed.z).entry idx, ?_⟩
  rw [e]
  unfold seedOfRow
  simp only [hboth, if_true, t0, t1, u0]
  show some (SampleSeed.mk _ (backB seed.beta ((onMask K s seed.z).entry idx))) = _
  by_cases hle : (Send.cube K s).maskBits ≤ (Send.cube K s).mainBits
  · have hn : (Send.cube K s).bits = (Send.cube K s).mainBits + 1 := by
      rw [hb, Nat.max_eq_left hle]
    rw [if_pos hle, if_pos hle, if_pos hle]
    unfold onMain
    rw [eq_pairs]
    show some (SampleSeed.mk (_ ++ [subE oneE (Send.front seed.z (Send.cube K s)
      (Send.cube K s).mainBits false)]) _) = _
    rw [front_longD seed.z _ _ false hboth (by omega)]
    rfl
  · have hn : (Send.cube K s).bits = (Send.cube K s).maskBits + 1 := by
      rw [hb, Nat.max_eq_right (by omega)]
    have hlt : (Send.cube K s).maskBits < seed.z.length := by omega
    rw [if_neg hle, if_neg hle, if_neg hle, hn, ← take_snocD seed.z _ hlt]
    show some (SampleSeed.mk ((onMask K s seed.z).pairs.map (·.2) ++ [(onMask K s seed.z).scalar])
      _) = _
    have e1 : (onMask K s seed.z).pairs.map (·.2) = seed.z.take (Send.cube K s).maskBits :=
      eq_pairs _ _
    have e2 : (onMask K s seed.z).scalar = seed.z.getD (Send.cube K s).maskBits zeroE := by
      show Send.front seed.z (Send.cube K s) (Send.cube K s).maskBits true = _
      rw [front_longD seed.z _ _ true hboth (by omega)]
      rfl
    rw [e1, e2]

/-- H2K.Pin.cube_both, from the one test. -/
theorem bits_both {K : Codes} {s : OracleShape}
    (hboth : ((Send.cube K s).hasMain && (Send.cube K s).hasMask) = true) :
    (Send.cube K s).bits = max (Send.cube K s).mainBits (Send.cube K s).maskBits + 1 := by
  rw [Bool.and_eq_true] at hboth
  exact cube_both K s hboth.1 hboth.2

/-- **What the five clauses want of what is read back**: a point of the cube's length at which
Send.form is Send.form at the seed's point. htop is asked where the two tables have as many bits,
and nowhere else. -/
theorem seed_back_any (K : Codes) (s : OracleShape) (o : Nat) (seed : SampleSeed) (row0 : Row)
    (tt : E) (h : Send.form K s o seed 0 = some row0) (h1 : s.answers = 1)
    (hboth : ((Send.cube K s).hasMain && (Send.cube K s).hasMask) = true)
    (hlen : (Send.cube K s).bits ≤ seed.z.length)
    (htop : (Send.cube K s).maskBits = (Send.cube K s).mainBits →
      okE (seed.z.getD ((Send.cube K s).bits - 1) zeroE) = true) :
    ∃ e zz, seedOfRow K s { row0 with target := tt } = some ⟨zz, backB seed.beta e⟩ ∧
      zz.length = (Send.cube K s).bits ∧
      ∀ β a, Send.form K s o ⟨zz, β⟩ a = Send.form K s o ⟨seed.z, β⟩ a := by
  by_cases hlt : (Send.cube K s).maskBits < (Send.cube K s).mainBits
  · obtain ⟨e, hr⟩ := seed_back_raw K s o seed row0 tt h h1 hboth hlen
    have hn : (Send.cube K s).bits = (Send.cube K s).mainBits + 1 := by
      rw [bits_both hboth, Nat.max_eq_left (by omega)]
    rw [if_pos (by omega)] at hr
    refine ⟨e, _, hr, ?_, fun β a => form_topB K s o seed.z β a hboth hn hlt (by omega)⟩
    rw [List.length_append, List.length_take, hn]
    simp only [List.length_cons, List.length_nil]
    omega
  · have ht : okE (seed.z.getD ((Send.cube K s).bits - 1) zeroE) = true ∨
        ¬ (Send.cube K s).maskBits ≤ (Send.cube K s).mainBits := by
      by_cases he : (Send.cube K s).maskBits = (Send.cube K s).mainBits
      · exact Or.inl (htop he)
      · exact Or.inr (by omega)
    have hb : ∃ e, seedOfRow K s { row0 with target := tt } =
        some ⟨seed.z.take (Send.cube K s).bits, backB seed.beta e⟩ := by
      rcases ht with ht | ht
      · have hMZ := hboth
        rw [Bool.and_eq_true] at hMZ
        exact seed_back₂ K s o seed row0 tt h h1 hMZ.1 hMZ.2 hlen ht
      · obtain ⟨e, hr⟩ := seed_back_raw K s o seed row0 tt h h1 hboth hlen
        rw [if_neg ht] at hr
        exact ⟨e, hr⟩
    obtain ⟨e, hr⟩ := hb
    refine ⟨e, _, hr, ?_, fun β a => form_take K s o seed.z β a⟩
    rw [List.length_take]
    omega

/-! ### The twelve clauses -/

/-- The twelve clauses, from what is read back: the tail of sampleL_of_seed's own proof, with the
point read back as a letter. -/
theorem sampleL_of_backZ (K : Codes) (m : Seat1) (x : OnBytes.Oracle) (seed : SampleSeed)
    (row0 : Row) (tt : E) (β : GEˣ) (e : E) (zz : List E) (hs : x.sampled = true)
    (hform : Send.form K m.sh m.id seed 0 = some row0)
    (hrows : x.sampleRows.toList = [{ row0 with target := tt }])
    (hβ : (β : GE) = readE seed.beta) (h1 : m.sh.answers = 1)
    (hback : seedOfRow K m.sh { row0 with target := tt } = some ⟨zz, backB seed.beta e⟩)
    (hzl : zz.length = (Send.cube K m.sh).bits)
    (hzf : ∀ β a, Send.form K m.sh m.id ⟨zz, β⟩ a = Send.form K m.sh m.id ⟨seed.z, β⟩ a)
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
  have hfb : Send.form K m.sh m.id ⟨zz, backB seed.beta e⟩ 0 = some row0 := by
    rw [form_back, hzf]
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
  refine ⟨hs, hsize, h1, hk, rfl, ?_, hzl, ?_, backB_ok _ _, hcase, hpM, hpZ⟩
  · unfold formIs
    rw [hfb]
    exact rowSame_self row0 tt (by rw [hr]; rfl) (by rw [hf]; rfl)
  · rw [hne]
    rfl

/-- **The twelve clauses at both tables.** -/
theorem sampleL_of_seed_both (K : Codes) (m : Seat1) (x : OnBytes.Oracle) (seed : SampleSeed)
    (row0 : Row) (tt : E) (β : GEˣ) (hs : x.sampled = true)
    (hform : Send.form K m.sh m.id seed 0 = some row0)
    (hrows : x.sampleRows.toList = [{ row0 with target := tt }])
    (hlen : bitsZ K m.sh ≤ seed.z.length) (hβ : (β : GE) = readE seed.beta)
    (h1 : m.sh.answers = 1) (hM : 0 < m.sh.mainRows) (hZ : 0 < m.sh.maskRows)
    (htop : (Send.cube K m.sh).maskBits = (Send.cube K m.sh).mainBits →
      okE (seed.z.getD (bitsZ K m.sh - 1) zeroE) = true)
    (hcase : (0 < m.sh.maskRows ∨ m.sh.mainDeg = 3) ∨ (m.sh.maskRows = 0 ∧ m.sh.mainDeg = 1))
    (hpM : m.sh.mainRows = 0 ∨ 2 ^ ceilLog2 (mainB K m.sh).ell = (mainB K m.sh).ell)
    (hpZ : m.sh.maskRows = 0 ∨ 2 ^ ceilLog2 (maskB K m.sh).ell = (maskB K m.sh).ell) :
    ok (sampleL K m x) = true := by
  have hboth : ((Send.cube K m.sh).hasMain && (Send.cube K m.sh).hasMask) = true := by
    have cM : (Send.cube K m.sh).hasMain = decide (0 < m.sh.mainRows) := rfl
    have cZ : (Send.cube K m.sh).hasMask = decide (0 < m.sh.maskRows) := rfl
    rw [cM, cZ, decide_eq_true hM, decide_eq_true hZ]
    rfl
  obtain ⟨e, zz, hback, hzl, hzf⟩ := seed_back_any K m.sh m.id seed row0 tt hform h1 hboth
    (by rw [cube_bits]; exact hlen) (by rw [cube_bits]; exact htop)
  exact sampleL_of_backZ K m x seed row0 tt β e zz hs hform hrows hβ h1 hback hzl hzf hcase hpM hpZ

/-- **sampleL_of_seed WITH hone STRUCK**: at every shape with a row and one answer. htop is asked
where the message has both tables AND these have as many bits, and nowhere else. -/
theorem sampleL_of_seed_all (K : Codes) (m : Seat1) (x : OnBytes.Oracle) (seed : SampleSeed)
    (row0 : Row) (tt : E) (β : GEˣ) (hs : x.sampled = true)
    (hform : Send.form K m.sh m.id seed 0 = some row0)
    (hrows : x.sampleRows.toList = [{ row0 with target := tt }])
    (hlen : bitsZ K m.sh ≤ seed.z.length) (hβ : (β : GE) = readE seed.beta)
    (h1 : m.sh.answers = 1)
    (hsome : 0 < m.sh.mainRows ∨ 0 < m.sh.maskRows)
    (hcase : (0 < m.sh.maskRows ∨ m.sh.mainDeg = 3) ∨ (m.sh.maskRows = 0 ∧ m.sh.mainDeg = 1))
    (hpM : m.sh.mainRows = 0 ∨ 2 ^ ceilLog2 (mainB K m.sh).ell = (mainB K m.sh).ell)
    (hpZ : m.sh.maskRows = 0 ∨ 2 ^ ceilLog2 (maskB K m.sh).ell = (maskB K m.sh).ell)
    (htop : 0 < m.sh.mainRows → 0 < m.sh.maskRows →
      (Send.cube K m.sh).maskBits = (Send.cube K m.sh).mainBits →
      okE (seed.z.getD (bitsZ K m.sh - 1) zeroE) = true) :
    ok (sampleL K m x) = true := by
  by_cases hone : 0 < m.sh.mainRows ∧ 0 < m.sh.maskRows
  · exact sampleL_of_seed_both K m x seed row0 tt β hs hform hrows hlen hβ h1 hone.1 hone.2
      (htop hone.1 hone.2) hcase hpM hpZ
  · exact sampleL_of_seed K m x seed row0 tt β hs hform hrows hlen hβ h1 hone hsome hcase hpM hpZ

/-! ### Two examples, by the kernel -/

/-- Two codes with messages of two elements. -/
def exK : Codes := { base := #[⟨3, 2, 1⟩], mask := #[⟨3, 2, 1⟩] }

/-- One main row and one mask row, one answer: both tables, with as many bits. -/
def exSh : OracleShape :=
  { code := 0, mainRows := 1, mainDeg := 1, maskRows := 1, maskCode := 0, answers := 1 }

def exM : Seat1 := ⟨0, exSh, 0, 0, default, 0⟩

/-- A seed whose point has the cube's two coordinates; the second is a letter. -/
def exSeed (top : E) : SampleSeed := ⟨[E.mk3 7 0 0, top], E.mk3 3 0 0⟩

/-- A message whose one sample row is Send.form's at that seed. -/
def exX (top : E) : OnBytes.Oracle :=
  { shape := exSh, sampled := true
    sampleRows := ((Send.form exK exSh 0 (exSeed top) 0).map fun r => #[r]).getD #[] }

/-- **All premises of sampleL_of_seed_all can be met together, at both tables.** -/
theorem example_met : ok (sampleL exK exM (exX (E.mk3 5 0 0))) = true := by
  have hs : (Send.form exK exSh 0 (exSeed (E.mk3 5 0 0)) 0).isSome = true := by decide +kernel
  obtain ⟨row0, hform⟩ := Option.isSome_iff_exists.1 hs
  have h3 : readE (E.mk3 3 0 0) ≠ 0 := fun q => by
    have := (isZeroE_iff (E.mk3 3 0 0) (by decide +kernel)).2 q
    revert this
    decide +kernel
  refine sampleL_of_seed_all exK exM (exX (E.mk3 5 0 0)) (exSeed (E.mk3 5 0 0)) row0 row0.target
    (Units.mk0 _ h3) rfl hform ?_ (by decide +kernel) rfl rfl (Or.inl (by decide))
    (Or.inl (Or.inl (by decide))) (Or.inr (by decide +kernel)) (Or.inr (by decide +kernel))
    (fun _ _ _ => by decide +kernel)
  unfold exX
  rw [hform]
  rfl

/-- The same, evaluated: the test accepts there. -/
theorem example_evaluated : ok (sampleL exK exM (exX (E.mk3 5 0 0))) = true := by decide +kernel

/-- **htop IS NEEDED**: at a top coordinate whose first word is the prime itself, the row is
Send.form's at the seed as before, and the test rejects. -/
theorem top_needed : okE (E.mk3 pW 0 0) = false ∧
    (Send.form exK exSh 0 (exSeed (E.mk3 pW 0 0)) 0).isSome = true ∧
    ok (sampleL exK exM (exX (E.mk3 pW 0 0))) = false := by decide +kernel

/-- The main code's messages have four elements, the mask code's two: the main table is the larger. -/
def exK2 : Codes := { base := #[⟨4, 4, 1⟩], mask := #[⟨3, 2, 1⟩] }

def exSeed2 (top : E) : SampleSeed := ⟨[E.mk3 7 0 0, E.mk3 9 0 0, top], E.mk3 3 0 0⟩

def exX2 (top : E) : OnBytes.Oracle :=
  { shape := exSh, sampled := true
    sampleRows := ((Send.form exK2 exSh 0 (exSeed2 top) 0).map fun r => #[r]).getD #[] }

/-- **Where the main table is the larger htop is not needed**: with the prime itself as the top
coordinate's first word the test accepts. -/
theorem top_idle : (Send.cube exK2 exSh).maskBits < (Send.cube exK2 exSh).mainBits ∧
    okE (E.mk3 pW 0 0) = false ∧ ok (sampleL exK2 exM (exX2 (E.mk3 pW 0 0))) = true := by
  decide +kernel

/-- sampleL_of_seed_all's statement without htop. -/
def WithoutTop : Prop := ∀ (K : Codes) (m : Seat1) (x : OnBytes.Oracle) (seed : SampleSeed)
    (row0 : Row) (tt : E) (β : GEˣ), x.sampled = true →
    Send.form K m.sh m.id seed 0 = some row0 →
    x.sampleRows.toList = [{ row0 with target := tt }] →
    bitsZ K m.sh ≤ seed.z.length → (β : GE) = readE seed.beta →
    m.sh.answers = 1 →
    (0 < m.sh.mainRows ∨ 0 < m.sh.maskRows) →
    ((0 < m.sh.maskRows ∨ m.sh.mainDeg = 3) ∨ (m.sh.maskRows = 0 ∧ m.sh.mainDeg = 1)) →
    (m.sh.mainRows = 0 ∨ 2 ^ ceilLog2 (mainB K m.sh).ell = (mainB K m.sh).ell) →
    (m.sh.maskRows = 0 ∨ 2 ^ ceilLog2 (maskB K m.sh).ell = (maskB K m.sh).ell) →
    ok (sampleL K m x) = true

/-- That WithoutTop's ten premises ARE sampleL_of_seed_all's other ten, in order: held by Lean: each
of that theorem's premises is taken at WithoutTop's place of the same number. -/
theorem withoutTop_is_all (H : WithoutTop) : type_of% @sampleL_of_seed_all :=
  fun K m x seed row0 tt β hs hform hrows hlen hβ h1 hsome hcase hpM hpZ _ =>
    H K m x seed row0 tt β hs hform hrows hlen hβ h1 hsome hcase hpM hpZ

/-- And they are those of H2K.Pin.sampleL_of_seed but hone. -/
theorem withoutTop_is_theirs (H : WithoutTop) : type_of% @sampleL_of_seed :=
  fun K m x seed row0 tt β hs hform hrows hlen hβ h1 _ hsome hcase hpM hpZ =>
    H K m x seed row0 tt β hs hform hrows hlen hβ h1 hsome hcase hpM hpZ

/-- **sampleL_of_seed_all WITHOUT htop IS FALSE**: at that seed the other ten premises are all met, and
the test rejects. -/
theorem without_top_false : ¬ WithoutTop := by
  intro H
  obtain ⟨row0, hform⟩ := Option.isSome_iff_exists.1 top_needed.2.1
  have h3 : readE (E.mk3 3 0 0) ≠ 0 := fun q => by
    have := (isZeroE_iff (E.mk3 3 0 0) (by decide +kernel)).2 q
    revert this
    decide +kernel
  have hy := H exK exM (exX (E.mk3 pW 0 0)) (exSeed (E.mk3 pW 0 0)) row0 row0.target
    (Units.mk0 _ h3) rfl hform
    (by
      unfold exX
      rw [hform]
      rfl)
    (by decide +kernel) rfl rfl (Or.inl (by decide))
    (Or.inl (Or.inl (by decide))) (Or.inr (by decide +kernel)) (Or.inr (by decide +kernel))
  rw [top_needed.2.2] at hy
  cases hy

end IM

#print axioms IM.form_topB
#print axioms IM.seed_back_raw
#print axioms IM.seed_back_any
#print axioms IM.sampleL_of_backZ
#print axioms IM.sampleL_of_seed_both
#print axioms IM.sampleL_of_seed_all
#print axioms IM.example_met
#print axioms IM.example_evaluated
#print axioms IM.top_needed
#print axioms IM.top_idle
#print axioms IM.withoutTop_is_all
#print axioms IM.withoutTop_is_theirs
#print axioms IM.without_top_false
