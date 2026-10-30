-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/ReadPrefix.lean: what Given.read returns on the parameter bytes of a plan, with
no bound on the number of the plan's entries.

OnBytes/Params/Fit/ReadNorm.lean asks that the plan have fewer than 2^64 entries. The number of
entries is spelled modulo 2^64 too. So the reader reads that many entries, a first part of the
plan's, and then looks for the item "configuration". If an entry were left, the reader would meet
that entry's name there. So, if no entry has that name, where the reader returns at all no entry is
left: the plan has fewer than 2^64 entries.

Main definitions: cutP (the plan with every number modulo 2^64 and the first length mod 2^64
entries); restB (the bytes of the entries that are left).
Main theorems.
 - bytes_cutP, fit_cutP; paramsRead_head (the library's reader on a fitting plan's bytes with any
   bytes behind: the plan, and that it found the item "configuration" behind the plan).
 - Given.read_prefix, read_mem: the plan as read back is cutP; each of its entries is an entry of
   the plan, reduced.
 - read_short, Given.read_whole: if no entry is named "configuration", the plan has fewer than
   2^64 entries, and the plan as read back is normP.

What is asked: each entry's name fits (Fmt.nameFit); for the last two, that no entry has the name
of the configuration's item. Nothing if the reader refuses. Nothing on soundness. For proofs only;
the program does not import this file.


-/
import OnBytes.Params.Fit.ReadNorm

set_option autoImplicit false

namespace OnBytes.Params

open Fmt

theorem cat_app (a b : List ByteArray) : cat (a ++ b) = cat a ++ cat b := by
  induction a with
  | nil => rw [List.nil_append, cat_nil, ByteArray.empty_append]
  | cons x a ih => rw [List.cons_append, cat_cons, cat_cons, ih, ByteArray.append_assoc]

/-- The plan with every number modulo 2^64, and as many entries as the spelled number says. -/
def cutP (P : Plan) : Plan where
  field := P.field
  salt := P.salt % 2 ^ 64
  nonce := P.nonce % 2 ^ 64
  posB := P.posB % 2 ^ 64
  samples := P.samples % 2 ^ 64
  saved := P.saved % 2 ^ 64
  entries := (P.entries.take (P.entries.length % 2 ^ 64)).map normE

/-- The bytes of the entries that are left. -/
def restB (P : Plan) : ByteArray :=
  cat ((P.entries.drop (P.entries.length % 2 ^ 64)).map Entry.bytes)

theorem length_cutP (P : Plan) : (cutP P).entries.length = P.entries.length % 2 ^ 64 := by
  show ((P.entries.take (P.entries.length % 2 ^ 64)).map normE).length = _
  rw [List.length_map, List.length_take]
  exact Nat.min_eq_left (Nat.mod_le _ _)

/-- The plan's bytes are those of the cut plan and then those of the entries that are left. -/
theorem bytes_cutP (P : Plan) : P.bytes = (cutP P).bytes ++ restB P := by
  have hA : ((P.entries.take (P.entries.length % 2 ^ 64)).map normE).map Entry.bytes =
      (P.entries.take (P.entries.length % 2 ^ 64)).map Entry.bytes := by
    rw [List.map_map]
    exact List.map_congr_left fun x _ => bytes_normE x
  have hs : P.entries.map Entry.bytes =
      (P.entries.take (P.entries.length % 2 ^ 64)).map Entry.bytes ++
        (P.entries.drop (P.entries.length % 2 ^ 64)).map Entry.bytes := by
    rw [← List.map_append, List.take_append_drop]
  have hb : (cutP P).bytes =
      u64n P.field.num ++ u64n 1 ++ u64n P.salt ++ u64n P.nonce ++ u64n P.posB ++
        u64n P.samples ++ u64n P.saved ++ u64n P.entries.length ++
        cat ((P.entries.take (P.entries.length % 2 ^ 64)).map Entry.bytes) := by
    unfold Plan.bytes
    rw [length_cutP]
    show u64n P.field.num ++ u64n 1 ++ u64n (P.salt % 2 ^ 64) ++ u64n (P.nonce % 2 ^ 64) ++
      u64n (P.posB % 2 ^ 64) ++ u64n (P.samples % 2 ^ 64) ++ u64n (P.saved % 2 ^ 64) ++
      u64n (P.entries.length % 2 ^ 64) ++
      cat (((P.entries.take (P.entries.length % 2 ^ 64)).map normE).map Entry.bytes) = _
    rw [hA]
    simp only [u64n_mod]
  rw [hb]
  unfold Plan.bytes restB
  rw [hs, cat_app]
  exact ByteArray.append_assoc.symm

/-- The cut plan fits the format's words. -/
theorem fit_cutP {P : Plan} (hn : ∀ e ∈ P.entries, nameFit e.name = true) :
    (cutP P).fit = true := by
  unfold Plan.fit
  rw [Bool.and_eq_true]
  constructor
  · refine List.all_eq_true.2 fun n h => decide_eq_true ?_
    rw [length_cutP] at h
    simp only [cutP, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Nat.mod_lt _ (Nat.two_pow_pos 64)
  · refine List.all_eq_true.2 fun e he => ?_
    obtain ⟨e0, h0, rfl⟩ := List.mem_map.1 he
    exact fit_normE (hn e0 (List.mem_of_mem_take h0))

/-- The library's reader on the version's item, a fitting plan's bytes and any bytes behind: it
returns that plan, and behind the plan it has found an item under the configuration's name. -/
theorem paramsRead_head {P : Plan} {T : ByteArray} {x : Fmt.Params} (hf : P.fit = true)
    (h : paramsRead (item versionName (versionValue P.field) ++ P.bytes ++ T) = some x) :
    x.plan = P ∧ ∃ cv k, rdItem (item versionName (versionValue P.field) ++ P.bytes ++ T)
      ((item versionName (versionValue P.field)).size + P.bytes.size) =
        some ((configName, cv), k) := by
  generalize hv : item versionName (versionValue P.field) = V at h ⊢
  have a := undoes_item _ (version_ok P.field) ByteArray.empty (P.bytes ++ T)
  simp only [hv, ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at a
  rw [← ByteArray.append_assoc] at a
  have b := undoes_plan P (okPlan_of_fit P hf) V T
  unfold paramsRead at h
  rw [a] at h
  simp only at h
  rw [b] at h
  simp only at h
  split at h
  · split at h
    · rename_i cn cv k hi
      split at h
      · rename_i hc
        obtain ⟨y, _, hy⟩ := Option.map_eq_some_iff.1 h
        cases hy
        have hcn : cn = configName := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          exact hc.1
        subst hcn
        exact ⟨rfl, cv, k, hi⟩
      · cases h
    · cases h
  · cases h

/-- The parameter bytes, with the cut plan in front. -/
theorem paramsBytes_cut (P : Plan) (cfg : ByteArray) (others : List (String × ByteArray)) :
    paramsBytes P cfg others =
      item versionName (versionValue (cutP P).field) ++ (cutP P).bytes ++
        (restB P ++ (item configName cfg ++ items others)) := by
  show item versionName (versionValue P.field) ++ P.bytes ++ item configName cfg ++
    items others = item versionName (versionValue P.field) ++ (cutP P).bytes ++
      (restB P ++ (item configName cfg ++ items others))
  rw [bytes_cutP]
  simp only [ByteArray.append_assoc]

/-- What the library's reader returns on the parameter bytes. -/
theorem paramsRead_cut {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {x : Fmt.Params} (hn : ∀ e ∈ P.entries, nameFit e.name = true)
    (h : paramsRead (paramsBytes P cfg others) = some x) : x.plan = cutP P := by
  rw [paramsBytes_cut] at h
  exact (paramsRead_head (fit_cutP hn) h).1

/-- If no entry has the name of the configuration's item, no entry is left. -/
theorem paramsRead_short {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {x : Fmt.Params} (hn : ∀ e ∈ P.entries, nameFit e.name = true)
    (hc : ∀ e ∈ P.entries, e.name ≠ configName)
    (h : paramsRead (paramsBytes P cfg others) = some x) : P.entries.length < 2 ^ 64 := by
  cases hd : P.entries.drop (P.entries.length % 2 ^ 64) with
  | nil =>
    exact Nat.lt_of_le_of_lt (List.drop_eq_nil_iff.1 hd) (Nat.mod_lt _ (Nat.two_pow_pos 64))
  | cons e B =>
    exfalso
    have he : e ∈ P.entries := List.mem_of_mem_drop (hd ▸ List.mem_cons_self)
    have hf := hn e he
    rw [nameFit_iff] at hf
    rw [paramsBytes_cut] at h
    obtain ⟨_, cv, k, hi⟩ := paramsRead_head (fit_cutP hn) h
    have hr : restB P = text (ascii e.name) ++
        (cat ((e.words.map UInt64.ofNat).map u64) ++ cat (B.map Entry.bytes)) := by
      unfold restB
      rw [hd, List.map_cons, cat_cons, entry_bytes, ByteArray.append_assoc]
    generalize item versionName (versionValue (cutP P).field) = V at hi
    have eb : V ++ (cutP P).bytes ++ (restB P ++ (item configName cfg ++ items others)) =
        (V ++ (cutP P).bytes) ++ text (ascii e.name) ++
          (cat ((e.words.map UInt64.ofNat).map u64) ++ cat (B.map Entry.bytes) ++
            (item configName cfg ++ items others)) := by
      rw [hr]
      simp only [ByteArray.append_assoc]
    have a := undoes_name (ascii e.name) ⟨hf.2, isName_ascii _ hf.1⟩ (V ++ (cutP P).bytes)
      (cat ((e.words.map UInt64.ofNat).map u64) ++ cat (B.map Entry.bytes) ++
        (item configName cfg ++ items others))
    rw [eb, ← ByteArray.size_append] at hi
    unfold rdItem at hi
    rw [a] at hi
    simp only at hi
    obtain ⟨y, _, hy⟩ := Option.map_eq_some_iff.1 hi
    have hname : nameOf (ascii e.name) = configName := congrArg (fun z => z.1.1) hy
    rw [nameOf_ascii _ hf.1] at hname
    exact hc e he hname

/-- **The plan as read back is the cut plan.** -/
theorem Given.read_prefix {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {g : Given} (hn : ∀ e ∈ P.entries, nameFit e.name = true)
    (h : Given.read (paramsBytes P cfg others) = some g) : g.plan = cutP P := by
  unfold Given.read at h
  rw [paramsReadT_eq] at h
  cases hp : paramsRead (paramsBytes P cfg others) with
  | none =>
    rw [hp] at h
    cases h
  | some x =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h
      exact paramsRead_cut hn hp
    · cases h

/-- Each entry as read back is an entry of the plan, reduced. -/
theorem read_mem {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)} {g : Given}
    (hn : ∀ e ∈ P.entries, nameFit e.name = true)
    (h : Given.read (paramsBytes P cfg others) = some g) :
    ∀ e' ∈ g.plan.entries, ∃ e ∈ P.entries, e' = normE e := by
  intro e' he'
  rw [Given.read_prefix hn h] at he'
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
  exact ⟨e, List.mem_of_mem_take he, rfl⟩

/-- Where Given.read returns and no entry is named as the configuration's item, the plan has fewer
than 2^64 entries. -/
theorem read_short {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)} {g : Given}
    (hn : ∀ e ∈ P.entries, nameFit e.name = true)
    (hc : ∀ e ∈ P.entries, e.name ≠ configName)
    (h : Given.read (paramsBytes P cfg others) = some g) : P.entries.length < 2 ^ 64 := by
  unfold Given.read at h
  rw [paramsReadT_eq] at h
  cases hp : paramsRead (paramsBytes P cfg others) with
  | none =>
    rw [hp] at h
    cases h
  | some x => exact paramsRead_short hn hc hp

/-- **The plan as read back is the whole plan, reduced.** -/
theorem Given.read_whole {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {g : Given} (hn : ∀ e ∈ P.entries, nameFit e.name = true)
    (hc : ∀ e ∈ P.entries, e.name ≠ configName)
    (h : Given.read (paramsBytes P cfg others) = some g) : g.plan = normP P :=
  Given.read_norm hn (read_short hn hc h) h

end OnBytes.Params
