-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/RowsShapes.lean: WHAT THE LIST OF ALL SENDINGS WITH THEIR RADII
(Johnson.G.sendRowsOf, Johnson/G/LinkSig.lean) SAYS OF SHAPES, BY ITS OWN TEXT: wherever it returns,
row by row, in order: the file, the chain, and THE SAMPLED MESSAGES' SHAPES are those of the list of
sendings (Johnson.G.sendsOf) at the same three files: the sent messages with an answer, in order.
Theorems. No value is evaluated; no scope, no public part.

  sampledOf x       the shapes of the messages of the sending x that are sampled
  zip_fst, zip_snd_map, zip_snd_prefix, flatMap_prefix, zip_map_of   five facts on lists
  ite_ok            where "unless c do throw" goes on, c holds, and so does what stands behind it
  pack_shapes       packListOf: its shapes are a first stretch of the sendings' sampled shapes
  rows_shapes       THE END: sendRowsOf

Why. Three named tests on the public parameters compare the rows' (shape, radius) pairs with the
planner's seats. That the SHAPES are the sendings' own needs no evaluation: it is the text's.
Limits. Nothing on the radii. Nothing on whether sendRowsOf returns. No soundness statement.

-/
import Johnson.G.LinkSig
import Johnson.G.DataEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Opts

open OnBytes OnBytes.Params
open Johnson.G (Sending ChainSends SendRow sendsOf packListOf sendRowsOf)
open Johnson.G.OfPlan (mapM_map bind_ok)

/-- The shapes of the messages of a sending that are sampled, in order. -/
def sampledOf (x : Sending) : List OracleShape :=
  (x.sent.filter fun m => 0 < m.shape.answers).map (·.shape)

theorem zip_fst {α β : Type} : ∀ (a : List α) (b : List β), a.length = b.length →
    (a.zip b).map (fun x => x.1) = a
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [zip_fst a b (by simpa using h)]

theorem zip_snd_map {α β γ : Type} (f : β → γ) : ∀ (a : List α) (b : List β),
    a.length = b.length → (a.zip b).map (fun x => f x.2) = b.map f
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [zip_snd_map f a b (by simpa using h)]

theorem zip_snd_prefix {α β : Type} : ∀ (a : List α) (b : List β), (a.zip b).map Prod.snd <+: b
  | [], b => by simp
  | _ :: _, [] => by simp
  | x :: a, y :: b => by
    simp only [List.zip_cons_cons, List.map_cons]
    exact (List.prefix_cons_inj y).2 (zip_snd_prefix a b)

theorem flatMap_prefix {α β : Type} (f : α → List β) {a b : List α} (h : a <+: b) :
    a.flatMap f <+: b.flatMap f := by
  obtain ⟨t, rfl⟩ := h
  rw [List.flatMap_append]
  exact List.prefix_append _ _

theorem zip_map_of {α β γ δ : Type} (F : α → γ) (g : β → δ) (g' : α → δ) :
    ∀ (a : List α) (b : List β), b.map g = a.map g' →
      (a.zip b).map (fun x => (F x.1, g x.2)) = a.map fun y => (F y, g' y)
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.zip_cons_cons, List.map_cons, h.1, zip_map_of F g g' a b h.2]

theorem ite_ok {c : Prop} [Decidable c] {α : Type} {e : String} {k k' : PUnit → Except String α}
    {r : α} (h : (if c then pure PUnit.unit >>= k else throw e >>= k') = .ok r) :
    c ∧ k PUnit.unit = .ok r := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact ⟨hc, h⟩
  · rw [if_neg hc] at h
    cases h

/-- **packListOf's shapes** are a first stretch of the sendings' sampled shapes. -/
theorem pack_shapes {pol lay KL : ByteArray} {pack : List (Codes × List (OracleShape × ℕ))}
    {sends : List ChainSends} (hp : packListOf pol lay KL = .ok pack)
    (hs : sendsOf pol lay KL = .ok sends) :
    pack.map (fun y => y.2.map fun z => z.1) <+: sends.flatMap fun d => d.sends.map sampledOf := by
  unfold packListOf at hp
  obtain ⟨⟨s, chains⟩, -, hp⟩ := bind_ok hp
  dsimp only at hp
  rw [hs] at hp
  obtain ⟨sends', e, hp⟩ := bind_ok hp
  obtain rfl : sends = sends' := Except.ok.inj e
  obtain ⟨per, hper, hp⟩ := bind_ok hp
  obtain rfl : per.flatten = pack := Except.ok.inj hp
  have key := mapM_map _
    (fun r : List (Codes × List (OracleShape × ℕ)) => r.map fun y => y.2.map fun z => z.1)
    (fun cd : Johnson.G.Chain × ChainSends => cd.2.sends.map sampledOf)
    (by
      rintro ⟨c, d⟩ r h
      dsimp only at h
      obtain ⟨h1, h⟩ := ite_ok h
      have hl := eq_of_beq h1
      have k2 := mapM_map _ (fun y : Codes × List (OracleShape × ℕ) => y.2.map fun z => z.1)
        (fun ox : List SampleSize × Sending => sampledOf ox.2)
        (by
          rintro ⟨o, x⟩ y h
          dsimp only at h
          obtain ⟨t1, h⟩ := ite_ok h
          have hl1 := eq_of_beq t1
          obtain ⟨l, hl2, h⟩ := bind_ok h
          obtain ⟨-, h⟩ := ite_ok h
          obtain ⟨-, h⟩ := ite_ok h
          obtain rfl : (d.codes, l) = y := Except.ok.inj h
          have k3 := mapM_map _ (fun z : OracleShape × ℕ => z.1)
            (fun q : OracleShape × SampleSize => q.1)
            (by
              rintro ⟨sh, sm⟩ b hb
              dsimp only at hb
              obtain ⟨ρ, -, hb⟩ := bind_ok hb
              obtain rfl := Except.ok.inj hb
              rfl) _ _ hl2
          show l.map (fun z => z.1) = sampledOf x
          rw [k3]
          exact zip_fst _ _ hl1.symm) _ _ h
      show r.map (fun y => y.2.map fun z => z.1) = d.sends.map sampledOf
      rw [k2]
      exact zip_snd_map sampledOf _ _ hl) _ _ hper
  rw [List.map_flatten, key]
  have e2 : ((chains.zip sends).map fun cd => cd.2.sends.map sampledOf).flatten =
      ((chains.zip sends).map Prod.snd).flatMap fun d => d.sends.map sampledOf := by
    rw [List.flatMap_def, List.map_map]
    rfl
  rw [e2]
  exact flatMap_prefix _ (zip_snd_prefix chains sends)

/-- **THE END: wherever sendRowsOf returns, its rows' files, chains and sampled shapes are the list
of sendings' own, row by row, in order.** -/
theorem rows_shapes {pol lay KL : ByteArray} {rows : List SendRow} {sends : List ChainSends}
    (hr : sendRowsOf pol lay KL = .ok rows) (hs : sendsOf pol lay KL = .ok sends) :
    rows.map (fun r => ((r.file, r.chain), r.sampled.map fun z => z.1)) =
      (sends.flatMap fun c => c.sends.map fun x => (c, x)).map
        fun cx => ((cx.1.file, cx.1.chain), sampledOf cx.2) := by
  unfold sendRowsOf at hr
  rw [hs] at hr
  obtain ⟨sends', e, hr⟩ := bind_ok hr
  obtain rfl : sends = sends' := Except.ok.inj e
  obtain ⟨pack, hp, hr⟩ := bind_ok hr
  dsimp only at hr
  obtain ⟨t, hr⟩ := ite_ok hr
  have hlen := eq_of_beq t
  obtain rfl := Except.ok.inj hr
  have hflat : (sends.flatMap fun d => d.sends.map sampledOf) =
      (sends.flatMap fun c => c.sends.map fun x => (c, x)).map fun cx => sampledOf cx.2 := by
    rw [List.map_flatMap]
    simp only [List.map_map, Function.comp_def]
  have heq : pack.map (fun y => y.2.map fun z => z.1) =
      (sends.flatMap fun c => c.sends.map fun x => (c, x)).map fun cx => sampledOf cx.2 := by
    rw [← hflat]
    refine (pack_shapes hp hs).eq_of_length ?_
    rw [hflat, List.length_map, List.length_map, hlen]
  rw [List.map_map, ← zip_map_of (fun cx : ChainSends × Sending => (cx.1.file, cx.1.chain))
    (fun y : Codes × List (OracleShape × ℕ) => y.2.map fun z => z.1)
    (fun cx => sampledOf cx.2) _ _ heq]
  refine List.map_congr_left ?_
  rintro ⟨⟨c, x⟩, p⟩ _
  rfl

end P1Opts

#print axioms P1Opts.pack_shapes
#print axioms P1Opts.rows_shapes
