-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/LitPow.lean: the one comparison of natural numbers of a sending's round of seeds (the text of powB's
body, Johnson/Desc/K1/Law/PowB.lean) AT EVERY PLACE THAT IS AN ELEMENT OF THE LIBRARY's TWO WRITTEN-OUT LISTS OF SENDINGS
(Johnson/G/PackLit.lean: packSmallLit, 46; packFullLit, 119), at the lists' own radii, at k = 128. Typed
over the K1/Law text in the library alone.

Main names (q: any number; the field's size enters at the two evaluations alone):
  termAt, countAt        a sampled message's term, and their sum over a list of shapes with radii, at c joint coordinates.
  sum_sampled            the sum over all of a place's messages «if sampled, its term, else 0» (eNat's own text) is countAt over
                         sampledList P rad.
  coordinates_bMax       P.coordinates = bMax P.codes (sampledList P rad).
  (seeds_one: under condPort a place has one seed: the library's Johnson/Desc/K1/Law/GoodSend4.lean's, CALLED.)
  blocks_seed            at one seed the block sampler of the place's entry of the seeds has blocksFor (18 c + 36) blocks.
  litPow q k x           the comparison as a Boolean on an element x of a list alone: no place in it; no work counted.
  pow_of_lit             ITS YES GIVES THE COMPARISON AT EVERY PLACE P WITH P.codes = x.1, sampledList P rad = x.2, one seed:
                         at the place's own entry, its own coordinates and its own work.
  lit_pow_small | lit_pow_full     litPow at the format's field and k = 128 is true at every element: by an evaluation in
                         Lean's kernel (decide +kernel). lit_pow_small_far | _full_far: at 192 it is true at none.
  PowAt, pow_small | pow_full      so the comparison at 128 at every such place. fits_full: in Lit.lean's letters (FitsLit).
How it is used. powB P rad k = true := decide_eq_true (pow_of_lit qN k P rad x …) (eNat and qN unfold to this file's text);
then powB_send | powB_open give Err.Below at 2^-k at the count errPort P rad.

What is not claimed. THE COMPARISON ALONE HAS NO TOOTH IN THE RADIUS: beyond the Johnson radius the library's lOf is 0 (a division by 0 in the natural numbers), the count is 0 and litPow | powB say yes (seen in a run: every radius one half more: all yes): it is condPort (meetsB's InJohnson) that refuses there: so a yes of the comparison counts only beside condPort's. That a place of a chain made of the public files is an element of a list (the two equations) is a
premise, as in Lit.lean. The limits of Johnson/G/PackLit.lean and PackList.lean on the map from a message to its radius stand.
One answer a message. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Lit
import Johnson.Desc.K1.Law.Price
import Johnson.Desc.K1.Law.GoodSend4
import Run.PlanDraws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob Run

/-! ## Plain lists -/

theorem sum_if_filter {α : Type} (p : α → Prop) [DecidablePred p] (f : α → Nat) :
    ∀ l : List α, (l.map fun a => if p a then f a else 0).sum = ((l.filter fun a => decide (p a)).map f).sum
  | [] => rfl
  | a :: l => by
      by_cases h : p a
      · simp [h, sum_if_filter p f l]
      · simp [h, sum_if_filter p f l]

private theorem maxOver_le {α : Type} (g : α → Nat) (B : Nat) :
    ∀ (l : List α) (acc : Nat), acc ≤ B → (∀ s ∈ l, g s ≤ B) → l.foldl (fun a s => max a (g s)) acc ≤ B
  | [], _, h, _ => h
  | t :: l, _, h, hl =>
      maxOver_le g B l _ (max_le h (hl t (by simp))) fun s hs => hl s (by simp [hs])

theorem foldr_max_le (B : Nat) : ∀ l : List Nat, (∀ n ∈ l, n ≤ B) → l.foldr max 0 ≤ B
  | [], _ => Nat.zero_le _
  | t :: l, hl => max_le (hl t (by simp)) (foldr_max_le B l fun n hn => hl n (by simp [hn]))

/-! ## A place's sampled messages -/

/-- A message of the tuple is a sampled message of the place. -/
theorem tuple_at (P : Par) (s : OracleShape) (hs : s ∈ P.tuple) :
    ∃ k : Fin (shapesOf P).length, shapeAt P k = s ∧ sampledAt P k := by
  simp only [Par.tuple, List.mem_filter] at hs
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (show s ∈ shapesOf P from hs1)
  have h : ¬ ((shapesOf P)[i]).answers = 0 := by simpa using hs2
  exact ⟨⟨i, hi⟩, rfl, h⟩

theorem mem_sampledList (P : Par) (rad : Nat → Nat) (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    (shapeAt P k, rad k.val) ∈ sampledList P rad :=
  List.mem_map.2 ⟨k, List.mem_filter.2 ⟨List.mem_finRange k, decide_eq_true hk⟩, rfl⟩

/-- **The joint point's coordinates are the largest cube's bits among the sampled messages.** -/
theorem coordinates_bMax (P : Par) (rad : Nat → Nat) : P.coordinates = bMax P.codes (sampledList P rad) := by
  apply Nat.le_antisymm
  · refine maxOver_le (fun s => (Msg.of P.codes s).v) _ P.tuple 0 (Nat.zero_le _) fun s hs => ?_
    obtain ⟨k, rfl, hk⟩ := tuple_at P s hs
    show (Msg.of P.codes (shapeAt P k)).v ≤ _
    rw [v_bitsZ]
    exact le_foldr_max _ _ (List.mem_map.2 ⟨_, mem_sampledList P rad k hk, rfl⟩)
  · refine foldr_max_le _ _ fun n hn => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact bits_le_coordinates P k (of_decide_eq_true (List.mem_filter.1 hk).2)

/-! ## The count -/

/-- A sampled message's term, at c joint coordinates. -/
def termAt (q : Nat) (cs : Codes) (c : Nat) (x : OracleShape × Nat) : Nat :=
  (lOf cs x.1 x.2).choose 2 * clashSeeds q (bitsZ cs x.1) * q ^ (c - bitsZ cs x.1)

def countAt (q : Nat) (cs : Codes) (c : Nat) (l : List (OracleShape × Nat)) : Nat := (l.map (termAt q cs c)).sum

/-- **eNat's own text is the sum over the sampled messages' list.** -/
theorem sum_sampled (q c : Nat) (P : Par) (rad : Nat → Nat) :
    (List.ofFn fun k : Fin (shapesOf P).length => if sampledAt P k then
      (lOf P.codes (shapeAt P k) (rad k.val)).choose 2 * clashSeeds q (bitsZ P.codes (shapeAt P k)) *
        q ^ (c - bitsZ P.codes (shapeAt P k)) else 0).sum = countAt q P.codes c (sampledList P rad) := by
  rw [List.ofFn_eq_map]
  refine (sum_if_filter (fun k => sampledAt P k) (fun k => termAt q P.codes c (shapeAt P k, rad k.val)) _).trans ?_
  unfold countAt sampledList
  rw [List.map_map]
  rfl

/-- The same term with n (n − 1) / 2: so that it is evaluated fast. -/
def termB (q : Nat) (cs : Codes) (c : Nat) (x : OracleShape × Nat) : Nat :=
  (lOf cs x.1 x.2 * (lOf cs x.1 x.2 - 1) / 2) * clashSeeds q (bitsZ cs x.1) * q ^ (c - bitsZ cs x.1)

theorem termB_eq (q : Nat) (cs : Codes) (c : Nat) : termB q cs c = termAt q cs c := by
  funext x
  unfold termB termAt
  rw [Nat.choose_two_right]

/-! ## The round's blocks -/

/-- **At one seed: the blocks of the place's entry of the seeds.** -/
theorem blocks_seed (P : Par) (h1 : P.seeds = 1) :
    (bsRound .two (seedEntry P) .seeds).b = Fmt.blocksFor (18 * P.coordinates + 36) := by
  rw [(planDraws_law .two (seedEntry P) .seeds (Nat.zero_le _)).2]
  show Fmt.blocksFor (0 + (18 * (P.seeds * (P.coordinates + 1) - P.seeds) + 36 * P.seeds) + (0 + 31) / 32 + 0) = _
  rw [h1]
  congr 1
  omega

/-! ## The comparison -/

/-- The comparison on an element of a list alone; no work counted. -/
def litPow (q k : Nat) (x : Codes × List (OracleShape × Nat)) : Bool :=
  decide ((2 ^ 128 + 1) ^ Fmt.blocksFor (18 * bMax x.1 x.2 + 36) * (x.2.map (termB q x.1 (bMax x.1 x.2))).sum * 2 ^ k ≤
    (2 ^ 128) ^ Fmt.blocksFor (18 * bMax x.1 x.2 + 36) * allSeeds q (bMax x.1 x.2))

/-- **Its yes gives the comparison at every place that is that element.** -/
theorem pow_of_lit (q k : Nat) (P : Par) (rad : Nat → Nat) (x : Codes × List (OracleShape × Nat))
    (hc : P.codes = x.1) (hl : sampledList P rad = x.2) (h1 : P.seeds = 1) (h : litPow q k x = true) :
    (2 ^ 128 + 1) ^ (bsRound .two (seedEntry P) .seeds).b *
        (List.ofFn fun k : Fin (shapesOf P).length => if sampledAt P k then
          (lOf P.codes (shapeAt P k) (rad k.val)).choose 2 * clashSeeds q (bitsZ P.codes (shapeAt P k)) *
            q ^ (P.coordinates - bitsZ P.codes (shapeAt P k)) else 0).sum * 2 ^ k ≤
      (2 ^ 128) ^ (bsRound .two (seedEntry P) .seeds).b * allSeeds q P.coordinates * 2 ^ P.work := by
  have h' := of_decide_eq_true h
  rw [termB_eq, ← hc, ← hl, ← coordinates_bMax P rad] at h'
  rw [sum_sampled, blocks_seed P h1]
  calc _ ≤ (2 ^ 128) ^ Fmt.blocksFor (18 * P.coordinates + 36) * allSeeds q P.coordinates := h'
    _ = (2 ^ 128) ^ Fmt.blocksFor (18 * P.coordinates + 36) * allSeeds q P.coordinates * 1 := (Nat.mul_one _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ Nat.one_le_two_pow

/-! ## At the two written-out lists -/

theorem lit_pow_small : (!Johnson.G.packSmallLit.isEmpty &&
    Johnson.G.packSmallLit.all (litPow (Fmt.Fld.two.p ^ 3) 128)) = true := by decide +kernel
theorem lit_pow_full : (!Johnson.G.packFullLit.isEmpty &&
    Johnson.G.packFullLit.all (litPow (Fmt.Fld.two.p ^ 3) 128)) = true := by decide +kernel
/-- The test can fail. -/
theorem lit_pow_small_far : Johnson.G.packSmallLit.any (litPow (Fmt.Fld.two.p ^ 3) 192) = false := by decide +kernel
theorem lit_pow_full_far : Johnson.G.packFullLit.any (litPow (Fmt.Fld.two.p ^ 3) 192) = false := by decide +kernel

/-- The comparison at a place, as a proposition: powB's body, the field's size written out. -/
def PowAt (P : Par) (rad : Nat → Nat) (k : Nat) : Prop :=
  (2 ^ 128 + 1) ^ (bsRound .two (seedEntry P) .seeds).b *
      (List.ofFn fun k : Fin (shapesOf P).length => if sampledAt P k then
        (lOf P.codes (shapeAt P k) (rad k.val)).choose 2 * clashSeeds (Fmt.Fld.two.p ^ 3) (bitsZ P.codes (shapeAt P k)) *
          (Fmt.Fld.two.p ^ 3) ^ (P.coordinates - bitsZ P.codes (shapeAt P k)) else 0).sum * 2 ^ k ≤
    (2 ^ 128) ^ (bsRound .two (seedEntry P) .seeds).b * allSeeds (Fmt.Fld.two.p ^ 3) P.coordinates * 2 ^ P.work

/-- **At every place that is an element of the small list: the comparison at 128.** -/
theorem pow_small (P : Par) (rad : Nat → Nat) (x : Codes × List (OracleShape × Nat)) (hx : x ∈ Johnson.G.packSmallLit)
    (hc : P.codes = x.1) (hl : sampledList P rad = x.2) (h1 : P.seeds = 1) : PowAt P rad 128 := by
  have h := lit_pow_small
  simp only [Bool.and_eq_true] at h
  exact pow_of_lit _ 128 P rad x hc hl h1 (List.all_eq_true.1 h.2 x hx)

/-- **At every place that is an element of the full-size list: the comparison at 128.** -/
theorem pow_full (P : Par) (rad : Nat → Nat) (x : Codes × List (OracleShape × Nat)) (hx : x ∈ Johnson.G.packFullLit)
    (hc : P.codes = x.1) (hl : sampledList P rad = x.2) (h1 : P.seeds = 1) : PowAt P rad 128 := by
  have h := lit_pow_full
  simp only [Bool.and_eq_true] at h
  exact pow_of_lit _ 128 P rad x hc hl h1 (List.all_eq_true.1 h.2 x hx)

/-- In Lit.lean's letters, at the full-size list: a place that fits an element has the kind's one Boolean, one seed, and the comparison at 128, at the list's own radii. -/
theorem fits_full (P : Par) (x : Codes × List (OracleShape × Nat)) (hx : x ∈ Johnson.G.packFullLit) (h : FitsLit P x) :
    condPort P (radFrom P x.2) = true ∧ P.seeds = 1 ∧ PowAt P (radFrom P x.2) 128 :=
  ⟨cond_of_lit P x hx h, seeds_one P _ (cond_of_lit P x hx h),
    pow_full P _ x hx h.1 h.2.1 (seeds_one P _ (cond_of_lit P x hx h))⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.coordinates_bMax
#print axioms VerifiableInference.Desc.K1.sum_sampled
#print axioms VerifiableInference.Desc.K1.blocks_seed
#print axioms VerifiableInference.Desc.K1.pow_of_lit
#print axioms VerifiableInference.Desc.K1.lit_pow_small
#print axioms VerifiableInference.Desc.K1.lit_pow_full
#print axioms VerifiableInference.Desc.K1.lit_pow_small_far
#print axioms VerifiableInference.Desc.K1.lit_pow_full_far
#print axioms VerifiableInference.Desc.K1.pow_small
#print axioms VerifiableInference.Desc.K1.pow_full
#print axioms VerifiableInference.Desc.K1.fits_full
