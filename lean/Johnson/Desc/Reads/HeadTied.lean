-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/HeadTied.lean: at the output head's link, for the form `clip`: the tie of the
uses to the text, clause (T) of Reads/Stated.lean, holds of the kind's text, and it fails of a text
that writes the bytes of the number paid with their coefficients in the other order.

The kind's text writes a hidden number as the sum over its digits l of 256 ^ l times an entry of the
read rowAtCosts (`atCosts`, Johnson/Desc/Kinds/HeadCells.lean). The relation takes byte l with 256 ^
l (`value_bytes`, Reads/HeadStated.lean). A text with 256 ^ (4 - l) at digit l of paid names the
same places in the same form, so a statement on places alone is true of it.

What is here.
  `atCostsWith R c n`, `clipWith R c`: the kind's `atCosts` and `clip`, over the reads R, with the
    coefficient c l in the place of 256 ^ l at the digits of one number: in `clip`, of paid.
    `atCosts_is`, `clip_is`: at c l = 256 ^ l they are the kind's own, by rfl.
  `tied_clip`: a step of the row at the head: it speaks of the kind's written form `clip`, at
    letters. Where the letter val is a reading's map, for all values v at the places of U3, the part
    in U3 of the kind's `clip` is the value of the uses of form number 2.
  `tied_bytes`: what (T) pins at `clip`. At a reading's map, where the letters whose third form is
    `clipWith c` are tied, c j is 256 ^ j in K for each of the five bytes j of paid.
  `tooth_clip_turned`, `tooth_turned_reading`: a case in which the statement fails. At a reading's
    map (`IsReading`, Reads/Stated.lean), where 1 ≠ 0 in K, the letters whose third form is
    `clipWith` with c l = 256 ^ (4 - l) are not tied, at any state. So the row fails of them
    wherever there is a state with closed tables. Without such a state the row holds of the turned
    text too; `NotEmpty` shuts that. No theorem of this file says it of the row.
  Tools. `range_sum`: a sum over a list of the first n numbers; it is `list_range_sum` of
    Johnson/Road/FormsKeysKit.lean, with its proof, said again here for a commutative ring.
    `value_sumTo`, `value_smulNat`, `value_addE`, `value_subE`: the value of a form under the kinds'
    own signs for sums and multiples. `atCostsWith_part`, `clipWith_part`: what turns in a form's
    value with the entries of rowAtCosts. `clip_text`: the text's side. `uses_two`, `clip_clause`:
    the relation's side. `pick_first`, `pick_second`: the values 1 at one place and 0 elsewhere.
    `clauseValue_with`: the value of the uses does not read the letter forms.

What carries the failing case. By `tied_bytes` the turned text is tied only where 256 ^ 2 = 1 in K.
Where there is a reading and 1 ≠ 0 that is false, since the programs' prime is 0 in K (`sq_ne_one`,
Reads/Numeral.lean). At a free map val, in a K with 256 ^ 2 = 1, nothing here refuses the turned
text: it is refused behind the reading's laws alone.

Premises. hval: the letter val is the map of a reading ρ (OnBytes/Model/HideLaws.lean). K is a
commutative ring. That a reading takes the programs' numerals to numbers is shown in
Reads/Numeral.lean.

Of OnBytes/Model/ this file names `Aff`, `Reading`, `World` and `Aff.value`, as Reads/Value.lean
does.

Limits. (T) for the forms mean, count and table, and that entries lie inside their rows, are shown
in Reads/HeadTiedFour.lean, not here. Clauses (A) and (L) of the row are shown nowhere. Nothing is
said on what a verifier would say to the turned text. Nothing on soundness.


-/
import Johnson.Desc.Reads.HeadStated
import Johnson.Desc.Reads.Value
import Johnson.Desc.Reads.Numeral

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtHead

open Finset
open OnBytes (E)
open OnBytes.Model (Aff Reading World)
open VerifiableInference.Desc.Kinds
open Inst.Model.Head (nV)

variable {K : Type} [CommRing K] {ρ : Reading K}

/-! ## The value of a form under the kinds' signs -/

/-- A sum over a list of the first n numbers is the sum over the range. -/
theorem range_sum (g : ℕ → K) (n : ℕ) : ((List.range n).map g).sum = ∑ x ∈ range n, g x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem value_smulNat (ρ : Reading K) (W : World K) (k : ℕ) (f : Aff) :
    (k • f).value ρ W = (k : K) * f.value ρ W := by
  show (Aff.scale f (natE k)).value ρ W = _
  rw [Aff.value_scale]
  exact congrArg (· * f.value ρ W) (reading_ofNat ρ k)

theorem value_addE (W : World K) (f : Aff) (x : E) :
    (HAdd.hAdd (α := Aff) (β := E) (γ := Aff) f x).value ρ W = f.value ρ W + ρ.val x := by
  show (f + Aff.ofConst x).value ρ W = _
  rw [Aff.value_add, Aff.value_ofConst]

theorem value_subE (W : World K) (f : Aff) (x : E) :
    (HSub.hSub (α := Aff) (β := E) (γ := Aff) f x).value ρ W = f.value ρ W - ρ.val x := by
  show (f - Aff.ofConst x).value ρ W = _
  rw [Aff.value_sub, Aff.value_ofConst]

theorem value_sumTo (ρ : Reading K) (W : World K) (n : ℕ) (f : ℕ → Aff) :
    (sumTo n f).value ρ W = ∑ i ∈ range n, (f i).value ρ W := by
  induction n with
  | zero =>
    show (Aff.ofConst (natE 0)).value ρ W = _
    rw [Aff.value_ofConst]
    exact (reading_ofNat ρ 0).trans (by simp)
  | succ n ih =>
    have e : sumTo (n + 1) f = sumTo n f + f n := by
      unfold sumTo
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [e, Aff.value_add, ih, Finset.sum_range_succ]

/-! ## The text, with other coefficients -/

section Text
variable [iS : Head.Sizes] [iR : Head.Request] [iI : FinalNorm.In]

/-- The kind's atCosts over the reads R, with the coefficient c l at digit l. -/
def atCostsWith (R : Head.Reads) (c : ℕ → ℕ) (n : Head.Number) : Form :=
  sumTo n.digits.2 fun l =>
    (c l : ℕ) • (R.entry .rowAtCosts (NR + n.digits.1 + l) + off1 * Head.ERC)

theorem atCosts_is (R : Head.Reads) (n : Head.Number) :
    (letI := R; Head.atCosts n) = atCostsWith R (fun l => 256 ^ l) n := rfl

/-- What turns in its value with the entries of rowAtCosts. -/
theorem atCostsWith_part (ρ : Reading K) (R : Head.Reads) (W W0 : World K) (a : ℕ → K)
    (hW : ∀ i, (R.entry .rowAtCosts i).value ρ W - (R.entry .rowAtCosts i).value ρ W0 = a i)
    (c : ℕ → ℕ) (n : Head.Number) :
    (atCostsWith R c n).value ρ W - (atCostsWith R c n).value ρ W0 =
      ∑ l ∈ range n.digits.2, (c l : K) * a (NR + n.digits.1 + l) := by
  unfold atCostsWith
  rw [value_sumTo ρ, value_sumTo ρ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [value_smulNat ρ, value_smulNat ρ, value_addE, value_addE, ← hW]
  ring

variable [iP : Head.Policy]

/-- The kind's clip over the reads R, with the coefficient c l at digit l of paid. -/
def clipWith (R : Head.Reads) (c : ℕ → ℕ) : Form :=
  atCostsWith R c .paid + atCostsWith R (fun l => 256 ^ l) .slackClip - Head.C * Head.ERC

theorem clip_is (R : Head.Reads) : (letI := R; Head.clip) = clipWith R fun l => 256 ^ l := rfl

theorem clipWith_part (ρ : Reading K) (R : Head.Reads) (W W0 : World K) (a : ℕ → K)
    (hW : ∀ i, (R.entry .rowAtCosts i).value ρ W - (R.entry .rowAtCosts i).value ρ W0 = a i)
    (c : ℕ → ℕ) :
    (clipWith R c).value ρ W - (clipWith R c).value ρ W0 =
      ∑ l ∈ range 5, (c l : K) * a (NR + 0 + l) +
        ∑ l ∈ range 5, ((256 ^ l : ℕ) : K) * a (NR + 11 + l) := by
  have h1 : _ = ∑ l ∈ range 5, (c l : K) * a (NR + 0 + l) :=
    atCostsWith_part ρ R W W0 a hW c .paid
  have h2 : _ = ∑ l ∈ range 5, ((256 ^ l : ℕ) : K) * a (NR + 11 + l) :=
    atCostsWith_part ρ R W W0 a hW (fun l => 256 ^ l) .slackClip
  unfold clipWith
  rw [value_subE, value_subE, Aff.value_add, Aff.value_add]
  linear_combination h1 + h2

/-- **The text's side.** The part in U3 of clipWith, at a seat. -/
theorem clip_text (ρ : Reading K) (S : Seat) (c : ℕ → ℕ) (v : ℕ → K) :
    u3Value ρ.val S.iU3 S.cols (clipWith S.reads c) v =
      ∑ l ∈ range 5, (c l : K) * v (S.start .rowAtCosts + (NR + 0 + l)) +
        ∑ l ∈ range 5, ((256 ^ l : ℕ) : K) * v (S.start .rowAtCosts + (NR + 11 + l)) := by
  rw [u3Value_diff]
  refine clipWith_part ρ S.reads _ _ (fun i => v (S.start .rowAtCosts + i)) (fun i => ?_) c
  have e1 : (S.reads.entry .rowAtCosts i).value ρ (worldOf S.iU3 S.cols v) =
      v (S.start .rowAtCosts + i) := value_place ρ S.iU3 S.cols v _
  have e2 : (S.reads.entry .rowAtCosts i).value ρ (worldOf S.iU3 S.cols fun _ => (0 : K)) = 0 :=
    value_place ρ S.iU3 S.cols (fun _ => 0) _
  rw [e1, e2, sub_zero]

end Text

/-! ## The relation's side -/

/-- The uses of form number 2: the five bytes of c and the five of k in (B4). -/
theorem uses_two [iS : Head.Sizes] : (usesH.filter fun u => u.clause.no == 2) =
    (List.range 5).map (Use.byte .B4 .c) ++ (List.range 5).map (Use.byte .B4 .k) := by
  have hB : (((List.range 3).flatMap fun l =>
      (List.range (nV / Norm.S2)).map fun blk => Use.ex l blk).filter
        fun u => u.clause.no == 2) = [] := by
    refine List.filter_eq_nil_iff.2 fun u hu => ?_
    obtain ⟨l, -, hu⟩ := List.mem_flatMap.1 hu
    obtain ⟨blk, -, rfl⟩ := List.mem_map.1 hu
    exact Bool.false_ne_true
  unfold usesH
  rw [List.filter_append, hB, List.append_nil]
  rfl

/-- **The relation's side.** The value of the uses of form number 2. -/
theorem clip_clause (P : HeadLetters K) (s : P.State) (v : ℕ → K) :
    P.letters.clauseValue () s 2 v =
      ∑ l ∈ range 5, ((256 ^ l : ℕ) : K) * v (P.seat.start .rowAtCosts + (NR + 0 + l)) +
        ∑ l ∈ range 5, ((256 ^ l : ℕ) : K) * v (P.seat.start .rowAtCosts + (NR + 11 + l)) := by
  show (((@usesH P.sizes).filter fun u => u.clause.no == 2).map fun u =>
    u.coef (P.req s) * v (P.seat.start u.read + @Use.index P.sizes u)).sum = _
  rw [uses_two (iS := P.sizes), List.map_append, List.sum_append, List.map_map, List.map_map,
    range_sum, range_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun l _ => ?_)
    (Finset.sum_congr rfl fun l _ => ?_)
  · show (1 * (256 : K) ^ l) * v (P.seat.start .rowAtCosts + (NR + 0 + l)) = _
    push_cast
    ring
  · show (1 * (256 : K) ^ l) * v (P.seat.start .rowAtCosts + (NR + 11 + l)) = _
    push_cast
    ring

/-! ## The two together -/

/-- The form clipWith at the head's letters and a state. -/
def HeadLetters.clipWith (P : HeadLetters K) (c : ℕ → ℕ) (s : P.State) : Form :=
  AtHead.clipWith (iS := P.sizes) (iR := P.request s) (iI := P.points s) (iP := P.policy)
    P.seat.reads c

/-- The head's letters, with clipWith c in the place of the form clip. -/
def HeadLetters.lettersWith (P : HeadLetters K) (c : ℕ → ℕ) : Letters K :=
  { P.letters with
    forms := fun _ s =>
      letI := P.sizes
      letI := P.policy
      letI := P.request s
      letI := P.points s
      letI := P.seat.reads
      [Head.mean, Head.count, P.clipWith c s, Head.table] }

/-- The value of the uses does not read the letter forms. -/
theorem clauseValue_with (L : Letters K) (F : L.Link → L.State → List Aff) (l : L.Link)
    (s : L.State) (n : ℕ) (v : ℕ → K) :
    Letters.clauseValue { L with forms := F } l s n v = L.clauseValue l s n v := rfl

/-- At c l = 256 ^ l these are the head's letters. -/
theorem lettersWith_self (P : HeadLetters K) : P.lettersWith (fun l => 256 ^ l) = P.letters := rfl

/-- **(T) for the kind's form clip.** -/
theorem tied_clip (P : HeadLetters K) (hval : P.val = ρ.val) (s : P.State)
    (v : ℕ → K) :
    u3Value P.val P.seat.iU3 P.seat.cols (P.clipWith (fun l => 256 ^ l) s) v =
      P.letters.clauseValue () s 2 v := by
  rw [hval, clip_clause]
  exact clip_text (iS := P.sizes) (iR := P.request s) (iI := P.points s) (iP := P.policy) ρ
    P.seat _ v

/-! ## What (T) pins at clip, and the tooth -/

/-- The values 1 at the place st + (99 + j) and 0 elsewhere pick byte j of the first number. -/
theorem pick_first (st j : ℕ) (hj : j < 5) (c : ℕ → K) :
    ∑ l ∈ range 5, c l * (if st + (NR + 0 + l) = st + (99 + j) then (1 : K) else 0) = c j := by
  have hN : NR = 99 := rfl
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.2 hj)
    (fun l _ hl => by rw [if_neg (by omega), mul_zero]), if_pos (by omega), mul_one]

/-- They pick no byte of the second. -/
theorem pick_second (st j : ℕ) (hj : j < 5) (c : ℕ → K) :
    ∑ l ∈ range 5, c l * (if st + (NR + 11 + l) = st + (99 + j) then (1 : K) else 0) = 0 := by
  have hN : NR = 99 := rfl
  exact Finset.sum_eq_zero fun l _ => by rw [if_neg (by omega), mul_zero]

/-- **What (T) pins at clip.** Where the letters with clipWith c are tied, c j is 256 ^ j in K, for
each of the five bytes of paid. -/
theorem tied_bytes (P : HeadLetters K) (hval : P.val = ρ.val) (c : ℕ → ℕ)
    (s : P.State) (H : Tied (P.lettersWith c) () s) (j : ℕ) (hj : j < 5) :
    ((c j : ℕ) : K) = ((256 ^ j : ℕ) : K) := by
  have h := (H.2 2 (P.clipWith c s) rfl).2
    fun q => if q = P.seat.start .rowAtCosts + (99 + j) then 1 else 0
  have h' : u3Value P.val P.seat.iU3 P.seat.cols (P.clipWith c s)
      (fun q => if q = P.seat.start .rowAtCosts + (99 + j) then 1 else 0) =
      P.letters.clauseValue () s 2
        (fun q => if q = P.seat.start .rowAtCosts + (99 + j) then 1 else 0) :=
    h.trans (clauseValue_with P.letters _ () s 2 _)
  rw [hval, clip_clause] at h'
  have ht := clip_text (iS := P.sizes) (iR := P.request s) (iI := P.points s) (iP := P.policy) ρ
    P.seat c (fun q => if q = P.seat.start .rowAtCosts + (99 + j) then (1 : K) else 0)
  have e : ∑ l ∈ range 5, ((c l : ℕ) : K) *
        (if P.seat.start .rowAtCosts + (NR + 0 + l) = P.seat.start .rowAtCosts + (99 + j)
          then (1 : K) else 0) +
      ∑ l ∈ range 5, ((256 ^ l : ℕ) : K) *
        (if P.seat.start .rowAtCosts + (NR + 11 + l) = P.seat.start .rowAtCosts + (99 + j)
          then (1 : K) else 0) =
      ∑ l ∈ range 5, ((256 ^ l : ℕ) : K) *
        (if P.seat.start .rowAtCosts + (NR + 0 + l) = P.seat.start .rowAtCosts + (99 + j)
          then (1 : K) else 0) +
      ∑ l ∈ range 5, ((256 ^ l : ℕ) : K) *
        (if P.seat.start .rowAtCosts + (NR + 11 + l) = P.seat.start .rowAtCosts + (99 + j)
          then (1 : K) else 0) := ht.symm.trans h'
  rw [pick_first _ j hj fun l => ((c l : ℕ) : K), pick_first _ j hj fun l => ((256 ^ l : ℕ) : K),
    pick_second _ j hj fun l => ((256 ^ l : ℕ) : K), add_zero, add_zero] at e
  exact e

/-- **The bytes of paid with their coefficients in the other order are not tied.** By `tied_bytes`
at the bytes 0 and 1: 256 ^ 4 = 1 and 256 ^ 3 = 256 in K, so 256 ^ 2 = 1. -/
theorem tooth_clip_turned (P : HeadLetters K) (hval : P.val = ρ.val) (hne : (1 : K) ≠ 0)
    (s : P.State) : ¬ Tied (P.lettersWith fun l => 256 ^ (4 - l)) () s := by
  intro H
  have h0 := tied_bytes P hval (fun l => 256 ^ (4 - l)) s H 0 (by decide)
  have h1 := tied_bytes P hval (fun l => 256 ^ (4 - l)) s H 1 (by decide)
  have h0' : ((256 ^ 4 : ℕ) : K) = ((256 ^ 0 : ℕ) : K) := h0
  have h1' : ((256 ^ 3 : ℕ) : K) = ((256 ^ 1 : ℕ) : K) := h1
  push_cast at h0' h1'
  refine sq_ne_one ρ hne ?_
  linear_combination h0' - 256 * h1'

/-- The same, in the words of Reads/Stated.lean. -/
theorem tooth_turned_reading (P : HeadLetters K)
    (hR : IsReading (P.lettersWith fun l => 256 ^ (4 - l))) (hne : (1 : K) ≠ 0) (s : P.State) :
    ¬ Tied (P.lettersWith fun l => 256 ^ (4 - l)) () s := by
  obtain ⟨ρ, h⟩ := hR
  exact tooth_clip_turned P h.symm hne s

end VerifiableInference.Reads.AtHead

#print axioms VerifiableInference.Reads.AtHead.range_sum
#print axioms VerifiableInference.Reads.AtHead.value_smulNat
#print axioms VerifiableInference.Reads.AtHead.value_addE
#print axioms VerifiableInference.Reads.AtHead.value_subE
#print axioms VerifiableInference.Reads.AtHead.value_sumTo
#print axioms VerifiableInference.Reads.AtHead.atCosts_is
#print axioms VerifiableInference.Reads.AtHead.atCostsWith_part
#print axioms VerifiableInference.Reads.AtHead.clip_is
#print axioms VerifiableInference.Reads.AtHead.clipWith_part
#print axioms VerifiableInference.Reads.AtHead.clip_text
#print axioms VerifiableInference.Reads.AtHead.uses_two
#print axioms VerifiableInference.Reads.AtHead.clip_clause
#print axioms VerifiableInference.Reads.AtHead.clauseValue_with
#print axioms VerifiableInference.Reads.AtHead.lettersWith_self
#print axioms VerifiableInference.Reads.AtHead.tied_clip
#print axioms VerifiableInference.Reads.AtHead.pick_first
#print axioms VerifiableInference.Reads.AtHead.pick_second
#print axioms VerifiableInference.Reads.AtHead.tied_bytes
#print axioms VerifiableInference.Reads.AtHead.tooth_clip_turned
#print axioms VerifiableInference.Reads.AtHead.tooth_turned_reading
