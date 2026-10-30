-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/HearSum.lean: THE PART "A MASKED SUMCHECK"
(Johnson/Desc/Part/MaskedSum4.lean, MaskedSumMore.lean) ON SHAPES: the shape of the one form that it
leaves, and of its record and the ledger behind its hearing. General laws; nothing is evaluated.
  1 The shape of the part's record is AttOwn.lean's SumSh | sumSh (the start form's shape, the first
    slot, the variables' degrees, the number of challenges, the first end value's slot): called, not
    typed anew. `hidingLen`, `powersFrom_length`, `hidingAt_length`: how many coefficients the
    hiding polynomial has, of the degrees. `affSh_onSlots`. `msRowSh`, **`affSh_msRow`**: the shape
    of the part's one form (rowForm).
  2 `roundOf_sizes`, `varRounds_length`, `readAll_sizes`: what was read has as many rounds as there
    are variables and as many end values as the call names. `msHearS`, **`ms_hear_sh`**: the part's
    hearing with ends: the first slot is the next free number; the end values' first slot lies
    behind the own slots; the next free number moves on by both; the end values' slots are filled.
    `rowLaidS`, **`rowLaid_sh`**: n slots from the first slot on are filled; in the law n is the
    hiding polynomial's number of coefficients.
  3 `KSumSh`, `kSumSh`: the shape of a sumcheck as a kind's text keeps it (Kinds.Sum,
    Johnson/Desc/Kinds/HeadParts.lean); the element handed down is left out.
By Parts.lean's hide_of_B, affSh_addMul, affSh_sub, affSh_slot.
Limits. THE WEAK FORM, as in HearFrame.lean: under the step's own return. A call without ends has no
law here. NO LAW HERE SAYS THAT msHearS's own (in its law ownSlots k.all) AND rowLaidS's n (in its
law hidingLen of the degrees) ARE ONE NUMBER: at no variable they are 1 and 0; the library's law
that they agree (Kinds.Head.Law.hidingAt_length, Johnson/Desc/Kinds/Law/Decode.lean) asks a list
that is not empty and 1 ≤ d throughout. Where n is the smaller, some own slots stay free, and no
step says so. That the hearing returns is not said: its test that every slot which the start form
names is filled (Fork.publicPart) is not on these shapes' steps. Nothing on soundness, completeness
or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Shape.HearFrame
import Johnson.Desc.First.Shape.AttOwn
import Johnson.Desc.Part.MaskedSumMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.Kinds (Hear Hid Sum Point Form)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Heard ownSlots hidingAt onSlots powersFrom)

/-! ## 1 The part's record of a masked sumcheck, and its form -/

/-- How many coefficients the hiding polynomial has, of the degrees. -/
def hidingLen : List Nat → Nat
  | [] => 0
  | [d] => d
  | d :: e :: rest => (d - 1) + hidingLen (e :: rest)

theorem powersFrom_length (x : E) : ∀ (n : Nat) (a : E), (powersFrom x n a).length = n
  | 0, _ => rfl
  | n + 1, a => by
    show (powersFrom x n (mulE a x)).length + 1 = n + 1
    rw [powersFrom_length x n]

theorem hidingAt_length : ∀ l : List (Var × E), (hidingAt l).1.length = hidingLen (l.map (·.1.d))
  | [] => rfl
  | [(v, r)] => powersFrom_length r v.d oneE
  | (v, r) :: q :: rest => by
    show (powersFrom r (v.d - 1) _ ++ (hidingAt (q :: rest)).1).length = _
    rw [List.length_append, powersFrom_length, hidingAt_length (q :: rest)]
    rfl

/-- onSlots on shapes: the slots first, first + 1, … behind the form's. -/
theorem affSh_onSlots (f : Aff) (first : Nat) (u : List E) :
    affSh (onSlots f first u) = (affSh f).append (AffSh.mk [] (List.range' first u.length)) := by
  unfold onSlots
  induction u generalizing f first with
  | nil =>
    show affSh f = (affSh f).append (AffSh.mk [] [])
    simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots]
  | cons x u ih =>
    rw [List.foldl_cons, ih, affSh_addMul, affSh_slot, List.length_cons, List.range'_succ]
    simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots]

/-- The part's one form on shapes. n: the number of the hiding polynomial's coefficients. -/
def msRowSh (m : SumSh) (n : Nat) (kept : AffSh) : AffSh :=
  (((AffSh.mk [] []).append (AffSh.mk [] (List.range' m.first n))).append
    ((AffSh.mk [] []).append m.start)).append kept

theorem affSh_msRow (h : Heard) (S0 : E) (kept : Aff) :
    affSh (Part.MaskedSum.rowForm h S0 kept) =
      msRowSh (sumSh h) (hidingLen ((h.vars.zip h.r).map (·.1.d))) (affSh kept) := by
  unfold Part.MaskedSum.rowForm msRowSh
  dsimp only
  rw [affSh_addMul, affSh_addMul, affSh_onSlots, affSh_sub, hidingAt_length]
  rfl

/-! ## 2 The part's hearing and the laying of its own slots -/

theorem roundOf_sizes {n k : Nat} {r : Fmt.RoundView} {x : List E × List E}
    (h : Part.MaskedSum.roundOf n k r = some x) : x.1.length = n ∧ x.2.length = k := by
  unfold Part.MaskedSum.roundOf at h
  obtain ⟨s, -, hs⟩ := Option.bind_eq_some_iff.1 h
  split at hs
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain rfl := Option.some.inj hs
    exact ⟨hc.1, by rw [List.length_map]; exact hc.2⟩
  · cases hs

theorem varRounds_length : ∀ (vs : List Var) (rs : List Fmt.RoundView)
    (x : List (List E × E) × List Fmt.RoundView), Part.MaskedSum.varRounds vs rs = some x →
    x.1.length = vs.length
  | [], rs, x, h => by
    obtain rfl := Option.some.inj h
    rfl
  | _ :: _, [], x, h => by cases h
  | v :: vs, r :: rs, x, h => by
    unfold Part.MaskedSum.varRounds at h
    split at h
    · rename_i s g l rest _ h2
      obtain rfl := Option.some.inj h
      show l.length + 1 = vs.length + 1
      rw [varRounds_length vs rs (l, rest) h2]
    · cases h

/-- What was read has as many rounds as there are variables, and as many end values as the call
names. -/
theorem readAll_sizes {k : Part.MaskedSum.Call} {e : Ends} {rs : List Fmt.RoundView} {R :
           Part.MaskedSum.Read}
    (he : k.ends = some e) (h : Part.MaskedSum.readAll k rs = some R) :
    R.values.length = e.n ∧ R.rounds.length = k.all.length := by
  unfold Part.MaskedSum.readAll at h
  cases rs with
  | nil => cases h
  | cons r rest =>
    dsimp only at h
    rw [he] at h
    split at h
    · rename_i heq
      cases heq
    · rename_i a mu eps l rv e' h1 h2 heq
      obtain rfl : e = e' := Option.some.inj heq
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨(roundOf_sizes hx).1, varRounds_length _ _ _ h2⟩
    · cases h

/-- The part's hearing on shapes. C: the start form's shape; ds: the degrees, Y's last; own: by how
many own slots the next free number moves (in the law: ownSlots k.all); ends: the number of end
values. -/
def msHearS (C : AffSh) (ds : List Nat) (own ends : Nat) (L : LedSh) : Option (SumSh × LedSh) :=
  if freeB (L.moved (own + ends)) (L.next + own) ends then
    some (⟨C, L.next, ds, ds.length, L.next + own⟩,
      (L.moved (own + ends)).setGot (fillB L.got (L.next + own) ends))
  else none

theorem ms_hear_sh {C : Aff} {k : Part.MaskedSum.Call} {e : Ends} {F G : Fork} {rs : List Fmt.RoundView} {h
           : Heard}
    (he : k.ends = some e) (hh : Part.MaskedSum.hear C k F rs = some (h, G)) {y : SumSh × LedSh}
    (hf : msHearS (affSh C) (k.all.map Var.d) (ownSlots k.all) e.n (ledSh F) = some y) :
    y = (sumSh h, ledSh G) := by
  unfold Part.MaskedSum.hear at hh
  -- the text's lines, one by one: the guard; the start form's public part; the reading
  by_cases hs : Part.MaskedSum.shapeOk k = true
  · simp only [hs, guard, if_true, Option.bind_eq_bind, Option.pure_def, Option.bind_some] at hh
    obtain ⟨T, -, hh⟩ := Option.bind_eq_some_iff.1 hh
    obtain ⟨R, hR, hh⟩ := Option.bind_eq_some_iff.1 hh
    obtain ⟨G', hG, hh⟩ := Option.bind_eq_some_iff.1 hh
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
    obtain ⟨n1, n2⟩ := readAll_sizes he hR
    unfold msHearS at hf
    split at hf
    · rename_i hc
      have em : ledSh { F with next := F.next + ownSlots k.all + R.values.length } =
          (ledSh F).moved (ownSlots k.all + e.n) := by
        rw [n1, Nat.add_assoc]
        rfl
      have hc' : freeB (ledSh { F with next := F.next + ownSlots k.all + R.values.length })
          (F.next + ownSlots k.all) R.values.toArray.size = true := by
        rw [em, List.size_toArray, n1]
        exact hc
      obtain ⟨H, hH, -, -, eH⟩ := hide_of_B hc' ((R.rounds.map (·.2)).getLastD zeroE)
      obtain rfl : H = G' := Option.some.inj (hH.symm.trans hG)
      rw [← Option.some.inj hf, eH, em, List.size_toArray, n1]
      refine Prod.ext ?_ rfl
      show SumSh.mk _ _ _ (k.all.map Var.d).length _ = SumSh.mk _ _ _ (R.rounds.map (·.2)).length _
      rw [List.length_map, List.length_map, n2]
      rfl
    · cases hf
  · simp only [hs, guard, Bool.false_eq_true, if_false] at hh
    cases hh

/-- n slots from the record's first slot on are filled, on shapes. n is a free letter: in the law it
is hidingLen of the degrees. -/
def rowLaidS (m : SumSh) (n : Nat) (L : LedSh) : Option LedSh :=
  if freeB L m.first n then some (L.setGot (fillB L.got m.first n)) else none

theorem rowLaid_sh {h : Heard} {F G : Fork} (hh : Part.MaskedSum.rowLaid h F = some G) {y : LedSh}
    (hf : rowLaidS (sumSh h) (hidingLen ((h.vars.zip h.r).map (·.1.d))) (ledSh F) = some y) :
    y = ledSh G := by
  unfold rowLaidS at hf
  split at hf
  · rename_i hc
    unfold Part.MaskedSum.rowLaid at hh
    have hc' : freeB (ledSh F) h.first
        (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE).size = true := by
      rw [Array.size_replicate, hidingAt_length]
      exact hc
    obtain ⟨H, hH, -, -, eH⟩ := hide_of_B hc' (subE zeroE oneE)
    obtain rfl : H = G := Option.some.inj (hH.symm.trans hh)
    rw [← Option.some.inj hf, eH, Array.size_replicate, hidingAt_length]
    rfl
  · cases hf

/-! ## 3 A sumcheck as a kind's text keeps it -/

/-- The shape of Kinds.Sum; the element handed down is left out. -/
structure KSumSh where
  r : Nat
  claimed : AffSh
  ends : List AffSh
  psc : Option SumSh

def kSumSh (s : Sum) : KSumSh :=
  { r := s.r.size, claimed := hidSh s.claimed, ends := s.ends.toList.map hidSh
    psc := s.psc.map sumSh }

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.powersFrom_length
#print axioms VerifiableInference.Desc.First.Shape.hidingAt_length
#print axioms VerifiableInference.Desc.First.Shape.affSh_onSlots
#print axioms VerifiableInference.Desc.First.Shape.affSh_msRow
#print axioms VerifiableInference.Desc.First.Shape.roundOf_sizes
#print axioms VerifiableInference.Desc.First.Shape.varRounds_length
#print axioms VerifiableInference.Desc.First.Shape.readAll_sizes
#print axioms VerifiableInference.Desc.First.Shape.ms_hear_sh
#print axioms VerifiableInference.Desc.First.Shape.rowLaid_sh
#print axioms VerifiableInference.Desc.First.Shape.hidingLen
#print axioms VerifiableInference.Desc.First.Shape.msRowSh
#print axioms VerifiableInference.Desc.First.Shape.msHearS
#print axioms VerifiableInference.Desc.First.Shape.rowLaidS
#print axioms VerifiableInference.Desc.First.Shape.KSumSh
#print axioms VerifiableInference.Desc.First.Shape.kSumSh
