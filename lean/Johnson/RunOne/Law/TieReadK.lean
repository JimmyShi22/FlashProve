-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieReadK.lean: THE THIRD
READING LEMMA OF THE CLAIMS' TIE: the table's sentence on a part's keys (worth l "keys":
Johnson/Desc/Key/KeyK3Items.lean: the form's worth reads as the sum over the part's keys of the
equality weight at the point times alpha − key) holds exactly if the kind's law's claim on the
leaves alpha − key, read as a claim on the keys (rdCl of keyF: Johnson/Desc/First/Look/KeyLaw/
Readings.lean, Statement.lean), holds of the keys read.

Main names:
  read_keySum: the sentence's right side, read: alpha less the multilinear extension of the keys at
    the point.
  key_iff_rdCl: THE IFF, for one part.

Object: definitions of the table's files, of K3's files and of the library; no block's text.
User: TieDone.lean and TieDoneBack.lean call key_iff_rdCl.
Letters: G, a ledger · home, a table of homes · mk, the mask entries · al, alpha · v, the number of
the part's variables · k, what the part's tree leaves: a point and a form · key, the keys in machine
elements · kf, the keys in the field.

Limits. The sentence's side clauses are not treated. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieRead
import Johnson.RunOne.Law.TieTensor
import Johnson.Desc.First.Look.KeyLaw.KeyClaim
import OnBytes.Slice.KeyLeavesEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieReadK
open OnBytes OnBytes.Slice
open OnBytes.Model (Fork Aff)
open Lk6 (Dat)
open Lk6.PortSim (rdMF)
open Lk6.Mid (rdCl)
open VerifiableInference.Desc.Key (affAt sumE sumE_read)
open VerifiableInference.Desc.K3.KeyLaw (mfOf valOf keyF lowPt_ptTop sum_rdMF)
open Johnson.RunOne.Law.TieRead
open Johnson.RunOne.Law.TieTensor

/-- The sentence's right side, read. -/
theorem read_keySum (al : E) (z : List E) (key : ℕ → E) (kf : ℕ → GE)
    (hkey : ∀ n < 2 ^ z.length, readE (key n) = kf n) :
    readE (sumE (2 ^ z.length) fun n => mulE ((Tensor.eq z).entry n) (subE al (key n))) =
      readE al - ∑ n ∈ Finset.range (2 ^ z.length), Leaves.eqW (z.map readE) n * kf n := by
  rw [sumE_read readE readE_zero readE_add]
  have e : ∀ n ∈ Finset.range (2 ^ z.length),
      readE (mulE ((Tensor.eq z).entry n) (subE al (key n))) =
        Leaves.eqW (z.map readE) n * readE al - Leaves.eqW (z.map readE) n * kf n := fun n hn => by
    rw [readE_mul, readE_sub, read_eqEntry, hkey n (Finset.mem_range.1 hn)]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have s := Leaves.eqW_sum (z.map readE)
  rw [List.length_map] at s
  rw [s, one_mul]

variable (G : Fork) (home : Array Slot) (mk : Slot → E)

/-- **The sentence on a part's keys holds exactly if the kind's law's claim holds of the keys
read.** -/
theorem key_iff_rdCl {A : Dat GE} {sl : Slot → A.J} {μ : A.J → GE} (al : E) (v : ℕ)
    (k : Array E × Aff) (hk : k.1.size = v) (key : ℕ → E) (kf : ℕ → GE)
    (hkey : ∀ n < 2 ^ v, readE (key n) = kf n)
    (hμ : ∀ q ∈ mfOf G (fun n => home.getD n default) k.2, μ (sl q.1) = readE (mk q.1)) :
    readE (affAt G home mk k.2) =
        readE (sumE (2 ^ v) fun n => mulE ((Tensor.eq k.1.toList.reverse).entry n)
          (subE al (key n))) ↔
      (rdCl A sl (readE al) v (keyF G (fun n => home.getD n default) k)).Holds v kf μ := by
  have hl : k.1.toList.reverse.length = v := by rw [List.length_reverse, Array.length_toList, hk]
  have r := read_keySum al k.1.toList.reverse key kf (by rw [hl]; exact hkey)
  rw [hl] at r
  rw [r, read_affAt]
  unfold Cb.LdLkp.MCl.Holds rdCl keyF
  show _ ↔ Blocks.ext v kf (Lk6.Lev.ptTop v (k.1.toList.reverse.map readE)) +
    ∑ j, (- rdMF sl (mfOf G (fun n => home.getD n default) k.2) j) * μ j =
      readE al - valOf G k.2
  rw [Lk6.ext_eq_sum, lowPt_ptTop _ _ (by rw [List.length_map, hl])]
  simp only [neg_mul, Finset.sum_neg_distrib]
  rw [sum_rdMF A sl μ]
  have em : ((mfOf G (fun n => home.getD n default) k.2).map fun p => p.2 * μ (sl p.1)).sum =
      ((mfOf G (fun n => home.getD n default) k.2).map fun p => p.2 * readE (mk p.1)).sum :=
    congrArg List.sum (List.map_congr_left fun q hq => by rw [hμ q hq])
  rw [em]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

end Johnson.RunOne.Law.TieReadK

#print axioms Johnson.RunOne.Law.TieReadK.read_keySum
#print axioms Johnson.RunOne.Law.TieReadK.key_iff_rdCl
