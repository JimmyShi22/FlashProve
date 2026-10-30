-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/EndsMeetIndex.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: THE READER's FORM UNDER AN END VALUE IS WORTH THE PROVER's END VALUE AT THE
SUMCHECK's CHALLENGES, READ: for the three sumchecks on the index at which a row's maximum is
attained: the score at the index (its first end values), the key at the index, and "the index's
cells are bits". Statements with their proofs. It goes on from
Johnson/Desc/K5/Honest/Law/EndsMeet.lean.

The verifier's claims: Johnson/Desc/First/Att/Claims/Say58.lean (`Say7`: its fields `endsF`,
`endsK`; `Say8`: its field `ends`, on the form `endsH`). The readers' worths in the matrices' cells:
Claims/EndsE.lean, Claims/MeanRd.lean, Claims/EndsH.lean. The prover's end values, under the names
that the files on these summands give to the pieces of their text: Law/ReadSF.lean (`under3`,
`sfTab`), Law/ReadSD.lean (`kcAt`, `kcTab`, `ibpAt`), Law/ReadHB.lean (`hbA`).

Main names:
  `endsF_meets`      the score at the index: the query, pair by pair
  `endsK_lam_meets`  the key at the index: the keys of a layer
  `endsK_bit_meets`  the key at the index: a cell of a pair's index
  `endsH_meets`      "the index's cells are bits": the weighted cells, and these less 1

EVERY STATEMENT IS CONDITIONAL. The premises are those of
Johnson/Desc/K5/Honest/Law/AloneMeets.lean, whose head says who is meant to show each: `AttAt`
(among its clauses: every table of the list is true of the matrices in the world), `CellsAre`, that
the tables lie in the list with the named weights (`QaAt` and `AhAt`,
Johnson/Road/Rows/AttEnds58.lean, are `TabAt` at two of the matrices), that the indices read lie in
the tables, the challenges' numbers; and that the claims' named points are those of the kind's own
value m.
Limits. The second end values of the score at the index have no reader: they are the starts of the
key at the index. Nothing here says that a premise holds at any place.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.EndsMeet
import Johnson.Desc.K5.Honest.Law.ReadSF
import Johnson.Desc.K5.Honest.Law.ReadSD
import Johnson.Desc.K5.Honest.Law.ReadHB
import Johnson.Desc.First.Att.Claims.EndsH

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (W1 MaxP geoOf)
open Inst.Model.AttSeg (Raw Dim Pub Calls Step rd2 rd3 eqT sh qryV keyV rvKC Aext)
open K5Law (maxBack InLong)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- Where there is a pair, a head of keys and values has a query head. -/
theorem heads_pos' {S : Attention.Shape} {b : ℕ} (hb : b < S.NP) : 0 < S.HA := by
  rcases Nat.eq_zero_or_pos S.HA with e | e
  · have hb' : b < S.Lam * S.HA := hb
    rw [e, Nat.mul_zero] at hb'
    exact absurd hb' (Nat.not_lt_zero _)
  · exact e

variable (A : AttAt ρ W tl K3 M h lid cf fs) (w : K5In) (hc : CellsAre ρ h.S M w)
include A hc

/-- **The score at the index, first end value of pair b.** m.scF.r: the sumcheck's challenges. The
right side is the summand's end value number 2 b there (`sSF_endAt`, Law/ReadSF.lean). CONDITIONAL
on what the head lists. -/
theorem endsF_meets {m : MaxP} (hx : h.x = maxBack m) (hr : m.scF.r.size = h.S.nvF) {b : ℕ}
    (hb : b < h.S.NP) (Tb : QaAt tl h h.t.qF (m.rc (geoOf h.S)) (eqTab (m.ri (geoOf h.S))))
    (I : InLong h h.t.qF h.S.atQ (b / h.S.HA) (fun g => g * h.S.HA + b % h.S.HA)
      (m.rc (geoOf h.S))) :
    (Fo.readHeadT h K3 h.t.qF h.S.atQ (h.x.rg h.S) (h.x.rc h.S) (b / h.S.HA)
      (b % h.S.HA)).value ρ W =
      ρ.val (under3 h.S.cf.lt h.S.cf.lgk h.S.cf.ldh m.scF.r (sfTab (geoOf h.S) w (2 * b))) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  have hlt : h.S.cf.lt = (L5.dimOf h.S).lT := H.lt
  have hr' : m.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh := hr
  have s1 : (m.rg (geoOf h.S)).size = h.S.cf.lgk := by
    show (m.scF.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_extract_le _ (by omega)]
    omega
  have s2 : (m.ri (geoOf h.S)).size = h.S.cf.lt := by
    show (m.scF.r.extract 0 h.S.cf.lt).size = _
    rw [size_extract_le _ (by omega)]
    omega
  have s3 : (m.rc (geoOf h.S)).size = h.S.cf.ldh := by
    show (m.scF.r.extract (h.S.cf.lt + h.S.cf.lgk) m.scF.r.size).size = _
    rw [size_extract_le _ (Nat.le_refl _)]
    omega
  have sT := size_eqTab_tok (P := ⟨h.S, default⟩) (s2.trans H.lt)
  rw [hx]
  show (Fo.readHeadT h K3 h.t.qF h.S.atQ (m.rg (geoOf h.S)) (m.rc (geoOf h.S)) (b / h.S.HA)
    (b % h.S.HA)).value ρ W = _
  rw [K5Law.readHeadT_qry A Tb (sT.trans H.T.symm) (Nat.le_of_eq s1.symm) s3
    (Nat.mod_lt _ (heads_pos' hb)) I, Nat.div_add_mod' b h.S.HA]
  refine (rd3_on _ _ _ _ fun g hg i hi n hn => cells_qry hc hb hg hi hn).trans ?_
  refine Eq.trans ?_ (sfA_reads ρ (P := ⟨h.S, default⟩) H w ⟨fun _ => 0, 0, 0⟩
    ⟨fun _ => 0, 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
      fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
    (x := m.scF.r) (by
      show _ = (L5.dimOf h.S).lT + h.S.cf.lgk + h.S.cf.ldh
      rw [← hlt]
      exact hr') b).symm
  rw [Cb.Pv.Att.aext16]
  refine rd3_congr _ (fun j hj => ?_) (fun i hi => ?_) (fun j hj => ?_) _
  · have hj' : j < h.S.cf.lgk := hj
    show pt ρ (m.scF.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j =
      pt ρ m.scF.r ((L5.dimOf h.S).lT + j)
    rw [← hlt]
    exact pt_extract ρ _ _ _ j (by omega)
  · refine read_eqTab ρ (s2.trans hlt) (fun j hj => ?_) (by rw [← Dim.T_eq]; exact hi)
    show pt ρ (m.scF.r.extract 0 h.S.cf.lt) j = pt ρ m.scF.r j
    rw [pt_extract ρ _ 0 _ j (by rw [hlt]; omega), Nat.zero_add]
  · have hj' : j < h.S.cf.ldh := hj
    show pt ρ (m.scF.r.extract (h.S.cf.lt + h.S.cf.lgk) m.scF.r.size) j =
      pt ρ m.scF.r ((L5.dimOf h.S).lT + h.S.cf.lgk + j)
    rw [← hlt]
    exact pt_extract ρ _ _ _ j (by omega)

/-- **The key at the index, the end value of cell k of pair b's index.** m.scd.r: the sumcheck's
challenges. The right side is the summand's end value number Lam + b lt + k there (`sd_endAt_ib`,
Law/ReadSD.lean). CONDITIONAL on what the head lists. -/
theorem endsK_bit_meets {m : MaxP} (hx : h.x = maxBack m)
    (hr : m.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk) {b k : ℕ} (hb : b < h.S.NP)
    (hk : k < h.S.cf.lt) (Tb : AhAt tl h h.t.hPi (eqTab (m.pi (geoOf h.S))))
    (hin : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 1,
      h.S.oIb + (l * h.S.Lam + b / h.S.HA) * (h.S.cf.lt * h.S.cf.H) +
        (k * h.S.cf.H + g * h.S.HA + b % h.S.HA) < (h.t.tabLen.lookup h.t.hPi).getD 0) :
    (K5Law.endsK h K3 (h.S.Lam + b * h.S.cf.lt + k)).value ρ W =
      ρ.val (ibpAt (geoOf h.S) w m.scd.r k b) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  have s1 : (m.pg (geoOf h.S)).size = h.S.cf.lgk := by
    show (m.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_extract_le _ (by omega)]
    omega
  have s2 : (m.pi (geoOf h.S)).size = h.S.cf.lt := by
    show (m.scd.r.extract (h.S.cf.lt + h.S.cf.lgk) (2 * h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_extract_le _ (by omega)]
    omega
  rw [K5Law.endsK_bit h K3 b hk, hx]
  show (Fo.readIndexBitF h K3 h.t.hPi (m.pg (geoOf h.S)) (b / h.S.HA) (b % h.S.HA) k).value ρ W = _
  rw [K5Law.readIndexBitF_rd2 A Tb (Nat.le_of_eq s1.symm) (Nat.mod_lt _ (heads_pos' hb)) hin,
    Nat.div_add_mod' b h.S.HA]
  refine (rd2_on _ _ _ fun g hg i hi =>
    hc (.ib k b g i) ⟨hk.trans_eq H.lt, hb, hg, hi⟩).trans ?_
  exact (read_row ρ (D := L5.dimOf h.S) (zg := m.pg (geoOf h.S))
    (tk := P.eqTab (m.pi (geoOf h.S))) (f := w.ibit k b)
    (a := Inst.Model.AttSeg.ibV (tOf ρ w) k b) s1 (fun _ _ => rfl)
    (size_eqTab_tok (P := ⟨h.S, default⟩) (s2.trans H.lt)) (fun _ _ => rfl)
    (read_ibit ρ w k b)).symm

/-- **The key at the index, end value number lam: the keys of layer lam.** m.scd.r: the sumcheck's
challenges; m.scF.r: those of the score at the index, whose last coordinates are the channel point.
The right side is the summand's end value number lam there (`sd_endAt_kc`, Law/ReadSD.lean).
CONDITIONAL on what the head lists. -/
theorem endsK_lam_meets {m : MaxP} (hx : h.x = maxBack m) (hrF : m.scF.r.size = h.S.nvF)
    (hr : m.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk) {lam : ℕ} (hl : lam < h.S.Lam)
    (Tb : QaAt tl h h.t.qKx (m.rc (geoOf h.S)) (eqTab (m.pj (geoOf h.S))))
    (I : InLong h h.t.qKx h.S.atK lam (fun g => g) (m.rc (geoOf h.S))) :
    (K5Law.endsK h K3 lam).value ρ W =
      ρ.val (kcAt (geoOf h.S) m.scd.r (kcTab (geoOf h.S) w m.scF.r lam)) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  have hlt : h.S.cf.lt = (L5.dimOf h.S).lT := H.lt
  have hrF' : m.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh := hrF
  have s1 : (m.pg (geoOf h.S)).size = h.S.cf.lgk := by
    show (m.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_extract_le _ (by omega)]
    omega
  have s2 : (m.pj (geoOf h.S)).size = h.S.cf.lt := by
    show (m.scd.r.extract 0 h.S.cf.lt).size = _
    rw [size_extract_le _ (by omega)]
    omega
  have s3 : (m.rc (geoOf h.S)).size = h.S.cf.ldh := by
    show (m.scF.r.extract (h.S.cf.lt + h.S.cf.lgk) m.scF.r.size).size = _
    rw [size_extract_le _ (Nat.le_refl _)]
    omega
  have sT := size_eqTab_tok (P := ⟨h.S, default⟩) (s2.trans H.lt)
  have Q : KeyPub ρ (⟨h.S, default⟩ : Pub5) m.scF.r #[]
      ⟨fun _ => 0, 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
        pt ρ #[], fun _ => 0, pt ρ m.scF.r, fun k => pt ρ m.scF.r ((L5.dimOf h.S).lT + k),
        fun k => pt ρ m.scF.r ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg + k)⟩ :=
    ⟨by
      show _ = (L5.dimOf h.S).lT + h.S.cf.lgk + h.S.cf.ldh
      rw [← hlt]
      exact hrF', fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have e := kc_reads ρ H w Q (x := m.scd.r.toList) (by
    rw [Array.length_toList, hr]
    show _ = (L5.dimOf h.S).lT + h.S.cf.lgk + (L5.dimOf h.S).lT
    rw [← hlt]
    omega) (lam := lam) hl
  rw [sd_endAt_kc _ w _ _ _ hl, Array.toArray_toList, ptL_eq, Array.toArray_toList] at e
  rw [K5Law.endsK_lam h K3 hl, hx]
  show (Fo.readGroupT h K3 h.t.qKx h.S.atK (m.pg (geoOf h.S)) (m.rc (geoOf h.S)) lam).value ρ W = _
  rw [K5Law.readGroupT_key A Tb (sT.trans H.T.symm) (Nat.le_of_eq s1.symm) s3 I]
  refine (rd3_on _ _ _ _ fun g hg i hi n hn => cells_key hc hl hg hi hn).trans ?_
  refine Eq.trans ?_ e.symm
  unfold rvKC
  refine rd3_congr _ (fun j hj => ?_) (fun i hi => ?_) (fun j hj => ?_) _
  · have hj' : j < h.S.cf.lgk := hj
    show pt ρ (m.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j =
      pt ρ m.scd.r ((L5.dimOf h.S).lT + j)
    rw [← hlt]
    exact pt_extract ρ _ _ _ j (by omega)
  · refine read_eqTab ρ (s2.trans hlt) (fun j hj => ?_) (by rw [← Dim.T_eq]; exact hi)
    show pt ρ (m.scd.r.extract 0 h.S.cf.lt) j = pt ρ m.scd.r j
    rw [pt_extract ρ _ 0 _ j (by rw [hlt]; omega), Nat.zero_add]
  · have hj' : j < h.S.cf.ldh := hj
    show pt ρ (m.scF.r.extract (h.S.cf.lt + h.S.cf.lgk) m.scF.r.size) j =
      pt ρ m.scF.r ((L5.dimOf h.S).lT + h.S.cf.lgk + j)
    rw [← hlt]
    exact pt_extract ρ _ _ _ j (by omega)

/-- **"The index's cells are bits".** m.scH.r: the sumcheck's challenges. The right side is the
summand's end value number j there (`sHB_even`, `sHB_odd`, Law/ReadHB.lean). CONDITIONAL on what the
head lists. -/
theorem endsH_meets {m : MaxP} (hx : h.x = maxBack m) (hr : m.scH.r.size = h.S.nvH) {j : ℕ}
    (hj : j < 2 * h.S.NP) (Tb : AhAt tl h h.t.hR2 (eqTab (m.ri2 (geoOf h.S))))
    (hin : ∀ k < h.S.cf.lt, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 1,
      h.S.oIb + (l * h.S.Lam + j / 2 / h.S.HA) * (h.S.cf.lt * h.S.cf.H) +
        (k * h.S.cf.H + g * h.S.HA + j / 2 % h.S.HA) < (h.t.tabLen.lookup h.t.hR2).getD 0) :
    (K5Law.endsH h K3 j).value ρ W =
      ρ.val (if j % 2 = 0 then hbA (geoOf h.S) w m.scH.r (j / 2)
        else subE (hbA (geoOf h.S) w m.scH.r (j / 2)) oneE) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  have hlt : h.S.cf.lt = (L5.dimOf h.S).lT := H.lt
  have hb : j / 2 < h.S.NP := by omega
  obtain ⟨S0, hS0⟩ := L5.shape_of_hid A.shape
  have h16 : h.S.cf.lt ≤ 16 := by
    rw [(L5.shaped_of_hid A.shape).cfg]
    exact lt_le_16 hS0
  have hr' : m.scH.r.size = h.S.cf.lt + h.S.cf.lgk + 4 := hr
  have e0 : (K5Law.bitsF h K3 (j / 2)).value ρ W = ρ.val (hbA (geoOf h.S) w m.scH.r (j / 2)) := by
    rw [K5Law.bitsF_ext A (by rw [hx]; exact hr) hb (by rw [hx]; exact Tb) hin, hx]
    show Blocks.ext _ _ (pt ρ m.scH.r) = _
    refine Eq.trans ?_ (hbA_reads ρ (P := ⟨h.S, default⟩) H w (by rw [← hlt]; omega)
      (x := m.scH.r) (by
        show _ = (L5.dimOf h.S).lT + h.S.cf.lgk + 4
        rw [← hlt]
        exact hr') (j / 2)).symm
    refine Blocks.ext_congr (fun X hX => ?_) _
    unfold Cb.Pv.Att.bitCube
    by_cases c : X % 2 ^ 4 < (L5.dimOf h.S).lT
    · rw [if_pos c, if_pos c]
      have hG : 0 < (L5.dimOf h.S).nG := Nat.two_pow_pos _
      refine hc (.ib _ _ _ _) ⟨c, hb, Nat.mod_lt _ hG, ?_⟩
      rw [Dim.T_eq]
      have h1 : X / 2 ^ 4 < 2 ^ ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg) :=
        Nat.div_lt_of_lt_mul (by rw [← pow_add, Nat.add_comm 4]; exact hX)
      exact Nat.div_lt_of_lt_mul (by
        show _ < 2 ^ (L5.dimOf h.S).lg * 2 ^ (L5.dimOf h.S).lT
        rw [← pow_add, Nat.add_comm (L5.dimOf h.S).lg]
        exact h1)
    · rw [if_neg c, if_neg c]
  unfold K5Law.endsH
  by_cases e : j % 2 = 0
  · rw [if_pos e, if_pos e, e0]
  · rw [if_neg e, if_neg e, Aff.value_sub, Aff.value_ofConst, e0, ρ.sub]

end H2K5.Honest

#print axioms H2K5.Honest.heads_pos'
#print axioms H2K5.Honest.endsF_meets
#print axioms H2K5.Honest.endsK_bit_meets
#print axioms H2K5.Honest.endsK_lam_meets
#print axioms H2K5.Honest.endsH_meets
